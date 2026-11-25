import Applied.Statistics.DobribanCertificate

/-!
# Benjamini–Hochberg exceeds its level for correlated two-sided Gaussian tests

The model of E. Dobriban, "The Benjamini–Hochberg Procedure Can Fail to Control the FDR for
Correlated Two-Sided Gaussian Tests", arXiv:2607.12208 (2026), equations (1)–(3): with `Z` and
all `ε`, `η`, `ξ` independent standard normal, and `100 N` hypotheses,

* `96 N` true nulls `(3/10) Z + (√91/10) ε`,
* `N` non-nulls `12/5 - (3/10) Z + (√91/10) η`,
* `3 N` non-nulls `22/5 - (18/25) Z + (√301/25) ξ`.

* `exists_fdr_gt`: there is `N₀` such that for every `N ≥ N₀` the Benjamini–Hochberg procedure
  at level `1/100`, applied to the two-sided p-values, has false discovery rate strictly larger
  than `0.0104`. This is Theorem 1 of the preprint; `N₀` is not explicit.
* `blk_mult`, `blk_θ`, `blk_b`, `sd_eq`: the parameters of the checked model are the ones above;
  `exists_fdr_gt_explicit` restates `exists_fdr_gt` with these numbers written out.
* `exists_gaussian_bh_fdr_gt`: the same as an instance of the general two-sided Gaussian
  setting, indexed by `Fin n`.

The proof is finite-sample: Chebyshev's inequality conditionally on the factor
(`Applied.Statistics.FactorModelBH`), a certificate over bins of the factor checked in the
kernel (`Applied.Statistics.DobribanCertificate`), and a kernel-checked table of the normal
distribution function (`Applied.Statistics.NormalTableData`). No `native_decide`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting.DobribanCert

open Applied.Statistics Applied.Statistics.NormalTable Applied.Statistics.NormalTableData
open Applied.MultipleTesting.BlockCert

local notation "Φ" => cdf (gaussianReal 0 1)

/-- Residual standard deviation of block `g`: `√(1 - b²)`. -/
noncomputable def sd (g : Fin 3) : ℝ := √(1 - (blk g).b ^ 2)

lemma blk_mult : (fun g => (blk g).mult) = ![96, 1, 3] := by
  funext g; fin_cases g <;> rfl

lemma blk_θ : (fun g => (blk g).θ) = ![0, 12 / 5, 22 / 5] := by
  funext g; fin_cases g <;> norm_num [blk, BlockQ.θ, block0, block1, block2]

lemma blk_b : (fun g => (blk g).b) = ![3 / 10, -3 / 10, -18 / 25] := by
  funext g; fin_cases g <;> norm_num [blk, BlockQ.b, block0, block1, block2]

lemma blk_b_sq_lt (g : Fin 3) : (blk g).b ^ 2 < 1 := by
  have hb : (blk g).b = (![3 / 10, -3 / 10, -18 / 25] : Fin 3 → ℝ) g := congrFun blk_b g
  rw [hb]
  fin_cases g <;> norm_num

lemma sd_pos (g : Fin 3) : 0 < sd g :=
  Real.sqrt_pos.mpr (by linarith [blk_b_sq_lt g])

lemma b_sq_add_sd_sq (g : Fin 3) : (blk g).b ^ 2 + sd g ^ 2 = 1 := by
  rw [sd, Real.sq_sqrt (by linarith [blk_b_sq_lt g])]; ring

lemma sd_eq : sd = ![√91 / 10, √91 / 10, √301 / 25] := by
  funext g
  have hb : (blk g).b = (![3 / 10, -3 / 10, -18 / 25] : Fin 3 → ℝ) g := congrFun blk_b g
  unfold sd
  rw [hb]
  fin_cases g
  · show √(1 - (3 / 10 : ℝ) ^ 2) = √91 / 10
    rw [show (1 : ℝ) - (3 / 10) ^ 2 = 91 / 10 ^ 2 by norm_num, Real.sqrt_div (by norm_num),
      Real.sqrt_sq (by norm_num)]
  · show √(1 - (-3 / 10 : ℝ) ^ 2) = √91 / 10
    rw [show (1 : ℝ) - (-3 / 10) ^ 2 = 91 / 10 ^ 2 by norm_num, Real.sqrt_div (by norm_num),
      Real.sqrt_sq (by norm_num)]
  · show √(1 - (-18 / 25 : ℝ) ^ 2) = √301 / 25
    rw [show (1 : ℝ) - (-18 / 25) ^ 2 = 301 / 25 ^ 2 by norm_num, Real.sqrt_div (by norm_num),
      Real.sqrt_sq (by norm_num)]

/-- **Benjamini–Hochberg at level `1/100` has false discovery rate above `0.0104` in Dobriban's
model, for every sufficiently large replication number `N`** (Theorem 1 of arXiv:2607.12208). -/
theorem exists_fdr_gt : ∃ N₀ : ℕ, ∀ N ≥ N₀, ENNReal.ofReal (104 / 10000)
    < fdr (factorMeasure (blockIndex (fun g => (blk g).mult) N))
        (blockNulls (fun g => (blk g).mult) {0} N)
        (fun ω => bhReject (1 / 100)
          (factorP (fun i : blockIndex (fun g => (blk g).mult) N => (blk i.1.1).θ)
            (fun i => (blk i.1.1).b) (fun i => sd i.1.1) ω)) := by
  have hκ : (104 / 100 : ℝ) * D < ((bins.map (binTerm tab imax blk ETA)).sum : ℕ) := by
    have h1 : 104 * D < 100 * (bins.map (binTerm tab imax blk ETA)).sum :=
      lt_of_lt_of_le sum_gt (Nat.mul_le_mul_left 100 sum_le)
    have h2 : (104 : ℝ) * D < 100 * ((bins.map (binTerm tab imax blk ETA)).sum : ℕ) := by
      exact_mod_cast h1
    linarith
  have h := exists_fdr_gt_of_certOK' tab_valid imax_le sd_pos b_sq_add_sd_sq bins cert_ok
    (by norm_num) hκ
  have hα : ((αinv : ℕ) : ℝ) = 100 := by norm_num [αinv]
  rw [hα] at h
  have e : (1 : ℝ) / 100 * (104 / 100) = 104 / 10000 := by norm_num
  rw [e] at h
  exact h

/-- The same statement with the parameters written out: block sizes `96 N`, `N`, `3 N`; means
`0`, `12/5`, `22/5`; loadings `3/10`, `-3/10`, `-18/25`; residual standard deviations
`√91/10`, `√91/10`, `√301/25`; the true nulls are the statistics of the first block. -/
theorem exists_fdr_gt_explicit : ∃ N₀ : ℕ, ∀ N ≥ N₀, ENNReal.ofReal (104 / 10000)
    < fdr (factorMeasure (blockIndex ![96, 1, 3] N)) (blockNulls ![96, 1, 3] {0} N)
        (fun ω => bhReject (1 / 100)
          (factorP (fun i : blockIndex ![96, 1, 3] N => (![0, 12 / 5, 22 / 5] : Fin 3 → ℝ) i.1.1)
            (fun i => (![3 / 10, -3 / 10, -18 / 25] : Fin 3 → ℝ) i.1.1)
            (fun i => (![√91 / 10, √91 / 10, √301 / 25] : Fin 3 → ℝ) i.1.1) ω)) := by
  obtain ⟨N₀, h⟩ := exists_fdr_gt
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 := h N hN
  have hθ : ∀ g, (blk g).θ = (![0, 12 / 5, 22 / 5] : Fin 3 → ℝ) g := congrFun blk_θ
  have hb : ∀ g, (blk g).b = (![3 / 10, -3 / 10, -18 / 25] : Fin 3 → ℝ) g := congrFun blk_b
  have hs : ∀ g, sd g = (![√91 / 10, √91 / 10, √301 / 25] : Fin 3 → ℝ) g := congrFun sd_eq
  simp only [hθ, hb, hs] at h1
  have key : ∀ m : Fin 3 → ℕ, m = (fun g => (blk g).mult) → ENNReal.ofReal (104 / 10000)
      < fdr (factorMeasure (blockIndex m N)) (blockNulls m {0} N)
        (fun ω => bhReject (1 / 100)
          (factorP (fun i : blockIndex m N => (![0, 12 / 5, 22 / 5] : Fin 3 → ℝ) i.1.1)
            (fun i => (![3 / 10, -3 / 10, -18 / 25] : Fin 3 → ℝ) i.1.1)
            (fun i => (![√91 / 10, √91 / 10, √301 / 25] : Fin 3 → ℝ) i.1.1) ω)) := by
    intro m hm
    subst hm
    exact h1
  exact key _ blk_mult.symm

/-- **A jointly Gaussian vector with unit variances for which two-sided Benjamini–Hochberg at
level `1/100` has false discovery rate above `1/100`**, the true nulls being coordinates of
mean zero. -/
theorem exists_gaussian_bh_fdr_gt :
    ∃ (n : ℕ) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : Fin n → Ω → ℝ) (H₀ : Finset (Fin n)), (∀ i, Measurable (Z i)) ∧
      IsGaussian (P.map fun ω i => Z i ω) ∧ (∀ i, Var[Z i; P] = 1) ∧
      (∀ i ∈ H₀, ∫ ω, Z i ω ∂P = 0) ∧
      ENNReal.ofReal (1 / 100)
        < fdr P H₀ (fun ω => bhReject (1 / 100) fun i => 2 * (1 - Φ |Z i ω|)) := by
  obtain ⟨N₀, hN₀⟩ := exists_fdr_gt
  have hlt : ENNReal.ofReal (1 / 100) < ENNReal.ofReal (104 / 10000) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num
  refine exists_gaussian_fdr_gt_of_block (fun g => (blk g).mult) (fun g => (blk g).θ)
    (fun g => (blk g).b) sd b_sq_add_sd_sq {0} ?_ N₀ (hlt.trans (hN₀ N₀ le_rfl))
  intro g hg
  rw [Finset.mem_singleton.mp hg]
  norm_num [blk, BlockQ.θ, block0]

end Applied.MultipleTesting.DobribanCert
