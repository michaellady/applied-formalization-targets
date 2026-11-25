import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Massart's finite class lemma

For finitely many vectors `a k : ι → ℝ` (`k` in a finite nonempty type `κ`), the
(unnormalised) Rademacher average is

`rademacherAvg a = 2^{-n} ∑_{σ ∈ {±1}^n} max_k ∑_i σ_i (a k i)`,  `n = |ι|`.

* `rademacherAvg_le` (Massart's finite class lemma): if `∑_i (a k i)² ≤ R²` for all `k`, then
  `rademacherAvg a ≤ R √(2 log |κ|)`.
* `rademacherAvg_le_of_abs_le`: if `|a k i| ≤ B` for all `k, i`, then
  `rademacherAvg a ≤ B √(2 n log |κ|)`.

Signs are encoded by `Bool` (`true ↦ 1`, `false ↦ -1`). The usual empirical Rademacher
complexity of a class on a sample of size `n` is `rademacherAvg a / n`.
-/

open Finset

namespace Applied.Learning

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]

/-- The sign `±1` encoded by a Boolean. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

/-- The unnormalised Rademacher average of the finite family of vectors `a`: the average over
all sign patterns `σ` of `max_k ∑ i, σ i * a k i`. -/
noncomputable def rademacherAvg (a : κ → ι → ℝ) : ℝ :=
  (∑ σ : ι → Bool, univ.sup' univ_nonempty fun k => ∑ i, boolSign (σ i) * a k i)
    / 2 ^ Fintype.card ι

/-- Optimising `L / t + t Q / 2` over `t > 0`. -/
lemma le_sqrt_of_forall_le {z L Q : ℝ} (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (h : ∀ t : ℝ, 0 < t → z ≤ L / t + t * Q / 2) : z ≤ √(2 * L * Q) := by
  by_contra hcon
  rw [not_le] at hcon
  have hz : 0 < z := lt_of_le_of_lt (Real.sqrt_nonneg _) hcon
  rcases eq_or_lt_of_le hQ with hQ0 | hQ0
  · subst hQ0
    rcases eq_or_lt_of_le hL with hL0 | hL0
    · subst hL0
      have := h 1 one_pos
      simp at this
      linarith
    · have := h (2 * L / z) (by positivity)
      have e : L / (2 * L / z) + 2 * L / z * 0 / 2 = z / 2 := by
        rw [mul_zero, zero_div, add_zero]; field_simp
      rw [e] at this
      linarith
  · have := h (z / Q) (by positivity)
    have e : L / (z / Q) + z / Q * Q / 2 = L * Q / z + z / 2 := by field_simp
    rw [e] at this
    have h2 : z / 2 ≤ L * Q / z := by linarith
    rw [le_div_iff₀ hz] at h2
    have h3 : z ^ 2 ≤ 2 * L * Q := by nlinarith
    exact absurd (Real.le_sqrt_of_sq_le h3) (not_le.mpr hcon)

/-- The moment generating function of a Rademacher sum. -/
lemma sum_exp_sign_le (t : ℝ) (b : ι → ℝ) :
    ∑ σ : ι → Bool, Real.exp (t * ∑ i, boolSign (σ i) * b i)
      ≤ 2 ^ Fintype.card ι * Real.exp (t ^ 2 * (∑ i, b i ^ 2) / 2) := by
  have h1 : ∑ σ : ι → Bool, Real.exp (t * ∑ i, boolSign (σ i) * b i)
      = ∏ i, ∑ s : Bool, Real.exp (t * (boolSign s * b i)) := by
    rw [prod_univ_sum, Fintype.piFinset_univ]
    refine sum_congr rfl fun σ _ => ?_
    rw [mul_sum, Real.exp_sum]
  have h2 : ∀ i, ∑ s : Bool, Real.exp (t * (boolSign s * b i))
      ≤ 2 * Real.exp (t ^ 2 * b i ^ 2 / 2) := by
    intro i
    have hc := Real.cosh_le_exp_half_sq (t * b i)
    rw [Real.cosh_eq] at hc
    have e : ∑ s : Bool, Real.exp (t * (boolSign s * b i))
        = Real.exp (t * b i) + Real.exp (-(t * b i)) := by
      rw [Fintype.sum_bool]
      simp [boolSign]
    rw [e]
    have e2 : (t * b i) ^ 2 / 2 = t ^ 2 * b i ^ 2 / 2 := by ring
    rw [e2] at hc
    linarith
  rw [h1]
  calc ∏ i, ∑ s : Bool, Real.exp (t * (boolSign s * b i))
      ≤ ∏ i : ι, (2 * Real.exp (t ^ 2 * b i ^ 2 / 2)) :=
        Finset.prod_le_prod₀ (fun i _ => sum_nonneg fun s _ => (Real.exp_pos _).le) fun i _ => h2 i
    _ = 2 ^ Fintype.card ι * Real.exp (t ^ 2 * (∑ i, b i ^ 2) / 2) := by
        rw [prod_mul_distrib, prod_const, card_univ, ← Real.exp_sum]
        congr 2
        rw [mul_sum, sum_div]

/-- **Massart's finite class lemma.** If every vector of the finite family `a` has squared
Euclidean norm at most `R²` (with `R ≥ 0`), then its Rademacher average is at most
`R √(2 log |κ|)`. -/
theorem rademacherAvg_le (a : κ → ι → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (ha : ∀ k, ∑ i, a k i ^ 2 ≤ R ^ 2) :
    rademacherAvg a ≤ R * √(2 * Real.log (Fintype.card κ)) := by
  set n := Fintype.card ι with hn
  set Z : (ι → Bool) → ℝ := fun σ => univ.sup' univ_nonempty fun k => ∑ i, boolSign (σ i) * a k i
    with hZ
  have hcard : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos (α := κ)
  have hlog : 0 ≤ Real.log (Fintype.card κ) := Real.log_nonneg hcard
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have key : ∀ t : ℝ, 0 < t →
      rademacherAvg a ≤ Real.log (Fintype.card κ) / t + t * R ^ 2 / 2 := by
    intro t ht
    -- Jensen
    have hJ : Real.exp (t * rademacherAvg a) ≤ ∑ σ : ι → Bool, (1 / 2 ^ n) * Real.exp (t * Z σ) := by
      have hw : ∑ _σ : ι → Bool, (1 / 2 ^ n : ℝ) = 1 := by
        rw [sum_const, card_univ, Fintype.card_pi, prod_const, card_univ, Fintype.card_bool,
          nsmul_eq_mul]
        push_cast
        rw [← hn]
        field_simp
      have := convexOn_exp.map_sum_le (t := (univ : Finset (ι → Bool)))
        (w := fun _ => (1 / 2 ^ n : ℝ)) (p := fun σ => t * Z σ)
        (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
      simp only [smul_eq_mul] at this
      refine le_trans (le_of_eq ?_) this
      congr 1
      rw [rademacherAvg, ← mul_sum, ← mul_sum]
      ring
    -- the maximum is at most the sum
    have hmax : ∀ σ, Real.exp (t * Z σ) ≤ ∑ k, Real.exp (t * ∑ i, boolSign (σ i) * a k i) := by
      intro σ
      obtain ⟨k, -, hk⟩ := exists_mem_eq_sup' (univ_nonempty (α := κ))
        fun k => ∑ i, boolSign (σ i) * a k i
      rw [hZ]
      simp only
      rw [hk]
      exact single_le_sum (f := fun k => Real.exp (t * ∑ i, boolSign (σ i) * a k i))
        (fun _ _ => (Real.exp_pos _).le) (mem_univ k)
    have hsum : ∑ σ : ι → Bool, Real.exp (t * Z σ)
        ≤ Fintype.card κ * (2 ^ n * Real.exp (t ^ 2 * R ^ 2 / 2)) := by
      calc ∑ σ : ι → Bool, Real.exp (t * Z σ)
          ≤ ∑ σ : ι → Bool, ∑ k, Real.exp (t * ∑ i, boolSign (σ i) * a k i) :=
            sum_le_sum fun σ _ => hmax σ
        _ = ∑ k, ∑ σ : ι → Bool, Real.exp (t * ∑ i, boolSign (σ i) * a k i) := sum_comm
        _ ≤ ∑ _k : κ, 2 ^ n * Real.exp (t ^ 2 * R ^ 2 / 2) := by
            refine sum_le_sum fun k _ => (sum_exp_sign_le t (a k)).trans ?_
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) h2n.le
            have := mul_le_mul_of_nonneg_left (ha k) (sq_nonneg t)
            linarith
        _ = Fintype.card κ * (2 ^ n * Real.exp (t ^ 2 * R ^ 2 / 2)) := by
            rw [sum_const, card_univ, nsmul_eq_mul]
    have hfinal : Real.exp (t * rademacherAvg a)
        ≤ Fintype.card κ * Real.exp (t ^ 2 * R ^ 2 / 2) := by
      refine hJ.trans ?_
      rw [← mul_sum]
      calc 1 / 2 ^ n * ∑ σ : ι → Bool, Real.exp (t * Z σ)
          ≤ 1 / 2 ^ n * (Fintype.card κ * (2 ^ n * Real.exp (t ^ 2 * R ^ 2 / 2))) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = Fintype.card κ * Real.exp (t ^ 2 * R ^ 2 / 2) := by field_simp
    have hl := Real.log_le_log (Real.exp_pos _) hfinal
    rw [Real.log_exp, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hl
    have e : Real.log (Fintype.card κ) / t + t * R ^ 2 / 2
        = (Real.log (Fintype.card κ) + t ^ 2 * R ^ 2 / 2) / t := by field_simp
    rw [e, le_div_iff₀ ht]
    linarith
  have h := le_sqrt_of_forall_le hlog (sq_nonneg R) key
  refine h.trans (le_of_eq ?_)
  have e : 2 * Real.log (Fintype.card κ) * R ^ 2 = R ^ 2 * (2 * Real.log (Fintype.card κ)) := by
    ring
  rw [e, Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR]

/-- **Massart's lemma for uniformly bounded vectors.** If `|a k i| ≤ B` for all `k` and `i`,
then the Rademacher average is at most `B √(2 n log |κ|)`, where `n = |ι|`. -/
theorem rademacherAvg_le_of_abs_le (a : κ → ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ k i, |a k i| ≤ B) :
    rademacherAvg a ≤ B * √(2 * Fintype.card ι * Real.log (Fintype.card κ)) := by
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have h := rademacherAvg_le a (B * √(Fintype.card ι)) (by positivity) (fun k => by
    rw [mul_pow, Real.sq_sqrt hn]
    have : ∑ i, a k i ^ 2 ≤ ∑ _i : ι, B ^ 2 :=
      sum_le_sum fun i _ => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (ha k i) 2
    rw [sum_const, card_univ, nsmul_eq_mul] at this
    linarith)
  refine h.trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.sqrt_mul hn]
  congr 2
  ring

end Applied.Learning
