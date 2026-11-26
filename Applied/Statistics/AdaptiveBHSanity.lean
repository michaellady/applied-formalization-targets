import Applied.Statistics.AdaptiveBH
import Applied.Statistics.MultipleTestingSanity

/-!
# Sanity checks for the adaptive Benjamini–Hochberg results

The hypotheses of `fdr_storeyBH_le`, `fdr_tstReject_le` and `fdr_adaptiveBH_le` are satisfiable
and the conclusions are not trivial. The model is the unit square `Fin 2 → ℝ` with the uniform
law (`Sanity.unifP`): two independent, exactly uniform p-values.

* `storeyBH_unif`, `tst_unif`, `adaptiveBH_unif`: the three theorems apply, with both
  hypotheses true nulls or with one.
* `tst_unif_lower`: with both hypotheses true nulls, the false discovery rate of the two-stage
  procedure at level `α ≥ 0` is at least `α / (1 + α)`, the level of its first stage. So the
  quantity bounded by `α` in `fdr_tstReject_le` is positive for `α > 0`, and the bound cannot
  be improved by more than the factor `1 + α`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting.Sanity

lemma unif_isValid (i : Fin 2) : IsValidPValue unifP fun ω : Fin 2 → ℝ => ω i :=
  (unif_isUniform i).isValidPValue

lemma unif_indep_update (i : Fin 2) :
    IndepFun (fun ω : Fin 2 → ℝ => ω i)
      (fun ω : Fin 2 → ℝ => Function.update (fun j => ω j) i 0) unifP :=
  indepFun_update_of_iIndepFun unifP _ measurable_pi_apply unif_iIndepFun i

/-- **Storey's adaptive procedure, non-vacuous**: any set of true nulls, any `λ ∈ [0, 1]`. -/
theorem storeyBH_unif (α lam : ℝ) (hα : 0 ≤ α) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (H₀ : Finset (Fin 2)) :
    fdr unifP H₀ (fun ω : Fin 2 → ℝ => storeyBH α lam fun j => ω j) ≤ ENNReal.ofReal α :=
  fdr_storeyBH_le unifP hα hlam0 hlam1 (fun (i : Fin 2) (ω : Fin 2 → ℝ) => ω i)
    measurable_pi_apply H₀ (fun i _ => unif_isValid i) (fun i _ => unif_indep_update i)

/-- **Two-stage procedure, non-vacuous.** -/
theorem tst_unif (α : ℝ) (hα : 0 ≤ α) (H₀ : Finset (Fin 2)) :
    fdr unifP H₀ (fun ω : Fin 2 → ℝ => tstReject α fun j => ω j) ≤ ENNReal.ofReal α :=
  fdr_tstReject_le unifP hα (fun (i : Fin 2) (ω : Fin 2 → ℝ) => ω i)
    measurable_pi_apply H₀ (fun i _ => unif_isValid i) (fun i _ => unif_indep_update i)

/-- With every hypothesis a true null, the false discovery proportion is the indicator of a
rejection, hence monotone in the rejection set. -/
lemma fdp_univ_mono {ι : Type*} [Fintype ι] [DecidableEq ι] {R R' : Finset ι} (h : R ⊆ R') :
    fdp univ R ≤ fdp univ R' := by
  unfold fdp
  rw [Finset.inter_univ, Finset.inter_univ]
  rcases R.eq_empty_or_nonempty with h0 | h0
  · simp [h0]
  · have h1 : ((R.card : ℝ≥0∞)) ≠ 0 := by exact_mod_cast h0.card_pos.ne'
    have h2 : ((R'.card : ℝ≥0∞)) ≠ 0 := by exact_mod_cast (h0.mono h).card_pos.ne'
    rw [ENNReal.div_self h1 (ENNReal.natCast_ne_top _),
      ENNReal.div_self h2 (ENNReal.natCast_ne_top _)]

/-- **The bound of the two-stage theorem is not trivial**: under the global null on the unit
square, the false discovery rate of the two-stage procedure at level `α ≥ 0` lies between
`α / (1 + α)` and `α`. -/
theorem tst_unif_lower (α : ℝ) (hα0 : 0 ≤ α) :
    ENNReal.ofReal (α / (1 + α))
      ≤ fdr unifP univ (fun ω : Fin 2 → ℝ => tstReject α fun j => ω j) := by
  have h1 : (0 : ℝ) < 1 + α := by linarith
  have ha0 : 0 ≤ α / (1 + α) := by positivity
  have ha1 : α / (1 + α) ≤ 1 := by rw [div_le_one h1]; linarith
  have h := fdr_bhReject_eq unifP ha0 ha1 (fun (i : Fin 2) (ω : Fin 2 → ℝ) => ω i)
    measurable_pi_apply univ (fun i _ => unif_isUniform i) (fun i _ => unif_indep_update i)
  have h' : fdr unifP univ (fun ω : Fin 2 → ℝ => bhReject (α / (1 + α)) fun j => ω j)
      = ENNReal.ofReal (α / (1 + α)) := by
    rw [h]; congr 1; simp
  rw [← h']
  exact lintegral_mono fun ω => fdp_univ_mono (bhReject_subset_tstRejectAt ha0 _)

/-- **The general plug-in theorem, non-vacuous**: the constant estimator `G = 1` gives back the
Benjamini–Hochberg bound `α m₀ / m` (here with `m = 2`). The p-values of the model are not
non-negative everywhere, so they are clamped at `0` first; this changes nothing almost
surely. -/
theorem adaptiveBH_unif (α : ℝ) (hα : 0 ≤ α) (H₀ : Finset (Fin 2)) :
    fdr unifP H₀ (fun ω : Fin 2 → ℝ => adaptiveBH α (fun _ => 1) fun j => max (ω j) 0)
      ≤ ENNReal.ofReal (α * H₀.card / 2) := by
  have hmeas : ∀ i : Fin 2, Measurable fun ω : Fin 2 → ℝ => max (ω i) 0 :=
    fun i => (measurable_pi_apply i).max measurable_const
  have hvalid : ∀ i : Fin 2, IsValidPValue unifP fun ω : Fin 2 → ℝ => max (ω i) 0 := by
    intro i t ht
    have : {ω : Fin 2 → ℝ | max (ω i) 0 ≤ t} = {ω | ω i ≤ t} := by
      ext ω; simp [ht]
    rw [this]
    exact unif_isValid i t ht
  have hind : iIndepFun (fun (i : Fin 2) (ω : Fin 2 → ℝ) => max (ω i) 0) unifP :=
    unif_iIndepFun.comp (fun _ x => max x 0) fun _ => measurable_id.max measurable_const
  have h := fdr_adaptiveBH_le unifP hα (fun (i : Fin 2) (ω : Fin 2 → ℝ) => max (ω i) 0)
    hmeas H₀ (fun i _ => hvalid i)
    (fun i _ => indepFun_update_of_iIndepFun unifP _ hmeas hind i)
    (fun i _ ω => le_max_right _ _) (fun _ => 1) (fun _ => zero_le_one) measurable_const
    (fun _ _ _ => le_rfl)
  refine h.trans (le_of_eq ?_)
  simp only [mul_one, lintegral_const, measure_univ, Fintype.card_fin, Finset.sum_const,
    nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast H₀.card, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

end Applied.MultipleTesting.Sanity
