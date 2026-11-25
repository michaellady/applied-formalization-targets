import Mathlib.Tactic

/-!
# The Vickrey–Clarke–Groves mechanism with Clarke pivot payments is truthful

A finite nonempty set `A` of outcomes and finitely many agents `i : ι`. Agent `i` has a
valuation `v i : A → ℝ` and reports a valuation `b i : A → ℝ`. The mechanism chooses an outcome
`f b` maximising the reported welfare `∑ j, b j a` and charges agent `i` the *Clarke pivot
payment*: the maximal welfare the other agents could get if `i`'s report were ignored, minus
the other agents' (reported) welfare at the chosen outcome.

Ties are handled by an arbitrary choice rule: `f : (ι → A → ℝ) → A` is any function that always
selects a welfare maximiser (`IsWelfareMaximizer f`). All results hold for every such rule;
`exists_isWelfareMaximizer` shows that such rules exist.

* `vcg_truthful`: reporting one's true valuation is a weakly dominant strategy.
* `clarkePayment_nonneg`: payments are non-negative (no positive transfers).
* `vcg_truthful_utility_nonneg`: a truthful agent with a non-negative valuation gets
  non-negative utility (individual rationality).
* `isWelfareMaximizer_truthful`: under truthful reports the outcome maximises true welfare.
-/

open Finset Function

namespace Applied.Economics

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]

/-- Total welfare of outcome `a` under the valuation profile `b`. -/
def socialWelfare (b : ι → A → ℝ) (a : A) : ℝ := ∑ j, b j a

/-- Welfare at outcome `a` of the agents other than `i`. -/
def othersWelfare (b : ι → A → ℝ) (i : ι) (a : A) : ℝ := ∑ j ∈ univ.erase i, b j a

/-- The best welfare the agents other than `i` can get over all outcomes. -/
noncomputable def maxOthersWelfare (b : ι → A → ℝ) (i : ι) : ℝ :=
  univ.sup' univ_nonempty (othersWelfare b i)

/-- An outcome rule that always selects a welfare-maximising outcome for the reported
valuations. Different rules differ only in how they break ties. -/
def IsWelfareMaximizer (f : (ι → A → ℝ) → A) : Prop :=
  ∀ (b : ι → A → ℝ) (a : A), socialWelfare b a ≤ socialWelfare b (f b)

/-- The Clarke pivot payment of agent `i` under reports `b`: the externality `i` imposes on
the others. -/
noncomputable def clarkePayment (f : (ι → A → ℝ) → A) (b : ι → A → ℝ) (i : ι) : ℝ :=
  maxOthersWelfare b i - othersWelfare b i (f b)

/-- Quasi-linear utility of agent `i` with true valuation `v i` when the reports are `b`. -/
noncomputable def vcgUtility (f : (ι → A → ℝ) → A) (v b : ι → A → ℝ) (i : ι) : ℝ :=
  v i (f b) - clarkePayment f b i

omit [Fintype A] [Nonempty A] in
/-- Reported social welfare of an outcome is agent `i`'s reported value plus the reported
welfare of the others. -/
lemma socialWelfare_eq_add_othersWelfare (b : ι → A → ℝ) (i : ι) (a : A) :
    socialWelfare b a = b i a + othersWelfare b i a := by
  unfold socialWelfare othersWelfare
  exact (add_sum_erase univ (fun j => b j a) (mem_univ i)).symm

omit [Fintype A] [Nonempty A] in
/-- The others' welfare does not depend on one's own report. -/
lemma othersWelfare_update (b : ι → A → ℝ) (i : ι) (x : A → ℝ) (a : A) :
    othersWelfare (update b i x) i a = othersWelfare b i a := by
  unfold othersWelfare
  exact sum_congr rfl (fun j hj => by rw [update_of_ne (mem_erase.1 hj).1])

/-- The largest reported welfare of the agents other than `i` does not depend on `i`'s report. -/
lemma maxOthersWelfare_update (b : ι → A → ℝ) (i : ι) (x : A → ℝ) :
    maxOthersWelfare (update b i x) i = maxOthersWelfare b i := by
  unfold maxOthersWelfare
  exact sup'_congr _ rfl (fun a _ => othersWelfare_update b i x a)

/-- The others' welfare at any outcome is at most its maximum over all outcomes. -/
lemma othersWelfare_le_max (b : ι → A → ℝ) (i : ι) (a : A) :
    othersWelfare b i a ≤ maxOthersWelfare b i :=
  le_sup' (othersWelfare b i) (mem_univ a)

/-- The maximum of the others' welfare is attained at some outcome. -/
lemma exists_othersWelfare_eq_max (b : ι → A → ℝ) (i : ι) :
    ∃ a, othersWelfare b i a = maxOthersWelfare b i := by
  obtain ⟨a, -, ha⟩ := exists_mem_eq_sup' univ_nonempty (othersWelfare b i)
  exact ⟨a, ha.symm⟩

omit [DecidableEq ι] [Fintype A] [Nonempty A] in
/-- Welfare-maximising outcome rules exist. -/
theorem exists_isWelfareMaximizer [Finite A] [Nonempty A] :
    ∃ f : (ι → A → ℝ) → A, IsWelfareMaximizer f := by
  have h : ∀ b : ι → A → ℝ, ∃ a₀, ∀ a, socialWelfare b a ≤ socialWelfare b a₀ :=
    fun b => Finite.exists_max (socialWelfare b)
  choose f hf using h
  exact ⟨f, hf⟩

/-- **Truthfulness of VCG.** For every welfare-maximising outcome rule, every agent `i`, every
profile `b` of reports (only the others' entries matter) and every alternative report `x`,
reporting the true valuation `v i` gives agent `i` at least as much utility as reporting `x`. -/
theorem vcg_truthful (f : (ι → A → ℝ) → A) (hf : IsWelfareMaximizer f) (v b : ι → A → ℝ)
    (i : ι) (x : A → ℝ) :
    vcgUtility f v (update b i x) i ≤ vcgUtility f v (update b i (v i)) i := by
  unfold vcgUtility clarkePayment
  rw [maxOthersWelfare_update, maxOthersWelfare_update, othersWelfare_update,
    othersWelfare_update]
  have h := hf (update b i (v i)) (f (update b i x))
  rw [socialWelfare_eq_add_othersWelfare _ i, socialWelfare_eq_add_othersWelfare _ i, update_self,
    othersWelfare_update, othersWelfare_update] at h
  linarith

/-- Clarke pivot payments are never negative: the mechanism makes no positive transfers.
(No sign condition on the valuations is needed for this.) -/
theorem clarkePayment_nonneg (f : (ι → A → ℝ) → A) (b : ι → A → ℝ) (i : ι) :
    0 ≤ clarkePayment f b i :=
  sub_nonneg.2 (othersWelfare_le_max b i (f b))

/-- **Individual rationality of VCG.** A truthful agent whose valuation is non-negative on
every outcome never gets negative utility, whatever the others report. -/
theorem vcg_truthful_utility_nonneg (f : (ι → A → ℝ) → A) (hf : IsWelfareMaximizer f)
    (v b : ι → A → ℝ) (i : ι) (hv : ∀ a, 0 ≤ v i a) :
    0 ≤ vcgUtility f v (update b i (v i)) i := by
  unfold vcgUtility clarkePayment
  rw [maxOthersWelfare_update, othersWelfare_update]
  obtain ⟨a, ha⟩ := exists_othersWelfare_eq_max b i
  have h := hf (update b i (v i)) a
  rw [socialWelfare_eq_add_othersWelfare _ i, socialWelfare_eq_add_othersWelfare _ i, update_self,
    othersWelfare_update, othersWelfare_update] at h
  have := hv a
  linarith

omit [DecidableEq ι] [Nonempty A] [Fintype A] in
/-- Under truthful reports the chosen outcome maximises the true welfare (efficiency). This is
immediate from the definition of the outcome rule and is recorded for completeness. -/
theorem isWelfareMaximizer_truthful (f : (ι → A → ℝ) → A) (hf : IsWelfareMaximizer f)
    (v : ι → A → ℝ) (a : A) : socialWelfare v a ≤ socialWelfare v (f v) :=
  hf v a

end Applied.Economics
