import Applied.Statistics.GroupSequential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Group-sequential designs: exact alpha-spending boundaries

Looks are indexed `0, 1, …, K - 1` (as in `GroupSequential.lean`); `X k : Ω → ℝ` is the test
statistic at look `k`, and look `k` rejects when `X k ≥ c k` for a boundary `c k : EReal`.
The value `c k = ⊤` means that look `k` never rejects and `c k = ⊥` that it always rejects.

## Main results

* `exists_boundary_measureReal`: if `X` has no atoms (`P {X = x} = 0` for every `x`), then for
  every measurable `A` and every `p ∈ [0, P(A)]` there is `c : EReal` with
  `P (A ∩ {X ≥ c}) = p`. This uses continuity of `c ↦ P (A ∩ {X ≥ c})` on `ℝ` (dominated
  convergence) and the intermediate value theorem.
* `measure_biUnion_eq_sum_firstCrossing`: first-crossing events are disjoint, so the
  probability of crossing at some look *equals* the sum of the first-crossing probabilities.
* `measure_biUnion_eq_of_alphaSpending`: if every first-crossing probability equals the
  increment `s (k + 1) - s k` of a non-decreasing spending function, the type-I error equals
  `s K - s 0`.
* `exists_alphaSpending_boundaries`: if `X 0, …, X (K - 1)` have no atoms and `s` is
  non-decreasing with `s 0 = 0` and `s K ≤ 1`, there are boundaries `c` with first-crossing
  probability *exactly* `s (k + 1) - s k` at each look `k < K` (Lan and DeMets 1983).
* `exists_common_boundary`: for `K ≥ 1` looks without atoms and `0 ≤ α ≤ 1` there is one
  boundary `c` common to all looks whose overall rejection probability is exactly `α`
  (the defining property of a Pocock-type design).

Nothing is assumed about the joint law of the statistics beyond measurability and the absence
of atoms of each `X k`; the Gaussian case is in `GroupSequentialJointLaw.lean`. The boundaries
are shown to exist; they are not computed.
-/

open MeasureTheory Filter Topology Set Finset
open scoped ENNReal

namespace Applied.GroupSequential

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- For a statistic without atoms, `c ↦ P (A ∩ {X ≥ c})` is continuous on `ℝ`. -/
lemma continuous_measureReal_inter_le [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {X : Ω → ℝ} (hX : Measurable X) (hatom : ∀ x, P {ω | X ω = x} = 0) :
    Continuous fun c : ℝ => P.real (A ∩ {ω | c ≤ X ω}) := by
  have hmeas : ∀ c : ℝ, MeasurableSet (A ∩ {ω | c ≤ X ω}) := fun c =>
    hA.inter (measurableSet_le measurable_const hX)
  have heq : (fun c : ℝ => P.real (A ∩ {ω | c ≤ X ω})) =
      fun c => ∫ ω, (A ∩ {ω | c ≤ X ω}).indicator (fun _ => (1 : ℝ)) ω ∂P := by
    funext c
    exact (integral_indicator_one (hmeas c)).symm
  rw [heq, continuous_iff_continuousAt]
  intro c₀
  refine continuousAt_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun c =>
      (measurable_const.indicator (hmeas c)).aestronglyMeasurable
  · refine Eventually.of_forall fun c => Eventually.of_forall fun ω => ?_
    by_cases h : ω ∈ A ∩ {ω | c ≤ X ω} <;> simp [h]
  · have hae : ∀ᵐ ω ∂P, X ω ≠ c₀ := by
      rw [ae_iff]; simpa using hatom c₀
    filter_upwards [hae] with ω hω
    rcases lt_or_gt_of_ne hω with hlt | hgt
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [Ioi_mem_nhds hlt] with c hc
      have : ¬ c ≤ X ω := not_le.mpr hc
      simp [this]
    · refine (continuousAt_const (y := A.indicator (fun _ => (1 : ℝ)) ω)).congr ?_
      filter_upwards [Iio_mem_nhds hgt] with c hc
      have : c ≤ X ω := le_of_lt hc
      by_cases hωA : ω ∈ A <;> simp [hωA, this]

/-- **A boundary attaining a prescribed probability.** If `X` has no atoms, every
`p ∈ [0, P(A)]` is `P (A ∩ {X ≥ c})` for some extended real `c`. -/
theorem exists_boundary_measureReal [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {X : Ω → ℝ} (hX : Measurable X) (hatom : ∀ x, P {ω | X ω = x} = 0) {p : ℝ}
    (hp0 : 0 ≤ p) (hpA : p ≤ P.real A) :
    ∃ c : EReal, P.real (A ∩ {ω | c ≤ (X ω : EReal)}) = p := by
  rcases hpA.lt_or_eq with hpA | hpA
  swap
  · exact ⟨⊥, by simp [hpA]⟩
  rcases hp0.lt_or_eq with hp0 | hp0
  swap
  · exact ⟨⊤, by simp [← hp0]⟩
  set F : ℝ → ℝ := fun c => P.real (A ∩ {ω | c ≤ X ω}) with hF
  have hFc : Continuous F := continuous_measureReal_inter_le hA hX hatom
  have hmeas : ∀ c : ℝ, MeasurableSet (A ∩ {ω | c ≤ X ω}) := fun c =>
    hA.inter (measurableSet_le measurable_const hX)
  -- a point where `F > p`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, p < F a := by
    have hmono : Monotone fun n : ℕ => A ∩ {ω | -(n : ℝ) ≤ X ω} := by
      intro m n hmn ω hω
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      exact ⟨hω.1, show -(n : ℝ) ≤ X ω from le_trans (by linarith) hω.2⟩
    have hU : (⋃ n : ℕ, A ∩ {ω | -(n : ℝ) ≤ X ω}) = A := by
      ext ω
      simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨n, h, -⟩; exact h
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_ge (-X ω)
        exact ⟨n, h, by linarith⟩
    have ht := tendsto_measure_iUnion_atTop (μ := P) hmono
    rw [hU] at ht
    have hlt : ENNReal.ofReal p < P A := by
      rw [← ofReal_measureReal (measure_ne_top P A)]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hp0.le).mpr hpA
    obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hlt)).exists
    refine ⟨-(n : ℝ), ?_⟩
    rw [hF]
    simp only
    rw [measureReal_def]
    exact (ENNReal.ofReal_lt_iff_lt_toReal hp0.le (measure_ne_top _ _)).mp hn
  -- a point where `F < p`
  obtain ⟨b, hb⟩ : ∃ b : ℝ, F b < p := by
    have hanti : Antitone fun n : ℕ => A ∩ {ω | (n : ℝ) ≤ X ω} := by
      intro m n hmn ω hω
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      exact ⟨hω.1, show (m : ℝ) ≤ X ω from le_trans this hω.2⟩
    have hI : (⋂ n : ℕ, A ∩ {ω | (n : ℝ) ≤ X ω}) = ∅ := by
      ext ω
      simp only [mem_iInter, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false,
        not_forall]
      obtain ⟨n, hn⟩ := exists_nat_gt (X ω)
      exact ⟨n, fun h => absurd h.2 (not_le.mpr hn)⟩
    have ht := tendsto_measure_iInter_atTop (μ := P)
      (fun n : ℕ => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hI, measure_empty] at ht
    have hlt : (0 : ℝ≥0∞) < ENNReal.ofReal p := ENNReal.ofReal_pos.mpr hp0
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hlt)).exists
    refine ⟨n, ?_⟩
    rw [hF]
    simp only
    rw [measureReal_def]
    exact (ENNReal.toReal_lt_of_lt_ofReal hn)
  have hFanti : Antitone F := by
    intro x y hxy
    exact measureReal_mono (fun ω hω => ⟨hω.1, le_trans hxy hω.2⟩)
  have hab : a ≤ b := by
    by_contra h
    have := hFanti (le_of_lt (not_le.mp h))
    linarith
  obtain ⟨c, -, hc⟩ := intermediate_value_Icc' hab hFc.continuousOn ⟨hb.le, ha.le⟩
  refine ⟨c, ?_⟩
  simpa [EReal.coe_le_coe_iff] using hc


omit [MeasurableSpace Ω] in
/-- First-crossing events at different looks are disjoint. -/
lemma pairwiseDisjoint_firstCrossing (A : ℕ → Set Ω) (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint (firstCrossing A) := by
  intro j _ k _ hjk
  rcases lt_or_gt_of_ne hjk with h | h
  · refine Set.disjoint_left.mpr fun ω hj hk => hk.2 ?_
    exact Set.mem_biUnion (mem_range.mpr h) hj.1
  · refine Set.disjoint_left.mpr fun ω hj hk => hj.2 ?_
    exact Set.mem_biUnion (mem_range.mpr h) hk.1

omit [MeasurableSpace Ω] in
/-- Crossing at some look is the same as first crossing at some look. -/
lemma biUnion_firstCrossing_eq (A : ℕ → Set Ω) (K : ℕ) :
    ⋃ k ∈ range K, firstCrossing A k = ⋃ k ∈ range K, A k :=
  Set.Subset.antisymm (Set.biUnion_mono subset_rfl fun _ _ => Set.sdiff_subset)
    (biUnion_subset_biUnion_firstCrossing A K)

omit [MeasurableSpace Ω] in
/-- The first-crossing event at look `k` only depends on the events at looks `j ≤ k`. -/
lemma firstCrossing_congr {A B : ℕ → Set Ω} {k : ℕ} (h : ∀ j ≤ k, A j = B j) :
    firstCrossing A k = firstCrossing B k := by
  unfold firstCrossing
  rw [h k le_rfl]
  congr 1
  refine Set.iUnion₂_congr fun j hj => h j (mem_range.mp hj).le

/-- For measurable crossing events, the type-I error *equals* the sum of the first-crossing
probabilities. -/
theorem measure_biUnion_eq_sum_firstCrossing (P : Measure Ω) {A : ℕ → Set Ω}
    (hA : ∀ k, MeasurableSet (A k)) (K : ℕ) :
    P (⋃ k ∈ range K, A k) = ∑ k ∈ range K, P (firstCrossing A k) := by
  rw [← biUnion_firstCrossing_eq, measure_biUnion_finset (pairwiseDisjoint_firstCrossing A _)]
  intro k _
  exact (hA k).diff (Finset.measurableSet_biUnion _ fun j _ => hA j)

/-- **Exact alpha-spending.** If at each look the first-crossing probability equals the
increment of the spending function, the type-I error equals `s K - s 0`. -/
theorem measure_biUnion_eq_of_alphaSpending (P : Measure Ω) {A : ℕ → Set Ω}
    (hA : ∀ k, MeasurableSet (A k)) (K : ℕ) (s : ℕ → ℝ) (hs : Monotone s)
    (hspend : ∀ k < K, P (firstCrossing A k) = ENNReal.ofReal (s (k + 1) - s k)) :
    P (⋃ k ∈ range K, A k) = ENNReal.ofReal (s K - s 0) := by
  rw [measure_biUnion_eq_sum_firstCrossing P hA K,
    Finset.sum_congr rfl fun k hk => hspend k (mem_range.mp hk),
    ← ENNReal.ofReal_sum_of_nonneg fun k _ => sub_nonneg.mpr (hs (Nat.le_succ k)),
    Finset.sum_range_sub]

/-- The event that the statistic `X k` reaches the boundary `c k` (an extended real: `⊤` means
that look `k` never rejects, `⊥` that it always rejects). -/
def crossing (c : ℕ → EReal) (X : ℕ → Ω → ℝ) (k : ℕ) : Set Ω := {ω | c k ≤ (X k ω : EReal)}

/-- Crossing events of measurable statistics are measurable. -/
lemma measurableSet_crossing (c : ℕ → EReal) {X : ℕ → Ω → ℝ} (hX : ∀ k, Measurable (X k))
    (k : ℕ) : MeasurableSet (crossing c X k) :=
  measurableSet_le measurable_const (measurable_coe_real_ereal.comp (hX k))

/-- **Existence of exact alpha-spending boundaries.** If the statistics at the looks
`0, …, K - 1` are measurable and have no atoms, and `s` is a non-decreasing spending function
with `s 0 = 0` and `s K ≤ 1`, there are boundaries `c : ℕ → EReal` such that at every look
`k < K` the probability of crossing for the first time at look `k` is exactly
`s (k + 1) - s k`. Combined with `measure_biUnion_eq_of_alphaSpending`, the overall type-I
error is then exactly `s K`. -/
theorem exists_alphaSpending_boundaries (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hX : ∀ k, Measurable (X k)) (K : ℕ)
    (hatom : ∀ k < K, ∀ x, P {ω | X k ω = x} = 0) (s : ℕ → ℝ) (hs : Monotone s)
    (hs0 : s 0 = 0) (hsK : s K ≤ 1) :
    ∃ c : ℕ → EReal, ∀ k < K,
      P (firstCrossing (crossing c X) k) = ENNReal.ofReal (s (k + 1) - s k) := by
  suffices H : ∀ n ≤ K, ∃ c : ℕ → EReal, ∀ k < n,
      P (firstCrossing (crossing c X) k) = ENNReal.ofReal (s (k + 1) - s k) from H K le_rfl
  intro n
  induction n with
  | zero => exact fun _ => ⟨fun _ => ⊤, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ n ih =>
    intro hn
    obtain ⟨c, hc⟩ := ih (Nat.le_of_succ_le hn)
    set U := ⋃ j ∈ range n, crossing c X j with hU
    have hUm : MeasurableSet U := Finset.measurableSet_biUnion _ fun j _ =>
      measurableSet_crossing c hX j
    have hPU : P U = ENNReal.ofReal (s n - s 0) :=
      measure_biUnion_eq_of_alphaSpending P (measurableSet_crossing c hX) n s hs hc
    have hPUc : P.real Uᶜ = 1 - s n := by
      rw [measureReal_compl hUm, measureReal_def P U, hPU, hs0, sub_zero,
        ENNReal.toReal_ofReal (by simpa [hs0] using hs (Nat.zero_le n))]
      simp
    have hp0 : 0 ≤ s (n + 1) - s n := sub_nonneg.mpr (hs (Nat.le_succ n))
    have hp1 : s (n + 1) - s n ≤ P.real Uᶜ := by
      rw [hPUc]; linarith [hs hn]
    obtain ⟨x, hx⟩ := exists_boundary_measureReal hUm.compl (hX n) (hatom n hn) hp0 hp1
    refine ⟨Function.update c n x, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [← hc k hk]
      refine congrArg P (firstCrossing_congr fun j hj => ?_)
      simp only [crossing, Function.update_of_ne (show j ≠ n by omega)]
    · have hset : firstCrossing (crossing (Function.update c k x) X) k =
          Uᶜ ∩ {ω | x ≤ (X k ω : EReal)} := by
        rw [firstCrossing, Set.sdiff_eq, Set.inter_comm, hU]
        congr 1
        · congr 1
          refine Set.iUnion₂_congr fun j hj => ?_
          simp only [crossing, Function.update_of_ne (mem_range.mp hj).ne]
        · simp [crossing]
      rw [hset, ← hx, ofReal_measureReal (measure_ne_top _ _)]

/-- **Common (Pocock-type) boundary.** For `K ≥ 1` looks whose statistics have no atoms and
any `α ∈ [0, 1]`, there is a single boundary `c` used at every look such that the probability
of crossing it at some look is exactly `α`. -/
theorem exists_common_boundary (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hX : ∀ k, Measurable (X k)) {K : ℕ} (hK : 0 < K)
    (hatom : ∀ k < K, ∀ x, P {ω | X k ω = x} = 0) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ c : EReal, P (⋃ k ∈ range K, {ω | c ≤ (X k ω : EReal)}) = ENNReal.ofReal α := by
  have hne : (range K).Nonempty := nonempty_range_iff.mpr hK.ne'
  set M : Ω → ℝ := fun ω => (range K).sup' hne fun k => X k ω with hM
  have hMm : Measurable M := by
    have : M = (range K).sup' hne X := by
      funext ω; simp [hM, Finset.sup'_apply]
    rw [this]
    exact Finset.measurable_sup' hne fun k _ => hX k
  have hMatom : ∀ x, P {ω | M ω = x} = 0 := by
    intro x
    refine measure_mono_null (t := ⋃ k ∈ range K, {ω | X k ω = x}) ?_
      ((measure_biUnion_null_iff (Finset.countable_toSet _)).mpr fun k hk =>
        hatom k (mem_range.mp hk) x)
    intro ω hω
    obtain ⟨k, hk, hkM⟩ := Finset.exists_mem_eq_sup' hne fun k => X k ω
    exact Set.mem_biUnion hk (by simpa [hM, ← hkM] using hω)
  obtain ⟨c, hc⟩ := exists_boundary_measureReal MeasurableSet.univ hMm hMatom hα0
    (by simpa using hα1)
  refine ⟨c, ?_⟩
  have hset : (⋃ k ∈ range K, {ω | c ≤ (X k ω : EReal)}) = Set.univ ∩ {ω | c ≤ (M ω : EReal)} := by
    ext ω
    have hcoe : ((M ω : ℝ) : EReal) = (range K).sup' hne fun k => (X k ω : EReal) := by
      rw [hM]
      exact Finset.apply_sup'_eq_sup'_comp hne _ fun a b => (Monotone.map_max (fun _ _ h => EReal.coe_le_coe_iff.mpr h) : ((max a b : ℝ) : EReal) = _)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, Set.univ_inter, hcoe,
      Finset.le_sup'_iff]
  rw [hset, ← hc, ofReal_measureReal (measure_ne_top _ _)]

end Applied.GroupSequential
