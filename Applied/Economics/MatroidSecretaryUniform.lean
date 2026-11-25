import Applied.Economics.MatroidSecretaryDirectSum
import Applied.Economics.SecretaryOneOverE
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The matroid secretary problem for uniform matroids of rank `k`

Everything uses the model of `Applied/Economics/MatroidSecretary.lean` unchanged.

* `uniform E k`: the uniform matroid of rank `k` on the finite type `E` (a set is independent
  iff it has at most `k` elements), ground set `univ`.
* `colourRule g` for a colouring `g : E → Fin k`: run the `⌊n/e⌋` rule `secretaryRuleLex`
  independently inside each colour class (`blockSum`). It accepts at most one element per
  colour, hence at most `k` elements (`colourRule_isFeasible`), and for every set `J` with at
  most one element per colour it is `1/e`-competitive against `J`
  (`colourRule_isCompetitive`).
* `card_isolated_div`: if `g` is a uniformly random colouring and `e ∈ I`, the probability that
  no other element of `I` has the colour of `e` is `((k-1)/k)^(|I|-1)`.
* `inv_exp_le_pow`: `((k-1)/k)^(k-1) ≥ 1/e` for `k ≥ 1`.
* `hasCompetitiveRandomized_uniform`: the randomized algorithm that draws a uniformly random
  colouring and then runs `colourRule` is feasible and `e⁻²`-competitive for the uniform
  matroid of rank `k`, for every `k` and every `E`.
* `hasCompetitiveRandomized_of_indep_iff`: the same for every matroid whose independent sets
  are exactly the sets of at most `k` elements.
* `partitionCap f cap` (finite `ι`, `f : E → ι`, `cap : ι → ℕ`): the partition matroid with
  capacities (at most `cap i` elements of block `i`). `partitionCap_isBlockSum`: it is the
  direct sum of the uniform matroids `uniform (Block f i) (cap i)`;
  `hasCompetitiveRandomized_partitionCap`: hence it is `e⁻²`-competitive.
-/

open Finset Function

open scoped Nat

open Classical

noncomputable section

namespace Applied.Economics.MatroidSecretary

variable {E : Type*} [Fintype E]

/-! ### The uniform matroid -/

/-- The uniform matroid of rank `k` on `E`: a set is independent iff it has at most `k`
elements. -/
def uniform (E : Type*) [Fintype E] (k : ℕ) : Matroid E :=
  (IndepMatroid.ofFinite (E := (Set.univ : Set E)) Set.finite_univ (fun I => I.ncard ≤ k)
    (by simp) (fun I J hJ hIJ => (Set.ncard_le_ncard hIJ (Set.toFinite J)).trans hJ)
    (by
      intro I J hI hJ hlt
      have hns : ¬ J ⊆ I := fun hsub =>
        absurd (Set.ncard_le_ncard hsub (Set.toFinite _)) (not_le.2 hlt)
      obtain ⟨e, heJ, heI⟩ := Set.not_subset.1 hns
      refine ⟨e, heJ, heI, ?_⟩
      rw [Set.ncard_insert_of_notMem heI (Set.toFinite I)]
      omega)
    (fun _ _ => Set.subset_univ _)).matroid

@[simp] lemma uniform_ground (k : ℕ) : (uniform E k).E = Set.univ := rfl

@[simp] lemma uniform_indep_iff {k : ℕ} {I : Set E} : (uniform E k).Indep I ↔ I.ncard ≤ k := by
  simp [uniform]

/-! ### Running the `1/e` rule in every colour class -/

/-- Given a colouring `g : E → Fin k`, run the `⌊n/e⌋` rule (ties broken by a fixed order)
independently inside each colour class, on the arrivals of that class only. -/
def colourRule {k : ℕ} (g : E → Fin k) : OnlineAlg E :=
  blockSum g fun i => secretaryRuleLex (Block g i)

lemma colourRule_isFeasible_partitionOne {k : ℕ} (g : E → Fin k) :
    IsFeasible (partitionOne g) (colourRule g) :=
  blockSum_isFeasible (partitionOne_isBlockSum g) fun _ => secretaryRuleLex_isFeasible

/-- The colour rule is `1/e`-competitive against every set with at most one element of each
colour. -/
theorem colourRule_isCompetitive {k : ℕ} (g : E → Fin k) :
    IsCompetitive (partitionOne g) (colourRule g) (1 / Real.exp 1) :=
  blockSum_isCompetitive (partitionOne_isBlockSum g) fun _ => secretaryRuleLex_isCompetitive

omit [Fintype E] in
/-- A set with at most one element of each of `k` colours has at most `k` elements. -/
lemma ncard_le_of_injOn {k : ℕ} (g : E → Fin k) {S : Finset E} (h : Set.InjOn g (S : Set E)) :
    (S : Set E).ncard ≤ k := by
  rw [Set.ncard_coe_finset]
  have := Finset.card_le_card_of_injOn g (t := (univ : Finset (Fin k)))
    (fun _ _ => by simp) h
  simpa using this

/-- The colour rule always accepts at most `k` elements. -/
theorem colourRule_isFeasible {k : ℕ} (g : E → Fin k) :
    IsFeasible (uniform E k) (colourRule g) := by
  intro σ w hw
  rw [uniform_indep_iff]
  exact ncard_le_of_injOn g (partitionOne_indep_iff.1 (colourRule_isFeasible_partitionOne g σ w hw))

/-! ### Isolated elements under a random colouring -/

/-- `e` is isolated in `I` under the colouring `g`: no other element of `I` has its colour. -/
def Isolated {k : ℕ} (g : E → Fin k) (I : Finset E) (e : E) : Prop :=
  ∀ e' ∈ I, g e' = g e → e' = e

omit [Fintype E] in
lemma injOn_isolated {k : ℕ} (g : E → Fin k) (I : Finset E) :
    Set.InjOn g ((I.filter (Isolated g I) : Finset E) : Set E) := by
  intro a ha b hb hab
  simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
  exact hb.2 a ha.1 hab

/-- The colourings under which `e` has colour `c` and is isolated in `I`, as a product set. -/
lemma filter_isolated_colour {k : ℕ} (I : Finset E) (e : E) (c : Fin k) :
    (univ.filter fun g : E → Fin k => Isolated g I e ∧ g e = c) =
      Fintype.piFinset fun x => if x = e then {c} else if x ∈ I then univ.erase c else univ := by
  ext g
  rw [Finset.mem_filter_univ, Fintype.mem_piFinset]
  unfold Isolated
  constructor
  · rintro ⟨hiso, rfl⟩ x
    split_ifs with h1 h2
    · simp [h1]
    · simp only [mem_erase, mem_univ, and_true]
      exact fun h => h1 (hiso x h2 h)
    · simp
  · intro h
    have hc : g e = c := by simpa using h e
    refine ⟨fun e' he' hg => ?_, hc⟩
    by_contra hne
    have := h e'
    rw [ite_eq_right hne, ite_eq_left he', hg, hc] at this
    simp at this

lemma card_filter_isolated_colour {k : ℕ} (I : Finset E) (e : E) (c : Fin k) :
    ((#(univ.filter fun g : E → Fin k => Isolated g I e ∧ g e = c) : ℕ) : ℝ) =
      ∏ x : E, (if x = e then 1 else if x ∈ I then ((k : ℝ) - 1) else k) := by
  rw [filter_isolated_colour I e c, Fintype.card_piFinset, Nat.cast_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  split_ifs with h1 h2
  · simp
  · rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have : 1 ≤ k := Fin.pos c
    push_cast [this]
    ring
  · simp

/-- Under a uniformly random colouring with `k ≥ 1` colours, an element `e ∈ I` is isolated in
`I` with probability `((k - 1)/k)^(|I| - 1)`. -/
theorem card_isolated_div {k : ℕ} (hk : 1 ≤ k) (I : Finset E) (e : E) (he : e ∈ I) :
    ((#(univ.filter fun g : E → Fin k => Isolated g I e) : ℕ) : ℝ) / (k : ℝ) ^ Fintype.card E =
      (((k : ℝ) - 1) / k) ^ (#I - 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  -- split according to the colour of `e`
  have hsplit : #(univ.filter fun g : E → Fin k => Isolated g I e) =
      ∑ c : Fin k, #(univ.filter fun g : E → Fin k => Isolated g I e ∧ g e = c) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun g : E → Fin k => g e) (t := univ)
      (fun _ _ => mem_coe.2 (mem_univ _))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.filter_filter]
  rw [hsplit, Nat.cast_sum, Finset.sum_congr rfl fun c _ => card_filter_isolated_colour I e c,
    Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- evaluate the product
  have hprod : ∏ x : E, (if x = e then 1 else if x ∈ I then ((k : ℝ) - 1) else k) =
      ((k : ℝ) - 1) ^ (#I - 1) * (k : ℝ) ^ (Fintype.card E - #I) := by
    rw [← Finset.prod_mul_prod_compl I, ← Finset.mul_prod_erase I _ he, ite_eq_left rfl, one_mul]
    have h1 : ∏ x ∈ I.erase e, (if x = e then 1 else if x ∈ I then ((k : ℝ) - 1) else k) =
        ((k : ℝ) - 1) ^ (#I - 1) := by
      rw [Finset.prod_congr rfl fun x hx => by
        rw [ite_eq_right (Finset.ne_of_mem_erase hx), ite_eq_left (Finset.mem_of_mem_erase hx)],
        Finset.prod_const, card_erase_of_mem he]
    have h2 : ∏ x ∈ Iᶜ, (if x = e then 1 else if x ∈ I then ((k : ℝ) - 1) else k) =
        (k : ℝ) ^ (Fintype.card E - #I) := by
      rw [Finset.prod_congr rfl fun x hx => by
        have hxI : x ∉ I := Finset.mem_compl.1 hx
        rw [ite_eq_right (fun h : x = e => hxI (h ▸ he)), ite_eq_right hxI],
        Finset.prod_const, card_compl]
    rw [h1, h2]
  rw [hprod]
  have hIn : #I ≤ Fintype.card E := Finset.card_le_univ I
  have hI1 : 1 ≤ #I := Finset.card_pos.2 ⟨e, he⟩
  have hpow : (k : ℝ) ^ Fintype.card E =
      (k : ℝ) * (k : ℝ) ^ (#I - 1) * (k : ℝ) ^ (Fintype.card E - #I) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  rw [hpow, div_pow]
  have h3 : (k : ℝ) ^ (Fintype.card E - #I) ≠ 0 := pow_ne_zero _ hk0.ne'
  have h4 : (k : ℝ) ^ (#I - 1) ≠ 0 := pow_ne_zero _ hk0.ne'
  field_simp

/-- `((k - 1)/k)^(k - 1) ≥ 1/e` for every `k ≥ 1`. -/
theorem inv_exp_le_pow {k : ℕ} (hk : 1 ≤ k) :
    1 / Real.exp 1 ≤ (((k : ℝ) - 1) / k) ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  rw [add_sub_cancel_right]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [pow_zero]
    rw [div_le_one (Real.exp_pos 1)]
    exact Real.one_lt_exp_iff.2 one_pos |>.le
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  -- `(1 + 1/j)^j ≤ e`
  have hle : (1 + 1 / (j : ℝ)) ^ j ≤ Real.exp 1 := by
    calc (1 + 1 / (j : ℝ)) ^ j ≤ (Real.exp (1 / j)) ^ j := by
          exact pow_le_pow_left₀ (by positivity)
            (by linarith [Real.add_one_le_exp (1 / (j : ℝ))]) j
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have hbase : (j : ℝ) / (j + 1) = (1 + 1 / (j : ℝ))⁻¹ := by
    field_simp
  rw [hbase, inv_pow, one_div]
  exact inv_anti₀ (by positivity) hle

lemma pow_ge_inv_exp {k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ k - 1) :
    1 / Real.exp 1 ≤ (((k : ℝ) - 1) / k) ^ m := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine (inv_exp_le_pow hk).trans (pow_le_pow_of_le_one ?_ ?_ hm)
  · exact div_nonneg (by linarith) hk0.le
  · rw [div_le_one hk0]; linarith

/-! ### The randomized algorithm -/

/-- The uniform probability measure on colourings `E → Fin k`. -/
def colouringMeasure (E : Type*) [Fintype E] (k : ℕ) : MeasureTheory.Measure (E → Fin k) :=
  ((Fintype.card (E → Fin k) : ENNReal)⁻¹) • MeasureTheory.Measure.count

lemma colouringMeasure_isProbability {k : ℕ} (hk : 1 ≤ k) :
    MeasureTheory.IsProbabilityMeasure (colouringMeasure E k) := by
  have hne : Nonempty (E → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  have hpos : (Fintype.card (E → Fin k) : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := E → Fin k)).ne'
  constructor
  rw [colouringMeasure, _root_.smul_apply, MeasureTheory.Measure.count_univ,
    smul_eq_mul, ENat.card_eq_coe_fintype_card]
  simp only [ENat.toENNReal_coe]
  exact ENNReal.inv_mul_cancel hpos (ENNReal.natCast_ne_top _)

lemma integral_colouringMeasure {k : ℕ} (F : (E → Fin k) → ℝ) :
    ∫ g, F g ∂(colouringMeasure E k) = (∑ g, F g) / (k : ℝ) ^ Fintype.card E := by
  rw [colouringMeasure, MeasureTheory.integral_smul_measure, MeasureTheory.integral_count,
    smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [inv_mul_eq_div]

/-- **Uniform matroids of rank `k`.** Drawing a uniformly random colouring `g : E → Fin k` and
running the `⌊n/e⌋` rule inside each colour class is a feasible randomized online algorithm
for the uniform matroid of rank `k`, `e⁻²`-competitive for all non-negative weights. -/
theorem hasCompetitiveRandomized_uniform (E : Type) [Fintype E] (k : ℕ) :
    HasCompetitiveRandomized (uniform E k) (1 / Real.exp 1 ^ 2) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- rank zero: only the empty set is independent
    refine IsCompetitive.hasCompetitiveRandomized (never_isFeasible _) fun w hw I hI => ?_
    rw [uniform_indep_iff, Nat.le_zero, Set.ncard_eq_zero (Set.toFinite _),
      Finset.coe_eq_empty] at hI
    simp [hI]
  have hk1 : 1 ≤ k := hk
  have := colouringMeasure_isProbability (E := E) hk1
  refine ⟨E → Fin k, inferInstance, colouringMeasure E k, inferInstance, colourRule,
    colourRule_isFeasible, fun w hw I hI => ?_⟩
  rw [uniform_indep_iff, Set.ncard_coe_finset] at hI
  rw [integral_colouringMeasure]
  have hkpow : (0 : ℝ) < (k : ℝ) ^ Fintype.card E := by positivity
  have he1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  -- for each colouring, the algorithm beats `1/e` times the weight of the isolated elements
  have hstep : ∀ g : E → Fin k, 1 / Real.exp 1 * ∑ e ∈ I, (if Isolated g I e then w e else 0) ≤
      expWeight (colourRule g) w := by
    intro g
    rw [← Finset.sum_filter]
    exact colourRule_isCompetitive g w hw _ (partitionOne_indep_iff.2 (injOn_isolated g I))
  -- average over colourings
  have hswap : ∑ g : E → Fin k, ∑ e ∈ I, (if Isolated g I e then w e else 0) =
      ∑ e ∈ I, ((#(univ.filter fun g : E → Fin k => Isolated g I e) : ℕ) : ℝ) * w e := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hiso : ∀ e ∈ I, 1 / Real.exp 1 * w e ≤
      ((#(univ.filter fun g : E → Fin k => Isolated g I e) : ℕ) : ℝ) /
        (k : ℝ) ^ Fintype.card E * w e := by
    intro e he
    rw [card_isolated_div hk1 I e he]
    exact mul_le_mul_of_nonneg_right (pow_ge_inv_exp hk1 (by omega)) (hw e)
  rw [le_div_iff₀ hkpow]
  calc (1 / Real.exp 1 ^ 2 * ∑ e ∈ I, w e) * (k : ℝ) ^ Fintype.card E
      = 1 / Real.exp 1 * (∑ e ∈ I, 1 / Real.exp 1 * w e) * (k : ℝ) ^ Fintype.card E := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 1 / Real.exp 1 * (∑ e ∈ I, ((#(univ.filter fun g : E → Fin k => Isolated g I e) : ℕ) : ℝ) /
          (k : ℝ) ^ Fintype.card E * w e) * (k : ℝ) ^ Fintype.card E := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hiso) (by positivity)) hkpow.le
    _ = 1 / Real.exp 1 * ∑ g : E → Fin k, ∑ e ∈ I, (if Isolated g I e then w e else 0) := by
        rw [hswap, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        field_simp
    _ ≤ ∑ g : E → Fin k, expWeight (colourRule g) w := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun g _ => hstep g

/-- Every matroid whose independent sets are exactly the sets of at most `k` elements has an
`e⁻²`-competitive randomized online algorithm. -/
theorem hasCompetitiveRandomized_of_indep_iff {E : Type} [Fintype E] {M : Matroid E} {k : ℕ}
    (hM : ∀ I : Set E, M.Indep I ↔ I.ncard ≤ k) :
    HasCompetitiveRandomized M (1 / Real.exp 1 ^ 2) := by
  obtain ⟨Ω, mΩ, P, hP, A, hA, hcomp⟩ := hasCompetitiveRandomized_uniform E k
  have hiff : ∀ I : Set E, M.Indep I ↔ (uniform E k).Indep I := fun I => by
    rw [hM, uniform_indep_iff]
  refine ⟨Ω, mΩ, P, hP, A, fun ω σ w hw => (hiff _).2 (hA ω σ w hw),
    fun w hw I hI => hcomp w hw I ((hiff _).1 hI)⟩

/-! ### Partition matroids with arbitrary capacities -/

section PartitionCap

variable {ι : Type*} [Fintype ι]

/-- The size of a set is the sum of the sizes of its traces on the blocks of `f`. -/
lemma ncard_eq_sum_blocks (f : E → ι) (S : Set E) :
    S.ncard = ∑ i, (S ∩ {e | f e = i}).ncard := by
  rw [Set.ncard_eq_toFinset_card' S,
    Finset.card_eq_sum_card_fiberwise (f := f) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp

/-- The partition matroid with capacities `cap`: a set is independent iff it contains at most
`cap i` elements of each block `{e | f e = i}`. -/
def partitionCap (f : E → ι) (cap : ι → ℕ) : Matroid E :=
  (IndepMatroid.ofFinite (E := (Set.univ : Set E)) Set.finite_univ
    (fun I => ∀ i, (I ∩ {e | f e = i}).ncard ≤ cap i)
    (fun i => by simp)
    (fun I J hJ hIJ i =>
      (Set.ncard_le_ncard (Set.inter_subset_inter_left _ hIJ) (Set.toFinite _)).trans (hJ i))
    (by
      intro I J hI hJ hlt
      obtain ⟨i, hi⟩ : ∃ i, (I ∩ {e | f e = i}).ncard < (J ∩ {e | f e = i}).ncard := by
        by_contra h
        push Not at h
        have := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset ι)) => h i
        rw [← ncard_eq_sum_blocks, ← ncard_eq_sum_blocks] at this
        omega
      have hns : ¬ J ∩ {e | f e = i} ⊆ I ∩ {e | f e = i} := fun hsub =>
        absurd (Set.ncard_le_ncard hsub (Set.toFinite _)) (not_le.2 hi)
      obtain ⟨e, ⟨heJ, hei⟩, heI⟩ := Set.not_subset.1 hns
      have heI' : e ∉ I := fun h => heI ⟨h, hei⟩
      refine ⟨e, heJ, heI', fun j => ?_⟩
      by_cases hj : f e = j
      · have hji : j = i := hj.symm.trans hei
        subst hji
        rw [Set.insert_inter_of_mem hei, Set.ncard_insert_of_notMem heI (Set.toFinite _)]
        exact (Nat.succ_le_of_lt hi).trans (hJ _)
      · rw [Set.insert_inter_of_notMem hj]
        exact hI j)
    (fun _ _ => Set.subset_univ _)).matroid

@[simp] lemma partitionCap_ground (f : E → ι) (cap : ι → ℕ) :
    (partitionCap f cap).E = Set.univ := rfl

@[simp] lemma partitionCap_indep_iff {f : E → ι} {cap : ι → ℕ} {I : Set E} :
    (partitionCap f cap).Indep I ↔ ∀ i, (I ∩ {e | f e = i}).ncard ≤ cap i := by
  simp [partitionCap]

/-- The partition matroid with capacities `cap` is the direct sum of the uniform matroids of
rank `cap i` on its blocks. -/
lemma partitionCap_isBlockSum [DecidableEq ι] (f : E → ι) (cap : ι → ℕ) :
    IsBlockSum (partitionCap f cap) fun i => uniform (Block f i) (cap i) := by
  intro I
  rw [partitionCap_indep_iff]
  refine forall_congr' fun i => ?_
  rw [uniform_indep_iff, ← Set.ncard_image_of_injective _ Subtype.val_injective]
  have : Subtype.val '' (Subtype.val ⁻¹' I : Set (Block f i)) = I ∩ {e | f e = i} := by
    ext e
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨he, hfe⟩
      exact ⟨⟨e, hfe⟩, he, rfl⟩
  rw [this]

end PartitionCap

/-- **Partition matroids with arbitrary capacities.** For a finite index type `ι`, a map
`f : E → ι` and capacities `cap : ι → ℕ`, the partition matroid `partitionCap f cap` has an
`e⁻²`-competitive randomized online algorithm (the uniform-matroid algorithm run independently
in each block). -/
theorem hasCompetitiveRandomized_partitionCap {E : Type} [Fintype E] {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : E → ι) (cap : ι → ℕ) :
    HasCompetitiveRandomized (partitionCap f cap) (1 / Real.exp 1 ^ 2) :=
  HasCompetitiveRandomized.blockSum (partitionCap_isBlockSum f cap)
    fun i => hasCompetitiveRandomized_uniform (Block f i) (cap i)

end Applied.Economics.MatroidSecretary
