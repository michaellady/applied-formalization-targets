import Applied.Statistics.SimesExact
import Applied.Statistics.SidakExact
import Applied.Statistics.GraphicalInstances
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Sanity checks for the multiple-testing core (adversarial review)

Concrete instances showing that the hypotheses of the headline theorems on Simes, Hochberg,
Hommel, Šidák, the graphical approach and the exact identities are satisfiable, and that the
bounded quantities are not trivially zero.

* **Finite model.** `Ω = ι → Bool` with independent fair coins, `p i ω = 1/2` or `1`.
  These p-values are measurable, mutually independent and valid (`coinP_*`). At level `1/2`
  with two hypotheses, all true nulls: the Simes test, Hochberg and Hommel have family-wise
  error rate in `(0, 1/2]` (`simes_coin`, `hochberg_coin`, `hommel_coin`), and Šidák's is at
  most `1/2` (`sidak_coin`).
* **The graphical procedure terminates.** `exists_seqRejectable_stuck`: for every weight
  family, level and p-values there is a set reachable by the sequentially rejective procedure
  at which no further rejection is possible; `seqRejectable_closedTest`: for monotone weights
  the closed test is such a set. So the hypotheses `hR`, `hstuck` of `fwer_graphical_le` and
  `graphical_eq_closedTest` can always be met.
* **The graphical bound is attained.** In the coin model with the fixed-sequence graph on two
  hypotheses at level `1/2`, the graphical procedure has family-wise error rate exactly `1/2`
  (`fwer_graphical_coin_eq`).
* **Worked example.** The graph is the two-primary, two-secondary graph of Bretz, Maurer,
  Brannath and Posch (2009); the p-values are those of the example in Bretz, Posch, Glimm,
  Klinglmueller, Maurer and Rohmeyer, Biometrical J. 53 (2011), Example 1 and Figure 3, which
  states that `H₁` and `H₂` are rejected and nothing else. Weights `(1/2, 1/2, 0, 0)`,
  `p = (0.01, 0.005, 0.1, 0.5)`, `α = 0.025` (the level is our choice; `0.05` gives the same
  decisions):
  Algorithm 1 rejects `H₂`, then `H₁`, and stops; the updated weights and transition matrices
  are computed (`bretz_update_one`, `bretz_update_two`), and the closed test rejects exactly
  `{H₁, H₂}` (`bretz_closedTest`).
* **Exact identities.** On `Fin 2 → ℝ` with the uniform law on `[0, 1]²` the coordinates are
  independent and exactly uniform, so the Simes identity, the exact Šidák error rate and the
  exact Benjamini–Hochberg false discovery rate apply (`simes_identity_unif`,
  `sidak_exact_unif`, `bh_exact_unif`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting.Sanity

/-! ### The coin model -/

/-- A fair coin. -/
noncomputable def coin : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure coin := ⟨by
  simp only [coin, smul_apply, add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top⟩

lemma coin_false : coin {false} = 2⁻¹ := by
  simp [coin]

/-- The p-value attached to a coin: `1/2` on `false`, `1` on `true`. -/
noncomputable def val (b : Bool) : ℝ := if b then 1 else 1 / 2

lemma coin_val_le (t : ℝ) (_ht : 0 ≤ t) : coin {b | val b ≤ t} ≤ ENNReal.ofReal t := by
  rcases lt_or_ge t (1 / 2) with h1 | h1
  · have : {b | val b ≤ t} = ∅ := by
      ext b; cases b <;> simp [val] <;> linarith
    rw [this]; simp
  rcases lt_or_ge t 1 with h2 | h2
  · have : {b | val b ≤ t} ⊆ {false} := by
      intro b hb; cases b
      · rfl
      · simp [val] at hb; linarith
    refine (measure_mono this).trans ?_
    have h2' : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    rw [coin_false, h2']
    exact ENNReal.ofReal_le_ofReal h1
  · exact prob_le_one.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h2)

variable {ι : Type*} [Fintype ι]

set_option linter.unusedSectionVars false

/-- Independent fair coins. -/
noncomputable def coinP (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi fun _ => coin

instance : IsProbabilityMeasure (coinP ι) := by unfold coinP; infer_instance

/-- The p-values of the coin model. -/
noncomputable def coinp (i : ι) (ω : ι → Bool) : ℝ := val (ω i)

lemma coinp_measurable (i : ι) : Measurable (coinp i) :=
  (measurable_of_finite val).comp (measurable_pi_apply i)

lemma coinp_iIndepFun : iIndepFun (coinp (ι := ι)) (coinP ι) :=
  iIndepFun_pi (X := fun _ : ι => val) fun _ => (measurable_of_finite val).aemeasurable

lemma coinP_eval (i : ι) (S : Set Bool) : coinP ι {ω | ω i ∈ S} = coin S :=
  (measurePreserving_eval (fun _ : ι => coin) i).measure_preimage
    (MeasurableSet.of_discrete (s := S)).nullMeasurableSet

lemma coinp_valid (i : ι) : IsValidPValue (coinP ι) (coinp i) := by
  intro t ht
  exact (coinP_eval i {b | val b ≤ t}).le.trans (coin_val_le t ht)

/-- The outcome in which every coin shows `false` has positive probability. -/
lemma coinP_allFalse_pos : 0 < coinP ι {fun _ => false} := by
  have h : ({fun _ => false} : Set (ι → Bool)) = Set.pi Set.univ fun _ => {false} := by
    rw [Set.univ_pi_singleton]
  rw [h, coinP, Measure.pi_pi]
  simp only [coin_false, Finset.prod_const]
  exact ENNReal.pow_pos (by simp) _

/-! ### Simes, Hochberg, Hommel and Šidák in the coin model -/

/-- At the outcome "all false" both p-values are `1/2 ≤ α = 1/2`, so Hochberg rejects
everything. -/
lemma hochberg_allFalse :
    hochberg (1 / 2) (coinp (ι := Fin 2)) (fun _ => false) = univ :=
  hochberg_eq_univ_of_forall_eq (x := 1 / 2) (fun i => by simp [coinp, val]) le_rfl

/-- **Hochberg, non-vacuous.** Two true nulls with independent valid p-values on a four-point
space, level `1/2`: all hypotheses of `fwer_hochberg_le` hold, and the family-wise error rate
is positive and at most `1/2`. -/
theorem hochberg_coin :
    0 < fwer (coinP (Fin 2)) univ (hochberg (1 / 2) coinp) ∧
      fwer (coinP (Fin 2)) univ (hochberg (1 / 2) coinp) ≤ ENNReal.ofReal (1 / 2) := by
  refine ⟨coinP_allFalse_pos.trans_le (measure_mono ?_),
    fwer_hochberg_le _ (by norm_num) _ coinp_measurable coinp_iIndepFun univ
      fun i _ => coinp_valid i⟩
  rintro ω rfl
  exact ⟨0, mem_univ _, by rw [hochberg_allFalse]; exact mem_univ _⟩

/-- **Hommel, non-vacuous**, in the same model. -/
theorem hommel_coin :
    0 < fwer (coinP (Fin 2)) univ (hommel (1 / 2) coinp) ∧
      fwer (coinP (Fin 2)) univ (hommel (1 / 2) coinp) ≤ ENNReal.ofReal (1 / 2) := by
  refine ⟨coinP_allFalse_pos.trans_le (measure_mono ?_),
    fwer_hommel_le _ (by norm_num) _ coinp_measurable coinp_iIndepFun univ
      fun i _ => coinp_valid i⟩
  rintro ω rfl
  refine ⟨0, mem_univ _, hochberg_subset_hommel (by norm_num) _ _ ?_⟩
  rw [hochberg_allFalse]; exact mem_univ _

/-- **Simes, non-vacuous**, in the same model: the Simes test at level `1/2` rejects with
positive probability at most `1/2`. -/
theorem simes_coin :
    0 < coinP (Fin 2) {ω | 1 ≤ bhK (1 / 2) fun j => coinp j ω} ∧
      coinP (Fin 2) {ω | 1 ≤ bhK (1 / 2) fun j => coinp j ω} ≤ ENNReal.ofReal (1 / 2) := by
  refine ⟨coinP_allFalse_pos.trans_le (measure_mono ?_),
    measure_one_le_bhK_le _ (by norm_num) _ coinp_measurable coinp_iIndepFun coinp_valid⟩
  rintro ω rfl
  have h2 : 2 ≤ bhK (1 / 2) fun j : Fin 2 => coinp j fun _ => false := by
    refine le_bhK _ (by simp) ?_
    unfold bhCount
    rw [Finset.filter_true_of_mem fun j _ => by simp [coinp, val]]
    simp
  exact (by norm_num : 1 ≤ 2).trans h2

/-- **Šidák, non-vacuous**, in the same model. -/
theorem sidak_coin :
    fwer (coinP (Fin 2)) univ (sidak (1 / 2) coinp) ≤ ENNReal.ofReal (1 / 2) :=
  fwer_sidak_le _ _ coinp_measurable coinp_iIndepFun univ (fun i _ => coinp_valid i) _
    (by norm_num) (by norm_num)

/-! ### The sequentially rejective procedure terminates -/

section Terminates

variable [DecidableEq ι]

/-- **Termination.** For every family of weights, every level and every p-values, the
sequentially rejective procedure reaches a set at which no further hypothesis can be
rejected. -/
theorem exists_seqRejectable_stuck (α : ℝ) (w : Finset ι → ι → ℝ) (q : ι → ℝ) :
    ∃ R, SeqRejectable α w q R ∧ ∀ i ∉ R, w (univ \ R) i * α < q i := by
  classical
  obtain ⟨R, hR, hmax⟩ := Finset.exists_max_image
    (univ.filter fun R : Finset ι => SeqRejectable α w q R) Finset.card
    ⟨∅, mem_filter.mpr ⟨mem_univ _, SeqRejectable.empty⟩⟩
  have hR' := (mem_filter.mp hR).2
  refine ⟨R, hR', fun i hi => ?_⟩
  by_contra hle
  have hstep : SeqRejectable α w q (insert i R) := SeqRejectable.step hR' hi (not_lt.mp hle)
  have := hmax _ (mem_filter.mpr ⟨mem_univ _, hstep⟩)
  rw [Finset.card_insert_of_notMem hi] at this
  omega

variable {Ω : Type*}

/-- For monotone weights and `α ≥ 0`, the closed test is itself a set reached by the
sequentially rejective procedure, and nothing more can be rejected from it. -/
theorem seqRejectable_closedTest {α : ℝ} (hα : 0 ≤ α) {w : Finset ι → ι → ℝ}
    (hw : MonotoneWeights w) (p : ι → Ω → ℝ) (ω : Ω) :
    SeqRejectable α w (fun j => p j ω) (closedTest (weightedLocal α w p) ω) ∧
      ∀ i ∉ closedTest (weightedLocal α w p) ω,
        w (univ \ closedTest (weightedLocal α w p) ω) i * α < p i ω := by
  obtain ⟨R, hR, hstuck⟩ := exists_seqRejectable_stuck α w fun j => p j ω
  have h := closedTest_eq_of_seqRejectable_of_stuck hα hw p ω hR
    fun i hi => hstuck i (mem_sdiff.mp hi).2
  rw [h]
  exact ⟨hR, hstuck⟩

end Terminates

/-! ### The graphical bound is attained -/

/-- The set rejected by the graphical procedure for the fixed-sequence graph on two
hypotheses at level `1/2` in the coin model, run until it stops. -/
noncomputable def graphR (ω : Fin 2 → Bool) : Finset (Fin 2) :=
  closedTest (weightedLocal (1 / 2) (graphWeights fixedSequenceGraph) coinp) ω

lemma graphR_seqRejectable (ω : Fin 2 → Bool) :
    SeqRejectable (1 / 2) (graphWeights fixedSequenceGraph) (fun j => coinp j ω) (graphR ω) :=
  (seqRejectable_closedTest (by norm_num) (monotoneWeights_graphWeights _) coinp ω).1

/-- **The graphical approach, non-vacuous and tight.** Fixed-sequence graph on two true nulls
(all weight on the first, edge of weight one to the second), level `1/2`, coin model: every
hypothesis of `fwer_graphical_le` holds and the family-wise error rate is exactly `1/2`. -/
theorem fwer_graphical_coin_eq :
    fwer (coinP (Fin 2)) univ graphR = ENNReal.ofReal (1 / 2) := by
  apply le_antisymm
  · exact fwer_graphical_le _ coinp univ (fun i _ => coinp_valid i) _ (by norm_num)
      fixedSequenceGraph graphR graphR_seqRejectable
  · have h1 : coinP (Fin 2) {ω | ω 0 ∈ ({false} : Set Bool)} = 2⁻¹ := by
      rw [coinP_eval, coin_false]
    have h2 : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    rw [h2, ← h1]
    refine measure_mono fun ω hω => ⟨0, mem_univ _, ?_⟩
    have hω' : ω 0 = false := hω
    have hstep : SeqRejectable (1 / 2) (graphWeights fixedSequenceGraph)
        (fun j => coinp j ω) (insert 0 ∅) := by
      refine SeqRejectable.step SeqRejectable.empty (notMem_empty _) ?_
      rw [sdiff_empty, graphWeights_fixedSequenceGraph univ (mem_univ _)]
      simp [coinp, val, hω']
    exact (hstep.subset_closedTest (by norm_num) (monotoneWeights_graphWeights _) coinp ω)
      (mem_insert_self _ _)

/-! ### A worked example (graph of Bretz et al. 2009, p-values of Bretz et al. 2011) -/

/-- Initial weights: the level is split between the two primary hypotheses. -/
noncomputable def bretzW : Fin 4 → ℝ := ![1 / 2, 1 / 2, 0, 0]

/-- Initial transition matrix: each primary hypothesis passes half of its level to the other
primary hypothesis and half to its own secondary hypothesis; each secondary hypothesis passes
its level to the other primary hypothesis. -/
noncomputable def bretzG : Fin 4 → Fin 4 → ℝ :=
  !![0, 1 / 2, 1 / 2, 0; 1 / 2, 0, 0, 1 / 2; 0, 1, 0, 0; 1, 0, 0, 0]

lemma bretz_isGraph : IsGraph bretzW bretzG := by
  refine ⟨fun l => ?_, ?_, fun l m => ?_, fun l => ?_, fun l => ?_⟩
  · fin_cases l <;> simp [bretzW]
  · simp [Fin.sum_univ_four, bretzW]; norm_num
  · fin_cases l <;> fin_cases m <;> simp [bretzG]
  · fin_cases l <;> simp [bretzG]
  · fin_cases l <;> simp [Fin.sum_univ_four, bretzG] <;> norm_num

/-- The graph of the example. -/
noncomputable def bretz : GraphState (Fin 4) := GraphState.ofGraph bretz_isGraph

/-- **First update** (reject `H₂`, index `1`): weights `(3/4, 0, 0, 1/4)` and the transition
matrix of the paper's second graph. -/
theorem bretz_update_one :
    weightUpdate bretzW bretzG 1 = ![3 / 4, 0, 0, 1 / 4] ∧
      graphUpdate bretzG 1 = !![0, 0, 2 / 3, 1 / 3; 0, 0, 0, 0; 1 / 2, 0, 0, 1 / 2; 1, 0, 0, 0] := by
  constructor
  · funext l
    fin_cases l <;> simp [weightUpdate, bretzW, bretzG] <;> norm_num
  · funext l m
    fin_cases l <;> fin_cases m <;> simp [graphUpdate, bretzG] <;> norm_num

/-- **Second update** (then reject `H₁`, index `0`): weights `(0, 0, 1/2, 1/2)` and the two
secondary hypotheses pass their level to each other. -/
theorem bretz_update_two :
    weightUpdate ![3 / 4, 0, 0, 1 / 4]
        !![0, 0, 2 / 3, 1 / 3; 0, 0, 0, 0; 1 / 2, 0, 0, 1 / 2; 1, 0, 0, 0] 0
        = ![0, 0, 1 / 2, 1 / 2] ∧
      graphUpdate !![0, 0, 2 / 3, 1 / 3; 0, 0, 0, 0; 1 / 2, 0, 0, 1 / 2; (1 : ℝ), 0, 0, 0] 0
        = !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := by
  constructor
  · funext l
    fin_cases l <;> simp [weightUpdate] <;> norm_num
  · funext l m
    fin_cases l <;> fin_cases m <;> simp [graphUpdate] <;> norm_num

lemma bretz_weights_one : graphWeights bretz (univ \ {1}) = ![3 / 4, 0, 0, 1 / 4] := by
  have h : graphWeights bretz (univ \ insert 1 ∅)
      = weightUpdate (graphWeights bretz (univ \ ∅)) (bretz.removeAll ∅).trans 1 :=
    graphWeights_sdiff_insert bretz (notMem_empty _)
  rw [sdiff_empty, graphWeights_univ, GraphState.removeAll_empty] at h
  rw [show ({1} : Finset (Fin 4)) = insert 1 ∅ from rfl, h]
  exact bretz_update_one.1

lemma bretz_trans_one : (bretz.removeAll {1}).trans
    = !![0, 0, 2 / 3, 1 / 3; 0, 0, 0, 0; 1 / 2, 0, 0, 1 / 2; 1, 0, 0, 0] := by
  rw [show ({1} : Finset (Fin 4)) = insert 1 ∅ from rfl,
    GraphState.removeAll_insert _ (notMem_empty _), GraphState.removeAll_empty,
    GraphState.trans_remove]
  exact bretz_update_one.2

lemma bretz_weights_two : graphWeights bretz (univ \ {0, 1}) = ![0, 0, 1 / 2, 1 / 2] := by
  have h01 : (0 : Fin 4) ∉ ({1} : Finset (Fin 4)) := by decide
  rw [show ({0, 1} : Finset (Fin 4)) = insert 0 {1} from rfl,
    graphWeights_sdiff_insert bretz h01, bretz_weights_one, bretz_trans_one]
  exact bretz_update_two.1

/-- The unadjusted p-values of the example. -/
noncomputable def bretzP : Fin 4 → Unit → ℝ := fun i _ => ![0.01, 0.005, 0.1, 0.5] i

/-- **The worked example.** At level `α = 0.025` Algorithm 1 rejects `H₂` (`0.005 ≤ α / 2`),
then `H₁` (`0.01 ≤ 3 α / 4`), and then stops (`0.1, 0.5 > α / 2`); hence the closed weighted
Bonferroni test of the graph rejects exactly `{H₁, H₂}`. -/
theorem bretz_closedTest :
    closedTest (weightedLocal 0.025 (graphWeights bretz) bretzP) () = {0, 1} := by
  have h01 : (0 : Fin 4) ∉ ({1} : Finset (Fin 4)) := by decide
  refine graphical_eq_closedTest (by norm_num) bretz bretzP () ?_ ?_
  · have h1 : SeqRejectable 0.025 (graphWeights bretz) (fun j => bretzP j ()) (insert 1 ∅) := by
      refine SeqRejectable.step SeqRejectable.empty (notMem_empty _) ?_
      rw [sdiff_empty, graphWeights_univ]
      simp [bretz, bretzW, bretzP]; norm_num
    refine SeqRejectable.step h1 h01 ?_
    rw [bretz_weights_one]
    simp [bretzP]; norm_num
  · intro i hi
    rw [bretz_weights_two]
    fin_cases i
    · exact absurd (by decide) hi
    · exact absurd (by decide) hi
    · simp [bretzP]; norm_num
    · simp [bretzP]; norm_num

/-! ### Exact identities: independent uniform p-values exist -/

/-- The uniform law on `[0, 1]`. -/
noncomputable def unif : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure unif := ⟨by simp [unif]⟩

/-- The uniform law on the unit square. -/
noncomputable def unifP : Measure (Fin 2 → ℝ) := Measure.pi fun _ => unif

instance : IsProbabilityMeasure unifP := by unfold unifP; infer_instance

lemma unif_iIndepFun : iIndepFun (fun (i : Fin 2) (ω : Fin 2 → ℝ) => ω i) unifP :=
  iIndepFun_pi (X := fun _ : Fin 2 => (id : ℝ → ℝ)) fun _ => measurable_id.aemeasurable

lemma unif_isUniform (i : Fin 2) : IsUniformPValue unifP fun ω : Fin 2 → ℝ => ω i :=
  isUniformPValue_of_map_eq (measurable_pi_apply i)
    (measurePreserving_eval (fun _ : Fin 2 => unif) i).map_eq

/-- **Simes identity, non-vacuous**: on the unit square the Simes test at level `α ∈ [0, 1]`
rejects with probability exactly `α`. -/
theorem simes_identity_unif (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    unifP {ω | 1 ≤ bhK α fun j : Fin 2 => ω j} = ENNReal.ofReal α :=
  measure_one_le_bhK_eq unifP hα0 hα1 _ measurable_pi_apply unif_iIndepFun unif_isUniform

/-- **Exact Šidák, non-vacuous.** -/
theorem sidak_exact_unif (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    fwer unifP univ (sidak α fun (i : Fin 2) (ω : Fin 2 → ℝ) => ω i) = ENNReal.ofReal α :=
  fwer_sidak_eq unifP _ measurable_pi_apply unif_iIndepFun unif_isUniform α hα0 hα1

/-- **Exact Benjamini–Hochberg, non-vacuous**: with both hypotheses true nulls the false
discovery rate is exactly `α`; with one of two it is exactly `α / 2`. -/
theorem bh_exact_unif (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    fdr unifP {0} (fun ω : Fin 2 → ℝ => bhReject α fun j => ω j) = ENNReal.ofReal (α / 2) := by
  have h := fdr_bhReject_eq unifP hα0 hα1 (fun (i : Fin 2) (ω : Fin 2 → ℝ) => ω i)
    measurable_pi_apply {0} (fun i _ => unif_isUniform i)
    (fun i _ => indepFun_update_of_iIndepFun unifP _ measurable_pi_apply unif_iIndepFun i)
  simpa using h

end Applied.MultipleTesting.Sanity
