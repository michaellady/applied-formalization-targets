import Applied.Statistics.Dunnett
import Applied.Statistics.WeightedSimes
import Applied.Statistics.CompatibleBounds
import Applied.Statistics.ConditionalError
import Applied.Statistics.InverseNormalCombination
import Applied.Statistics.GroupSequentialJointLaw

/-!
# More sanity checks on the canonical Gaussian model (red-team review)

Explicit instances, on `Applied.GroupSequential.canonicalMeasure` (independent standard
normal coordinates `coord i` on `ℝ^ℕ`), of the hypotheses of

* Dunnett's step-down and single-step theorems (`dunnett_canonical`): control `coord 0`,
  treatments `coord (j + 1)`;
* the weighted Simes local level under independence (`weightedSimes_canonical`), with the
  unequal weights `3/4`, `1/4`;
* the Holm-compatible simultaneous bounds (`holm_compatible_canonical`), with the p-value
  driven bounds `L i γ = ⊤` if `p i ≤ γ` and `⊥` otherwise, in `EReal` (the example described,
  but not formalized, in `Targets/Statistics/CompatibleBounds.lean`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Applied.RegulatorySanity

open Applied.GroupSequential Applied.MultipleTesting Applied.ConditionalError
  Applied.CombinationTests

/-! ### Dunnett -/

lemma indepFun_coord_zero_later (k : ℕ) :
    IndepFun (coord 0) (fun ω (j : Fin k) => coord ((j : ℕ) + 1) ω) canonicalMeasure := by
  have h := indep_firstStage_laterStages measurable_coord iIndepFun_coord 1
  have h1 : MeasurableSpace.comap (coord 0) inferInstance ≤ firstStage coord 1 :=
    le_biSup (fun j => MeasurableSpace.comap (coord j) inferInstance)
      (show (0 : ℕ) ∈ {i : ℕ | i < 1} by simp)
  have h2 : MeasurableSpace.comap (fun ω (j : Fin k) => coord ((j : ℕ) + 1) ω) inferInstance
      ≤ laterStages coord 1 := by
    refine (measurable_iff_comap_le (m₁ := laterStages coord 1)).mp ?_
    refine (@measurable_pi_iff _ _ _ (laterStages coord 1) _ _).mpr fun j => ?_
    exact (comap_measurable (coord ((j : ℕ) + 1))).mono
      (le_biSup (fun j => MeasurableSpace.comap (coord j) inferInstance)
        (show (j : ℕ) + 1 ∈ {i : ℕ | 1 ≤ i} by simp)) le_rfl
  exact indep_of_indep_of_le_left (indep_of_indep_of_le_right h h2) h1

/-- **The hypotheses of the Dunnett theorems are satisfiable**: `k` treatments against one
control in the canonical model, shifts `μ j`, true nulls `H₀` (those with `μ i ≤ 0`). -/
theorem dunnett_canonical {k : ℕ} (μ : Fin k → ℝ) (H₀ : Finset (Fin k)) (hμ : ∀ i ∈ H₀, μ i ≤ 0)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    fwer canonicalMeasure H₀ (dunnettStepDown α fun (j : Fin k) ω =>
        (coord ((j : ℕ) + 1) ω - coord 0 ω) / √2 + μ j) ≤ ENNReal.ofReal α ∧
    fwer canonicalMeasure H₀ (dunnettSingleStep α fun (j : Fin k) ω =>
        (coord ((j : ℕ) + 1) ω - coord 0 ω) / √2 + μ j) ≤ ENNReal.ofReal α := by
  have hinj : Function.Injective fun j : Fin k => (j : ℕ) + 1 := fun a b h =>
    Fin.val_injective (Nat.succ_injective h)
  exact ⟨fwer_dunnettStepDown_le canonicalMeasure (coord 0) (fun j : Fin k => coord ((j : ℕ) + 1))
      (measurable_coord 0) (fun j => measurable_coord _) (indepFun_coord_zero_later k)
      (iIndepFun_coord.precomp hinj) (map_coord 0) μ H₀ (fun i _ => map_coord _) hμ hα0 hα1,
    fwer_dunnettSingleStep_le canonicalMeasure (coord 0) (fun j : Fin k => coord ((j : ℕ) + 1))
      (measurable_coord 0) (fun j => measurable_coord _) (indepFun_coord_zero_later k)
      (iIndepFun_coord.precomp hinj) (map_coord 0) μ H₀ (fun i _ => map_coord _) hμ hα0 hα1⟩

/-- Dunnett's integral formula on the canonical model: the maximum of `k` comparison
statistics has distribution function `dunnettCDF k`. -/
theorem dunnett_integral_canonical (k : ℕ) (d : ℝ) :
    canonicalMeasure {ω | ∀ i ∈ (univ : Finset (Fin k)),
        (coord ((i : ℕ) + 1) ω - coord 0 ω) / √2 ≤ d} = ENNReal.ofReal (dunnettCDF k d) := by
  have hinj : Function.Injective fun j : Fin k => (j : ℕ) + 1 := fun a b h =>
    Fin.val_injective (Nat.succ_injective h)
  have := measure_forall_manyToOne_le canonicalMeasure (coord 0)
    (fun j : Fin k => coord ((j : ℕ) + 1)) (measurable_coord 0) (fun j => measurable_coord _)
    (indepFun_coord_zero_later k) (iIndepFun_coord.precomp hinj) (map_coord 0) univ
    (fun i _ => map_coord _) d
  simpa using this

/-! ### Weighted Simes -/

/-- **The hypotheses of the weighted Simes level theorem are satisfiable** with unequal
weights `3/4`, `1/4` on two independent one-sided z-test p-values. -/
theorem weightedSimes_canonical (H₀ : Finset (Fin 2)) {α : ℝ} (hα : 0 ≤ α) :
    canonicalMeasure {ω | weightedSimesLocal α (fun _ i => if i = 0 then 3 / 4 else 1 / 4)
        (fun (j : Fin 2) ω => normalTail (coord j ω)) H₀ ω} ≤ ENNReal.ofReal α := by
  refine measure_weightedSimesLocal_le canonicalMeasure hα
    (fun (j : Fin 2) ω => normalTail (coord j ω))
    (fun i => measurable_normalTail.comp (measurable_coord i))
    ((iIndepFun_coord.precomp Fin.val_injective).comp (fun _ => normalTail)
      fun _ => measurable_normalTail)
    H₀ (fun i _ => isValidPValue_zTest_upper canonicalMeasure (coord i) (measurable_coord i)
      (map_coord i)) (fun _ i => if i = 0 then 3 / 4 else 1 / 4)
    (fun i _ => by split_ifs <;> norm_num) ?_
  calc ∑ i ∈ H₀, (if i = 0 then (3 : ℝ) / 4 else 1 / 4)
      ≤ ∑ i : Fin 2, (if i = 0 then (3 : ℝ) / 4 else 1 / 4) :=
        Finset.sum_le_univ_sum_of_nonneg fun i => by split_ifs <;> norm_num
    _ = 1 := by rw [Fin.sum_univ_two]; norm_num

/-! ### Compatible simultaneous bounds -/

/-- P-value driven lower bounds in `EReal`: `⊤` if the p-value is at most `γ`, else `⊥`. -/
noncomputable def pBound (K : ℕ) (i : Fin K) (γ : ℝ) (ω : ℕ → ℝ) : EReal :=
  if normalTail (coord i ω) ≤ γ then ⊤ else ⊥

/-- **The hypotheses of the Holm-compatible bounds theorem are satisfiable.** True parameters
`θ i = 0`, margins `δ i = 0` (all nulls `θ i ≤ δ i` true), bounds `pBound`. -/
theorem holm_compatible_canonical (K : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    1 - ENNReal.ofReal α ≤ canonicalMeasure {ω |
      (∀ i ∈ holm α (fun (j : Fin K) ω => normalTail (coord j ω)) ω, (0 : EReal) < 0) ∧
      (∀ i ∉ holm α (fun (j : Fin K) ω => normalTail (coord j ω)) ω,
        pBound K i (α / ((univ \ holm α (fun (j : Fin K) ω => normalTail (coord j ω)) ω).card : ℝ))
          ω ≤ 0) ∧
      (holm α (fun (j : Fin K) ω => normalTail (coord j ω)) ω = univ →
        ∀ i, pBound K i (α / (Fintype.card (Fin K) : ℝ)) ω ≤ 0)} := by
  refine one_sub_le_measure_holm_compatible canonicalMeasure (fun _ => (0 : EReal))
    (fun _ => (0 : EReal)) (pBound K) (fun (j : Fin K) ω => normalTail (coord j ω)) α hα ?_ ?_ ?_
  · intro ω i γ₁ γ₂ _ h12
    unfold pBound
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans h12) h2
    · exact bot_le
    · exact le_rfl
  · intro i γ hγ
    refine (measure_mono ?_).trans
      (isValidPValue_zTest_upper canonicalMeasure (coord i) (measurable_coord i) (map_coord i)
        γ hγ)
    intro ω hω
    simp only [Set.mem_ofPred_eq, pBound] at hω ⊢
    by_contra hcon
    have hcon' : ¬ normalTail (coord i ω) ≤ γ := hcon
    simp only [hcon', ↓reduceIte] at hω
    exact not_lt_bot hω
  · intro ω i γ _
    unfold pBound
    split_ifs with h
    · simp [h]
    · simp [h]

end Applied.RegulatorySanity
