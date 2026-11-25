import Applied.Learning.SampleCompressionBounds
import Applied.Learning.PACFinite

/-!
# Compression implies generalization (Littlestone–Warmuth, realizable case)

The sample is a family `Z : Fin n → Ω → X × Bool` of independent labelled examples on a
probability space `(Ω, μ)`, each with law `P` (`μ.map (Z i) = P`), on a finite domain `X` whose
singletons are measurable. The sample, as a finite set of labelled examples, is
`sampleSet Z ω`; a hypothesis `h` errs on the region `errorRegion h = {(x, y) | h x ≠ y}` and
its true error is `P (errorRegion h)`.

* `measureReal_forall_mem_notMem`: for a finite set `S` of indices,
  `P(∀ i ∈ S, Z i ∉ A) = (1 - P A) ^ |S|`.
* `measureReal_bad_index`: for a fixed index set `I` and any reconstruction map, the
  probability that the hypothesis rebuilt from the examples indexed by `I` has true error
  above `ε` and makes no error on the other examples is at most `(1 - ε) ^ (n - |I|)`.
* `compression_generalization`: for a compression scheme of size `k`,
  `P(sample realizable ∧ reconstructed hypothesis has true error > ε)
  ≤ ∑_{i ≤ k} C(n, i) (1 - ε) ^ (n - i)`. (On a realizable sample the reconstructed hypothesis
  is automatically consistent with the sample.)
* `compression_generalization_target`: the same bound for the event "true error > ε" when every
  example is labelled by a fixed target concept of the class.
* `compression_generalization_pi`: the bound on the product space `((X × Bool)ⁿ, Pⁿ)`.
-/

open MeasureTheory ProbabilityTheory Finset

set_option linter.unusedSectionVars false

namespace Applied.Learning

variable {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X]
  [MeasurableSingletonClass X]
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Measure (X × Bool)} {n : ℕ} {Z : Fin n → Ω → X × Bool}

/-- The examples on which the hypothesis `h` errs. -/
def errorRegion (h : X → Bool) : Set (X × Bool) := {z | h z.1 ≠ z.2}

/-- The sample `Z 1 ω, …, Z n ω` as a finite set of labelled examples (repetitions merged). -/
def sampleSet (Z : Fin n → Ω → X × Bool) (ω : Ω) : Finset (X × Bool) :=
  univ.image (fun i => Z i ω)

/-- Every set in a finite type with measurable singletons is measurable. -/
lemma measurableSet_of_finite {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Finite α] (s : Set α) : MeasurableSet s :=
  s.toFinite.measurableSet

/-- For a finite set `S` of indices, the probability that none of the independent examples
`W i`, `i ∈ S`, falls in `A` is `(1 - Q A) ^ |S|`. -/
theorem measureReal_forall_mem_notMem {ι Y : Type*} [MeasurableSpace Y] {W : ι → Ω → Y}
    {Q : Measure Y} (hW : ∀ i, Measurable (W i)) (hind : iIndepFun W μ)
    (hlaw : ∀ i, μ.map (W i) = Q) (S : Finset ι) {A : Set Y} (hA : MeasurableSet A) :
    μ.real {ω | ∀ i ∈ S, W i ω ∉ A} = (1 - Q.real A) ^ S.card := by
  have hset : {ω | ∀ i ∈ S, W i ω ∉ A} = ⋂ i ∈ S, W i ⁻¹' Aᶜ := by
    ext ω; simp
  have hprod : μ (⋂ i ∈ S, W i ⁻¹' Aᶜ) = ∏ i ∈ S, μ (W i ⁻¹' Aᶜ) :=
    hind.meas_biInter (fun i _ => ⟨Aᶜ, hA.compl, rfl⟩)
  have hone : ∀ i, μ.real (W i ⁻¹' Aᶜ) = 1 - Q.real A := by
    intro i
    have h1 : μ.real (W i ⁻¹' Aᶜ) = 1 - μ.real (W i ⁻¹' A) := by
      rw [Set.preimage_compl, probReal_compl_eq_one_sub (hW i hA)]
    have h2 : μ.real (W i ⁻¹' A) = Q.real A := by
      rw [measureReal_def, measureReal_def, ← hlaw i, Measure.map_apply (hW i) hA]
    rw [h1, h2]
  rw [hset, measureReal_def, hprod, ENNReal.toReal_prod]
  simp only [← measureReal_def, hone, prod_const]

/-- **One index set.** For a fixed set `I` of indices and any reconstruction map `R`, the
probability that the hypothesis `R {Z i | i ∈ I}` has true error above `ε` and makes no error
on the examples outside `I` is at most `(1 - ε) ^ (n - |I|)`. -/
theorem measureReal_bad_index (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = P) (R : Finset (X × Bool) → X → Bool) (I : Finset (Fin n))
    {ε : ℝ} (hε : ε ≤ 1) :
    μ.real {ω | ε < P.real (errorRegion (R (I.image (fun i => Z i ω)))) ∧
        ∀ j ∉ I, Z j ω ∉ errorRegion (R (I.image (fun i => Z i ω)))}
      ≤ (1 - ε) ^ (n - I.card) := by
  classical
  set W : Ω → (I → X × Bool) := fun ω i => Z i ω with hW
  set V : Ω → ((Iᶜ : Finset (Fin n)) → X × Bool) := fun ω j => Z j ω with hV
  have hWm : Measurable W := measurable_pi_iff.2 (fun i => hZ i)
  have hWV : IndepFun W V μ := hind.indepFun_finset I Iᶜ disjoint_compl_right hZ
  set Φ : (I → X × Bool) → X → Bool := fun w => R (I.attach.image w) with hΦ
  have hΦW : ∀ ω, R (I.image (fun i => Z i ω)) = Φ (W ω) := by
    intro ω
    simp only [hΦ, hW]
    congr 1
    ext e
    simp
  have hc : (0 : ℝ) ≤ (1 - ε) ^ (n - I.card) := pow_nonneg (by linarith) _
  set bad := (univ : Finset (X → Bool)).filter (fun h => ε < P.real (errorRegion h)) with hbad
  have hsub : {ω | ε < P.real (errorRegion (R (I.image (fun i => Z i ω)))) ∧
        ∀ j ∉ I, Z j ω ∉ errorRegion (R (I.image (fun i => Z i ω)))}
      ⊆ ⋃ h ∈ bad, (W ⁻¹' (Φ ⁻¹' {h}) ∩ V ⁻¹' {v | ∀ j, v j ∉ errorRegion h}) := by
    rintro ω ⟨h1, h2⟩
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, exists_prop, hbad, mem_filter, mem_univ, true_and]
    refine ⟨Φ (W ω), by rwa [← hΦW], rfl, fun j => ?_⟩
    rw [← hΦW]
    exact h2 j (mem_compl.1 j.2)
  have hfac : ∀ h ∈ bad, μ.real (W ⁻¹' (Φ ⁻¹' {h}) ∩ V ⁻¹' {v | ∀ j, v j ∉ errorRegion h})
      ≤ μ.real (W ⁻¹' (Φ ⁻¹' {h})) * (1 - ε) ^ (n - I.card) := by
    intro h hh
    rw [hbad, mem_filter] at hh
    have hmul : μ.real (W ⁻¹' (Φ ⁻¹' {h}) ∩ V ⁻¹' {v | ∀ j, v j ∉ errorRegion h})
        = μ.real (W ⁻¹' (Φ ⁻¹' {h})) * μ.real (V ⁻¹' {v | ∀ j, v j ∉ errorRegion h}) := by
      simp only [measureReal_def]
      rw [hWV.measure_inter_preimage_eq_mul _ _ (measurableSet_of_finite _)
        (measurableSet_of_finite _), ENNReal.toReal_mul]
    rw [hmul]
    apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
    have hVset : V ⁻¹' {v | ∀ j, v j ∉ errorRegion h}
        = {ω | ∀ j ∈ Iᶜ, Z j ω ∉ errorRegion h} := by
      ext ω; simp [hV]
    rw [hVset, measureReal_forall_mem_notMem hZ hind hlaw Iᶜ (measurableSet_of_finite _),
      card_compl, Fintype.card_fin]
    rcases Nat.eq_zero_or_pos (n - I.card) with h0 | hpos
    · simp [h0]
    · have : IsProbabilityMeasure P := by
        obtain ⟨j, hj⟩ : ∃ j, j ∉ I := by
          by_contra hcon
          push Not at hcon
          have hI : I = univ := eq_univ_of_forall hcon
          rw [hI, card_univ, Fintype.card_fin] at hpos
          omega
        rw [← hlaw j]
        exact (Measure.isProbabilityMeasure_map_iff (hZ _).aemeasurable).mpr inferInstance
      have h1 : P.real (errorRegion h) ≤ 1 := measureReal_le_one
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hpart : ∑ h ∈ (univ : Finset (X → Bool)), μ.real (W ⁻¹' (Φ ⁻¹' {h})) ≤ 1 := by
    have := sum_measureReal_preimage_singleton (μ := μ) (univ : Finset (X → Bool))
      (f := Φ ∘ W) (fun y _ => hWm (measurableSet_of_finite (Φ ⁻¹' {y})))
    calc ∑ h ∈ (univ : Finset (X → Bool)), μ.real (W ⁻¹' (Φ ⁻¹' {h}))
        = μ.real ((Φ ∘ W) ⁻¹' ↑(univ : Finset (X → Bool))) := this
      _ ≤ 1 := measureReal_le_one
  calc μ.real {ω | ε < P.real (errorRegion (R (I.image (fun i => Z i ω)))) ∧
        ∀ j ∉ I, Z j ω ∉ errorRegion (R (I.image (fun i => Z i ω)))}
      ≤ μ.real (⋃ h ∈ bad, (W ⁻¹' (Φ ⁻¹' {h}) ∩ V ⁻¹' {v | ∀ j, v j ∉ errorRegion h})) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ h ∈ bad, μ.real (W ⁻¹' (Φ ⁻¹' {h}) ∩ V ⁻¹' {v | ∀ j, v j ∉ errorRegion h}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ h ∈ bad, μ.real (W ⁻¹' (Φ ⁻¹' {h})) * (1 - ε) ^ (n - I.card) := sum_le_sum hfac
    _ ≤ ∑ h ∈ (univ : Finset (X → Bool)), μ.real (W ⁻¹' (Φ ⁻¹' {h})) * (1 - ε) ^ (n - I.card) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => mul_nonneg measureReal_nonneg hc)
    _ = (∑ h ∈ (univ : Finset (X → Bool)), μ.real (W ⁻¹' (Φ ⁻¹' {h}))) *
          (1 - ε) ^ (n - I.card) := (sum_mul _ _ _).symm
    _ ≤ 1 * (1 - ε) ^ (n - I.card) := mul_le_mul_of_nonneg_right hpart hc
    _ = (1 - ε) ^ (n - I.card) := one_mul _

/-- **Compression implies generalization (Littlestone–Warmuth), realizable case.** For a
compression scheme `κ` of size `k` and `n` i.i.d. labelled examples, the probability that the
sample is realizable by `𝒞` and the hypothesis reconstructed from its compression has true error
above `ε` is at most `∑_{i ≤ k} C(n, i) (1 - ε) ^ (n - i)`. On a realizable sample that
hypothesis is consistent with the whole sample (`CompressionScheme.consistent`). -/
theorem compression_generalization {𝒞 : Finset (X → Bool)} {k : ℕ}
    (κ : CompressionScheme 𝒞 k) (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = P) {ε : ℝ} (hε : ε ≤ 1) :
    μ.real {ω | Realizable 𝒞 (sampleSet Z ω) ∧
        ε < P.real (errorRegion (κ.reconstruct (κ.compress (sampleSet Z ω))))}
      ≤ ∑ i ∈ range (k + 1), (n.choose i : ℝ) * (1 - ε) ^ (n - i) := by
  classical
  set B : Finset (Finset (Fin n)) :=
    (univ : Finset (Fin n)).powerset.filter (fun I => I.card ≤ k) with hB
  set bad : Finset (Fin n) → Set Ω := fun I =>
    {ω | ε < P.real (errorRegion (κ.reconstruct (I.image (fun i => Z i ω)))) ∧
      ∀ j ∉ I, Z j ω ∉ errorRegion (κ.reconstruct (I.image (fun i => Z i ω)))} with hbad
  have hsub : {ω | Realizable 𝒞 (sampleSet Z ω) ∧
        ε < P.real (errorRegion (κ.reconstruct (κ.compress (sampleSet Z ω))))}
      ⊆ ⋃ I ∈ B, bad I := by
    rintro ω ⟨hreal, hbig⟩
    set T := κ.compress (sampleSet Z ω) with hTdef
    have hT : T ⊆ sampleSet Z ω := κ.compress_subset _ hreal
    have hTk : T.card ≤ k := κ.card_compress_le _ hreal
    have hidx : ∀ t ∈ T, ∃ i, Z i ω = t := fun t ht => by
      obtain ⟨i, -, hi⟩ := mem_image.1 (hT ht)
      exact ⟨i, hi⟩
    let ι : T → Fin n := fun t => (hidx t.1 t.2).choose
    have hIT : (T.attach.image ι).image (fun i => Z i ω) = T := by
      ext e
      simp only [mem_image, mem_attach, true_and]
      constructor
      · rintro ⟨i, ⟨t, rfl⟩, rfl⟩
        rw [(hidx t.1 t.2).choose_spec]
        exact t.2
      · intro he
        exact ⟨ι ⟨e, he⟩, ⟨⟨e, he⟩, rfl⟩, (hidx e he).choose_spec⟩
    have hIk : (T.attach.image ι).card ≤ k :=
      card_image_le.trans (by rw [card_attach]; exact hTk)
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨T.attach.image ι, mem_filter.2 ⟨mem_powerset.2 (subset_univ _), hIk⟩, ?_, ?_⟩
    · rw [hIT]; exact hbig
    · intro j _
      rw [hIT]
      have := κ.consistent _ hreal (Z j ω) (mem_image_of_mem _ (mem_univ j))
      rw [← hTdef] at this
      simp [errorRegion, this]
  calc μ.real {ω | Realizable 𝒞 (sampleSet Z ω) ∧
        ε < P.real (errorRegion (κ.reconstruct (κ.compress (sampleSet Z ω))))}
      ≤ μ.real (⋃ I ∈ B, bad I) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ I ∈ B, μ.real (bad I) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ I ∈ B, (1 - ε) ^ (n - I.card) :=
        sum_le_sum fun I _ => measureReal_bad_index hZ hind hlaw κ.reconstruct I hε
    _ = ∑ i ∈ range (k + 1), (univ : Finset (Fin n)).card.choose i • (1 - ε) ^ (n - i) :=
        sum_powerset_filter_card_le _ k (fun i => (1 - ε) ^ (n - i))
    _ = ∑ i ∈ range (k + 1), (n.choose i : ℝ) * (1 - ε) ^ (n - i) := by
        simp [nsmul_eq_mul]

/-- **Compression implies generalization, with a target concept.** If every example is labelled
by a fixed concept `c ∈ 𝒞`, the probability that the hypothesis reconstructed from the
compressed sample has true error above `ε` is at most `∑_{i ≤ k} C(n, i) (1 - ε) ^ (n - i)`. -/
theorem compression_generalization_target {𝒞 : Finset (X → Bool)} {k : ℕ}
    (κ : CompressionScheme 𝒞 k) (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = P) {c : X → Bool} (hc : c ∈ 𝒞)
    (hlab : ∀ i ω, (Z i ω).2 = c (Z i ω).1) {ε : ℝ} (hε : ε ≤ 1) :
    μ.real {ω | ε < P.real (errorRegion (κ.reconstruct (κ.compress (sampleSet Z ω))))}
      ≤ ∑ i ∈ range (k + 1), (n.choose i : ℝ) * (1 - ε) ^ (n - i) := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (compression_generalization κ hZ hind hlaw hε)
  intro ω hω
  refine ⟨⟨c, hc, fun e he => ?_⟩, hω⟩
  obtain ⟨i, -, rfl⟩ := mem_image.1 he
  exact (hlab i ω).symm

/-- **Compression implies generalization on the product space.** The bound of
`compression_generalization` for `((X × Bool)ⁿ, Pⁿ)` with the coordinates as examples. -/
theorem compression_generalization_pi (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (n : ℕ) {𝒞 : Finset (X → Bool)} {k : ℕ} (κ : CompressionScheme 𝒞 k) {ε : ℝ}
    (hε : ε ≤ 1) :
    (Measure.pi fun _ : Fin n => P).real {s | Realizable 𝒞 (univ.image s) ∧
        ε < P.real (errorRegion (κ.reconstruct (κ.compress (univ.image s))))}
      ≤ ∑ i ∈ range (k + 1), (n.choose i : ℝ) * (1 - ε) ^ (n - i) := by
  refine compression_generalization (μ := Measure.pi fun _ : Fin n => P) (P := P)
    (Z := fun i s => s i) κ (fun i => measurable_pi_apply i) ?_ ?_ hε
  · exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  · intro i
    exact (measurePreserving_eval (μ := fun _ : Fin n => P) i).map_eq

end Applied.Learning
