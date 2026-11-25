import Applied.Statistics.PRDSCommonFactor
import Applied.Statistics.StochasticOrderProduct

/-!
# Positive regression dependence in a mixture model ordered by a rank of the latent variable

`isPRDSOn_of_commonFactor` (`Applied/Statistics/PRDSCommonFactor.lean`) needs each p-value to be a
pointwise monotone function of a real common factor. That fails for two-sided tests: the
p-value `2 (1 - Φ(|a W + b ε|))` is not monotone in `W`, only its conditional *law* given `W = w`
is monotone, and it is monotone in `|w|`, not in `w`.

`isPRDSOn_of_rankedFactor` removes both restrictions. The latent variable `W` takes values in any
measurable space and is compared through a rank `r : 𝒲 → ℝ`; the noise variables take values in
any measurable space; and monotonicity is required of the conditional laws only:

* for every hypothesis `j`, the law of `h j w (ε j)` is stochastically non-increasing in `r w`;
* for every true null `i`, the law of `h i w (ε i)` is non-increasing in `r w` in the likelihood
  ratio order (set form).

The conclusion is `IsPRDSOn`, the conditioning-on-`p i ≤ t` form of positive regression
dependence of `Applied/Statistics/PRDS.lean` (not the definition of Benjamini and Yekutieli).

The proof follows `isPRDSOn_of_commonFactor`; the step "given `p i ≤ t` and the factor, the chance
of an increasing event decreases with the factor" now uses that the stochastic order is preserved
by finite products (`pi_upperSet_mul_le`).
-/

open MeasureTheory Finset ProbabilityTheory
open scoped ENNReal NNReal

namespace Applied.MultipleTesting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]

/-- **Positive regression dependence in a mixture model with a ranked latent variable.** Let `W`
be a random element of a measurable space `𝒲`, independent of the vector `(ε j)` of mutually
independent random elements of a measurable space `𝓔`, and let `p j = h j W (ε j)` with `h j`
jointly measurable. Let `r : 𝒲 → ℝ` be any function (the rank). Assume, for `r v ≤ r w`:

* (`hstoch`) for every `j` and measurable upper set `U ⊆ ℝ`,
  `P (h j w (ε j) ∈ U) ≤ P (h j v (ε j) ∈ U)`;
* (`hMLR`) for every true null `i` and measurable `L`, `R ⊆ ℝ` with every point of `L` strictly
  below every point of `R`,
  `P (h i v (ε i) ∈ L) * P (h i w (ε i) ∈ R) ≤ P (h i w (ε i) ∈ L) * P (h i v (ε i) ∈ R)`.

Then the p-values are positively regression dependent on the true nulls. -/
theorem isPRDSOn_of_rankedFactor {𝒲 𝓔 : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝓔]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → 𝒲) (ε : ι → Ω → 𝓔) (hW : Measurable W)
    (hε : ∀ j, Measurable (ε j)) (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (h : ι → 𝒲 → 𝓔 → ℝ) (hh : ∀ j, Measurable (Function.uncurry (h j))) (r : 𝒲 → ℝ)
    (H₀ : Finset ι)
    (hstoch : ∀ j, ∀ v w : 𝒲, r v ≤ r w → ∀ U : Set ℝ, MeasurableSet U → IsUpperSet U →
      P {ω | h j w (ε j ω) ∈ U} ≤ P {ω | h j v (ε j ω) ∈ U})
    (hMLR : ∀ i ∈ H₀, ∀ v w : 𝒲, r v ≤ r w → ∀ L R : Set ℝ, MeasurableSet L →
      MeasurableSet R → (∀ x ∈ L, ∀ y ∈ R, x < y) →
      P {ω | h i v (ε i ω) ∈ L} * P {ω | h i w (ε i ω) ∈ R} ≤
        P {ω | h i w (ε i ω) ∈ L} * P {ω | h i v (ε i ω) ∈ R}) :
    IsPRDSOn P (fun j ω => h j (W ω) (ε j ω)) H₀ := by
  intro i hi D hD hup s t hst
  have hhw : ∀ j w, Measurable (h j w) := fun j w => (hh j).comp measurable_prodMk_left
  -- the probabilities with the latent variable frozen at `w`
  set A : ℝ → 𝒲 → ℝ≥0∞ := fun u w =>
    P ((fun ω j => h j w (ε j ω)) ⁻¹' D ∩ (fun ω => h i w (ε i ω)) ⁻¹' Set.Iic u) with hAdef
  set q : ℝ → 𝒲 → ℝ≥0∞ := fun u w => P ((fun ω => h i w (ε i ω)) ⁻¹' Set.Iic u) with hqdef
  have hAfin : ∀ u w, A u w ≠ ∞ := fun u w => measure_ne_top _ _
  have hqfin : ∀ u w, q u w ≠ ∞ := fun u w => measure_ne_top _ _
  -- (i) for a frozen latent variable the p-values are independent, hence PRDS
  have hI : ∀ w, A s w * q t w ≤ A t w * q s w := by
    intro w
    have hprds := isPRDSOn_of_iIndepFun P (fun j ω => h j w (ε j ω))
      (fun j => (hhw j w).comp (hε j)) (hindep.comp (fun j => h j w) (fun j => hhw j w)) {i}
    exact hprds i (mem_singleton_self i) D hD hup s t hst
  -- the likelihood-ratio hypothesis, in terms of `lam w S = P (p i ∈ S | W = w)`
  set lam : 𝒲 → Set ℝ → ℝ≥0∞ := fun w S => P {ω | h i w (ε i ω) ∈ S} with hlam
  have hlamIic : ∀ u w, lam w (Set.Iic u) = q u w := fun u w => rfl
  have hmlr : ∀ v w : 𝒲, r v ≤ r w → ∀ L R : Set ℝ, MeasurableSet L → MeasurableSet R →
      (∀ x ∈ L, ∀ y ∈ R, x < y) → lam v L * lam w R ≤ lam w L * lam v R := hMLR i hi
  have hlam_meas : ∀ w S, MeasurableSet S → MeasurableSet {ω | h i w (ε i ω) ∈ S} :=
    fun w S hS => ((hhw i w).comp (hε i)) hS
  have hlam_split : ∀ w (L R : Set ℝ), MeasurableSet R → Disjoint L R →
      lam w (L ∪ R) = lam w L + lam w R := by
    intro w L R hR hLR
    have hd : Disjoint {ω | h i w (ε i ω) ∈ L} {ω | h i w (ε i ω) ∈ R} :=
      Set.disjoint_left.mpr fun ω hL hR' => Set.disjoint_left.mp hLR hL hR'
    exact measure_union hd (hlam_meas w R hR)
  -- (iii) total positivity of the conditional distribution functions
  have hIII : ∀ v w, r v ≤ r w → q s v * q t w ≤ q s w * q t v := by
    intro v w hvw
    have hsplit : ∀ x, q t x = q s x + lam x (Set.Ioc s t) := by
      intro x
      rw [← hlamIic t x, ← hlamIic s x, ← Set.Iic_union_Ioc_eq_Iic hst]
      exact hlam_split x _ _ measurableSet_Ioc
        (Set.disjoint_left.mpr fun y hy hy' => not_lt.mpr hy hy'.1)
    have hm := hmlr v w hvw (Set.Iic s) (Set.Ioc s t) measurableSet_Iic measurableSet_Ioc
      (fun x hx y hy => lt_of_le_of_lt hx hy.1)
    rw [hlamIic, hlamIic] at hm
    rw [hsplit w, hsplit v, mul_add, mul_add, mul_comm (q s v) (q s w)]
    exact add_le_add le_rfl hm
  -- given `p i ≤ t`, the law of `p i` decreases stochastically with the rank
  have hC : ∀ v w, r v ≤ r w → ∀ U : Set ℝ, MeasurableSet U → IsUpperSet U →
      lam w (U ∩ Set.Iic t) * q t v ≤ lam v (U ∩ Set.Iic t) * q t w := by
    intro v w hvw U hU hUup
    have hset : (Set.Iic t \ U) ∪ (U ∩ Set.Iic t) = Set.Iic t := by
      ext y
      by_cases hy : y ∈ U <;> simp [hy]
    have hsplit : ∀ x, q t x = lam x (Set.Iic t \ U) + lam x (U ∩ Set.Iic t) := by
      intro x
      rw [← hlamIic t x, ← hlam_split x _ _ (hU.inter measurableSet_Iic)
        (Set.disjoint_left.mpr fun y (hy : y ∈ Set.Iic t \ U) (hy' : y ∈ U ∩ Set.Iic t) =>
          hy.2 hy'.1), hset]
    have hm := hmlr v w hvw (Set.Iic t \ U) (U ∩ Set.Iic t) (measurableSet_Iic.diff hU)
      (hU.inter measurableSet_Iic)
      (fun x (hx : x ∈ Set.Iic t \ U) y (hy : y ∈ U ∩ Set.Iic t) => by
        by_contra hcon
        exact hx.2 (hUup (not_lt.mp hcon) hy.1))
    rw [hsplit v, hsplit w, mul_add, mul_add,
      mul_comm (lam w (U ∩ Set.Iic t)) (lam v (U ∩ Set.Iic t))]
    refine add_le_add ?_ le_rfl
    rw [mul_comm (lam w (U ∩ Set.Iic t)), mul_comm (lam v (U ∩ Set.Iic t))]
    exact hm
  -- (ii) given `p i ≤ t`, the chance of the increasing event decreases with the rank:
  -- for a frozen latent variable the vector of p-values has a product law
  set S : ι → Set ℝ := Function.update (fun _ => Set.univ) i (Set.Iic t) with hS
  have hSi : S i = Set.Iic t := by simp [hS]
  have hSj : ∀ j, j ≠ i → S j = Set.univ := fun j hj => by simp [hS, hj]
  have hSpi : {y : ι → ℝ | y i ≤ t} = Set.univ.pi S := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hy j
      by_cases hj : j = i
      · subst hj; rw [hSi]; exact hy
      · rw [hSj j hj]; exact Set.mem_univ _
    · intro hy
      have := hy i
      rwa [hSi] at this
  have hApi : ∀ w, A t w =
      Measure.pi (fun j => (P.map fun ω => h j w (ε j ω)).restrict (S j)) D := by
    intro w
    have hm : ∀ j, Measurable fun ω => h j w (ε j ω) := fun j => (hhw j w).comp (hε j)
    have hpi : P.map (fun ω j => h j w (ε j ω)) = Measure.pi fun j => P.map fun ω => h j w (ε j ω) :=
      (iIndepFun_iff_map_fun_eq_pi_map fun j => (hm j).aemeasurable).mp
        (hindep.comp (fun j => h j w) (fun j => hhw j w))
    have hTm : MeasurableSet {y : ι → ℝ | y i ≤ t} :=
      measurableSet_le (measurable_pi_apply i) measurable_const
    have hpre : (fun ω j => h j w (ε j ω)) ⁻¹' D ∩ (fun ω => h i w (ε i ω)) ⁻¹' Set.Iic t
        = (fun ω j => h j w (ε j ω)) ⁻¹' (D ∩ {y : ι → ℝ | y i ≤ t}) := rfl
    simp only [hAdef]
    rw [hpre, ← Measure.map_apply (measurable_pi_iff.mpr hm) (hD.inter hTm), hpi,
      ← Measure.restrict_apply hD, hSpi, Measure.restrict_pi_pi]
  have hII : ∀ v w, r v ≤ r w → A t w * q t v ≤ A t v * q t w := by
    intro v w hvw
    have hmx : ∀ j x, Measurable fun ω => h j x (ε j ω) := fun j x => (hhw j x).comp (hε j)
    rw [hApi w, hApi v, mul_comm, mul_comm _ (q t w)]
    refine pi_upperSet_mul_le _ _ i (q t w) (q t v) (fun j hj U hU hUup => ?_)
      (fun U hU hUup => ?_) hD hup
    · rw [hSj j hj, Measure.restrict_univ, Measure.restrict_univ,
        Measure.map_apply (hmx j w) hU, Measure.map_apply (hmx j v) hU]
      exact hstoch j v w hvw U hU hUup
    · rw [hSi, Measure.restrict_apply hU, Measure.restrict_apply hU,
        Measure.map_apply (hmx i w) (hU.inter measurableSet_Iic),
        Measure.map_apply (hmx i v) (hU.inter measurableSet_Iic),
        mul_comm, mul_comm (q t w)]
      exact hC v w hvw U hU hUup
  -- the symmetrised pointwise inequality
  have hpt : ∀ v w, r v ≤ r w →
      A s w * q t v + A s v * q t w ≤ A t w * q s v + A t v * q s w := by
    intro v w hvw
    have hAq : ∀ u x, A u x ≤ q u x := fun u x => measure_mono Set.inter_subset_right
    have hqmono : ∀ x, q s x ≤ q t x := fun x =>
      measure_mono (Set.preimage_mono (Set.Iic_subset_Iic.mpr hst))
    have toR : ∀ {a b c d : ℝ≥0∞}, a ≠ ∞ → b ≠ ∞ → c ≠ ∞ → d ≠ ∞ → a * b ≤ c * d →
        a.toReal * b.toReal ≤ c.toReal * d.toReal := by
      intro a b c d ha hb hc hd hle
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top hc hd) hle
      rwa [ENNReal.toReal_mul, ENNReal.toReal_mul] at this
    have hcore := commonFactor_core (X := (A s w).toReal) (X' := (A s v).toReal)
      (Y := (A t w).toReal) (Y' := (A t v).toReal) (a := (q s w).toReal)
      (a' := (q s v).toReal) (b := (q t w).toReal) (b' := (q t v).toReal)
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (ENNReal.toReal_mono (hqfin s w) (hAq s w)) (ENNReal.toReal_mono (hqfin t w) (hqmono w))
      (ENNReal.toReal_mono (hqfin s v) (hAq s v)) (ENNReal.toReal_mono (hqfin t v) (hqmono v))
      (toR (hAfin s w) (hqfin t w) (hAfin t w) (hqfin s w) (hI w))
      (toR (hAfin s v) (hqfin t v) (hAfin t v) (hqfin s v) (hI v))
      (toR (hAfin t w) (hqfin t v) (hAfin t v) (hqfin t w) (hII v w hvw))
      (toR (hqfin s v) (hqfin t w) (hqfin s w) (hqfin t v) (hIII v w hvw))
    have hfinL : A s w * q t v + A s v * q t w ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (hAfin s w) (hqfin t v),
        ENNReal.mul_ne_top (hAfin s v) (hqfin t w)⟩
    have hfinR : A t w * q s v + A t v * q s w ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (hAfin t w) (hqfin s v),
        ENNReal.mul_ne_top (hAfin t v) (hqfin s w)⟩
    rw [← ENNReal.toReal_le_toReal hfinL hfinR,
      ENNReal.toReal_add (ENNReal.mul_ne_top (hAfin s w) (hqfin t v))
        (ENNReal.mul_ne_top (hAfin s v) (hqfin t w)),
      ENNReal.toReal_add (ENNReal.mul_ne_top (hAfin t w) (hqfin s v))
        (ENNReal.mul_ne_top (hAfin t v) (hqfin s w)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul]
    exact hcore
  -- disintegration along the latent variable
  set E : Ω → ι → 𝓔 := fun ω j => ε j ω with hE
  have hEm : Measurable E := measurable_pi_iff.mpr hε
  set μ : Measure 𝒲 := P.map W with hμ
  set ν : Measure (ι → 𝓔) := P.map E with hν
  have hjoint : P.map (fun ω => (W ω, E ω)) = μ.prod ν :=
    hWε.map_prod_eq_prod_map_map hW.aemeasurable hEm.aemeasurable
  set G : 𝒲 × (ι → 𝓔) → ι → ℝ := fun z j => h j z.1 (z.2 j) with hG
  have hGm : Measurable G := measurable_pi_iff.mpr fun j =>
    (hh j).comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hTm : ∀ u, MeasurableSet {z : 𝒲 × (ι → 𝓔) | h i z.1 (z.2 i) ≤ u} := fun u =>
    measurableSet_le
      ((hh i).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
      measurable_const
  have hSm : ∀ u, MeasurableSet (G ⁻¹' D ∩ {z : 𝒲 × (ι → 𝓔) | h i z.1 (z.2 i) ≤ u}) :=
    fun u => (hGm hD).inter (hTm u)
  have hAsec : ∀ u w, ν (Prod.mk w ⁻¹' (G ⁻¹' D ∩ {z : 𝒲 × (ι → 𝓔) | h i z.1 (z.2 i) ≤ u}))
      = A u w := by
    intro u w
    rw [hν, Measure.map_apply hEm (measurable_prodMk_left (hSm u))]
    rfl
  have hqsec : ∀ u w, ν (Prod.mk w ⁻¹' {z : 𝒲 × (ι → 𝓔) | h i z.1 (z.2 i) ≤ u}) = q u w := by
    intro u w
    rw [hν, Measure.map_apply hEm (measurable_prodMk_left (hTm u))]
    rfl
  have hAm : ∀ u, Measurable (A u) := by
    intro u
    have := measurable_measure_prodMk_left (ν := ν) (hSm u)
    simpa only [hAsec] using this
  have hqm : ∀ u, Measurable (q u) := by
    intro u
    have := measurable_measure_prodMk_left (ν := ν) (hTm u)
    simpa only [hqsec] using this
  have hAint : ∀ u, P ((fun ω j => h j (W ω) (ε j ω)) ⁻¹' D ∩
      (fun ω => h i (W ω) (ε i ω)) ⁻¹' Set.Iic u) = ∫⁻ w, A u w ∂μ := by
    intro u
    have hpre : (fun ω j => h j (W ω) (ε j ω)) ⁻¹' D ∩ (fun ω => h i (W ω) (ε i ω)) ⁻¹' Set.Iic u
        = (fun ω => (W ω, E ω)) ⁻¹' (G ⁻¹' D ∩ {z : 𝒲 × (ι → 𝓔) | h i z.1 (z.2 i) ≤ u}) := rfl
    rw [hpre, ← Measure.map_apply (hW.prodMk hEm) (hSm u), hjoint, Measure.prod_apply (hSm u)]
    exact lintegral_congr fun w => hAsec u w
  have hqint : ∀ u, P ((fun ω => h i (W ω) (ε i ω)) ⁻¹' Set.Iic u) = ∫⁻ w, q u w ∂μ := by
    intro u
    have hpre : (fun ω => h i (W ω) (ε i ω)) ⁻¹' Set.Iic u
        = (fun ω => (W ω, E ω)) ⁻¹' {z : 𝒲 × (ι → 𝓔) | h i z.1 (z.2 i) ≤ u} := rfl
    rw [hpre, ← Measure.map_apply (hW.prodMk hEm) (hTm u), hjoint, Measure.prod_apply (hTm u)]
    exact lintegral_congr fun w => hqsec u w
  -- symmetrisation over two independent copies of the latent variable
  have hsym : ∀ u u' : ℝ, 2 * ((∫⁻ w, A u w ∂μ) * ∫⁻ w, q u' w ∂μ) =
      ∫⁻ z, (A u z.1 * q u' z.2 + A u z.2 * q u' z.1) ∂(μ.prod μ) := by
    intro u u'
    rw [lintegral_add_left (show Measurable (fun z : 𝒲 × 𝒲 => A u z.1 * q u' z.2) from
        ((hAm u).comp measurable_fst).mul ((hqm u').comp measurable_snd)),
      lintegral_prod_mul (hAm u).aemeasurable (hqm u').aemeasurable]
    have hswap : ∫⁻ z, A u z.2 * q u' z.1 ∂(μ.prod μ) =
        (∫⁻ w, A u w ∂μ) * ∫⁻ w, q u' w ∂μ := by
      have : (fun z : 𝒲 × 𝒲 => A u z.2 * q u' z.1) = fun z => q u' z.1 * A u z.2 := by
        funext z; exact mul_comm _ _
      rw [this, lintegral_prod_mul (hqm u').aemeasurable (hAm u).aemeasurable, mul_comm]
    rw [hswap, two_mul]
  change P ((fun ω j => h j (W ω) (ε j ω)) ⁻¹' D ∩ (fun ω => h i (W ω) (ε i ω)) ⁻¹' Set.Iic s) *
      P ((fun ω => h i (W ω) (ε i ω)) ⁻¹' Set.Iic t) ≤
    P ((fun ω j => h j (W ω) (ε j ω)) ⁻¹' D ∩ (fun ω => h i (W ω) (ε i ω)) ⁻¹' Set.Iic t) *
      P ((fun ω => h i (W ω) (ε i ω)) ⁻¹' Set.Iic s)
  rw [hAint s, hAint t, hqint s, hqint t]
  have h2 : (2 : ℝ≥0∞) * ((∫⁻ w, A s w ∂μ) * ∫⁻ w, q t w ∂μ) ≤
      2 * ((∫⁻ w, A t w ∂μ) * ∫⁻ w, q s w ∂μ) := by
    rw [hsym s t, hsym t s]
    refine lintegral_mono fun z => ?_
    rcases le_total (r z.2) (r z.1) with hle | hle
    · exact hpt z.2 z.1 hle
    · have := hpt z.1 z.2 hle
      rw [add_comm (A s z.1 * q t z.2), add_comm (A t z.1 * q s z.2)]
      exact this
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2

end Applied.MultipleTesting
