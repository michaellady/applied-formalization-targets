import Applied.Statistics.PRDSIndependent
import Applied.Statistics.PRDSExamples
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF

/-!
# Positive dependence in the common-factor model

Test statistics `Z j = c j * W + d j * ε j` share a common factor `W` and have independent
idiosyncratic noise `ε j`. With non-negative loadings `c j` and one-sided p-values
`p j = ψ j (Z j)`, `ψ j` non-increasing, the p-values are positively regression dependent on
the true nulls (`IsPRDSOn`, the conditioning-on-`p i ≤ t` form of `Applied/Statistics/PRDS.lean`)
as soon as the noise of every true null is normal. The equicorrelated normal model
`Z j = √ρ W + √(1 - ρ) ε j`, `p j = 1 - Φ (Z j)`, `0 ≤ ρ ≤ 1`, is the special case of interest.

## Main results

* `isPRDSOn_of_commonFactor`: the general statement. `p j = h j W (ε j)` with `W` independent
  of the mutually independent `ε j`, each `h j` non-increasing in the common factor, and a
  monotone likelihood ratio condition (in set form) on the conditional law of each true-null
  p-value given `W = w`.
* `gaussianReal_mul_le_of_le`: the monotone likelihood ratio property of the normal location
  family, in set form.
* `isPRDSOn_gaussian_commonFactor`: `p j = ψ j (c j * W + d j * ε j)`, `ψ j` non-increasing,
  `c j ≥ 0`, and for the true nulls `d i ≠ 0` and `ε i` standard normal.
* `isPRDSOn_equicorrelated_gaussian`: `p j = 1 - Φ (√ρ W + √(1 - ρ) ε j)` for `0 ≤ ρ ≤ 1`.
* `map_equicorrelated_gaussian`: in that model with `W` standard normal, each `Z j` is
  standard normal.
* `covariance_equicorrelated`: two such statistics have covariance `ρ`.

## Proof

Condition on `W = w`. Given `w` the p-values are independent, hence positively regression
dependent (`isPRDSOn_of_iIndepFun`). As `w` grows every p-value decreases, and the conditional
law of a true-null p-value given `W = w` decreases in the likelihood ratio order. The two
facts are combined by symmetrising a double integral over two independent copies of `W`
(Chebyshev's association inequality for two monotone functions of one variable, in a
denominator-free form).
-/

open MeasureTheory Finset ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Applied.MultipleTesting

/-- Algebraic core of the mixture argument. -/
lemma commonFactor_core {X X' Y Y' a a' b b' : ℝ} (hX : 0 ≤ X) (hX' : 0 ≤ X') (hY : 0 ≤ Y)
    (hY' : 0 ≤ Y') (ha : 0 ≤ a) (ha' : 0 ≤ a') (hXa : X ≤ a) (hab : a ≤ b) (hXa' : X' ≤ a')
    (hab' : a' ≤ b') (h1 : X * b ≤ Y * a) (h1' : X' * b' ≤ Y' * a') (h2 : Y * b' ≤ Y' * b)
    (h3 : a' * b ≤ a * b') : X * b' + X' * b ≤ Y * a' + Y' * a := by
  have hb : 0 ≤ b := ha.trans hab
  have hb' : 0 ≤ b' := ha'.trans hab'
  rcases hb.eq_or_lt with hb0 | hbpos
  · have hX0 : X = 0 := le_antisymm (by linarith) hX
    rw [hX0, ← hb0]
    have := mul_nonneg hY ha'
    have := mul_nonneg hY' ha
    linarith
  rcases hb'.eq_or_lt with hb0' | hbpos'
  · have hX0 : X' = 0 := le_antisymm (by linarith) hX'
    rw [hX0, ← hb0']
    have := mul_nonneg hY ha'
    have := mul_nonneg hY' ha
    linarith
  have key : (X * b' + X' * b) * (b * b') ≤ (Y * a' + Y' * a) * (b * b') := by
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg b'),
      mul_le_mul_of_nonneg_right h1' (sq_nonneg b),
      mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3)]
  exact le_of_mul_le_mul_right key (mul_pos hbpos hbpos')

section GaussianMLR

/-- Monotone likelihood ratio of the normal location family, for densities. -/
lemma gaussianPDFReal_mul_le {m m' : ℝ} (hm : m' ≤ m) (v : ℝ≥0) {x y : ℝ} (hxy : y ≤ x) :
    gaussianPDFReal m' v x * gaussianPDFReal m v y ≤
      gaussianPDFReal m v x * gaussianPDFReal m' v y := by
  simp only [gaussianPDFReal]
  have hC : 0 ≤ (√(2 * π * v))⁻¹ := by positivity
  have hv : (0 : ℝ) ≤ 2 * v := by positivity
  have hexp : rexp (-(x - m') ^ 2 / (2 * v)) * rexp (-(y - m) ^ 2 / (2 * v)) ≤
      rexp (-(x - m) ^ 2 / (2 * v)) * rexp (-(y - m') ^ 2 / (2 * v)) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp, ← add_div, ← add_div]
    refine div_le_div_of_nonneg_right ?_ hv
    nlinarith [mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 hxy)]
  calc (√(2 * π * v))⁻¹ * rexp (-(x - m') ^ 2 / (2 * v)) *
        ((√(2 * π * v))⁻¹ * rexp (-(y - m) ^ 2 / (2 * v)))
      = (√(2 * π * v))⁻¹ * (√(2 * π * v))⁻¹ *
        (rexp (-(x - m') ^ 2 / (2 * v)) * rexp (-(y - m) ^ 2 / (2 * v))) := by ring
    _ ≤ (√(2 * π * v))⁻¹ * (√(2 * π * v))⁻¹ *
        (rexp (-(x - m) ^ 2 / (2 * v)) * rexp (-(y - m') ^ 2 / (2 * v))) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hC hC)
    _ = _ := by ring

/-- **Monotone likelihood ratio of the normal location family, set form.** If every point of
`A` is at least every point of `B` and `m' ≤ m`, then
`N(m', v)(A) * N(m, v)(B) ≤ N(m, v)(A) * N(m', v)(B)`: raising the mean moves mass towards the
higher set. The variance must be non-zero. -/
theorem gaussianReal_mul_le_of_le {m m' : ℝ} (hm : m' ≤ m) {v : ℝ≥0} (hv : v ≠ 0)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, y ≤ x) :
    gaussianReal m' v A * gaussianReal m v B ≤ gaussianReal m v A * gaussianReal m' v B := by
  simp only [gaussianReal_of_var_ne_zero _ hv, withDensity_apply _ hA, withDensity_apply _ hB]
  have e : ∀ m₁ m₂ : ℝ, (∫⁻ x in A, gaussianPDF m₁ v x) * (∫⁻ y in B, gaussianPDF m₂ v y) =
      ∫⁻ x in A, ∫⁻ y in B, gaussianPDF m₁ v x * gaussianPDF m₂ v y := by
    intro m₁ m₂
    rw [← lintegral_mul_const _ (measurable_gaussianPDF m₁ v)]
    refine lintegral_congr fun x => ?_
    rw [lintegral_const_mul _ (measurable_gaussianPDF m₂ v)]
  rw [e m' m, e m m']
  refine setLIntegral_mono' hA fun x hx => setLIntegral_mono' hB fun y hy => ?_
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_mul_le hm v (hAB x hx y hy))

end GaussianMLR

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]

/-- **Positive regression dependence in a common-factor model.** Let `W` be a real random
variable independent of the vector `(ε j)`, whose coordinates are mutually independent, and
let `p j = h j W (ε j)` with `h j` jointly measurable and non-increasing in its first argument.
Assume that for every true null `i` the conditional law of `p i` given `W = w` decreases with
`w` in the likelihood ratio order, in set form: for `v ≤ w` and measurable sets `L`, `R` of
reals with every point of `L` strictly below every point of `R`,
`P (h i v (ε i) ∈ L) * P (h i w (ε i) ∈ R) ≤ P (h i w (ε i) ∈ L) * P (h i v (ε i) ∈ R)`.
Then the p-values are positively regression dependent on the true nulls. -/
theorem isPRDSOn_of_commonFactor (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (h : ι → ℝ → ℝ → ℝ) (hh : ∀ j, Measurable (Function.uncurry (h j)))
    (hanti : ∀ j e, Antitone fun w => h j w e) (H₀ : Finset ι)
    (hMLR : ∀ i ∈ H₀, ∀ v w : ℝ, v ≤ w → ∀ L R : Set ℝ, MeasurableSet L → MeasurableSet R →
      (∀ x ∈ L, ∀ y ∈ R, x < y) →
      P {ω | h i v (ε i ω) ∈ L} * P {ω | h i w (ε i ω) ∈ R} ≤
        P {ω | h i w (ε i ω) ∈ L} * P {ω | h i v (ε i ω) ∈ R}) :
    IsPRDSOn P (fun j ω => h j (W ω) (ε j ω)) H₀ := by
  intro i hi D hD hup s t hst
  have hhw : ∀ j w, Measurable (h j w) := fun j w => (hh j).comp measurable_prodMk_left
  -- the probabilities with the common factor frozen at `w`
  set A : ℝ → ℝ → ℝ≥0∞ := fun u w =>
    P ((fun ω j => h j w (ε j ω)) ⁻¹' D ∩ (fun ω => h i w (ε i ω)) ⁻¹' Set.Iic u) with hAdef
  set q : ℝ → ℝ → ℝ≥0∞ := fun u w => P ((fun ω => h i w (ε i ω)) ⁻¹' Set.Iic u) with hqdef
  have hAfin : ∀ u w, A u w ≠ ∞ := fun u w => measure_ne_top _ _
  have hqfin : ∀ u w, q u w ≠ ∞ := fun u w => measure_ne_top _ _
  -- (i) for a frozen factor the p-values are independent, hence PRDS
  have hI : ∀ w, A s w * q t w ≤ A t w * q s w := by
    intro w
    have hprds := isPRDSOn_of_iIndepFun P (fun j ω => h j w (ε j ω))
      (fun j => (hhw j w).comp (hε j)) (hindep.comp (fun j => h j w) (fun j => hhw j w)) {i}
    exact hprds i (mem_singleton_self i) D hD hup s t hst
  -- the likelihood-ratio hypothesis, in terms of `lam w S = P (p i ∈ S | W = w)`
  set lam : ℝ → Set ℝ → ℝ≥0∞ := fun w S => P {ω | h i w (ε i ω) ∈ S} with hlam
  have hlamIic : ∀ u w, lam w (Set.Iic u) = q u w := fun u w => rfl
  have hmlr : ∀ v w : ℝ, v ≤ w → ∀ L R : Set ℝ, MeasurableSet L → MeasurableSet R →
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
  have hIII : ∀ v w, v ≤ w → q s v * q t w ≤ q s w * q t v := by
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
  -- (ii) given `p i ≤ t`, the chance of the increasing event decreases with the factor
  have hC : ∀ v w, v ≤ w → ∀ U : Set ℝ, MeasurableSet U → IsUpperSet U →
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
  -- fibre decomposition of `A t w` along the `i`-th noise variable
  set E : Ω → ι → ℝ := fun ω j => ε j ω with hE
  have hEm : Measurable E := measurable_pi_iff.mpr hε
  set Y : Ω → ι → ℝ := fun ω => Function.update (E ω) i 0 with hY
  have hYm : Measurable Y := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hj : j = i
    · have : (fun ω => Y ω j) = fun _ => 0 := by funext ω; simp [hY, hj]
      rw [this]; exact measurable_const
    · have : (fun ω => Y ω j) = ε j := by funext ω; simp [hY, hE, hj]
      rw [this]; exact hε j
  set μi : Measure ℝ := P.map (ε i) with hμi
  set ν' : Measure (ι → ℝ) := P.map Y with hν'
  have hjointY : P.map (fun ω => (Y ω, ε i ω)) = ν'.prod μi :=
    (indepFun_update_of_iIndepFun P ε hε hindep i).symm.map_prod_eq_prod_map_map
      hYm.aemeasurable (hε i).aemeasurable
  set U : ℝ → (ι → ℝ) → Set ℝ := fun w y =>
    {r | Function.update (fun j => h j w (y j)) i r ∈ D} with hUdef
  have hUm : ∀ w y, MeasurableSet (U w y) := fun w y => (measurable_update _) hD
  have hUup : ∀ w y, IsUpperSet (U w y) := by
    intro w y a b hab ha
    refine hup (fun j => ?_) ha
    by_cases hj : j = i
    · subst hj; simpa using hab
    · simp [hj]
  have hUanti : ∀ v w, v ≤ w → ∀ y, U w y ⊆ U v y := by
    intro v w hvw y r hr
    refine hup (fun j => ?_) hr
    by_cases hj : j = i
    · subst hj; simp
    · simpa [hj] using hanti j (y j) hvw
  have hfib : ∀ w, A t w = ∫⁻ y, lam w (U w y ∩ Set.Iic t) ∂ν' := by
    intro w
    set g : (ι → ℝ) × ℝ → ι → ℝ := fun z j => h j w (Function.update z.1 i z.2 j) with hg
    have hgm : Measurable g := measurable_pi_iff.mpr fun j =>
      (hhw j w).comp ((measurable_pi_apply j).comp measurable_update')
    have hS : MeasurableSet (g ⁻¹' D ∩ {z : (ι → ℝ) × ℝ | h i w z.2 ≤ t}) :=
      (hgm hD).inter (measurableSet_le ((hhw i w).comp measurable_snd) measurable_const)
    have hgY : ∀ ω, g (Y ω, ε i ω) = fun j => h j w (ε j ω) := by
      intro ω
      funext j
      by_cases hj : j = i
      · subst hj; simp [hg]
      · simp [hg, hY, hE, hj]
    have hpre : (fun ω j => h j w (ε j ω)) ⁻¹' D ∩ (fun ω => h i w (ε i ω)) ⁻¹' Set.Iic t
        = (fun ω => (Y ω, ε i ω)) ⁻¹' (g ⁻¹' D ∩ {z : (ι → ℝ) × ℝ | h i w z.2 ≤ t}) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, hgY, Set.mem_Iic, Set.mem_ofPred_eq]
    simp only [hAdef]
    rw [hpre, ← Measure.map_apply (hYm.prodMk (hε i)) hS, hjointY, Measure.prod_apply hS]
    refine lintegral_congr fun y => ?_
    have hsec : Prod.mk y ⁻¹' (g ⁻¹' D ∩ {z : (ι → ℝ) × ℝ | h i w z.2 ≤ t})
        = (h i w) ⁻¹' (U w y ∩ Set.Iic t) := by
      ext x
      have hgx : g (y, x) = Function.update (fun j => h j w (y j)) i (h i w x) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [hg]
        · simp [hg, hj]
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iic, hgx,
        hUdef]
    rw [hsec, hμi, Measure.map_apply (hε i) ((hhw i w) ((hUm w y).inter measurableSet_Iic))]
    rfl
  have hII : ∀ v w, v ≤ w → A t w * q t v ≤ A t v * q t w := by
    intro v w hvw
    rw [hfib w, hfib v, ← lintegral_mul_const' _ _ (hqfin t v),
      ← lintegral_mul_const' _ _ (hqfin t w)]
    refine lintegral_mono fun y => ?_
    refine (hC v w hvw (U w y) (hUm w y) (hUup w y)).trans ?_
    refine mul_le_mul' (measure_mono fun ω hω => ?_) le_rfl
    exact ⟨hUanti v w hvw y hω.1, hω.2⟩
  -- the symmetrised pointwise inequality
  have hpt : ∀ v w, v ≤ w →
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
  -- disintegration along the common factor
  set μ : Measure ℝ := P.map W with hμ
  set ν : Measure (ι → ℝ) := P.map E with hν
  have hjoint : P.map (fun ω => (W ω, E ω)) = μ.prod ν :=
    hWε.map_prod_eq_prod_map_map hW.aemeasurable hEm.aemeasurable
  set G : ℝ × (ι → ℝ) → ι → ℝ := fun z j => h j z.1 (z.2 j) with hG
  have hGm : Measurable G := measurable_pi_iff.mpr fun j =>
    (hh j).comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hTm : ∀ u, MeasurableSet {z : ℝ × (ι → ℝ) | h i z.1 (z.2 i) ≤ u} := fun u =>
    measurableSet_le
      ((hh i).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
      measurable_const
  have hSm : ∀ u, MeasurableSet (G ⁻¹' D ∩ {z : ℝ × (ι → ℝ) | h i z.1 (z.2 i) ≤ u}) :=
    fun u => (hGm hD).inter (hTm u)
  have hAsec : ∀ u w, ν (Prod.mk w ⁻¹' (G ⁻¹' D ∩ {z : ℝ × (ι → ℝ) | h i z.1 (z.2 i) ≤ u}))
      = A u w := by
    intro u w
    rw [hν, Measure.map_apply hEm (measurable_prodMk_left (hSm u))]
    rfl
  have hqsec : ∀ u w, ν (Prod.mk w ⁻¹' {z : ℝ × (ι → ℝ) | h i z.1 (z.2 i) ≤ u}) = q u w := by
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
        = (fun ω => (W ω, E ω)) ⁻¹' (G ⁻¹' D ∩ {z : ℝ × (ι → ℝ) | h i z.1 (z.2 i) ≤ u}) := rfl
    rw [hpre, ← Measure.map_apply (hW.prodMk hEm) (hSm u), hjoint, Measure.prod_apply (hSm u)]
    exact lintegral_congr fun w => hAsec u w
  have hqint : ∀ u, P ((fun ω => h i (W ω) (ε i ω)) ⁻¹' Set.Iic u) = ∫⁻ w, q u w ∂μ := by
    intro u
    have hpre : (fun ω => h i (W ω) (ε i ω)) ⁻¹' Set.Iic u
        = (fun ω => (W ω, E ω)) ⁻¹' {z : ℝ × (ι → ℝ) | h i z.1 (z.2 i) ≤ u} := rfl
    rw [hpre, ← Measure.map_apply (hW.prodMk hEm) (hTm u), hjoint, Measure.prod_apply (hTm u)]
    exact lintegral_congr fun w => hqsec u w
  -- symmetrisation over two independent copies of the factor
  have hsym : ∀ u u' : ℝ, 2 * ((∫⁻ w, A u w ∂μ) * ∫⁻ w, q u' w ∂μ) =
      ∫⁻ z, (A u z.1 * q u' z.2 + A u z.2 * q u' z.1) ∂(μ.prod μ) := by
    intro u u'
    rw [lintegral_add_left (show Measurable (fun z : ℝ × ℝ => A u z.1 * q u' z.2) from
        ((hAm u).comp measurable_fst).mul ((hqm u').comp measurable_snd)),
      lintegral_prod_mul (hAm u).aemeasurable (hqm u').aemeasurable]
    have hswap : ∫⁻ z, A u z.2 * q u' z.1 ∂(μ.prod μ) =
        (∫⁻ w, A u w ∂μ) * ∫⁻ w, q u' w ∂μ := by
      have : (fun z : ℝ × ℝ => A u z.2 * q u' z.1) = fun z => q u' z.1 * A u z.2 := by
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
    rcases le_total z.2 z.1 with hle | hle
    · exact hpt z.2 z.1 hle
    · have := hpt z.1 z.2 hle
      rw [add_comm (A s z.1 * q t z.2), add_comm (A t z.1 * q s z.2)]
      exact this
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2

/-- **Positive regression dependence for one-sided tests in a normal common-factor model.**
Let `Z j = c j * W + d j * ε j`, where `W` is a real random variable (of any law) independent of
the vector `(ε j)`, the `ε j` are mutually independent, and the loadings `c j` are non-negative.
Let `p j = ψ j (Z j)` with `ψ j` non-increasing. If for every true null `i` the noise `ε i` is
standard normal and `d i ≠ 0`, then the p-values are positively regression dependent on the
true nulls. Nothing is assumed on the law of the noise of the other hypotheses. -/
theorem isPRDSOn_gaussian_commonFactor (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (c d : ι → ℝ) (hc : ∀ j, 0 ≤ c j) (ψ : ι → ℝ → ℝ) (hψ : ∀ j, Antitone (ψ j))
    (H₀ : Finset ι) (hd : ∀ i ∈ H₀, d i ≠ 0)
    (hlaw : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1) :
    IsPRDSOn P (fun j ω => ψ j (c j * W ω + d j * ε j ω)) H₀ := by
  have hψm : ∀ j, Measurable (ψ j) := fun j => (hψ j).measurable
  refine isPRDSOn_of_commonFactor P W ε hW hε hWε hindep (fun j w e => ψ j (c j * w + d j * e))
    (fun j => (hψm j).comp ((measurable_fst.const_mul (c j)).add (measurable_snd.const_mul (d j))))
    (fun j e v w hvw => hψ j (by
      have := mul_le_mul_of_nonneg_left hvw (hc j)
      simpa using add_le_add_right this (d j * e)))
    H₀ ?_
  intro i hi v w hvw L R hL hR hLR
  set V : ℝ≥0 := .mk (d i ^ 2) (sq_nonneg _) with hV
  have hV0 : V ≠ 0 := by
    intro h0
    have : d i ^ 2 = 0 := by simpa [hV] using congrArg NNReal.toReal h0
    exact hd i hi (pow_eq_zero_iff (two_ne_zero) |>.mp this)
  have hmap : ∀ x : ℝ, (gaussianReal 0 1).map (fun e => c i * x + d i * e)
      = gaussianReal (c i * x) V := by
    intro x
    have h1 : (fun e : ℝ => c i * x + d i * e) = (fun y => c i * x + y) ∘ (fun e => d i * e) :=
      rfl
    rw [h1, ← Measure.map_map (measurable_const_add _) (measurable_const_mul _),
      gaussianReal_map_const_mul, gaussianReal_map_const_add]
    simp [hV]
  have hlam : ∀ (x : ℝ) (S : Set ℝ), MeasurableSet S →
      P {ω | ψ i (c i * x + d i * ε i ω) ∈ S} = gaussianReal (c i * x) V (ψ i ⁻¹' S) := by
    intro x S hS
    have hpre : {ω | ψ i (c i * x + d i * ε i ω) ∈ S}
        = ε i ⁻¹' ((fun e => c i * x + d i * e) ⁻¹' (ψ i ⁻¹' S)) := rfl
    have hm : Measurable fun e : ℝ => c i * x + d i * e :=
      (measurable_const_mul _).const_add _
    rw [hpre, ← Measure.map_apply (hε i) (hm (hψm i hS)), hlaw i hi,
      ← Measure.map_apply hm (hψm i hS), hmap x]
  rw [hlam v L hL, hlam w R hR, hlam w L hL, hlam v R hR]
  refine gaussianReal_mul_le_of_le (mul_le_mul_of_nonneg_left hvw (hc i)) hV0 (hψm i hL)
    (hψm i hR) fun x hx y hy => ?_
  by_contra hcon
  exact absurd (hLR _ hx _ hy) (not_lt.mpr (hψ i (not_le.mp hcon).le))

/-- In the equicorrelated model with standard normal factor and noise, each statistic
`Z j = √ρ W + √(1 - ρ) ε j` is standard normal, for `0 ≤ ρ ≤ 1`. Only the independence of `W`
and `ε j` is used. -/
theorem map_equicorrelated_gaussian (P : Measure Ω) (W : Ω → ℝ) (e : Ω → ℝ)
    (hW : Measurable W) (he : Measurable e) (hWe : IndepFun W e P)
    (hlawW : P.map W = gaussianReal 0 1) (hlawe : P.map e = gaussianReal 0 1)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    P.map (fun ω => √ρ * W ω + √(1 - ρ) * e ω) = gaussianReal 0 1 := by
  have h1 := gaussianReal_const_mul (⟨hW.aemeasurable, hlawW⟩ : HasLaw W (gaussianReal 0 1) P)
    (√ρ)
  have h2 := gaussianReal_const_mul (⟨he.aemeasurable, hlawe⟩ : HasLaw e (gaussianReal 0 1) P)
    (√(1 - ρ))
  have hind : (fun ω => √ρ * W ω) ⟂ᵢ[P] (fun ω => √(1 - ρ) * e ω) :=
    hWe.comp (measurable_const_mul _) (measurable_const_mul _)
  have h := gaussianReal_add_gaussianReal_of_indepFun hind h1 h2
  have hfun : (fun ω => √ρ * W ω + √(1 - ρ) * e ω)
      = (fun ω => √ρ * W ω) + fun ω => √(1 - ρ) * e ω := rfl
  rw [hfun, h]
  have hv : (NNReal.mk (√ρ ^ 2) (sq_nonneg _)) * 1 + (NNReal.mk (√(1 - ρ) ^ 2) (sq_nonneg _)) * 1
      = 1 := by
    apply NNReal.eq
    simp only [mul_one, NNReal.coe_add, NNReal.coe_mk, NNReal.coe_one,
      Real.sq_sqrt hρ0, Real.sq_sqrt (sub_nonneg.mpr hρ1)]
    ring
  rw [hv]
  simp

/-- In the equicorrelated model two statistics `√ρ W + √(1 - ρ) e₁` and `√ρ W + √(1 - ρ) e₂`
have covariance `ρ`, when `W`, `e₁`, `e₂` are pairwise independent, square-integrable and `W`
has variance one (`0 ≤ ρ`). -/
theorem covariance_equicorrelated (P : Measure Ω) [IsProbabilityMeasure P] (W e₁ e₂ : Ω → ℝ)
    (hW : MemLp W 2 P) (he₁ : MemLp e₁ 2 P) (he₂ : MemLp e₂ 2 P)
    (hWe₁ : IndepFun W e₁ P) (hWe₂ : IndepFun W e₂ P) (he : IndepFun e₁ e₂ P)
    (hvar : Var[W; P] = 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) :
    cov[fun ω => √ρ * W ω + √(1 - ρ) * e₁ ω, fun ω => √ρ * W ω + √(1 - ρ) * e₂ ω; P] = ρ := by
  have hA : MemLp (fun ω => √ρ * W ω) 2 P := hW.const_mul _
  have hB₁ : MemLp (fun ω => √(1 - ρ) * e₁ ω) 2 P := he₁.const_mul _
  have hB₂ : MemLp (fun ω => √(1 - ρ) * e₂ ω) 2 P := he₂.const_mul _
  change cov[(fun ω => √ρ * W ω) + (fun ω => √(1 - ρ) * e₁ ω),
    (fun ω => √ρ * W ω) + (fun ω => √(1 - ρ) * e₂ ω); P] = ρ
  rw [covariance_add_left hA hB₁ (hA.add hB₂), covariance_add_right hA hA hB₂,
    covariance_add_right hB₁ hA hB₂]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  rw [covariance_self hW.aestronglyMeasurable.aemeasurable, hvar,
    hWe₂.covariance_eq_zero hW he₂, hWe₁.symm.covariance_eq_zero he₁ hW,
    he.covariance_eq_zero he₁ he₂]
  simp [Real.mul_self_sqrt hρ0]

/-- **Equicorrelated normal statistics, one-sided tests.** Let `W` be a real random variable
independent of the mutually independent standard normal variables `ε j`, let `0 ≤ ρ ≤ 1`,
`Z j = √ρ W + √(1 - ρ) ε j` and `p j = 1 - Φ (Z j)`, where `Φ` is the standard normal
distribution function. Then the p-values are positively regression dependent on every set of
hypotheses. The law of `W` is not used; when `W` is standard normal the `Z j` are standard
normal (`map_equicorrelated_gaussian`) with pairwise covariance `ρ`
(`covariance_equicorrelated`). -/
theorem isPRDSOn_equicorrelated_gaussian (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (hlaw : ∀ j, P.map (ε j) = gaussianReal 0 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (H₀ : Finset ι) :
    IsPRDSOn P (fun j ω => 1 - cdf (gaussianReal 0 1) (√ρ * W ω + √(1 - ρ) * ε j ω)) H₀ := by
  have hψ : Antitone fun z : ℝ => 1 - cdf (gaussianReal 0 1) z :=
    fun a b hab => sub_le_sub_left (monotone_cdf _ hab) 1
  rcases hρ1.eq_or_lt with h1 | hlt
  · -- perfectly correlated statistics: comonotone p-values
    subst h1
    have hfun : (fun (j : ι) ω => 1 - cdf (gaussianReal 0 1) (√(1 : ℝ) * W ω + √(1 - 1) * ε j ω))
        = fun (_ : ι) ω => (fun u : ℝ => 1 - cdf (gaussianReal 0 1) (-u)) (-W ω) := by
      funext j ω
      simp
    rw [hfun]
    exact isPRDSOn_of_comonotone P (fun ω => -W ω) hW.neg
      (fun _ u => 1 - cdf (gaussianReal 0 1) (-u))
      (fun _ a b hab => hψ (neg_le_neg hab)) H₀
  · exact isPRDSOn_gaussian_commonFactor P W ε hW hε hWε hindep (fun _ => √ρ)
      (fun _ => √(1 - ρ)) (fun _ => Real.sqrt_nonneg _)
      (fun _ z => 1 - cdf (gaussianReal 0 1) z) (fun _ => hψ) H₀
      (fun _ _ => (Real.sqrt_pos.mpr (sub_pos.mpr hlt)).ne') (fun j _ => hlaw j)

end Applied.MultipleTesting
