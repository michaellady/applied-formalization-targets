import Applied.Statistics.PRDSRankedFactor
import Applied.Statistics.TwoSidedSimes

/-!
# Two-sided z-tests in a one-factor model: Simes, Hochberg, Hommel and Benjamini–Hochberg for
any number of hypotheses

Statistics `Z j = a j * W + b j * ε j` share one factor `W`, independent of the mutually
independent noises `ε j`. The loadings `a j` may have either sign. With `W`, `ε j` standard
normal and `a j ^ 2 + b j ^ 2 = 1` the vector `Z` is normal with standard normal coordinates and
correlations `a i * a j`; the equicorrelated case `a j = √ρ` is included, and so is perfect
correlation (`a j = ± 1`, `b j = 0`).

The two-sided p-values `p j = 2 (1 - Φ(|Z j|))` are *not* monotone functions of the factor, so
`Applied/Statistics/PRDSCommonFactor.lean` does not apply. But given `W = w` they are
independent, and the law of `|Z j|` is a folded normal law with location `|a j w|`, which
increases with `|w|` both stochastically and in the likelihood ratio order
(`foldedMeasure_mul_le`). `isPRDSOn_of_rankedFactor` with the rank `|w|` therefore gives positive
regression dependence, in the conditioning-on-`p i ≤ t` form `IsPRDSOn` of
`Applied/Statistics/PRDS.lean` (not the definition of Benjamini and Yekutieli).

## Main results

* `isPRDSOn_abs_gaussian_oneFactor`: `p j = ψ j |c j * W + d j * ε j + m j|` is `IsPRDSOn` on
  the true nulls, when every hypothesis either does not load on the factor (`c j = 0`; then
  `ψ j` and the law of `ε j` are arbitrary) or has `m j = 0`, `ψ j` non-increasing on `[0, ∞)`
  and standard normal noise, and the true nulls are of the second kind. The law of `W` is
  arbitrary.
* `isPRDSOn_twoSided_oneFactor`: the case `ψ j x = 2 (1 - Φ x)`.
* `measure_simes_le_twoSided_oneFactor`: the Simes inequality, all hypotheses null.
* `fdr_bhReject_le_twoSided_oneFactor`: Benjamini–Hochberg has false discovery rate at most
  `α m₀ / m`, when every false null either does not load on the factor or is centred.
* `fwer_hochberg_le_twoSided_oneFactor`, `fwer_hommel_le_twoSided_oneFactor`: family-wise error
  rate at most `α`; nothing is assumed about the false nulls.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace Applied.MultipleTesting

variable {Ω : Type*} [MeasurableSpace Ω]

section FoldedFamily

variable {ψ : ℝ → ℝ}

/-- For `ψ` non-increasing on `[0, ∞)`, the law of `ψ |c w + d X|`, `X` standard normal,
decreases stochastically as `|w|` grows. The case `d = 0` (a point mass) is included. -/
lemma gaussianReal_absAffine_stoch (hψm : Measurable ψ) (hψ : AntitoneOn ψ (Set.Ici 0))
    (c d : ℝ) {v w : ℝ} (hvw : |v| ≤ |w|) {U : Set ℝ} (hU : MeasurableSet U)
    (hUup : IsUpperSet U) :
    gaussianReal 0 1 {x | ψ |c * w + d * x| ∈ U} ≤ gaussianReal 0 1 {x | ψ |c * v + d * x| ∈ U} := by
  have hcvw : |c * v| ≤ |c * w| := by
    rw [abs_mul, abs_mul]; exact mul_le_mul_of_nonneg_left hvw (abs_nonneg c)
  by_cases hd : d = 0
  · subst hd
    by_cases hw : ψ |c * w| ∈ U
    · have hv : ψ |c * v| ∈ U :=
        hUup (hψ (Set.mem_Ici.mpr (abs_nonneg _)) (Set.mem_Ici.mpr (abs_nonneg _)) hcvw) hw
      simp only [zero_mul, add_zero, hw, hv, Set.ofPred_true]
      exact le_rfl
    · simp only [zero_mul, add_zero, hw, Set.ofPred_false, measure_empty]
      exact bot_le
  · set D' : Set ℝ := (ψ ⁻¹' U)ᶜ with hD'
    have hD'm : MeasurableSet D' := (hψm hU).compl
    have hDup : ∀ x y, 0 ≤ x → x ≤ y → x ∈ D' → y ∈ D' := by
      intro x y hx hxy hxD hyU
      exact hxD (hUup (hψ hx (hx.trans hxy) hxy) hyU)
    have hmono := gaussianReal_abs_affine_mono c hd hD'm hDup hvw
    have hcompl : ∀ t : ℝ, {x : ℝ | ψ |c * t + d * x| ∈ U} = {y | |c * t + d * y| ∈ D'}ᶜ := by
      intro t; ext x; simp [hD']
    have hmeas : ∀ t : ℝ, MeasurableSet {y : ℝ | |c * t + d * y| ∈ D'} := fun t =>
      (measurable_norm.comp ((measurable_const_mul d).const_add (c * t))) hD'm
    rw [hcompl w, hcompl v, prob_compl_eq_one_sub (hmeas w), prob_compl_eq_one_sub (hmeas v)]
    exact tsub_le_tsub_left hmono 1

/-- For `ψ` non-increasing on `[0, ∞)`, the law of `ψ |c w + d X|`, `X` standard normal,
decreases in the likelihood ratio order (set form) as `|w|` grows. The case `d = 0` is
included. -/
lemma gaussianReal_absAffine_mlr (hψm : Measurable ψ) (hψ : AntitoneOn ψ (Set.Ici 0))
    (c d : ℝ) {v w : ℝ} (hvw : |v| ≤ |w|) {L R : Set ℝ} (hL : MeasurableSet L)
    (hR : MeasurableSet R) (hLR : ∀ x ∈ L, ∀ y ∈ R, x < y) :
    gaussianReal 0 1 {x | ψ |c * v + d * x| ∈ L} * gaussianReal 0 1 {x | ψ |c * w + d * x| ∈ R} ≤
      gaussianReal 0 1 {x | ψ |c * w + d * x| ∈ L} *
        gaussianReal 0 1 {x | ψ |c * v + d * x| ∈ R} := by
  have hcvw : |c * v| ≤ |c * w| := by
    rw [abs_mul, abs_mul]; exact mul_le_mul_of_nonneg_left hvw (abs_nonneg c)
  by_cases hd : d = 0
  · subst hd
    by_cases hv : ψ |c * v| ∈ L
    · by_cases hw : ψ |c * w| ∈ R
      · exact absurd (hLR _ hv _ hw) (not_lt.mpr
          (hψ (Set.mem_Ici.mpr (abs_nonneg _)) (Set.mem_Ici.mpr (abs_nonneg _)) hcvw))
      · simp only [zero_mul, add_zero, hw, Set.ofPred_false, measure_empty, mul_zero]
        exact bot_le
    · simp only [zero_mul, add_zero, hv, Set.ofPred_false, measure_empty]
      exact bot_le
  · have e : ∀ (t : ℝ) (S : Set ℝ), MeasurableSet S →
        gaussianReal 0 1 {x | ψ |c * t + d * x| ∈ S}
          = foldedMeasure (c * t) (sqNN d) (ψ ⁻¹' S ∩ Set.Ioi 0) :=
      fun t S hS => gaussianReal_abs_affine_mem (c * t) hd (hψm hS)
    rw [e v L hL, e w R hR, e w L hL, e v R hR, mul_comm]
    refine foldedMeasure_mul_le hcvw (sqNN_ne_zero hd) ((hψm hL).inter measurableSet_Ioi)
      ((hψm hR).inter measurableSet_Ioi) fun x hx y hy => ⟨le_of_lt hy.2, ?_⟩
    by_contra hcon
    exact absurd (hLR _ hx.1 _ hy.1)
      (not_lt.mpr (hψ (Set.mem_Ici.mpr (le_of_lt hx.2)) (Set.mem_Ici.mpr (le_of_lt hy.2))
        (not_le.mp hcon).le))

end FoldedFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Positive regression dependence of absolute values in a normal one-factor model.** Let `W`
be a real random variable (of any law) independent of the vector `(ε j)` of mutually independent
real random variables, and `p j = ψ j |c j * W + d j * ε j + m j|` with `ψ j` measurable. Assume
that every hypothesis `j` either does not load on the factor (`c j = 0`), or has `m j = 0`, `ψ j`
non-increasing on `[0, ∞)` and `ε j` standard normal; and that every true null is of the second
kind. Then the `p j` are positively regression dependent on the true nulls (`IsPRDSOn`). The
loadings `c j` may have any signs and `d j` may vanish. -/
theorem isPRDSOn_abs_gaussian_oneFactor (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (c d m : ι → ℝ) (ψ : ι → ℝ → ℝ) (hψm : ∀ j, Measurable (ψ j)) (H₀ : Finset ι)
    (hfac : ∀ j, c j = 0 ∨
      (m j = 0 ∧ AntitoneOn (ψ j) (Set.Ici 0) ∧ P.map (ε j) = gaussianReal 0 1))
    (hnull : ∀ i ∈ H₀, m i = 0 ∧ AntitoneOn (ψ i) (Set.Ici 0) ∧ P.map (ε i) = gaussianReal 0 1) :
    IsPRDSOn P (fun j ω => ψ j |c j * W ω + d j * ε j ω + m j|) H₀ := by
  have hlaw : ∀ j, P.map (ε j) = gaussianReal 0 1 → ∀ (t : ℝ) (S : Set ℝ), MeasurableSet S →
      P {ω | ψ j |c j * t + d j * ε j ω + 0| ∈ S}
        = gaussianReal 0 1 {x | ψ j |c j * t + d j * x| ∈ S} := by
    intro j hj t S hS
    have hm : Measurable fun x : ℝ => ψ j |c j * t + d j * x| :=
      (hψm j).comp (measurable_norm.comp ((measurable_const_mul _).const_add _))
    have hset : {ω | ψ j |c j * t + d j * ε j ω + 0| ∈ S}
        = ε j ⁻¹' ((fun x : ℝ => ψ j |c j * t + d j * x|) ⁻¹' S) := by
      ext ω; simp
    rw [hset, ← Measure.map_apply (hε j) (hm hS), hj]
    rfl
  refine isPRDSOn_of_rankedFactor P W ε hW hε hWε hindep
    (fun j w e => ψ j |c j * w + d j * e + m j|)
    (fun j => (hψm j).comp (measurable_norm.comp
      (((measurable_fst.const_mul (c j)).add (measurable_snd.const_mul (d j))).add
        measurable_const)))
    (fun w => |w|) H₀ ?_ ?_
  · intro j v w hvw U hU hUup
    rcases hfac j with hc | ⟨hm, hanti, hl⟩
    · simp [hc]
    · simp only [hm]
      rw [hlaw j hl w U hU, hlaw j hl v U hU]
      exact gaussianReal_absAffine_stoch (hψm j) hanti (c j) (d j) hvw hU hUup
  · intro i hi v w hvw L R hL hR hLR
    obtain ⟨hm, hanti, hl⟩ := hnull i hi
    simp only [hm]
    rw [hlaw i hl v L hL, hlaw i hl w R hR, hlaw i hl w L hL, hlaw i hl v R hR]
    exact gaussianReal_absAffine_mlr (hψm i) hanti (c i) (d i) hvw hL hR hLR

section TwoSided

/-- **Two-sided p-values in a one-factor model are positively regression dependent.** Let
`Z j = a j * W + b j * ε j + μ j`, with `W` (of any law) independent of the mutually independent
`ε j`, and `p j = 2 (1 - Φ(|Z j|))`. If every hypothesis either does not load on the factor
(`a j = 0`) or is centred with standard normal noise (`μ j = 0`, `ε j ∼ N(0, 1)`), and the true
nulls are of the second kind, then the `p j` are `IsPRDSOn` on the true nulls. Loadings of any
sign; `b j` arbitrary. -/
theorem isPRDSOn_twoSided_oneFactor (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (a b μ : ι → ℝ) (H₀ : Finset ι)
    (hfac : ∀ j, a j = 0 ∨ (μ j = 0 ∧ P.map (ε j) = gaussianReal 0 1))
    (hnull : ∀ i ∈ H₀, μ i = 0 ∧ P.map (ε i) = gaussianReal 0 1) :
    IsPRDSOn P
      (fun j ω => 2 * (1 - cdf (gaussianReal 0 1) |a j * W ω + b j * ε j ω + μ j|)) H₀ :=
  isPRDSOn_abs_gaussian_oneFactor P W ε hW hε hWε hindep a b μ
    (fun _ x => 2 * (1 - cdf (gaussianReal 0 1) x)) (fun _ => measurable_twoSided) H₀
    (fun j => (hfac j).imp id fun h => ⟨h.1, antitone_twoSided.antitoneOn _, h.2⟩)
    (fun i hi => ⟨(hnull i hi).1, antitone_twoSided.antitoneOn _, (hnull i hi).2⟩)

/-- Validity of the two-sided p-value of a true null in the one-factor model. -/
lemma isValidPValue_twoSided_oneFactor (P : Measure Ω) {W e : Ω → ℝ} (hW : Measurable W)
    (he : Measurable e) (hWe : IndepFun W e P) (hlawW : P.map W = gaussianReal 0 1)
    (hlawe : P.map e = gaussianReal 0 1) {a b m : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (hm : m = 0) :
    IsValidPValue P fun ω => 2 * (1 - cdf (gaussianReal 0 1) |a * W ω + b * e ω + m|) := by
  subst hm
  simpa using isValidPValue_zTest_twoSided P _ ((hW.const_mul a).add (he.const_mul b))
    (map_oneFactor_gaussian P W e hW he hWe hlawW hlawe hab)

/-- **Benjamini–Hochberg for two-sided z-tests in a one-factor model.** Let
`Z j = a j * W + b j * ε j + μ j`, with `W` standard normal and independent of the mutually
independent `ε j`. For the true nulls: `a i ^ 2 + b i ^ 2 = 1` (loadings of either sign,
`|a i| = 1` allowed), `ε i` standard normal, `μ i = 0`, so `Z i` is standard normal. Each false
null either does not load on the factor (`a j = 0`; its noise law, scale and shift are then
arbitrary) or is centred with standard normal noise (`μ j = 0`; arbitrary `a j`, `b j`). Then
the Benjamini–Hochberg procedure applied to `2 (1 - Φ(|Z j|))` at level `α ≥ 0` has false
discovery rate at most `α m₀ / m`. -/
theorem fdr_bhReject_le_twoSided_oneFactor (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (hlawW : P.map W = gaussianReal 0 1) (a b μ : ι → ℝ) (H₀ : Finset ι)
    (hab : ∀ i ∈ H₀, a i ^ 2 + b i ^ 2 = 1) (hlawε : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1)
    (hμ : ∀ i ∈ H₀, μ i = 0)
    (halt : ∀ j ∉ H₀, a j = 0 ∨ (μ j = 0 ∧ P.map (ε j) = gaussianReal 0 1)) {α : ℝ}
    (hα : 0 ≤ α) :
    fdr P H₀ (fun ω => bhReject α fun j =>
        2 * (1 - cdf (gaussianReal 0 1) |a j * W ω + b j * ε j ω + μ j|))
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) :=
  fdr_bhReject_le_of_prds P hα _
    (fun j => measurable_twoSided_abs
      (((hW.const_mul _).add ((hε j).const_mul _)).add measurable_const)) H₀
    (fun i hi => isValidPValue_twoSided_oneFactor P hW (hε i)
      (hWε.comp measurable_id (measurable_pi_apply i)) hlawW (hlawε i hi) (hab i hi) (hμ i hi))
    (isPRDSOn_twoSided_oneFactor P W ε hW hε hWε hindep a b μ H₀
      (fun j => by
        by_cases hj : j ∈ H₀
        · exact Or.inr ⟨hμ j hj, hlawε j hj⟩
        · exact halt j hj)
      (fun i hi => ⟨hμ i hi, hlawε i hi⟩))

/-- **The Simes inequality for two-sided z-tests in a one-factor model, any number of
hypotheses.** Let `Z j = a j * W + b j * ε j` with `W`, `ε j` standard normal, `W` independent of
the mutually independent `ε j`, and `a j ^ 2 + b j ^ 2 = 1` (so `Z` is a normal vector with
standard normal coordinates and correlations `a i * a j`; loadings of either sign). Then the
Simes test applied to `2 (1 - Φ(|Z j|))` at level `α ≥ 0` rejects with probability at most
`α`. -/
theorem measure_simes_le_twoSided_oneFactor (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (hlawW : P.map W = gaussianReal 0 1) (hlawε : ∀ j, P.map (ε j) = gaussianReal 0 1)
    (a b : ι → ℝ) (hab : ∀ j, a j ^ 2 + b j ^ 2 = 1) {α : ℝ} (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun j => 2 * (1 - cdf (gaussianReal 0 1) |a j * W ω + b j * ε j ω|)}
      ≤ ENNReal.ofReal α := by
  have h := measure_one_le_bhK_le_of_prds P hα
    (fun j ω => 2 * (1 - cdf (gaussianReal 0 1) |a j * W ω + b j * ε j ω + (0 : ι → ℝ) j|))
    (fun j => measurable_twoSided_abs
      (((hW.const_mul _).add ((hε j).const_mul _)).add measurable_const))
    (fun i => isValidPValue_twoSided_oneFactor P hW (hε i)
      (hWε.comp measurable_id (measurable_pi_apply i)) hlawW (hlawε i) (hab i) rfl)
    (isPRDSOn_twoSided_oneFactor P W ε hW hε hWε hindep a b 0 univ
      (fun j => Or.inr ⟨rfl, hlawε j⟩) (fun i _ => ⟨rfl, hlawε i⟩))
  simpa using h

omit [Fintype ι] in
/-- The one-factor structure of the two-sided p-values restricts to the subfamily of true nulls:
if `T i = a i * W + b i * ε i` for `i ∈ S` with standard normal noise, the p-values
`2 (1 - Φ(|T i|))`, `i ∈ S`, as a family on their own, are `IsPRDSOn` on all of `S`. -/
theorem isPRDSOn_twoSided_oneFactor_restrict (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P) (a b : ι → ℝ)
    (T : ι → Ω → ℝ) (S : Finset ι) (hT : ∀ i ∈ S, ∀ ω, T i ω = a i * W ω + b i * ε i ω)
    (hlaw : ∀ i ∈ S, P.map (ε i) = gaussianReal 0 1) :
    IsPRDSOn P (fun (j : S) ω => 2 * (1 - cdf (gaussianReal 0 1) |T j ω|)) univ := by
  have hres : Measurable fun (v : ι → ℝ) (j : S) => v j :=
    measurable_pi_iff.mpr fun j => measurable_pi_apply j.1
  have h := isPRDSOn_twoSided_oneFactor (ι := S) P W (fun j => ε j) hW (fun j => hε j)
    (hWε.comp measurable_id hres) (hindep.precomp Subtype.val_injective)
    (fun j => a j) (fun j => b j) 0 univ (fun j => Or.inr ⟨rfl, hlaw j j.2⟩)
    (fun j _ => ⟨rfl, hlaw j j.2⟩)
  have heq : (fun (j : S) ω => 2 * (1 - cdf (gaussianReal 0 1) |T j ω|))
      = fun (j : S) ω => 2 * (1 - cdf (gaussianReal 0 1)
          |a j * W ω + b j * ε j ω + (0 : S → ℝ) j|) := by
    funext j ω
    rw [hT j j.2 ω]
    simp
  rw [heq]
  exact h

/-- **Hommel's procedure for two-sided z-tests whose true nulls follow a one-factor model.**
The statistics `T j` are arbitrary measurable functions; for the true nulls
`T i = a i * W + b i * ε i` with `W`, `ε i` standard normal, `W` independent of the mutually
independent `ε j`, and `a i ^ 2 + b i ^ 2 = 1`. Then Hommel's procedure based on
`2 (1 - Φ(|T j|))` has family-wise error rate at most `α`. -/
theorem fwer_hommel_le_twoSided_oneFactor (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (hlawW : P.map W = gaussianReal 0 1) (a b : ι → ℝ) (T : ι → Ω → ℝ)
    (hTm : ∀ j, Measurable (T j)) (H₀ : Finset ι)
    (hT : ∀ i ∈ H₀, ∀ ω, T i ω = a i * W ω + b i * ε i ω)
    (hab : ∀ i ∈ H₀, a i ^ 2 + b i ^ 2 = 1) (hlawε : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1)
    {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hommel α fun j ω => 2 * (1 - cdf (gaussianReal 0 1) |T j ω|))
      ≤ ENNReal.ofReal α :=
  fwer_hommel_le_of_prds P hα _ (fun j => measurable_twoSided_abs (hTm j)) H₀
    (fun i hi => by
      have hfun : T i = fun ω => a i * W ω + b i * ε i ω := funext (hT i hi)
      rw [hfun]
      exact isValidPValue_zTest_twoSided P _ ((hW.const_mul _).add ((hε i).const_mul _))
        (map_oneFactor_gaussian P W (ε i) hW (hε i)
          (hWε.comp measurable_id (measurable_pi_apply i)) hlawW (hlawε i hi) (hab i hi)))
    (isPRDSOn_twoSided_oneFactor_restrict P W ε hW hε hWε hindep a b T H₀ hT hlawε)

/-- **Hochberg's procedure for two-sided z-tests whose true nulls follow a one-factor model**:
same hypotheses as `fwer_hommel_le_twoSided_oneFactor`. `hochberg` is the textbook step-up rule,
ties included. -/
theorem fwer_hochberg_le_twoSided_oneFactor (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (hlawW : P.map W = gaussianReal 0 1) (a b : ι → ℝ) (T : ι → Ω → ℝ)
    (hTm : ∀ j, Measurable (T j)) (H₀ : Finset ι)
    (hT : ∀ i ∈ H₀, ∀ ω, T i ω = a i * W ω + b i * ε i ω)
    (hab : ∀ i ∈ H₀, a i ^ 2 + b i ^ 2 = 1) (hlawε : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1)
    {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hochberg α fun j ω => 2 * (1 - cdf (gaussianReal 0 1) |T j ω|))
      ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans (fwer_hommel_le_twoSided_oneFactor P W ε hW hε hWε hindep hlawW
    a b T hTm H₀ hT hab hlawε hα)
  rintro ω ⟨i, hi, hrej⟩
  exact ⟨i, hi, hochberg_subset_hommel hα _ ω hrej⟩

end TwoSided

end Applied.MultipleTesting
