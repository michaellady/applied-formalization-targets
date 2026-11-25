import Applied.Statistics.TwoSidedFoldedNormal
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-!
# The key inequality behind the two-sided Simes test for two normal statistics

For two statistics `Z₁ = a W + b X` and `Z₂ = c W + d Y` with `W`, `X`, `Y` independent, `X`, `Y`
standard normal and `b, d ≠ 0`, and for sets `U₁ ⊆ U₂ ⊆ [0, ∞)` with `U₁` "above" the rest of
`U₂` and an upper set `D ⊆ [0, ∞)`:

`P (|Z₁| ∈ U₂, |Z₂| ∈ D) * P (|Z₁| ∈ U₁) ≤ P (|Z₁| ∈ U₁, |Z₂| ∈ D) * P (|Z₁| ∈ U₂)`.

In words: among two nested rejection regions `{|Z₁| ∈ U₁} ⊆ {|Z₁| ∈ U₂}` for the first statistic
(think `p₁ ≤ α / 2` and `p₁ ≤ α`), the smaller one makes a large `|Z₂|` at least as likely. This
is positive regression dependence of the two-sided p-values for two statistics, in the
conditioning-on-`p ≤ t` form.

* `measure_abs_inter_eq_lintegral`, `measure_abs_inter_eq_lintegral_direct`: conditioning on the
  factor `W` (general loading), and on `Z₁` itself (the second statistic is `c Z₁ + d Y`).
* `gaussianReal_abs_affine_mono`: `w ↦ P (|c w + d ε| ∈ D)` is non-decreasing in `|w|` for an
  upper set `D`.
* `twoSided_key_ineq`: the inequality above.
* `twoSided_key_ineq_direct`: the same when the first statistic is the factor itself
  (`Z₁ = X` with an arbitrary law, `Z₂ = c X + d Y`); used for a bivariate normal pair after
  regressing `Z₂` on `Z₁`.

The proofs condition on the factor and apply `foldedMeasure_mul_le` and
`lintegral_mixture_mul_le` of `Applied/Statistics/TwoSidedFoldedNormal.lean`. The Simes
inequality itself is deduced in `Applied/Statistics/TwoSidedSimes.lean`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace Applied.MultipleTesting

section KeyInequality

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Conditioning on the common factor: with `W` independent of `(X, Y)`, `X` independent of `Y`,
both standard normal, the joint probability of `|a W + b X| ∈ U` and `|c W + d Y| ∈ D` is the
mixture over the law of `W` of the product of the two conditional probabilities. -/
lemma measure_abs_inter_eq_lintegral (P : Measure Ω) [IsProbabilityMeasure P] {W X Y : Ω → ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y)
    (hWXY : IndepFun W (fun ω => (X ω, Y ω)) P) (hXY : IndepFun X Y P)
    (hlawX : P.map X = gaussianReal 0 1) (hlawY : P.map Y = gaussianReal 0 1)
    (a b c d : ℝ) {U D : Set ℝ} (hU : MeasurableSet U) (hD : MeasurableSet D) :
    P ({ω | |a * W ω + b * X ω| ∈ U} ∩ {ω | |c * W ω + d * Y ω| ∈ D}) =
      ∫⁻ w, gaussianReal 0 1 {x | |a * w + b * x| ∈ U} *
        gaussianReal 0 1 {y | |c * w + d * y| ∈ D} ∂(P.map W) := by
  have hpair : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hjoint : P.map (fun ω => (W ω, (X ω, Y ω))) =
      (P.map W).prod (P.map (fun ω => (X ω, Y ω))) :=
    hWXY.map_prod_eq_prod_map_map hW.aemeasurable (hX.prodMk hY).aemeasurable
  set S : Set (ℝ × ℝ × ℝ) :=
    {z | |a * z.1 + b * z.2.1| ∈ U} ∩ {z | |c * z.1 + d * z.2.2| ∈ D} with hSdef
  have hS : MeasurableSet S := by
    refine MeasurableSet.inter ?_ ?_
    · exact (measurable_norm.comp ((measurable_fst.const_mul a).add
        ((measurable_fst.comp measurable_snd).const_mul b))) hU
    · exact (measurable_norm.comp ((measurable_fst.const_mul c).add
        ((measurable_snd.comp measurable_snd).const_mul d))) hD
  have hset : {ω | |a * W ω + b * X ω| ∈ U} ∩ {ω | |c * W ω + d * Y ω| ∈ D} =
      (fun ω => (W ω, (X ω, Y ω))) ⁻¹' S := rfl
  rw [hset, ← Measure.map_apply (hW.prodMk (hX.prodMk hY)) hS, hjoint, hpair, hlawX, hlawY,
    Measure.prod_apply hS]
  refine lintegral_congr fun w => ?_
  have hsec : Prod.mk w ⁻¹' S = {x | |a * w + b * x| ∈ U} ×ˢ {y | |c * w + d * y| ∈ D} := rfl
  rw [hsec, Measure.prod_prod]

lemma measurable_gaussianReal_abs_affine (a b : ℝ) {U : Set ℝ} (hU : MeasurableSet U) :
    Measurable fun w => gaussianReal 0 1 {x | |a * w + b * x| ∈ U} := by
  have hT : MeasurableSet {z : ℝ × ℝ | |a * z.1 + b * z.2| ∈ U} :=
    (measurable_norm.comp ((measurable_fst.const_mul a).add (measurable_snd.const_mul b))) hU
  exact measurable_measure_prodMk_left hT

/-- The probability that `|c w + d Y| ∈ D`, `Y` standard normal, `d ≠ 0`, is non-decreasing in
`|w|` when `D` is upward closed on `[0, ∞)` (stochastic monotonicity of the folded normal
family in its location). -/
lemma gaussianReal_abs_affine_mono (c : ℝ) {d : ℝ} (hd : d ≠ 0) {D : Set ℝ}
    (hD : MeasurableSet D) (hDup : ∀ x y, 0 ≤ x → x ≤ y → x ∈ D → y ∈ D) {w v : ℝ}
    (hvw : |v| ≤ |w|) :
    gaussianReal 0 1 {y | |c * v + d * y| ∈ D} ≤ gaussianReal 0 1 {y | |c * w + d * y| ∈ D} := by
  rw [gaussianReal_abs_affine_mem _ hd hD, gaussianReal_abs_affine_mem _ hd hD]
  have htot : ∀ t : ℝ, foldedMeasure t (sqNN d) (D ∩ Set.Ioi 0) +
      foldedMeasure t (sqNN d) (Set.Ioi 0 \ D) = 1 := by
    intro t
    have h1 := gaussianReal_abs_affine_mem t hd MeasurableSet.univ
    simp only [Set.mem_univ, Set.ofPred_true, measure_univ, Set.univ_inter] at h1
    rw [h1, ← foldedMeasure_union _ _ _ (measurableSet_Ioi.diff hD)]
    · congr 1; ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]; tauto
    · rw [Set.disjoint_left]; intro x hx hx'; exact hx'.2 hx.1
  have hm : |c * v| ≤ |c * w| := by
    rw [abs_mul, abs_mul]; exact mul_le_mul_of_nonneg_left hvw (abs_nonneg c)
  have hmlr := foldedMeasure_mul_le hm (sqNN_ne_zero hd) (hD.inter measurableSet_Ioi)
    (measurableSet_Ioi.diff hD) (A := D ∩ Set.Ioi 0) (B := Set.Ioi 0 \ D)
    (fun x hx y hy => ⟨le_of_lt hy.1, le_of_not_gt fun hxy =>
      hy.2 (hDup x y (le_of_lt hx.2) hxy.le hx.1)⟩)
  set A' := foldedMeasure (c * v) (sqNN d) (D ∩ Set.Ioi 0)
  set A := foldedMeasure (c * w) (sqNN d) (D ∩ Set.Ioi 0)
  set B' := foldedMeasure (c * v) (sqNN d) (Set.Ioi 0 \ D)
  set B := foldedMeasure (c * w) (sqNN d) (Set.Ioi 0 \ D)
  have h1 : A + B = 1 := htot (c * w)
  have h2 : A' + B' = 1 := htot (c * v)
  calc A' = A' * (A + B) := by rw [h1, mul_one]
    _ = A' * A + B * A' := by ring
    _ ≤ A' * A + A * B' := by gcongr
    _ = A * (A' + B') := by ring
    _ = A := by rw [h2, mul_one]

/-- **Key inequality for two-sided tests in a one-factor model.** Let `W` be independent of
`(X, Y)`, `X` independent of `Y`, both standard normal, `b, d ≠ 0`, and let `U₁ ⊆ U₀` and `D`
be measurable sets that are upward closed on `[0, ∞)`. With `E U = {|a W + b X| ∈ U}` and
`F = {|c W + d Y| ∈ D}`, `P (E U₀ ∩ F) P (E U₁) ≤ P (E U₁ ∩ F) P (E U₀)`: conditioning on the
smaller event `E U₁` makes `F` more likely. The law of `W` is arbitrary. -/
theorem twoSided_key_ineq (P : Measure Ω) [IsProbabilityMeasure P] {W X Y : Ω → ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y)
    (hWXY : IndepFun W (fun ω => (X ω, Y ω)) P) (hXY : IndepFun X Y P)
    (hlawX : P.map X = gaussianReal 0 1) (hlawY : P.map Y = gaussianReal 0 1)
    (a c : ℝ) {b d : ℝ} (hb : b ≠ 0) (hd : d ≠ 0) {U₀ U₁ D : Set ℝ}
    (hU₀ : MeasurableSet U₀) (hU₁ : MeasurableSet U₁) (hD : MeasurableSet D) (hsub : U₁ ⊆ U₀)
    (hU₁up : ∀ x y, 0 ≤ x → x ≤ y → x ∈ U₁ → y ∈ U₁)
    (hDup : ∀ x y, 0 ≤ x → x ≤ y → x ∈ D → y ∈ D) :
    P ({ω | |a * W ω + b * X ω| ∈ U₀} ∩ {ω | |c * W ω + d * Y ω| ∈ D}) *
        P {ω | |a * W ω + b * X ω| ∈ U₁}
      ≤ P ({ω | |a * W ω + b * X ω| ∈ U₁} ∩ {ω | |c * W ω + d * Y ω| ∈ D}) *
        P {ω | |a * W ω + b * X ω| ∈ U₀} := by
  have huniv : ∀ U : Set ℝ, P {ω | |a * W ω + b * X ω| ∈ U} =
      P ({ω | |a * W ω + b * X ω| ∈ U} ∩ {ω | |c * W ω + d * Y ω| ∈ (Set.univ : Set ℝ)}) := by
    intro U; congr 1; ext ω; simp
  rw [huniv U₀, huniv U₁]
  rw [measure_abs_inter_eq_lintegral P hW hX hY hWXY hXY hlawX hlawY a b c d hU₀ hD,
    measure_abs_inter_eq_lintegral P hW hX hY hWXY hXY hlawX hlawY a b c d hU₁ hD,
    measure_abs_inter_eq_lintegral P hW hX hY hWXY hXY hlawX hlawY a b c d hU₀ MeasurableSet.univ,
    measure_abs_inter_eq_lintegral P hW hX hY hWXY hXY hlawX hlawY a b c d hU₁ MeasurableSet.univ]
  simp only [Set.mem_univ, Set.ofPred_true, measure_univ, mul_one]
  refine lintegral_mixture_mul_le _ (measurable_gaussianReal_abs_affine a b hU₀)
    (measurable_gaussianReal_abs_affine a b hU₁) (measurable_gaussianReal_abs_affine c d hD)
    ?_ ?_
  · exact fun w v hvw => gaussianReal_abs_affine_mono c hd hD hDup hvw
  · -- monotone likelihood ratio of `g₁ / g₀` in `|w|`
    intro w v hvw
    rw [gaussianReal_abs_affine_mem _ hb hU₀, gaussianReal_abs_affine_mem _ hb hU₀,
      gaussianReal_abs_affine_mem _ hb hU₁, gaussianReal_abs_affine_mem _ hb hU₁]
    have hsplit : U₀ ∩ Set.Ioi 0 = U₁ ∩ Set.Ioi 0 ∪ (U₀ \ U₁) ∩ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
      constructor
      · rintro ⟨h0, hx⟩; by_cases h1 : x ∈ U₁
        · exact Or.inl ⟨h1, hx⟩
        · exact Or.inr ⟨⟨h0, h1⟩, hx⟩
      · rintro (⟨h1, hx⟩ | ⟨⟨h0, _⟩, hx⟩)
        · exact ⟨hsub h1, hx⟩
        · exact ⟨h0, hx⟩
    have hdisj : Disjoint (U₁ ∩ Set.Ioi 0) ((U₀ \ U₁) ∩ Set.Ioi 0) := by
      rw [Set.disjoint_left]; intro x hx hx'; exact hx'.1.2 hx.1
    have hBm : MeasurableSet ((U₀ \ U₁) ∩ Set.Ioi 0) := (hU₀.diff hU₁).inter measurableSet_Ioi
    rw [hsplit, foldedMeasure_union _ _ hdisj hBm, foldedMeasure_union _ _ hdisj hBm]
    have hm : |a * v| ≤ |a * w| := by
      rw [abs_mul, abs_mul]; exact mul_le_mul_of_nonneg_left hvw (abs_nonneg a)
    have hmlr := foldedMeasure_mul_le hm (sqNN_ne_zero hb) (hU₁.inter measurableSet_Ioi) hBm
      (A := U₁ ∩ Set.Ioi 0) (B := (U₀ \ U₁) ∩ Set.Ioi 0) (fun x hx y hy => ⟨le_of_lt hy.2, le_of_not_gt fun hxy =>
        hy.1.2 (hU₁up x y (le_of_lt hx.2) hxy.le hx.1)⟩)
    set A' := foldedMeasure (a * v) (sqNN b) (U₁ ∩ Set.Ioi 0)
    set A := foldedMeasure (a * w) (sqNN b) (U₁ ∩ Set.Ioi 0)
    set B' := foldedMeasure (a * v) (sqNN b) ((U₀ \ U₁) ∩ Set.Ioi 0)
    set B := foldedMeasure (a * w) (sqNN b) ((U₀ \ U₁) ∩ Set.Ioi 0)
    calc A' * (A + B) = A' * A + B * A' := by ring
      _ ≤ A' * A + A * B' := by gcongr
      _ = A * (A' + B') := by ring

/-- Conditioning on the first statistic itself: for `W` independent of a standard normal `Y`, the
joint probability of `|W| ∈ U` and `|c W + d Y| ∈ D` is a mixture over the law of `W`. -/
lemma measure_abs_inter_eq_lintegral_direct (P : Measure Ω) [IsProbabilityMeasure P]
    {W Y : Ω → ℝ} (hW : Measurable W) (hY : Measurable Y) (hWY : IndepFun W Y P)
    (hlawY : P.map Y = gaussianReal 0 1) (c d : ℝ) {U D : Set ℝ} (hU : MeasurableSet U)
    (hD : MeasurableSet D) :
    P ({ω | |W ω| ∈ U} ∩ {ω | |c * W ω + d * Y ω| ∈ D}) =
      ∫⁻ w, {x : ℝ | |x| ∈ U}.indicator 1 w *
        gaussianReal 0 1 {y | |c * w + d * y| ∈ D} ∂(P.map W) := by
  have hjoint : P.map (fun ω => (W ω, Y ω)) = (P.map W).prod (P.map Y) :=
    hWY.map_prod_eq_prod_map_map hW.aemeasurable hY.aemeasurable
  set S : Set (ℝ × ℝ) := {z | |z.1| ∈ U} ∩ {z | |c * z.1 + d * z.2| ∈ D} with hSdef
  have hS : MeasurableSet S := by
    refine MeasurableSet.inter ?_ ?_
    · exact (measurable_norm.comp measurable_fst) hU
    · exact (measurable_norm.comp ((measurable_fst.const_mul c).add
        (measurable_snd.const_mul d))) hD
  have hset : {ω | |W ω| ∈ U} ∩ {ω | |c * W ω + d * Y ω| ∈ D} =
      (fun ω => (W ω, Y ω)) ⁻¹' S := rfl
  rw [hset, ← Measure.map_apply (hW.prodMk hY) hS, hjoint, hlawY, Measure.prod_apply hS]
  refine lintegral_congr fun w => ?_
  by_cases hw : |w| ∈ U
  · have hsec : Prod.mk w ⁻¹' S = {y | |c * w + d * y| ∈ D} := by
      ext y; simp [S, hw]
    rw [hsec, Set.indicator_of_mem (show w ∈ {x : ℝ | |x| ∈ U} from hw), Pi.one_apply, one_mul]
  · have hsec : Prod.mk w ⁻¹' S = ∅ := by
      ext y; simp [S, hw]
    rw [hsec, measure_empty, Set.indicator_of_notMem (show w ∉ {x : ℝ | |x| ∈ U} from hw),
      zero_mul]

/-- **Key inequality, conditioning statistic without noise.** Let `W` be independent of a
standard normal `Y`, `d ≠ 0`, and let `U₁ ⊆ U₀` and `D` be measurable and upward closed on
`[0, ∞)`. With `E U = {|W| ∈ U}` and `F = {|c W + d Y| ∈ D}`,
`P (E U₀ ∩ F) P (E U₁) ≤ P (E U₁ ∩ F) P (E U₀)`. The law of `W` is arbitrary. -/
theorem twoSided_key_ineq_direct (P : Measure Ω) [IsProbabilityMeasure P] {W Y : Ω → ℝ}
    (hW : Measurable W) (hY : Measurable Y) (hWY : IndepFun W Y P)
    (hlawY : P.map Y = gaussianReal 0 1) (c : ℝ) {d : ℝ} (hd : d ≠ 0) {U₀ U₁ D : Set ℝ}
    (hU₀ : MeasurableSet U₀) (hU₁ : MeasurableSet U₁) (hD : MeasurableSet D) (hsub : U₁ ⊆ U₀)
    (hU₁up : ∀ x y, 0 ≤ x → x ≤ y → x ∈ U₁ → y ∈ U₁)
    (hDup : ∀ x y, 0 ≤ x → x ≤ y → x ∈ D → y ∈ D) :
    P ({ω | |W ω| ∈ U₀} ∩ {ω | |c * W ω + d * Y ω| ∈ D}) * P {ω | |W ω| ∈ U₁}
      ≤ P ({ω | |W ω| ∈ U₁} ∩ {ω | |c * W ω + d * Y ω| ∈ D}) * P {ω | |W ω| ∈ U₀} := by
  have huniv : ∀ U : Set ℝ, P {ω | |W ω| ∈ U} =
      P ({ω | |W ω| ∈ U} ∩ {ω | |c * W ω + d * Y ω| ∈ (Set.univ : Set ℝ)}) := by
    intro U; congr 1; ext ω; simp
  rw [huniv U₀, huniv U₁]
  rw [measure_abs_inter_eq_lintegral_direct P hW hY hWY hlawY c d hU₀ hD,
    measure_abs_inter_eq_lintegral_direct P hW hY hWY hlawY c d hU₁ hD,
    measure_abs_inter_eq_lintegral_direct P hW hY hWY hlawY c d hU₀ MeasurableSet.univ,
    measure_abs_inter_eq_lintegral_direct P hW hY hWY hlawY c d hU₁ MeasurableSet.univ]
  simp only [Set.mem_univ, Set.ofPred_true, measure_univ, mul_one]
  have hind : ∀ {U : Set ℝ}, MeasurableSet U →
      Measurable ({x : ℝ | |x| ∈ U}.indicator (1 : ℝ → ℝ≥0∞)) := fun hU =>
    measurable_const.indicator (measurable_norm hU)
  refine lintegral_mixture_mul_le _ (hind hU₀) (hind hU₁)
    (measurable_gaussianReal_abs_affine c d hD)
    (fun w v hvw => gaussianReal_abs_affine_mono c hd hD hDup hvw) ?_
  intro w v hvw
  by_cases h1 : |v| ∈ U₁
  · have h1w : |w| ∈ U₁ := hU₁up _ _ (abs_nonneg v) hvw h1
    have h0v : |v| ∈ U₀ := hsub h1
    rw [Set.indicator_of_mem (show v ∈ {x : ℝ | |x| ∈ U₁} from h1),
      Set.indicator_of_mem (show w ∈ {x : ℝ | |x| ∈ U₁} from h1w),
      Set.indicator_of_mem (show v ∈ {x : ℝ | |x| ∈ U₀} from h0v)]
    simp only [Pi.one_apply, one_mul]
    exact Set.indicator_le_self' (fun _ _ => zero_le) w |>.trans le_rfl
  · rw [Set.indicator_of_notMem (show v ∉ {x : ℝ | |x| ∈ U₁} from h1), zero_mul]
    exact zero_le

end KeyInequality

end Applied.MultipleTesting
