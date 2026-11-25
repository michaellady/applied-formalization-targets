import Applied.Statistics.IsingMTP2
import Applied.Statistics.PRDSMTP2
import Applied.Statistics.TwoSidedOneFactor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Two-sided z-tests of a normal vector satisfying the Karlin–Rinott sign condition

Let `Z` be a centred normal vector given by its density
`C * exp (-(1/2) * ∑ i j, B i j * z i * z j)` with respect to Lebesgue measure on `ℝ^ι`
(`gaussDensity C B`; `B` is the precision matrix, i.e. the inverse covariance matrix, and `C` the
normalising constant). Assume the **Karlin–Rinott sign condition**: there are signs `d i = ± 1`
with `B i j * d i * d j ≤ 0` for all `i ≠ j`.

* `map_abs_withDensity`: the vector of absolute values `(|Z i|)` of a vector with density `g` has
  density `w ↦ 1{w > 0} * ∑ over sign patterns σ of g (σ w)` (folding).
* `foldedGaussDensity_mtp2`: under the sign condition the folded normal density is multivariate
  totally positive of order two (from `signSum_mtp2`).
* `isPRDSOn_abs_of_gaussDensity`, `isPRDSOn_twoSided_of_gaussDensity`: hence the two-sided
  p-values are positively regression dependent (`IsPRDSOn`, the conditioning-on-`p i ≤ t` form).
* `measure_simes_le_twoSided_of_gaussDensity`: the Simes inequality, any number of statistics.
* `fdr_bhReject_le_twoSided_of_gaussDensity`, `fwer_hommel_le_twoSided_of_gaussDensity`,
  `fwer_hochberg_le_twoSided_of_gaussDensity`.

The sign condition holds for every tridiagonal precision matrix (Gaussian Markov chains, e.g.
stationary AR(1) statistics with correlation `ρ ^ |i - j|` of either sign), more generally when
the graph of non-zero off-diagonal entries of `B` is a forest, and for one-factor models; these
facts about particular matrices are not formalised here.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

open Applied.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Folding

/-- Coordinatewise sign change `z ↦ (σ i * z i)`. -/
def flip (σ : ι → Bool) (z : ι → ℝ) : ι → ℝ := fun i => sg (σ i) * z i

omit [Fintype ι] [DecidableEq ι] in
lemma flip_flip (σ : ι → Bool) (z : ι → ℝ) : flip σ (flip σ z) = z := by
  funext i
  simp only [flip]
  rw [← mul_assoc, sg_mul_self, one_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_flip (σ : ι → Bool) : Measurable (flip σ) :=
  measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_mul _

lemma sg_ne_zero (b : Bool) : sg b ≠ 0 := by cases b <;> simp

omit [DecidableEq ι] in
lemma measurePreserving_flip (σ : ι → Bool) :
    MeasurePreserving (flip σ) (Measure.pi fun _ : ι => (volume : Measure ℝ))
      (Measure.pi fun _ : ι => (volume : Measure ℝ)) := by
  refine measurePreserving_pi (fun _ => volume) (fun _ => volume)
    (f := fun i x => sg (σ i) * x) fun i => ⟨measurable_const_mul _, ?_⟩
  rw [Real.map_volume_mul_left (sg_ne_zero _), abs_inv, abs_sg]
  simp

/-- The open positive orthant. -/
def posOrthant : Set (ι → ℝ) := {w | ∀ i, 0 < w i}

omit [DecidableEq ι] in
lemma measurableSet_posOrthant : MeasurableSet (posOrthant : Set (ι → ℝ)) := by
  have : (posOrthant : Set (ι → ℝ)) = ⋂ i, {w | 0 < w i} := by
    ext w; simp [posOrthant]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)

/-- Away from the coordinate hyperplanes, exactly one sign change maps `z` into the positive
orthant, and it maps `z` to `(|z i|)`. -/
lemma indicator_abs_eq_sum_flip {z : ι → ℝ} (hz : ∀ i, z i ≠ 0) (E : Set (ι → ℝ))
    (g : (ι → ℝ) → ℝ≥0∞) :
    ((fun (z : ι → ℝ) i => |z i|) ⁻¹' E).indicator g z =
      ∑ σ : ι → Bool, (flip σ ⁻¹' (E ∩ posOrthant)).indicator g z := by
  classical
  set σ₀ : ι → Bool := fun i => decide (z i < 0) with hσ₀
  have hflip : flip σ₀ z = fun i => |z i| := by
    funext i
    simp only [flip, hσ₀]
    by_cases h : z i < 0
    · simp [h, abs_of_neg h]
    · simp [h, abs_of_nonneg (not_lt.mp h)]
  have hpos : (fun i => |z i|) ∈ (posOrthant : Set (ι → ℝ)) := fun i => abs_pos.mpr (hz i)
  rw [Finset.sum_eq_single σ₀ (fun σ _ hσ => Set.indicator_of_notMem (fun h => hσ ?_) _)
    (fun h => absurd (mem_univ _) h)]
  · by_cases hE : (fun i => |z i|) ∈ E
    · rw [Set.indicator_of_mem (show z ∈ (fun (z : ι → ℝ) i => |z i|) ⁻¹' E from hE),
        Set.indicator_of_mem]
      show flip σ₀ z ∈ E ∩ posOrthant
      rw [hflip]
      exact ⟨hE, hpos⟩
    · rw [Set.indicator_of_notMem (show z ∉ (fun (z : ι → ℝ) i => |z i|) ⁻¹' E from hE),
        Set.indicator_of_notMem]
      intro h
      have h' : flip σ₀ z ∈ E ∩ posOrthant := h
      rw [hflip] at h'
      exact hE h'.1
  · have hp : ∀ i, 0 < sg (σ i) * z i := h.2
    funext i
    have hpi := hp i
    by_cases hneg : z i < 0
    · cases hσi : σ i
      · rw [hσi] at hpi
        simp only [sg_false, one_mul] at hpi
        exact absurd hpi (not_lt.mpr hneg.le)
      · simp [hσ₀, hneg]
    · cases hσi : σ i
      · simp [hσ₀, hneg]
      · rw [hσi] at hpi
        simp only [sg_true] at hpi
        have : 0 ≤ z i := not_lt.mp hneg
        linarith

/-- **Folding.** If a random vector has density `g` with respect to Lebesgue measure on `ℝ^ι`,
the vector of its absolute values has density
`w ↦ 1{w ∈ (0, ∞)^ι} * ∑ over sign patterns σ of g (σ w)`. -/
theorem map_abs_withDensity (g : (ι → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ((Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity g).map (fun z i => |z i|) =
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity
        (fun w => posOrthant.indicator 1 w * ∑ σ : ι → Bool, g (flip σ w)) := by
  classical
  set V : Measure (ι → ℝ) := Measure.pi fun _ : ι => (volume : Measure ℝ) with hV
  have habs : Measurable fun (z : ι → ℝ) i => |z i| :=
    measurable_pi_iff.mpr fun i => measurable_norm.comp (measurable_pi_apply i)
  have hpos := measurableSet_posOrthant (ι := ι)
  ext E hE
  rw [Measure.map_apply habs hE, withDensity_apply _ (habs hE), withDensity_apply _ hE,
    ← lintegral_indicator (habs hE), ← lintegral_indicator hE]
  have hae : ∀ᵐ z ∂V, ∀ i, z i ≠ 0 := ae_all_iff.mpr fun i =>
    Measure.ae_eval_ne (μ := fun _ : ι => (volume : Measure ℝ)) i 0
  calc ∫⁻ z, ((fun (z : ι → ℝ) i => |z i|) ⁻¹' E).indicator g z ∂V
      = ∫⁻ z, ∑ σ : ι → Bool, (flip σ ⁻¹' (E ∩ posOrthant)).indicator g z ∂V :=
        lintegral_congr_ae (hae.mono fun z hz => indicator_abs_eq_sum_flip hz E g)
    _ = ∑ σ : ι → Bool, ∫⁻ z, (flip σ ⁻¹' (E ∩ posOrthant)).indicator g z ∂V :=
        lintegral_finsetSum _ fun σ _ => hg.indicator (measurable_flip σ (hE.inter hpos))
    _ = ∑ σ : ι → Bool, ∫⁻ w, (E ∩ posOrthant).indicator (fun w => g (flip σ w)) w ∂V := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        refine Eq.trans ?_ ((measurePreserving_flip σ).lintegral_comp
          (f := (E ∩ posOrthant).indicator fun w => g (flip σ w))
          ((hg.comp (measurable_flip σ)).indicator (hE.inter hpos)))
        refine lintegral_congr fun z => ?_
        by_cases h : flip σ z ∈ E ∩ posOrthant
        · rw [Set.indicator_of_mem (show z ∈ flip σ ⁻¹' (E ∩ posOrthant) from h),
            Set.indicator_of_mem h, flip_flip]
        · rw [Set.indicator_of_notMem (show z ∉ flip σ ⁻¹' (E ∩ posOrthant) from h),
            Set.indicator_of_notMem h]
    _ = ∫⁻ w, ∑ σ : ι → Bool, (E ∩ posOrthant).indicator (fun w => g (flip σ w)) w ∂V :=
        (lintegral_finsetSum _ fun σ _ =>
          (hg.comp (measurable_flip σ)).indicator (hE.inter hpos)).symm
    _ = ∫⁻ w, E.indicator
          (fun w => posOrthant.indicator 1 w * ∑ σ : ι → Bool, g (flip σ w)) w ∂V := by
        refine lintegral_congr fun w => ?_
        by_cases h1 : w ∈ E <;> by_cases h2 : w ∈ (posOrthant : Set (ι → ℝ)) <;>
          simp [Set.indicator_apply, h1, h2]

end Folding

section Density

/-- The centred normal density with precision matrix `B`, up to the constant `C`:
`C * exp (-(1/2) * ∑ i j, B i j * z i * z j)`. -/
noncomputable def gaussDensity (C : ℝ≥0∞) (B : ι → ι → ℝ) (z : ι → ℝ) : ℝ≥0∞ :=
  C * ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i, ∑ j, B i j * z i * z j))

omit [DecidableEq ι] in
lemma measurable_gaussDensity (C : ℝ≥0∞) (B : ι → ι → ℝ) : Measurable (gaussDensity C B) := by
  unfold gaussDensity
  refine measurable_const.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      (measurable_const.mul (measurable_pi_apply i)).mul (measurable_pi_apply j)))))

lemma sum_gaussDensity_flip (C : ℝ≥0∞) (B : ι → ι → ℝ) (w : ι → ℝ) :
    ∑ σ : ι → Bool, gaussDensity C B (flip σ w) =
      C * ENNReal.ofReal (signSum (fun i j => -(B i j) / 2) w) := by
  simp only [gaussDensity, signSum]
  rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun _ _ => (Real.exp_pos _).le]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [flip]
  ring

/-- Density of the vector of absolute values of a vector with density `gaussDensity C B`. -/
noncomputable def foldedGaussDensity (C : ℝ≥0∞) (B : ι → ι → ℝ) (w : ι → ℝ) : ℝ≥0∞ :=
  posOrthant.indicator 1 w * ∑ σ : ι → Bool, gaussDensity C B (flip σ w)

lemma measurable_foldedGaussDensity (C : ℝ≥0∞) (B : ι → ι → ℝ) :
    Measurable (foldedGaussDensity C B) :=
  (measurable_one.indicator measurableSet_posOrthant).mul
    (Finset.measurable_sum _ fun σ _ => (measurable_gaussDensity C B).comp (measurable_flip σ))

/-- **The folded normal density is MTP2 under the Karlin–Rinott sign condition.** -/
theorem foldedGaussDensity_mtp2 (C : ℝ≥0∞) (B : ι → ι → ℝ) (d : ι → Bool)
    (hB : ∀ i j, i ≠ j → B i j * sg (d i) * sg (d j) ≤ 0) (x y : ι → ℝ) :
    foldedGaussDensity C B x * foldedGaussDensity C B y ≤
      foldedGaussDensity C B (x ⊔ y) * foldedGaussDensity C B (x ⊓ y) := by
  unfold foldedGaussDensity
  by_cases hx : x ∈ (posOrthant : Set (ι → ℝ))
  · by_cases hy : y ∈ (posOrthant : Set (ι → ℝ))
    · have hs : x ⊔ y ∈ (posOrthant : Set (ι → ℝ)) := fun i => lt_of_lt_of_le (hx i) le_sup_left
      have hi : x ⊓ y ∈ (posOrthant : Set (ι → ℝ)) := fun i => lt_inf_iff.mpr ⟨hx i, hy i⟩
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hs,
        Set.indicator_of_mem hi, Pi.one_apply, one_mul, sum_gaussDensity_flip]
      have h := signSum_mtp2 (fun i j => -(B i j) / 2) d (fun i j hij => by
        have e : -(B i j) / 2 * sg (d i) * sg (d j) = -(B i j * sg (d i) * sg (d j)) / 2 := by
          ring
        rw [e]
        linarith [hB i j hij]) (x := x) (y := y) (fun i => (hx i).le) (fun i => (hy i).le)
      set G := signSum fun i j => -(B i j) / 2 with hG
      calc C * ENNReal.ofReal (G x) * (C * ENNReal.ofReal (G y))
          = C * C * ENNReal.ofReal (G x * G y) := by
            rw [ENNReal.ofReal_mul (signSum_pos _ _).le]; ring
        _ ≤ C * C * ENNReal.ofReal (G (x ⊔ y) * G (x ⊓ y)) :=
            mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal h)
        _ = C * ENNReal.ofReal (G (x ⊔ y)) * (C * ENNReal.ofReal (G (x ⊓ y))) := by
            rw [ENNReal.ofReal_mul (signSum_pos _ _).le]; ring
    · simp [Set.indicator_of_notMem hy]
  · simp [Set.indicator_of_notMem hx]

end Density

section Tests

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Absolute values of a normal vector under the Karlin–Rinott sign condition are positively
regression dependent.** Let the law of `Z` be `gaussDensity C B · Lebesgue` with
`B i j * d i * d j ≤ 0` for `i ≠ j`, and `p j = ψ j |Z j|` with `ψ j` measurable and
non-increasing. Then the `p j` are `IsPRDSOn` on every set of hypotheses. -/
theorem isPRDSOn_abs_of_gaussDensity (P : Measure Ω) (Z : ι → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (C : ℝ≥0∞) (B : ι → ι → ℝ) (d : ι → Bool)
    (hB : ∀ i j, i ≠ j → B i j * sg (d i) * sg (d j) ≤ 0)
    (hlaw : P.map (fun ω i => Z i ω) =
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity (gaussDensity C B))
    (ψ : ι → ℝ → ℝ) (hψm : ∀ j, Measurable (ψ j)) (hψ : ∀ j, Antitone (ψ j)) (H₀ : Finset ι) :
    IsPRDSOn P (fun j ω => ψ j |Z j ω|) H₀ := by
  have habs : Measurable fun (z : ι → ℝ) i => |z i| :=
    measurable_pi_iff.mpr fun i => measurable_norm.comp (measurable_pi_apply i)
  have hlaw' : P.map (fun ω j => |Z j ω|) =
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity (foldedGaussDensity C B) := by
    have hcomp : (fun ω j => |Z j ω|) = (fun (z : ι → ℝ) i => |z i|) ∘ fun ω i => Z i ω := rfl
    rw [hcomp, ← Measure.map_map habs (measurable_pi_iff.mpr hZ), hlaw,
      map_abs_withDensity _ (measurable_gaussDensity C B)]
    rfl
  exact isPRDSOn_of_mtp2_density P (fun j ω => |Z j ω|)
    (fun j => measurable_norm.comp (hZ j)) (fun _ => volume) (foldedGaussDensity C B)
    (measurable_foldedGaussDensity C B) (foldedGaussDensity_mtp2 C B d hB) hlaw' ψ hψm hψ H₀

/-- Two-sided p-values `2 (1 - Φ(|Z j|))` of a normal vector under the Karlin–Rinott sign
condition are `IsPRDSOn` on every set of hypotheses. -/
theorem isPRDSOn_twoSided_of_gaussDensity (P : Measure Ω) (Z : ι → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (C : ℝ≥0∞) (B : ι → ι → ℝ) (d : ι → Bool)
    (hB : ∀ i j, i ≠ j → B i j * sg (d i) * sg (d j) ≤ 0)
    (hlaw : P.map (fun ω i => Z i ω) =
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity (gaussDensity C B))
    (H₀ : Finset ι) :
    IsPRDSOn P (fun j ω => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|)) H₀ :=
  isPRDSOn_abs_of_gaussDensity P Z hZ C B d hB hlaw
    (fun _ x => 2 * (1 - cdf (gaussianReal 0 1) x)) (fun _ => measurable_twoSided)
    (fun _ => antitone_twoSided) H₀

/-- **The Simes inequality for two-sided z-tests under the Karlin–Rinott sign condition, any
number of statistics.** `Z` has density `gaussDensity C B` with `B i j * d i * d j ≤ 0` for
`i ≠ j`, and each `Z i` is standard normal. -/
theorem measure_simes_le_twoSided_of_gaussDensity (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (C : ℝ≥0∞) (B : ι → ι → ℝ) (d : ι → Bool)
    (hB : ∀ i j, i ≠ j → B i j * sg (d i) * sg (d j) ≤ 0)
    (hlaw : P.map (fun ω i => Z i ω) =
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity (gaussDensity C B))
    (hmarg : ∀ i, P.map (Z i) = gaussianReal 0 1) {α : ℝ} (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun j => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|)} ≤ ENNReal.ofReal α :=
  measure_one_le_bhK_le_of_prds P hα _ (fun j => measurable_twoSided_abs (hZ j))
    (fun i => isValidPValue_zTest_twoSided P (Z i) (hZ i) (hmarg i))
    (isPRDSOn_twoSided_of_gaussDensity P Z hZ C B d hB hlaw univ)

/-- **Benjamini–Hochberg for two-sided z-tests under the Karlin–Rinott sign condition.** The
whole vector `Z` has density `gaussDensity C B` (so every coordinate is centred normal); the true
nulls are standard normal. The false discovery rate is at most `α m₀ / m`. -/
theorem fdr_bhReject_le_twoSided_of_gaussDensity (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (C : ℝ≥0∞) (B : ι → ι → ℝ) (d : ι → Bool)
    (hB : ∀ i j, i ≠ j → B i j * sg (d i) * sg (d j) ≤ 0)
    (hlaw : P.map (fun ω i => Z i ω) =
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity (gaussDensity C B))
    (H₀ : Finset ι) (hmarg : ∀ i ∈ H₀, P.map (Z i) = gaussianReal 0 1) {α : ℝ} (hα : 0 ≤ α) :
    fdr P H₀ (fun ω => bhReject α fun j => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|))
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) :=
  fdr_bhReject_le_of_prds P hα _ (fun j => measurable_twoSided_abs (hZ j)) H₀
    (fun i hi => isValidPValue_zTest_twoSided P (Z i) (hZ i) (hmarg i hi))
    (isPRDSOn_twoSided_of_gaussDensity P Z hZ C B d hB hlaw H₀)

/-- **Hommel's procedure for two-sided z-tests whose true-null statistics satisfy the
Karlin–Rinott sign condition.** The vector `(Z i)_{i ∈ H₀}` of true-null statistics has density
`gaussDensity C B` on `ℝ^H₀` with `B i j * d i * d j ≤ 0` for `i ≠ j`, each `Z i`, `i ∈ H₀`, is
standard normal, and the false-null statistics are arbitrary measurable functions. -/
theorem fwer_hommel_le_twoSided_of_gaussDensity (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (H₀ : Finset ι) (C : ℝ≥0∞)
    (B : H₀ → H₀ → ℝ) (d : H₀ → Bool) (hB : ∀ i j, i ≠ j → B i j * sg (d i) * sg (d j) ≤ 0)
    (hlaw : P.map (fun ω (i : H₀) => Z i ω) =
      (Measure.pi fun _ : H₀ => (volume : Measure ℝ)).withDensity (gaussDensity C B))
    (hmarg : ∀ i ∈ H₀, P.map (Z i) = gaussianReal 0 1) {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hommel α fun j ω => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|))
      ≤ ENNReal.ofReal α :=
  fwer_closedTest_le P _ H₀ _
    (measure_simes_le_twoSided_of_gaussDensity (ι := H₀) P (fun j => Z j) (fun j => hZ j) C B d
      hB hlaw (fun j => hmarg j j.2) hα)

/-- **Hochberg's procedure** under the hypotheses of
`fwer_hommel_le_twoSided_of_gaussDensity`. -/
theorem fwer_hochberg_le_twoSided_of_gaussDensity (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (H₀ : Finset ι) (C : ℝ≥0∞)
    (B : H₀ → H₀ → ℝ) (d : H₀ → Bool) (hB : ∀ i j, i ≠ j → B i j * sg (d i) * sg (d j) ≤ 0)
    (hlaw : P.map (fun ω (i : H₀) => Z i ω) =
      (Measure.pi fun _ : H₀ => (volume : Measure ℝ)).withDensity (gaussDensity C B))
    (hmarg : ∀ i ∈ H₀, P.map (Z i) = gaussianReal 0 1) {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hochberg α fun j ω => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|))
      ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans
    (fwer_hommel_le_twoSided_of_gaussDensity P Z hZ H₀ C B d hB hlaw hmarg hα)
  rintro ω ⟨i, hi, hrej⟩
  exact ⟨i, hi, hochberg_subset_hommel hα _ ω hrej⟩

end Tests

end Applied.MultipleTesting
