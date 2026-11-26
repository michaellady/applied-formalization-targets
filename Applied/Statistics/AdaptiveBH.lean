import Applied.Statistics.BHMonotone
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Adaptive Benjamini–Hochberg procedures under independence

The Benjamini–Hochberg procedure at level `α` has false discovery rate at most `α m₀ / m`
(`fdr_bhReject_le`; with equality for exactly uniform true nulls and `α ≤ 1`,
`fdr_bhReject_eq`), so it is conservative when the proportion `m₀ / m` of
true nulls is small. Adaptive procedures estimate that proportion from the p-values and run
the step-up procedure at a correspondingly larger, data-dependent level. This file proves
false discovery rate control for such procedures when each true-null p-value is independent of
the other p-values. Notation as in `Applied.Statistics.BenjaminiHochberg`.

## Main results

* `lintegral_inv_of_le_mul_le`: the one-dimensional inequality behind everything. If `U` is
  super-uniform, `g` is a non-increasing function with values in `ℕ` and `c ≥ 0`, then
  `E[1{U ≤ c g(U), g(U) ≥ 1} / g(U)] ≤ c`.
* `fdr_le_of_selfConsistent`: a rejection rule `R` whose number of rejections is non-increasing
  in every p-value and which is self-consistent along the data, `i ∈ R → pᵢ ≤ cᵢ(p₀,ᵢ) |R|`
  with `cᵢ` evaluated at the p-values with `pᵢ` replaced by `0`, has
  `FDR ≤ ∑_{i ∈ H₀} E[cᵢ(p₀,ᵢ)]`.
* `fdr_adaptiveBH_le`: the plug-in adaptive linear step-up procedure `adaptiveBH α G`
  (Benjamini–Hochberg at level `α G(p)`, with `G` an estimator of `m / m₀`) has
  `FDR ≤ (α / m) ∑_{i ∈ H₀} E[G(p₀,ᵢ)]` when `G` is measurable, non-negative and
  non-increasing (Benjamini–Krieger–Yekutieli 2006; Blanchard–Roquain 2009, Theorem 3.3 of the
  arXiv version, for step-up procedures).
* `sum_lintegral_storey_le_one`: `∑_{i ∈ H₀} E[(1 - λ) / (Nᵢ + 1)] ≤ 1`, where `Nᵢ` is the
  number of p-values other than `pᵢ` that exceed `λ`.
* `fdr_storeyBH_le`: the adaptive procedure with Storey's estimator
  `π̂₀ = (1 + #{pⱼ > λ}) / (m (1 - λ))` (`storeyBH`) has `FDR ≤ α`.
* `fdr_tstRejectAt_le`, `fdr_tstReject_le`: the two-stage procedure of Benjamini, Krieger and
  Yekutieli (2006, Definition 6 and Theorem 1) with first-stage level `a` has
  `FDR ≤ a / (1 - a)`; with `a = α / (1 + α)` (`tstReject`) this is `FDR ≤ α`.

## Conventions

* `storeyBH` does not cap the rejection threshold at `λ` (the capped version is the one of
  Storey, Taylor and Siegmund 2004); it rejects at least as much as the capped version.
* `tstRejectAt a q` rejects everything when the first stage rejects everything, and is the
  Benjamini–Hochberg procedure at level `a m / (m - r₁)` otherwise, `r₁` being the number of
  first-stage rejections. When `r₁ = 0` this is the first stage again, which rejects nothing.
* Independence is assumed in the leave-one-out form of `fdr_bhReject_le`: every true-null
  p-value is independent of the vector of p-values with its own coordinate set to `0`.
  Nothing is assumed about the false nulls.

## Not in this file

Positive dependence. For identical uniform p-values, Storey's procedure with `λ = 1/2`, `m ≥ 3`
and `α < 1/2` has false discovery rate `min(1/2, α m / 2) > α` (Blanchard–Roquain 2009,
Proposition 3.8), so `fdr_storeyBH_le` fails under PRDS. For the two-stage procedure the same
model gives `α / (1 + α)`; no failure of `fdr_tstReject_le` under PRDS is claimed, and no proof
either. Also not here: data-dependent `λ`, the quantile estimator, the multi-stage procedure of
Benjamini–Krieger–Yekutieli, the sharper bound `(1 - λ^{m₀}) α` and step-down procedures.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Applied.MultipleTesting

/-! ### The one-dimensional inequality -/

/-- If `μ` is the law of a super-uniform variable, `g : ℝ → ℕ` is non-increasing and `c ≥ 0`,
then `∫ 1{u ≤ c g(u), g(u) ≥ 1} / g(u) dμ(u) ≤ c`. No measurability of `g` is needed. -/
theorem lintegral_inv_of_le_mul_le (μ : Measure ℝ)
    (hμ : ∀ t : ℝ, 0 ≤ t → μ (Set.Iic t) ≤ ENNReal.ofReal t) {c : ℝ} (hc : 0 ≤ c)
    (g : ℝ → ℕ) (hg : Antitone g) :
    ∫⁻ u, (if u ≤ c * g u ∧ 1 ≤ g u then ((g u : ℝ≥0∞))⁻¹ else 0) ∂μ ≤ ENNReal.ofReal c := by
  classical
  by_cases hS : ∃ k u, u ≤ c * g u ∧ 1 ≤ g u ∧ g u = k
  · -- `k₀` is the smallest value of `g` on the set where the integrand is non-zero
    obtain ⟨u₀, hu₀, h1, hgu₀⟩ := Nat.find_spec hS
    have hmin' : ∀ u, u ≤ c * g u ∧ 1 ≤ g u → Nat.find hS ≤ g u :=
      fun u h => Nat.find_min' hS ⟨u, h.1, h.2, rfl⟩
    generalize Nat.find hS = k₀ at hgu₀ hmin'
    have hk1 : 1 ≤ k₀ := hgu₀ ▸ h1
    have hbound : ∀ u, (if u ≤ c * g u ∧ 1 ≤ g u then ((g u : ℝ≥0∞))⁻¹ else 0)
        ≤ (Set.Iic (c * k₀)).indicator (fun _ => ((k₀ : ℝ≥0∞))⁻¹) u := by
      intro u
      split_ifs with h
      · have hmin : k₀ ≤ g u := hmin' u h
        have hu : u ≤ c * k₀ := by
          rcases le_total u u₀ with hle | hle
          · rw [← hgu₀]; exact hle.trans hu₀
          · have h2 : g u ≤ k₀ := hgu₀ ▸ hg hle
            have h3 : g u = k₀ := le_antisymm h2 hmin
            rw [← h3]; exact h.1
        rw [Set.indicator_of_mem (show u ∈ Set.Iic (c * k₀) from hu)]
        exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hmin)
      · exact zero_le
    have hk0 : (k₀ : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : k₀ ≠ 0)
    calc ∫⁻ u, (if u ≤ c * g u ∧ 1 ≤ g u then ((g u : ℝ≥0∞))⁻¹ else 0) ∂μ
        ≤ ∫⁻ u, (Set.Iic (c * k₀)).indicator (fun _ => ((k₀ : ℝ≥0∞))⁻¹) u ∂μ :=
          lintegral_mono hbound
      _ = ((k₀ : ℝ≥0∞))⁻¹ * μ (Set.Iic (c * k₀)) := lintegral_indicator_const measurableSet_Iic _
      _ ≤ ((k₀ : ℝ≥0∞))⁻¹ * ENNReal.ofReal (c * k₀) := by
          gcongr; exact hμ _ (by positivity)
      _ = ENNReal.ofReal c := by
          rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_natCast, mul_comm, mul_assoc,
            ENNReal.mul_inv_cancel hk0 (ENNReal.natCast_ne_top k₀), mul_one]
  · have h0 : ∀ u, (if u ≤ c * g u ∧ 1 ≤ g u then ((g u : ℝ≥0∞))⁻¹ else 0) = 0 := by
      intro u
      rw [ite_eq_right]
      exact fun h => hS ⟨g u, u, h.1, h.2, rfl⟩
    simp [h0]

/-! ### Self-consistent rejection rules -/

section General

variable {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]

/-- **False discovery rate of a self-consistent, non-increasing rejection rule under
independence.** Let `R` map a vector of p-values to a set of rejected hypotheses, with a
measurable number of rejections that is non-increasing in each true-null p-value. Let `c i`
be non-negative measurable functions such that, along the data, a rejected true null `i` has
`pᵢ ≤ cᵢ(p₀,ᵢ) |R|`, where `p₀,ᵢ` is the vector of p-values with `pᵢ` replaced by `0`. If every
true-null p-value is valid and independent of `p₀,ᵢ`, then `FDR ≤ ∑_{i ∈ H₀} E[cᵢ(p₀,ᵢ)]`. -/
theorem fdr_le_of_selfConsistent (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P)
    (R : (ι → ℝ) → Finset ι) (hRmeas : Measurable fun q => (R q).card)
    (hRanti : ∀ i ∈ H₀, ∀ q : ι → ℝ, Antitone fun u : ℝ => (R (Function.update q i u)).card)
    (c : ι → (ι → ℝ) → ℝ) (hc0 : ∀ i ∈ H₀, ∀ y, 0 ≤ c i y)
    (hcmeas : ∀ i ∈ H₀, Measurable (c i))
    (hsc : ∀ i ∈ H₀, ∀ ω, i ∈ R (fun j => p j ω) →
      p i ω ≤ c i (Function.update (fun j => p j ω) i 0) * (R fun j => p j ω).card) :
    fdr P H₀ (fun ω => R fun j => p j ω)
      ≤ ∑ i ∈ H₀, ∫⁻ ω, ENNReal.ofReal (c i (Function.update (fun j => p j ω) i 0)) ∂P := by
  classical
  set Y : ι → Ω → ι → ℝ := fun i ω => Function.update (fun j => p j ω) i 0 with hY
  have hYmeas : ∀ i, Measurable (Y i) := by
    intro i
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hji : j = i
    · subst hji; simp [hY]
    · simpa [hY, Function.update_of_ne hji] using hmeas j
  -- the contribution of `i`, as a function of the leave-one-out vector and of `p i`
  set F : ι → (ι → ℝ) × ℝ → ℝ≥0∞ := fun i z =>
    if z.2 ≤ c i z.1 * (R (Function.update z.1 i z.2)).card ∧
        1 ≤ (R (Function.update z.1 i z.2)).card
      then (((R (Function.update z.1 i z.2)).card : ℝ≥0∞))⁻¹ else 0 with hF
  have hupd : ∀ i ω, Function.update (Y i ω) i (p i ω) = fun j => p j ω := by
    intro i ω
    simp [hY]
  have hFmeas : ∀ i ∈ H₀, Measurable (F i) := by
    intro i hi
    have hκ : Measurable fun z : (ι → ℝ) × ℝ => (R (Function.update z.1 i z.2)).card :=
      hRmeas.comp measurable_update'
    have hκR : Measurable fun z : (ι → ℝ) × ℝ => ((R (Function.update z.1 i z.2)).card : ℝ) :=
      (measurable_from_top (f := fun n : ℕ => (n : ℝ))).comp hκ
    have hκE : Measurable fun z : (ι → ℝ) × ℝ =>
        ((R (Function.update z.1 i z.2)).card : ℝ≥0∞) :=
      (measurable_from_top (f := fun n : ℕ => (n : ℝ≥0∞))).comp hκ
    refine Measurable.ite ?_ hκE.inv measurable_const
    exact (measurableSet_le measurable_snd (((hcmeas i hi).comp measurable_fst).mul hκR)).inter
      (measurableSet_le measurable_const hκ)
  -- pointwise bound on the false discovery proportion
  have hpt : ∀ ω, fdp H₀ (R fun j => p j ω) ≤ ∑ i ∈ H₀, F i (Y i ω, p i ω) := by
    intro ω
    have hcard : (((R fun j => p j ω) ∩ H₀).card : ℝ≥0∞)
        = ∑ i ∈ H₀, if i ∈ R (fun j => p j ω) then (1 : ℝ≥0∞) else 0 := by
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
      push_cast
      rfl
    rw [fdp, hcard, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    by_cases hmem : i ∈ R fun j => p j ω
    · have h1 : 1 ≤ (R fun j => p j ω).card := Finset.card_pos.mpr ⟨i, hmem⟩
      have hval : F i (Y i ω, p i ω) = (((R fun j => p j ω).card : ℝ≥0∞))⁻¹ := by
        simp only [hF, hupd]
        rw [ite_eq_left ⟨hsc i hi ω hmem, h1⟩]
      rw [hval, ite_eq_left hmem, one_mul]
    · rw [ite_eq_right hmem, zero_mul]; exact zero_le
  -- one true null: integrate out `p i` first
  have hterm : ∀ i ∈ H₀,
      ∫⁻ ω, F i (Y i ω, p i ω) ∂P ≤ ∫⁻ ω, ENNReal.ofReal (c i (Y i ω)) ∂P := by
    intro i hi
    have hmap : P.map (fun ω => (Y i ω, p i ω)) = (P.map (Y i)).prod (P.map (p i)) :=
      (indepFun_iff_map_prod_eq_prod_map_map (hYmeas i).aemeasurable
        (hmeas i).aemeasurable).mp (hindep i hi).symm
    calc ∫⁻ ω, F i (Y i ω, p i ω) ∂P
        = ∫⁻ z, F i z ∂(P.map fun ω => (Y i ω, p i ω)) :=
          (lintegral_map (hFmeas i hi) ((hYmeas i).prodMk (hmeas i))).symm
      _ = ∫⁻ y, ∫⁻ u, F i (y, u) ∂(P.map (p i)) ∂(P.map (Y i)) := by
          rw [hmap, lintegral_prod _ (hFmeas i hi).aemeasurable]
      _ ≤ ∫⁻ y, ENNReal.ofReal (c i y) ∂(P.map (Y i)) := by
          refine lintegral_mono fun y => ?_
          exact lintegral_inv_of_le_mul_le (P.map (p i))
            (fun t ht => by
              rw [Measure.map_apply (hmeas i) measurableSet_Iic]
              exact hvalid i hi t ht)
            (hc0 i hi y) _ (hRanti i hi y)
      _ = ∫⁻ ω, ENNReal.ofReal (c i (Y i ω)) ∂P :=
          lintegral_map (ENNReal.measurable_ofReal.comp (hcmeas i hi)) (hYmeas i)
  calc fdr P H₀ (fun ω => R fun j => p j ω)
      ≤ ∫⁻ ω, ∑ i ∈ H₀, F i (Y i ω, p i ω) ∂P := lintegral_mono hpt
    _ = ∑ i ∈ H₀, ∫⁻ ω, F i (Y i ω, p i ω) ∂P :=
        lintegral_finsetSum _ fun i hi =>
          (hFmeas i hi).comp ((hYmeas i).prodMk (hmeas i))
    _ ≤ ∑ i ∈ H₀, ∫⁻ ω, ENNReal.ofReal (c i (Y i ω)) ∂P :=
        Finset.sum_le_sum hterm

end General

variable {ι : Type*} [Fintype ι]

/-! ### Plug-in adaptive linear step-up procedures -/

section Deterministic

/-- The Benjamini–Hochberg cut-off is non-decreasing in the level. -/
lemma bhK_mono_level {α β : ℝ} (h : α ≤ β) (q : ι → ℝ) : bhK α q ≤ bhK β q := by
  refine le_bhK q (bhK_le q) ((bhK_le_bhCount q).trans (Finset.card_le_card fun j hj => ?_))
  rw [mem_filter] at hj ⊢
  refine ⟨mem_univ _, hj.2.trans ?_⟩
  gcongr

/-- The Benjamini–Hochberg cut-off is jointly measurable in the level and the p-values. -/
lemma measurable_bhK_comp {X : Type*} [MeasurableSpace X] {a : X → ℝ} {x : X → ι → ℝ}
    (ha : Measurable a) (hx : Measurable x) : Measurable fun y => bhK (a y) (x y) := by
  classical
  have hcount : ∀ k : ℕ, Measurable fun y => bhCount (a y) (x y) k := by
    intro k
    have : (fun y => bhCount (a y) (x y) k)
        = fun y => ∑ j, if x y j ≤ a y * k / Fintype.card ι then 1 else 0 := by
      funext y; rw [bhCount, Finset.card_filter]
    rw [this]
    exact Finset.measurable_sum _ fun j _ =>
      Measurable.ite (measurableSet_le ((measurable_pi_apply j).comp hx)
        ((ha.mul_const _).div_const _)) measurable_const measurable_const
  have hterm : ∀ k : ℕ, Measurable fun y => if k ≤ bhCount (a y) (x y) k then k else 0 :=
    fun k => Measurable.ite (measurableSet_le measurable_const (hcount k))
      measurable_const measurable_const
  have : ∀ n : ℕ, Measurable fun y =>
      (range n).sup fun k => if k ≤ bhCount (a y) (x y) k then k else 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.range_add_one, Finset.sup_insert]
      exact (hterm n).sup ih
  exact this _

/-- The **plug-in adaptive linear step-up procedure** with estimator `G` of `m / m₀`: the
Benjamini–Hochberg procedure at the data-dependent level `α G(q)`. -/
noncomputable def adaptiveBH (α : ℝ) (G : (ι → ℝ) → ℝ) (q : ι → ℝ) : Finset ι :=
  bhReject (α * G q) q

variable {α : ℝ} {G : (ι → ℝ) → ℝ}

/-- The adaptive procedure rejects `bhK (α G(q)) q` hypotheses. -/
lemma card_adaptiveBH (hα : 0 ≤ α) (hG0 : ∀ q, 0 ≤ G q) (q : ι → ℝ) :
    (adaptiveBH α G q).card = bhK (α * G q) q :=
  card_bhReject (mul_nonneg hα (hG0 q)) q

/-- If the estimator is non-increasing in the p-values, so is the number of rejections of the
adaptive procedure. -/
lemma card_adaptiveBH_anti (hα : 0 ≤ α) (hG0 : ∀ q, 0 ≤ G q) (hGanti : Antitone G) :
    Antitone fun q : ι → ℝ => (adaptiveBH α G q).card := by
  intro q q' h
  simp only [card_adaptiveBH hα hG0]
  exact (bhK_mono_level (mul_le_mul_of_nonneg_left (hGanti h) hα) q').trans
    (bhK_anti _ h)

lemma measurable_card_adaptiveBH (hα : 0 ≤ α) (hG0 : ∀ q, 0 ≤ G q) (hGmeas : Measurable G) :
    Measurable fun q : ι → ℝ => (adaptiveBH α G q).card := by
  simp only [card_adaptiveBH hα hG0]
  exact measurable_bhK_comp (hGmeas.const_mul α) measurable_id

/-- Number of p-values above `lam`. -/
noncomputable def aboveCount (lam : ℝ) (q : ι → ℝ) : ℕ :=
  (univ.filter fun j => lam < q j).card

lemma aboveCount_mono (lam : ℝ) : Monotone (aboveCount lam : (ι → ℝ) → ℕ) := fun q q' h =>
  Finset.card_le_card fun j hj => by
    rw [mem_filter] at hj ⊢
    exact ⟨mem_univ _, hj.2.trans_le (h j)⟩

lemma measurable_aboveCount (lam : ℝ) : Measurable (aboveCount lam : (ι → ℝ) → ℕ) := by
  classical
  have : (aboveCount lam : (ι → ℝ) → ℕ) = fun q => ∑ j, if lam < q j then 1 else 0 := by
    funext q; rw [aboveCount, Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply j))
      measurable_const measurable_const

/-- Setting `q i` to `0` removes `i` from the count of p-values above `lam ≥ 0`, and nothing
else. -/
lemma aboveCount_update_add [DecidableEq ι] {lam : ℝ} (hlam : 0 ≤ lam) (q : ι → ℝ) (i : ι) :
    aboveCount lam (Function.update q i 0) + (if lam < q i then 1 else 0) = aboveCount lam q := by
  have heq : (univ.filter fun j => lam < Function.update q i 0 j)
      = (univ.filter fun j => lam < q j).erase i := by
    ext j
    by_cases hji : j = i
    · subst hji; simp [not_lt.mpr hlam]
    · simp [hji]
  unfold aboveCount
  rw [heq]
  by_cases hi : lam < q i
  · have hmem : i ∈ univ.filter fun j => lam < q j := by simpa using hi
    rw [ite_eq_left hi, Finset.card_erase_of_mem hmem]
    have := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  · have hmem : i ∉ univ.filter fun j => lam < q j := by simpa using hi
    rw [ite_eq_right hi, Finset.erase_eq_of_notMem hmem, add_zero]

lemma aboveCount_update_le [DecidableEq ι] {lam : ℝ} (hlam : 0 ≤ lam) (q : ι → ℝ) (i : ι) :
    aboveCount lam (Function.update q i 0) ≤ aboveCount lam q := by
  have := aboveCount_update_add hlam q i
  omega

/-- Leaving one hypothesis out, at most `m - 1` p-values exceed `lam ≥ 0`. -/
lemma aboveCount_update_add_one_le [DecidableEq ι] {lam : ℝ} (hlam : 0 ≤ lam) (q : ι → ℝ)
    (i : ι) : aboveCount lam (Function.update q i 0) + 1 ≤ Fintype.card ι := by
  have hsub : (univ.filter fun j => lam < Function.update q i 0 j) ⊆ univ.erase i := by
    intro j hj
    have hj' := (mem_filter.mp hj).2
    refine Finset.mem_erase.mpr ⟨fun hji => ?_, mem_univ _⟩
    subst hji
    simp at hj'
    linarith
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ] at h1
  have h2 : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  unfold aboveCount
  omega

/-- Storey's estimator of `m / m₀` with parameter `lam`, in the finite-sample form
`(1 - lam) m / (#{j : q j > lam} + 1)`; it is the reciprocal of
`π̂₀ = (#{j : q j > lam} + 1) / (m (1 - lam))`. -/
noncomputable def storeyG (lam : ℝ) (q : ι → ℝ) : ℝ :=
  (1 - lam) * Fintype.card ι / (aboveCount lam q + 1)

lemma storeyG_nonneg {lam : ℝ} (hlam : lam ≤ 1) (q : ι → ℝ) : 0 ≤ storeyG lam q := by
  have : 0 ≤ 1 - lam := by linarith
  unfold storeyG
  positivity

lemma storeyG_anti {lam : ℝ} (hlam : lam ≤ 1) : Antitone (storeyG lam : (ι → ℝ) → ℝ) := by
  intro q q' h
  have h1 : 0 ≤ 1 - lam := by linarith
  have h2 : (aboveCount lam q : ℝ) ≤ aboveCount lam q' := by exact_mod_cast aboveCount_mono lam h
  unfold storeyG
  gcongr

lemma measurable_storeyG (lam : ℝ) : Measurable (storeyG lam : (ι → ℝ) → ℝ) := by
  unfold storeyG
  exact measurable_const.div
    (((measurable_from_top (f := fun n : ℕ => (n : ℝ))).comp (measurable_aboveCount lam)).add_const
      1)

/-- The **Storey adaptive Benjamini–Hochberg procedure**: Benjamini–Hochberg at level
`α / π̂₀`, with `π̂₀ = (#{j : q j > lam} + 1) / (m (1 - lam))`. The rejection threshold is not
capped at `lam`. -/
noncomputable def storeyBH (α lam : ℝ) (q : ι → ℝ) : Finset ι :=
  adaptiveBH α (storeyG lam) q

/-- The **two-stage linear step-up procedure** with first-stage level `a`. Stage one is
Benjamini–Hochberg at level `a`, with `r₁` rejections. If `r₁ = m` everything is rejected;
otherwise stage two is Benjamini–Hochberg at level `a m / (m - r₁)`. -/
noncomputable def tstRejectAt (a : ℝ) (q : ι → ℝ) : Finset ι :=
  if bhK a q = Fintype.card ι then univ
  else bhReject (a * Fintype.card ι / (Fintype.card ι - bhK a q)) q

/-- The two-stage procedure of Benjamini, Krieger and Yekutieli (2006, Definition 6) at level
`α`: first-stage level `α / (1 + α)`. -/
noncomputable def tstReject (α : ℝ) (q : ι → ℝ) : Finset ι :=
  tstRejectAt (α / (1 + α)) q

/-- The second-stage level `a m / (m - r)`. -/
noncomputable def tstLevel (ι : Type*) [Fintype ι] (a : ℝ) (r : ℕ) : ℝ :=
  a * Fintype.card ι / (Fintype.card ι - r)

lemma tstLevel_ge {a : ℝ} (ha : 0 ≤ a) {r : ℕ} (hr : r < Fintype.card ι) :
    a ≤ tstLevel ι a r := by
  have h1 : (0 : ℝ) < Fintype.card ι - r := by
    have : (r : ℝ) < Fintype.card ι := by exact_mod_cast hr
    linarith
  unfold tstLevel
  rw [le_div_iff₀ h1]
  nlinarith [Nat.cast_nonneg (α := ℝ) r]

lemma tstLevel_mono {a : ℝ} (ha : 0 ≤ a) {r r' : ℕ} (h : r ≤ r') (hr : r' < Fintype.card ι) :
    tstLevel ι a r ≤ tstLevel ι a r' := by
  have h1 : (0 : ℝ) < Fintype.card ι - r' := by
    have : (r' : ℝ) < Fintype.card ι := by exact_mod_cast hr
    linarith
  have h2 : (r : ℝ) ≤ r' := by exact_mod_cast h
  unfold tstLevel
  gcongr

variable {a : ℝ}

/-- Number of rejections of the two-stage procedure. -/
lemma card_tstRejectAt (ha : 0 ≤ a) (q : ι → ℝ) :
    (tstRejectAt a q).card = if bhK a q = Fintype.card ι then Fintype.card ι
      else bhK (tstLevel ι a (bhK a q)) q := by
  unfold tstRejectAt
  split_ifs with h
  · exact Finset.card_univ
  · have hlt : bhK a q < Fintype.card ι := lt_of_le_of_ne (bhK_le q) h
    exact card_bhReject (ha.trans (tstLevel_ge ha hlt)) q

/-- The number of rejections of the two-stage procedure is non-increasing in the p-values. -/
lemma card_tstRejectAt_anti (ha : 0 ≤ a) : Antitone fun q : ι → ℝ => (tstRejectAt a q).card := by
  intro q q' h
  simp only [card_tstRejectAt ha]
  have hr : bhK a q' ≤ bhK a q := bhK_anti a h
  by_cases h' : bhK a q' = Fintype.card ι
  · have : bhK a q = Fintype.card ι := le_antisymm (bhK_le q) (h' ▸ hr)
    rw [ite_eq_left h', ite_eq_left this]
  · rw [ite_eq_right h']
    by_cases h'' : bhK a q = Fintype.card ι
    · rw [ite_eq_left h'']; exact bhK_le q'
    · rw [ite_eq_right h'']
      have hlt : bhK a q < Fintype.card ι := lt_of_le_of_ne (bhK_le q) h''
      exact (bhK_mono_level (tstLevel_mono ha hr hlt) q').trans (bhK_anti _ h)

lemma measurable_card_tstRejectAt (ha : 0 ≤ a) :
    Measurable fun q : ι → ℝ => (tstRejectAt a q).card := by
  simp only [card_tstRejectAt ha]
  refine Measurable.ite ?_ measurable_const ?_
  · exact (measurable_bhK (α := a)) (measurableSet_singleton _)
  · exact measurable_bhK_comp
      ((measurable_from_top (f := fun r : ℕ => tstLevel ι a r)).comp measurable_bhK) measurable_id

/-- The two-stage procedure rejects everything the first stage rejects. -/
lemma bhReject_subset_tstRejectAt (ha : 0 ≤ a) (q : ι → ℝ) :
    bhReject a q ⊆ tstRejectAt a q := by
  unfold tstRejectAt
  split_ifs with h
  · exact Finset.subset_univ _
  · have hlt : bhK a q < Fintype.card ι := lt_of_le_of_ne (bhK_le q) h
    have hle : a ≤ tstLevel ι a (bhK a q) := tstLevel_ge ha hlt
    intro j hj
    rw [bhReject, mem_filter] at hj ⊢
    refine ⟨mem_univ _, hj.2.trans ?_⟩
    have hK : (bhK a q : ℝ) ≤ bhK (tstLevel ι a (bhK a q)) q := by
      exact_mod_cast bhK_mono_level hle q
    have h0 : (0 : ℝ) ≤ tstLevel ι a (bhK a q) := ha.trans hle
    change a * (bhK a q : ℝ) / Fintype.card ι
      ≤ tstLevel ι a (bhK a q) * (bhK (tstLevel ι a (bhK a q)) q : ℝ) / Fintype.card ι
    gcongr

/-- If the first stage rejects nothing, the two-stage procedure rejects nothing ("if `r₁ = 0`
do not reject any hypothesis and stop"). -/
lemma tstRejectAt_eq_empty (ha : 0 ≤ a) (q : ι → ℝ) (h0 : bhK a q = 0) :
    tstRejectAt a q = ∅ := by
  rw [← Finset.card_eq_zero, card_tstRejectAt ha]
  split_ifs with h
  · exact h.symm.trans h0
  · have hm : (Fintype.card ι : ℝ) ≠ 0 := by
      have : Fintype.card ι ≠ 0 := fun h' => h (h0.trans h'.symm)
      exact_mod_cast this
    have hL : tstLevel ι a (bhK a q) = a := by
      unfold tstLevel
      rw [h0, Nat.cast_zero, sub_zero, mul_div_assoc, div_self hm, mul_one]
    rw [hL, h0]

/-- **Self-consistency of the two-stage procedure.** A rejected hypothesis `i` has
`q i ≤ a |R| / (Nᵢ + 1)`, where `Nᵢ` is the number of other p-values above `a`. -/
theorem le_of_mem_tstRejectAt [DecidableEq ι] (ha : 0 ≤ a) (q : ι → ℝ) {i : ι}
    (hi : i ∈ tstRejectAt a q) :
    q i ≤ a / (aboveCount a (Function.update q i 0) + 1) * (tstRejectAt a q).card := by
  set N := aboveCount a (Function.update q i 0) with hN
  set m := Fintype.card ι with hm
  have hNm : N + 1 ≤ m := aboveCount_update_add_one_le ha q i
  have hNm' : ((N : ℝ) + 1) ≤ m := by exact_mod_cast hNm
  have hmpos : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  -- a bound `q i ≤ a K / d` with `N + 1 ≤ d` and `K ≤ |R|` is enough
  have key : ∀ (K : ℕ) (d : ℝ), (N : ℝ) + 1 ≤ d → K ≤ (tstRejectAt a q).card →
      q i ≤ a * K / d → q i ≤ a / (N + 1) * (tstRejectAt a q).card := by
    intro K d hd hK hq
    have hK' : (K : ℝ) ≤ (tstRejectAt a q).card := by exact_mod_cast hK
    calc q i ≤ a * K / d := hq
      _ ≤ a * K / (N + 1) := by gcongr
      _ ≤ a * ((tstRejectAt a q).card : ℝ) / (N + 1) := by gcongr
      _ = a / (N + 1) * (tstRejectAt a q).card := by ring
  by_cases hfull : bhK a q = m
  · -- the first stage rejects everything
    have hcard : (tstRejectAt a q).card = m := by rw [card_tstRejectAt ha, ite_eq_left hfull]
    have hi1 : i ∈ bhReject a q := by
      have h1 : (bhReject a q).card = m := by rw [card_bhReject ha, hfull]
      have : bhReject a q = univ := Finset.eq_univ_of_card _ h1
      rw [this]; exact mem_univ _
    refine key m m hNm' hcard.ge ?_
    have := (mem_filter.mp hi1).2
    rwa [hfull] at this
  · have hlt : bhK a q < m := lt_of_le_of_ne (bhK_le q) hfull
    have hLge : a ≤ tstLevel ι a (bhK a q) := tstLevel_ge ha hlt
    have hcard : (tstRejectAt a q).card = bhK (tstLevel ι a (bhK a q)) q := by
      rw [card_tstRejectAt ha, ite_eq_right hfull]
    by_cases hi1 : i ∈ bhReject a q
    · -- rejected at the first stage
      refine key (bhK a q) m hNm' ?_ (mem_filter.mp hi1).2
      rw [hcard]; exact bhK_mono_level hLge q
    · -- not rejected at the first stage: at least `N + 1` hypotheses are not rejected there
      have hi2 : i ∈ bhReject (tstLevel ι a (bhK a q)) q := by
        have := hi
        unfold tstRejectAt at this
        rwa [ite_eq_right hfull] at this
      have hsub : insert i (univ.filter fun j => a < Function.update q i 0 j)
          ⊆ univ \ bhReject a q := by
        intro j hj
        rw [mem_sdiff]
        refine ⟨mem_univ _, ?_⟩
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hi1
        · have hj' := (mem_filter.mp hj).2
          have hji : j ≠ i := by
            rintro rfl
            simp at hj'
            linarith
          rw [Function.update_of_ne hji] at hj'
          intro hrej
          have h1 := (mem_filter.mp hrej).2
          have h2 : a * (bhK a q : ℝ) / m ≤ a := by
            rw [div_le_iff₀ hmpos]
            have : (bhK a q : ℝ) ≤ m := by exact_mod_cast bhK_le q
            nlinarith
          linarith
      have hnot : i ∉ univ.filter fun j => a < Function.update q i 0 j := by
        simp [not_lt.mpr ha]
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, card_bhReject ha] at hc
      have hd : (N : ℝ) + 1 ≤ (m : ℝ) - bhK a q := by
        have : N + 1 + bhK a q ≤ m := by
          have : N + 1 ≤ m - bhK a q := hc
          omega
        have : ((N : ℝ) + 1 + bhK a q) ≤ m := by exact_mod_cast this
        linarith
      refine key (bhK (tstLevel ι a (bhK a q)) q) ((m : ℝ) - bhK a q) hd hcard.ge ?_
      have h3 := (mem_filter.mp hi2).2
      have hd0 : (0 : ℝ) < (m : ℝ) - bhK a q := lt_of_lt_of_le hN1 hd
      calc q i ≤ tstLevel ι a (bhK a q) * (bhK (tstLevel ι a (bhK a q)) q : ℝ) / m := h3
        _ = a * (bhK (tstLevel ι a (bhK a q)) q : ℝ) / ((m : ℝ) - bhK a q) := by
            have hL : tstLevel ι a (bhK a q) = a * m / ((m : ℝ) - bhK a q) := rfl
            rw [hL]
            field_simp

end Deterministic

/-! ### False discovery rate -/

section Probabilistic

variable [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω] {α : ℝ}

/-- **False discovery rate of plug-in adaptive linear step-up procedures** (Benjamini, Krieger
and Yekutieli 2006; Blanchard and Roquain 2009, Theorem 3.3 of arXiv:0707.0536, for step-up
procedures). Let `G` be a measurable, non-negative, non-increasing estimator of `m / m₀`. If
every true-null p-value is non-negative, valid and independent of the other p-values, the
Benjamini–Hochberg procedure at level `α G(p)` has
`FDR ≤ (α / m) ∑_{i ∈ H₀} E[G(p₀,ᵢ)]`, where `p₀,ᵢ` is `p` with `pᵢ` replaced by `0`. -/
theorem fdr_adaptiveBH_le (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P)
    (hnonneg : ∀ i ∈ H₀, ∀ ω, 0 ≤ p i ω)
    (G : (ι → ℝ) → ℝ) (hG0 : ∀ q, 0 ≤ G q) (hGmeas : Measurable G) (hGanti : Antitone G) :
    fdr P H₀ (fun ω => adaptiveBH α G fun j => p j ω)
      ≤ ∑ i ∈ H₀, ∫⁻ ω, ENNReal.ofReal
          (α * G (Function.update (fun j => p j ω) i 0) / Fintype.card ι) ∂P := by
  refine fdr_le_of_selfConsistent P p hmeas H₀ hvalid hindep (adaptiveBH α G)
    (measurable_card_adaptiveBH hα hG0 hGmeas)
    (fun i _ q u u' h => card_adaptiveBH_anti hα hG0 hGanti ?_)
    (fun _ y => α * G y / Fintype.card ι) (fun _ _ y => ?_) (fun _ _ => ?_) ?_
  · intro j
    by_cases hji : j = i
    · subst hji; simpa using h
    · simp [Function.update_of_ne hji]
  · have := hG0 y
    positivity
  · exact (hGmeas.const_mul α).div_const _
  · intro i hi ω hmem
    have hq := (mem_filter.mp hmem).2
    rw [card_adaptiveBH hα hG0]
    have hle : Function.update (fun j => p j ω) i 0 ≤ fun j => p j ω := by
      intro j
      by_cases hji : j = i
      · subst hji; simpa using hnonneg j hi ω
      · simp [Function.update_of_ne hji]
    have hG := hGanti hle
    calc p i ω ≤ α * G (fun j => p j ω) * (bhK (α * G fun j => p j ω) fun j => p j ω)
          / Fintype.card ι := hq
      _ ≤ α * G (Function.update (fun j => p j ω) i 0)
          * (bhK (α * G fun j => p j ω) fun j => p j ω) / Fintype.card ι := by gcongr
      _ = _ := by ring

/-- **The property of Storey's estimator used for false discovery rate control.** Let `Nᵢ` be
the number of p-values other than `pᵢ` that exceed `lam ≥ 0`. If every true-null p-value is
independent of the others and `P(pᵢ ≤ lam) ≤ lam`, then
`∑_{i ∈ H₀} E[(1 - lam) / (Nᵢ + 1)] ≤ 1`. -/
theorem sum_lintegral_storey_le_one (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P)
    {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hvalid : ∀ i ∈ H₀, P {ω | p i ω ≤ lam} ≤ ENNReal.ofReal lam) :
    ∑ i ∈ H₀, ∫⁻ ω, ENNReal.ofReal
      ((1 - lam) / (aboveCount lam (Function.update (fun j => p j ω) i 0) + 1)) ∂P ≤ 1 := by
  classical
  set Y : ι → Ω → ι → ℝ := fun i ω => Function.update (fun j => p j ω) i 0 with hY
  have hYmeas : ∀ i, Measurable (Y i) := by
    intro i
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hji : j = i
    · subst hji; simp [hY]
    · simpa [hY, Function.update_of_ne hji] using hmeas j
  set φ : ℝ → ℝ≥0∞ := (Set.Ioi lam).indicator fun _ => 1 with hφ
  set ψ : (ι → ℝ) → ℝ≥0∞ := fun y => (((aboveCount lam y : ℕ) : ℝ≥0∞) + 1)⁻¹ with hψ
  have hφm : Measurable φ := measurable_const.indicator measurableSet_Ioi
  have hψm : Measurable ψ :=
    (((measurable_from_top (f := fun n : ℕ => (n : ℝ≥0∞))).comp
      (measurable_aboveCount lam)).add_const 1).inv
  -- the integrand, rewritten
  have hrew : ∀ i ω, ENNReal.ofReal ((1 - lam) / (aboveCount lam (Y i ω) + 1))
      = ENNReal.ofReal (1 - lam) * ψ (Y i ω) := by
    intro i ω
    have hpos : (0 : ℝ) < (aboveCount lam (Y i ω) : ℝ) + 1 := by positivity
    rw [ENNReal.ofReal_div_of_pos hpos, div_eq_mul_inv, hψ]
    congr 2
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  -- `1 - lam ≤ P (p i > lam)`
  have hP : ∀ i ∈ H₀, ENNReal.ofReal (1 - lam) ≤ ∫⁻ ω, φ (p i ω) ∂P := by
    intro i hi
    have hset : MeasurableSet {ω | p i ω ≤ lam} := hmeas i measurableSet_Iic
    have h1 : ∫⁻ ω, φ (p i ω) ∂P = P {ω | p i ω ≤ lam}ᶜ := by
      have : (fun ω => φ (p i ω)) = ({ω | p i ω ≤ lam}ᶜ).indicator fun _ => 1 := by
        funext ω
        by_cases h : lam < p i ω
        · have hm : ω ∈ ({ω | p i ω ≤ lam}ᶜ : Set Ω) := by simpa using h
          rw [Set.indicator_of_mem hm, hφ, Set.indicator_of_mem (show p i ω ∈ Set.Ioi lam from h)]
        · have hm : ω ∉ ({ω | p i ω ≤ lam}ᶜ : Set Ω) := by simpa using h
          rw [Set.indicator_of_notMem hm, hφ,
            Set.indicator_of_notMem (show p i ω ∉ Set.Ioi lam from h)]
      rw [this, lintegral_indicator_const hset.compl, one_mul]
    rw [h1, prob_compl_eq_one_sub hset, ENNReal.ofReal_sub _ hlam0, ENNReal.ofReal_one]
    exact tsub_le_tsub_left (hvalid i hi) _
  -- independence
  have hmul : ∀ i ∈ H₀, (∫⁻ ω, φ (p i ω) ∂P) * ∫⁻ ω, ψ (Y i ω) ∂P
      = ∫⁻ ω, φ (p i ω) * ψ (Y i ω) ∂P := by
    intro i hi
    exact (lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (hφm.comp (hmeas i)).aemeasurable
      (hψm.comp (hYmeas i)).aemeasurable ((hindep i hi).comp hφm hψm)).symm
  -- on `{p i > lam}`, `Nᵢ + 1` is the total number of p-values above `lam`
  have hpt : ∀ ω, ∑ i ∈ H₀, φ (p i ω) * ψ (Y i ω) ≤ 1 := by
    intro ω
    set A := aboveCount lam fun j => p j ω with hA
    have hterm : ∀ i ∈ H₀, φ (p i ω) * ψ (Y i ω)
        = if lam < p i ω then ((A : ℝ≥0∞))⁻¹ else 0 := by
      intro i _
      have hadd := aboveCount_update_add hlam0 (fun j => p j ω) i
      by_cases h : lam < p i ω
      · rw [ite_eq_left h] at hadd
        rw [ite_eq_left h, hφ, Set.indicator_of_mem (show p i ω ∈ Set.Ioi lam from h), one_mul, hψ]
        rw [hA, ← hadd]
        push_cast
        rfl
      · rw [ite_eq_right h, hφ, Set.indicator_of_notMem (show p i ω ∉ Set.Ioi lam from h), zero_mul]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hle : ((H₀.filter fun i => lam < p i ω).card : ℝ≥0∞) ≤ A := by
      have : (H₀.filter fun i => lam < p i ω).card ≤ A :=
        Finset.card_le_card fun j hj => by
          rw [mem_filter] at hj ⊢
          exact ⟨mem_univ _, hj.2⟩
      exact_mod_cast this
    calc ((H₀.filter fun i => lam < p i ω).card : ℝ≥0∞) * ((A : ℝ≥0∞))⁻¹
        ≤ (A : ℝ≥0∞) * ((A : ℝ≥0∞))⁻¹ := by gcongr
      _ ≤ 1 := ENNReal.mul_inv_le_one _
  calc ∑ i ∈ H₀, ∫⁻ ω, ENNReal.ofReal ((1 - lam) / (aboveCount lam (Y i ω) + 1)) ∂P
      = ∑ i ∈ H₀, ENNReal.ofReal (1 - lam) * ∫⁻ ω, ψ (Y i ω) ∂P := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp_rw [hrew]
        exact lintegral_const_mul _ (hψm.comp (hYmeas i))
    _ ≤ ∑ i ∈ H₀, (∫⁻ ω, φ (p i ω) ∂P) * ∫⁻ ω, ψ (Y i ω) ∂P :=
        Finset.sum_le_sum fun i hi => by gcongr; exact hP i hi
    _ = ∑ i ∈ H₀, ∫⁻ ω, φ (p i ω) * ψ (Y i ω) ∂P := Finset.sum_congr rfl hmul
    _ = ∫⁻ ω, ∑ i ∈ H₀, φ (p i ω) * ψ (Y i ω) ∂P :=
        (lintegral_finsetSum _ fun i _ =>
          (hφm.comp (hmeas i)).mul (hψm.comp (hYmeas i))).symm
    _ ≤ ∫⁻ _ω, 1 ∂P := lintegral_mono hpt
    _ = 1 := by simp

/-- Common last step: `∑_{i ∈ H₀} E[b (1 - lam) / (Nᵢ + 1)] ≤ b`. -/
private lemma sum_lintegral_scaled_le (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P)
    {lam b : ℝ} (hlam0 : 0 ≤ lam) (hb : 0 ≤ b) :
    ∑ i ∈ H₀, ∫⁻ ω, ENNReal.ofReal
      (b * ((1 - lam) / (aboveCount lam (Function.update (fun j => p j ω) i 0) + 1))) ∂P
      ≤ ENNReal.ofReal b := by
  have hYmeas : ∀ i, Measurable fun ω => Function.update (fun j => p j ω) i 0 := by
    intro i
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hji : j = i
    · subst hji; simp
    · simpa [Function.update_of_ne hji] using hmeas j
  have hm : ∀ i, Measurable fun ω => ENNReal.ofReal
      ((1 - lam) / (aboveCount lam (Function.update (fun j => p j ω) i 0) + 1)) := by
    intro i
    exact ENNReal.measurable_ofReal.comp (measurable_const.div
      ((((measurable_from_top (f := fun n : ℕ => (n : ℝ))).comp
        (measurable_aboveCount lam)).comp (hYmeas i)).add_const 1))
  calc _ = ∑ i ∈ H₀, ENNReal.ofReal b * ∫⁻ ω, ENNReal.ofReal
        ((1 - lam) / (aboveCount lam (Function.update (fun j => p j ω) i 0) + 1)) ∂P := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp_rw [ENNReal.ofReal_mul hb]
        exact lintegral_const_mul _ (hm i)
    _ = ENNReal.ofReal b * ∑ i ∈ H₀, ∫⁻ ω, ENNReal.ofReal
        ((1 - lam) / (aboveCount lam (Function.update (fun j => p j ω) i 0) + 1)) ∂P :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal b * 1 := by
        gcongr
        exact sum_lintegral_storey_le_one P p hmeas H₀ hindep hlam0
          fun i hi => hvalid i hi lam hlam0
    _ = ENNReal.ofReal b := mul_one _

/-- **Storey's adaptive Benjamini–Hochberg procedure controls the false discovery rate at
level `α` under independence** (Benjamini, Krieger and Yekutieli 2006; Blanchard and Roquain
2009, Corollary 3.4 of arXiv:0707.0536, estimator `G₁`). For `0 ≤ lam ≤ 1` and `α ≥ 0`, if
every true-null p-value is valid and independent of the other p-values, the Benjamini–Hochberg
procedure at level `α (1 - lam) m / (#{j : pⱼ > lam} + 1)` has false discovery rate at most
`α`. -/
theorem fdr_storeyBH_le (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P) :
    fdr P H₀ (fun ω => storeyBH α lam fun j => p j ω) ≤ ENNReal.ofReal α := by
  have hG0 : ∀ q : ι → ℝ, 0 ≤ storeyG lam q := storeyG_nonneg hlam1
  have h1 : (0 : ℝ) ≤ 1 - lam := by linarith
  refine (fdr_le_of_selfConsistent P p hmeas H₀ hvalid hindep (storeyBH α lam)
    (measurable_card_adaptiveBH hα hG0 (measurable_storeyG lam))
    (fun i _ q u u' h => card_adaptiveBH_anti hα hG0 (storeyG_anti hlam1) ?_)
    (fun _ y => α * ((1 - lam) / (aboveCount lam y + 1))) (fun _ _ y => by positivity)
    (fun _ _ => ?_) ?_).trans
    (sum_lintegral_scaled_le P p hmeas H₀ hvalid hindep hlam0 hα)
  · intro j
    by_cases hji : j = i
    · subst hji; simpa using h
    · simp [Function.update_of_ne hji]
  · exact measurable_const.mul (measurable_const.div
      (((measurable_from_top (f := fun n : ℕ => (n : ℝ))).comp
        (measurable_aboveCount lam)).add_const 1))
  · intro i hi ω hmem
    have hq := (mem_filter.mp hmem).2
    have hcard : (storeyBH α lam fun j => p j ω).card
        = bhK (α * storeyG lam fun j => p j ω) fun j => p j ω := card_adaptiveBH hα hG0 _
    rw [hcard]
    set K := bhK (α * storeyG lam fun j => p j ω) fun j => p j ω
    have hmpos : (0 : ℝ) < Fintype.card ι := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
    have hN : (aboveCount lam (Function.update (fun j => p j ω) i 0) : ℝ)
        ≤ aboveCount lam fun j => p j ω := by
      exact_mod_cast aboveCount_update_le hlam0 _ i
    calc p i ω ≤ α * storeyG lam (fun j => p j ω) * K / Fintype.card ι := hq
      _ = α * ((1 - lam) / (aboveCount lam (fun j => p j ω) + 1)) * K := by
          unfold storeyG
          field_simp
      _ ≤ α * ((1 - lam) / (aboveCount lam (Function.update (fun j => p j ω) i 0) + 1)) * K := by
          gcongr

/-- **The two-stage linear step-up procedure with first-stage level `a`** has false discovery
rate at most `a / (1 - a)` under independence, for `0 ≤ a < 1`. -/
theorem fdr_tstRejectAt_le (P : Measure Ω) [IsProbabilityMeasure P] {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a < 1)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P) :
    fdr P H₀ (fun ω => tstRejectAt a fun j => p j ω) ≤ ENNReal.ofReal (a / (1 - a)) := by
  have h1 : (0 : ℝ) < 1 - a := by linarith
  have hb : (0 : ℝ) ≤ a / (1 - a) := by positivity
  have hc0 : ∀ y : ι → ℝ, 0 ≤ a / (1 - a) * ((1 - a) / ((aboveCount a y : ℝ) + 1)) := by
    intro y
    positivity
  refine (fdr_le_of_selfConsistent P p hmeas H₀ hvalid hindep (tstRejectAt a)
    (measurable_card_tstRejectAt ha0)
    (fun i _ q u u' h => card_tstRejectAt_anti ha0 ?_)
    (fun _ y => a / (1 - a) * ((1 - a) / (aboveCount a y + 1))) (fun _ _ y => hc0 y)
    (fun _ _ => ?_) ?_).trans
    (sum_lintegral_scaled_le P p hmeas H₀ hvalid hindep (lam := a) (b := a / (1 - a)) ha0 hb)
  · intro j
    by_cases hji : j = i
    · subst hji; simpa using h
    · simp [Function.update_of_ne hji]
  · exact measurable_const.mul (measurable_const.div
      (((measurable_from_top (f := fun n : ℕ => (n : ℝ))).comp
        (measurable_aboveCount a)).add_const 1))
  · intro i _ ω hmem
    have h := le_of_mem_tstRejectAt ha0 (fun j => p j ω) hmem
    have heq : a / (1 - a) * ((1 - a) /
        ((aboveCount a (Function.update (fun j => p j ω) i 0) : ℝ) + 1))
        = a / ((aboveCount a (Function.update (fun j => p j ω) i 0) : ℝ) + 1) := by
      field_simp
    rw [heq]
    exact h

/-- **The two-stage procedure of Benjamini, Krieger and Yekutieli controls the false discovery
rate at level `α` under independence** (Benjamini, Krieger and Yekutieli 2006, Theorem 1). For
`α ≥ 0`, if every true-null p-value is valid and independent of the other p-values, the
two-stage procedure (first stage: Benjamini–Hochberg at level `α' = α / (1 + α)` with `r₁`
rejections; second stage: Benjamini–Hochberg at level `α' m / (m - r₁)`) has false discovery
rate at most `α`. -/
theorem fdr_tstReject_le (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P) :
    fdr P H₀ (fun ω => tstReject α fun j => p j ω) ≤ ENNReal.ofReal α := by
  have h1 : (0 : ℝ) < 1 + α := by linarith
  have ha0 : 0 ≤ α / (1 + α) := by positivity
  have ha1 : α / (1 + α) < 1 := by rw [div_lt_one h1]; linarith
  have heq : α / (1 + α) / (1 - α / (1 + α)) = α := by
    field_simp
    ring
  have := fdr_tstRejectAt_le P ha0 ha1 p hmeas H₀ hvalid hindep
  rwa [heq] at this

/-- Textbook form of `fdr_storeyBH_le` for mutually independent p-values. -/
theorem fdr_storeyBH_le_of_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    fdr P H₀ (fun ω => storeyBH α lam fun j => p j ω) ≤ ENNReal.ofReal α :=
  fdr_storeyBH_le P hα hlam0 hlam1 p hmeas H₀ hvalid fun i _ =>
    indepFun_update_of_iIndepFun P p hmeas hindep i

/-- Textbook form of `fdr_tstReject_le` for mutually independent p-values. -/
theorem fdr_tstReject_le_of_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    fdr P H₀ (fun ω => tstReject α fun j => p j ω) ≤ ENNReal.ofReal α :=
  fdr_tstReject_le P hα p hmeas H₀ hvalid fun i _ =>
    indepFun_update_of_iIndepFun P p hmeas hindep i

end Probabilistic

end Applied.MultipleTesting
