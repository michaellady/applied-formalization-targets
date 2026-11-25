import Applied.Economics.Welfare
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Second fundamental theorem of welfare economics (exchange economy)

Agents `i : ι` (finitely many) have utilities `u i : E → ℝ` over bundles in a real inner
product space `E`. An allocation is a family `x : ι → E`; a reallocation `y` uses the same
total resources when `∑ i, y i = ∑ i, x i`. There is no production.

## Consumption sets equal to the whole space (`E` a Hilbert space)

* `WeaklyParetoEfficient u x`: no reallocation makes every agent strictly better off.
* `ParetoEfficient u x`: no reallocation makes every agent at least as well off and some agent
  strictly better off.
* `exists_price_quasiEquilibrium`: if every `u i` is continuous, quasi-concave and locally
  non-satiated, a weakly Pareto-efficient allocation `x` is a price quasi-equilibrium: there is
  `p ≠ 0` such that every bundle strictly preferred to `x i` costs at least as much as `x i`.
* `second_welfare_theorem`: under the same hypotheses `x i` maximises `u i` over the budget set
  `{y | ⟪p, y⟫ ≤ ⟪p, x i⟫}`, i.e. `(p, x)` is a competitive equilibrium after wealth is
  redistributed so that agent `i` owns wealth `⟪p, x i⟫`.
* `paretoEfficient_iff_exists_supporting_price`: with the first welfare theorem, an allocation
  is Pareto efficient iff it is supported by some non-zero price in this sense.

Because consumption sets are all of `E`, a cheaper bundle than `x i` always exists once
`p ≠ 0` (namely `x i - p`), so no interiority assumption is needed in this setting.

## General consumption sets (`E` finite-dimensional)

Agent `i` may only consume bundles in `X i ⊆ E` (for instance the non-negative orthant).

* `exists_price_quasiEquilibrium_on`: if preferences are quasi-concave and locally non-satiated
  on `X i` (no continuity is needed), an allocation `x` with `x i ∈ X i` that is weakly Pareto
  efficient among allocations in the consumption sets is a price quasi-equilibrium.
* `utility_le_of_cheaper_point_on`: the cheaper-point lemma turning the quasi-equilibrium
  condition of one agent into utility maximisation over the budget set.
* `second_welfare_theorem_on`: if moreover the `X i` are convex, the `u i` are continuous on
  `X i` and every `x i` is interior to `X i`, then every `x i` maximises `u i` over the budget
  set `{y ∈ X i | ⟪p, y⟫ ≤ ⟪p, x i⟫}`.

The separation step is `exists_inner_le_of_convex_of_notMem`: in finite dimension a point
outside a non-empty convex set (not necessarily open or closed) can be weakly separated from
it by a non-zero linear functional.
-/

open scoped RealInnerProductSpace
open Finset Filter Topology

namespace Applied.Economics

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Definitions -/

/-- No allocation in the consumption sets `X` with the same total resources makes every agent
strictly better off. -/
def WeaklyParetoEfficientOn (X : ι → Set E) (u : ι → E → ℝ) (x : ι → E) : Prop :=
  ¬ ∃ y : ι → E, (∀ i, y i ∈ X i) ∧ ∑ i, y i = ∑ i, x i ∧ ∀ i, u i (x i) < u i (y i)

/-- No reallocation of the same total resources makes every agent strictly better off
(consumption sets equal to the whole space). -/
def WeaklyParetoEfficient (u : ι → E → ℝ) (x : ι → E) : Prop :=
  ¬ ∃ y : ι → E, ∑ i, y i = ∑ i, x i ∧ ∀ i, u i (x i) < u i (y i)

/-- No reallocation of the same total resources makes every agent at least as well off and some
agent strictly better off (consumption sets equal to the whole space). -/
def ParetoEfficient (u : ι → E → ℝ) (x : ι → E) : Prop :=
  ¬ ∃ y : ι → E, ∑ i, y i = ∑ i, x i ∧ (∀ i, u i (x i) ≤ u i (y i)) ∧ ∃ j, u j (x j) < u j (y j)

/-- Preferences are locally non-satiated on the consumption set `X`: arbitrarily close to any
bundle of `X` there is a strictly better bundle of `X`. -/
def LocallyNonSatiatedOn (X : Set E) (u : E → ℝ) : Prop :=
  ∀ y ∈ X, ∀ ε > 0, ∃ y' ∈ X, ‖y' - y‖ < ε ∧ u y < u y'

omit [Fintype ι] [InnerProductSpace ℝ E] in
/-- Local non-satiation on the whole space is local non-satiation. -/
lemma locallyNonSatiatedOn_univ {u : E → ℝ} :
    LocallyNonSatiatedOn Set.univ u ↔ LocallyNonSatiated u := by
  simp [LocallyNonSatiatedOn, LocallyNonSatiated]

omit [InnerProductSpace ℝ E] in
/-- Weak Pareto efficiency with all consumption sets equal to the whole space is weak Pareto
efficiency. -/
lemma weaklyParetoEfficientOn_univ {u : ι → E → ℝ} {x : ι → E} :
    WeaklyParetoEfficientOn (fun _ => Set.univ) u x ↔ WeaklyParetoEfficient u x := by
  simp [WeaklyParetoEfficientOn, WeaklyParetoEfficient]

omit [InnerProductSpace ℝ E] in
/-- With at least one agent, Pareto efficiency implies weak Pareto efficiency. -/
lemma ParetoEfficient.weakly [Nonempty ι] {u : ι → E → ℝ} {x : ι → E}
    (h : ParetoEfficient u x) : WeaklyParetoEfficient u x := by
  rintro ⟨y, hy, hlt⟩
  exact h ⟨y, hy, fun i => (hlt i).le, ⟨Classical.arbitrary ι, hlt _⟩⟩

/-! ### From quasi-equilibrium to equilibrium -/

/-- **Cheaper-point lemma.** Let `X` be a convex consumption set and `u` continuous on `X`.
Suppose every bundle of `X` strictly preferred to `x` costs at least as much as `x` at prices
`p`, and some bundle `z ∈ X` is strictly cheaper than `x`. Then `x` is at least as good as
every bundle of `X` in the budget set `{y | ⟪p, y⟫ ≤ ⟪p, x⟫}`. -/
lemma utility_le_of_cheaper_point_on {X : Set E} (hX : Convex ℝ X) {u : E → ℝ}
    (hu : ContinuousOn u X) {p x z : E}
    (hquasi : ∀ y ∈ X, u x < u y → ⟪p, x⟫ ≤ ⟪p, y⟫) (hzX : z ∈ X) (hz : ⟪p, z⟫ < ⟪p, x⟫)
    {y : E} (hyX : y ∈ X) (hy : ⟪p, y⟫ ≤ ⟪p, x⟫) : u y ≤ u x := by
  by_contra hlt
  rw [not_le] at hlt
  -- move from `y` a little towards the cheaper point `z`
  set g : ℕ → E := fun n => y + (1 / ((n : ℝ) + 1)) • (z - y) with hg
  have hgX : ∀ n, g n ∈ X := fun n =>
    hX.add_smul_sub_mem hyX hzX ⟨by positivity, by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
  have hgt : Tendsto g atTop (𝓝 y) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := (h0.smul_const (z - y)).const_add y
    simpa [hg] using this
  have hgt' : Tendsto g atTop (𝓝[X] y) :=
    tendsto_nhdsWithin_iff.mpr ⟨hgt, Eventually.of_forall hgX⟩
  have hut : Tendsto (fun n => u (g n)) atTop (𝓝 (u y)) := (hu y hyX).tendsto.comp hgt'
  obtain ⟨n, hn⟩ := (hut.eventually (lt_mem_nhds hlt)).exists
  have hcost := hquasi _ (hgX n) hn
  rw [hg] at hcost
  simp only [inner_add_right, inner_smul_right, inner_sub_right] at hcost
  have ht0 : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have ht1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  nlinarith [mul_pos ht0 (sub_pos.mpr hz), mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hy)]

/-- Cheaper-point lemma when the consumption set is the whole space. -/
lemma utility_le_of_cheaper_point {u : E → ℝ} (hu : Continuous u) {p x z : E}
    (hquasi : ∀ y, u x < u y → ⟪p, x⟫ ≤ ⟪p, y⟫) (hz : ⟪p, z⟫ < ⟪p, x⟫)
    {y : E} (hy : ⟪p, y⟫ ≤ ⟪p, x⟫) : u y ≤ u x :=
  utility_le_of_cheaper_point_on convex_univ hu.continuousOn (fun y _ => hquasi y)
    (Set.mem_univ z) hz (Set.mem_univ y) hy

/-! ### The limiting step shared by both versions -/

/-- If a continuous linear functional `f` does not exceed its value at the aggregate `∑ x` on
any aggregate of bundles `z j ∈ X j` strictly preferred to `x j`, and every agent is locally
non-satiated at `x j` within `X j`, then `f y ≤ f (x i)` for every single bundle `y ∈ X i`
strictly preferred to `x i`. -/
lemma le_of_aggregate_le (f : E →L[ℝ] ℝ) (X : ι → Set E) (u : ι → E → ℝ) (x : ι → E)
    (hnear : ∀ j, ∀ ε > 0, ∃ y' ∈ X j, ‖y' - x j‖ < ε ∧ u j (x j) < u j y')
    (hsep : ∀ z : ι → E, (∀ j, z j ∈ X j) → (∀ j, u j (x j) < u j (z j)) →
      f (∑ j, z j) ≤ f (∑ j, x j))
    (i : ι) (y : E) (hyX : y ∈ X i) (hy : u i (x i) < u i y) : f y ≤ f (x i) := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  set δ := f y - f (x i) with hδ
  have hδpos : 0 < δ := by linarith
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hnpos : 0 < n := by
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [hn]; exact_mod_cast this
  have hεpos : 0 < δ / (2 * n * (‖f‖ + 1)) := div_pos hδpos (by positivity)
  choose z hzX hz1 hz2 using fun j => hnear j _ hεpos
  have hlt' := hsep (Function.update z i y)
    (fun j => by
      by_cases h : j = i
      · subst h; simpa using hyX
      · simpa [Function.update_of_ne h] using hzX j)
    (fun j => by
      by_cases h : j = i
      · subst h; simpa using hy
      · simpa [Function.update_of_ne h] using hz2 j)
  rw [map_sum, map_sum] at hlt'
  -- termwise lower bound
  have hterm : ∀ j,
      f (x j) + (if j = i then δ else 0) - δ / (2 * n) ≤ f (Function.update z i y j) := by
    intro j
    have hsmall : ‖f‖ * (δ / (2 * n * (‖f‖ + 1))) ≤ δ / (2 * n) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [norm_nonneg f, mul_pos hδpos hnpos]
    by_cases h : j = i
    · subst h
      have : 0 ≤ δ / (2 * n) := by positivity
      simp only [Function.update_self, ite_true]
      linarith
    · simp only [Function.update_of_ne h, h, ite_false]
      have h1 : f (x j) - f (z j) = f (x j - z j) := by rw [map_sub]
      have h2 : f (x j - z j) ≤ ‖f‖ * ‖x j - z j‖ :=
        (le_abs_self _).trans (by simpa using f.le_opNorm (x j - z j))
      have h3 : ‖x j - z j‖ ≤ δ / (2 * n * (‖f‖ + 1)) := by
        rw [norm_sub_rev]; exact (hz1 j).le
      have h4 := mul_le_mul_of_nonneg_left h3 (norm_nonneg f)
      linarith
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ univ) => hterm j
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' univ i,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcancel : (Fintype.card ι : ℝ) * (δ / (2 * n)) = δ / 2 := by
    rw [← hn]; field_simp
  rw [hcancel] at hsum
  simp only [mem_univ, ite_true] at hsum
  linarith

/-! ### Consumption sets equal to the whole space -/

section WholeSpace

variable [CompleteSpace E]

/-- **Second welfare theorem, quasi-equilibrium form.** In an exchange economy with finitely
many agents whose utilities on the whole commodity space are continuous, quasi-concave and
locally non-satiated, every weakly Pareto-efficient allocation `x` is supported by a non-zero
price vector `p`: any bundle that agent `i` strictly prefers to `x i` costs at least as much
as `x i`. -/
theorem exists_price_quasiEquilibrium (u : ι → E → ℝ) (x : ι → E)
    (hcont : ∀ i, Continuous (u i))
    (hqc : ∀ i, QuasiconcaveOn ℝ Set.univ (u i))
    (hlns : ∀ i, LocallyNonSatiated (u i))
    (heff : WeaklyParetoEfficient u x) :
    ∃ p : E, p ≠ 0 ∧ ∀ i y, u i (x i) < u i y → ⟪p, x i⟫ ≤ ⟪p, y⟫ := by
  classical
  -- there is at least one agent, otherwise the empty reallocation contradicts efficiency
  have hne : Nonempty ι := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    exact heff ⟨x, rfl, fun i => (hemp.false i).elim⟩
  obtain ⟨i₀⟩ := hne
  -- the set of aggregate bundles that can be split so that everybody is strictly better off
  set P : Set E := {a | ∃ y : ι → E, (∀ i, u i (x i) < u i (y i)) ∧ ∑ i, y i = a} with hP
  have hPconv : Convex ℝ P := by
    rintro a ⟨y, hy, rfl⟩ b ⟨z, hz, rfl⟩ s t hs ht hst
    refine ⟨fun i => s • y i + t • z i, fun i => ?_, ?_⟩
    · have hc := (hqc i).convex_gt (u i (x i))
      have := hc (x := y i) ⟨Set.mem_univ _, hy i⟩ (y := z i) ⟨Set.mem_univ _, hz i⟩ hs ht hst
      exact this.2
    · rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
  have hPopen : IsOpen P := by
    rw [isOpen_iff_forall_mem_open]
    rintro a ⟨y, hy, rfl⟩
    refine ⟨{a' | u i₀ (x i₀) < u i₀ (y i₀ + (a' - ∑ i, y i))}, ?_, ?_, ?_⟩
    · intro a' ha'
      refine ⟨Function.update y i₀ (y i₀ + (a' - ∑ i, y i)), fun i => ?_, ?_⟩
      · by_cases h : i = i₀
        · subst h; simpa using ha'
        · simpa [Function.update_of_ne h] using hy i
      · rw [Finset.sum_update_of_mem (mem_univ i₀)]
        have := Finset.add_sum_erase univ y (mem_univ i₀)
        rw [Finset.sdiff_singleton_eq_erase]
        rw [← this]
        abel
    · exact isOpen_lt continuous_const ((hcont i₀).comp (by fun_prop))
    · simpa using hy i₀
  have hxP : (∑ i, x i) ∉ P := by
    rintro ⟨y, hy, hsum⟩
    exact heff ⟨y, hsum, hy⟩
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hPconv hPopen hxP
  have hnear : ∀ j, ∀ ε > 0, ∃ y' ∈ (Set.univ : Set E), ‖y' - x j‖ < ε ∧ u j (x j) < u j y' :=
    fun j ε hε => by simpa using hlns j (x j) ε hε
  have hkey : ∀ i y, u i (x i) < u i y → f y ≤ f (x i) := fun i y hy =>
    le_of_aggregate_le f (fun _ => Set.univ) u x hnear
      (fun z _ hz => (hf _ ⟨z, hz, rfl⟩).le) i y (Set.mem_univ y) hy
  have hf0 : f ≠ 0 := by
    rintro rfl
    choose z _ _ hz2 using fun j => hnear j 1 one_pos
    have := hf (∑ i, z i) ⟨z, hz2, rfl⟩
    simp at this
  refine ⟨-(InnerProductSpace.toDual ℝ E).symm f, ?_, fun i y hy => ?_⟩
  · simpa using hf0
  · rw [inner_neg_left, inner_neg_left, InnerProductSpace.toDual_symm_apply,
      InnerProductSpace.toDual_symm_apply]
    linarith [hkey i y hy]

/-- **Second welfare theorem** (exchange economy, consumption sets equal to the whole space).
If utilities are continuous, quasi-concave and locally non-satiated, then for every weakly
Pareto-efficient allocation `x` there is a non-zero price vector `p` such that every agent's
bundle `x i` maximises `u i` over the budget set `{y | ⟪p, y⟫ ≤ ⟪p, x i⟫}`. So `(p, x)` is a
competitive equilibrium for any redistribution of endowments `ω'` with `∑ i, ω' i = ∑ i, x i`
and `⟪p, ω' i⟫ = ⟪p, x i⟫` (for instance `ω' = x`). -/
theorem second_welfare_theorem (u : ι → E → ℝ) (x : ι → E)
    (hcont : ∀ i, Continuous (u i))
    (hqc : ∀ i, QuasiconcaveOn ℝ Set.univ (u i))
    (hlns : ∀ i, LocallyNonSatiated (u i))
    (heff : WeaklyParetoEfficient u x) :
    ∃ p : E, p ≠ 0 ∧ ∀ i y, ⟪p, y⟫ ≤ ⟪p, x i⟫ → u i y ≤ u i (x i) := by
  obtain ⟨p, hp, hquasi⟩ := exists_price_quasiEquilibrium u x hcont hqc hlns heff
  refine ⟨p, hp, fun i y hy => ?_⟩
  refine utility_le_of_cheaper_point (hcont i) (hquasi i) (z := x i - p) ?_ hy
  rw [inner_sub_right]
  have : 0 < ⟪p, p⟫ := real_inner_self_pos.mpr hp
  linarith

/-- Second welfare theorem stated with explicit redistributed endowments: if the efficient
allocation `x` is feasible for endowments `ω`, there are prices `p ≠ 0` and redistributed
endowments `ω'` with the same total as `ω` such that `x` is a competitive equilibrium
allocation for `ω'` at prices `p`: each `x i` is affordable, markets clear, and each `x i`
maximises `u i` over the budget set of wealth `⟪p, ω' i⟫`. (The proof takes `ω' = x`.) -/
theorem second_welfare_theorem_transfers (u : ι → E → ℝ) (ω x : ι → E)
    (hfeas : ∑ i, x i = ∑ i, ω i)
    (hcont : ∀ i, Continuous (u i))
    (hqc : ∀ i, QuasiconcaveOn ℝ Set.univ (u i))
    (hlns : ∀ i, LocallyNonSatiated (u i))
    (heff : WeaklyParetoEfficient u x) :
    ∃ (p : E) (ω' : ι → E), p ≠ 0 ∧ ∑ i, ω' i = ∑ i, ω i ∧
      (∀ i, ⟪p, x i⟫ ≤ ⟪p, ω' i⟫) ∧ ∑ i, x i = ∑ i, ω' i ∧
      ∀ i y, ⟪p, y⟫ ≤ ⟪p, ω' i⟫ → u i y ≤ u i (x i) := by
  obtain ⟨p, hp, h⟩ := second_welfare_theorem u x hcont hqc hlns heff
  exact ⟨p, x, hp, hfeas, fun _ => le_rfl, rfl, h⟩

/-- **Characterisation of Pareto efficiency by supporting prices.** With at least one agent and
continuous, quasi-concave, locally non-satiated utilities on the whole space, an allocation is
Pareto efficient if and only if some non-zero price vector makes every agent's bundle
utility-maximising over the budget set through that bundle. The "if" direction is the first
welfare theorem, the "only if" direction the second. -/
theorem paretoEfficient_iff_exists_supporting_price [Nonempty ι] (u : ι → E → ℝ) (x : ι → E)
    (hcont : ∀ i, Continuous (u i))
    (hqc : ∀ i, QuasiconcaveOn ℝ Set.univ (u i))
    (hlns : ∀ i, LocallyNonSatiated (u i)) :
    ParetoEfficient u x ↔
      ∃ p : E, p ≠ 0 ∧ ∀ i y, ⟪p, y⟫ ≤ ⟪p, x i⟫ → u i y ≤ u i (x i) := by
  constructor
  · exact fun h => second_welfare_theorem u x hcont hqc hlns h.weakly
  · rintro ⟨p, -, hopt⟩ ⟨y, hfeas, hweak, hj⟩
    exact competitive_equilibrium_pareto_efficient u x x p hlns hopt y hfeas hweak hj

/-- Under the hypotheses of the second welfare theorem (whole-space consumption sets, at least
one agent), weak and strong Pareto efficiency coincide. -/
theorem weaklyParetoEfficient_iff_paretoEfficient [Nonempty ι] (u : ι → E → ℝ) (x : ι → E)
    (hcont : ∀ i, Continuous (u i))
    (hqc : ∀ i, QuasiconcaveOn ℝ Set.univ (u i))
    (hlns : ∀ i, LocallyNonSatiated (u i)) :
    WeaklyParetoEfficient u x ↔ ParetoEfficient u x :=
  ⟨fun h => (paretoEfficient_iff_exists_supporting_price u x hcont hqc hlns).mpr
    (second_welfare_theorem u x hcont hqc hlns h), fun h => h.weakly⟩

end WholeSpace

/-! ### General consumption sets, finite-dimensional commodity space -/

section ConsumptionSets

variable [FiniteDimensional ℝ E]

omit [Fintype ι] in
/-- **Weak separation of a point from a convex set in finite dimension.** If `C` is a non-empty
convex subset of a finite-dimensional real inner product space and `a ∉ C`, there is a non-zero
vector `w` with `⟪w, c⟫ ≤ ⟪w, a⟫` for all `c ∈ C`. No openness or closedness of `C` is
required. -/
theorem exists_inner_le_of_convex_of_notMem {C : Set E} (hC : Convex ℝ C) (hne : C.Nonempty)
    {a : E} (ha : a ∉ C) : ∃ w : E, w ≠ 0 ∧ ∀ c ∈ C, ⟪w, c⟫ ≤ ⟪w, a⟫ := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  by_cases hint : (interior C).Nonempty
  · obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hC.interior isOpen_interior
      (fun h => ha (interior_subset h))
    have hcl : ∀ c ∈ C, f c ≤ f a := by
      intro c hc
      have hmem : c ∈ closure (interior C) := by
        rw [hC.closure_interior_eq_closure_of_nonempty_interior hint]
        exact subset_closure hc
      exact closure_minimal (s := interior C) (t := {c | f c ≤ f a})
        (fun c hc => (hf c hc).le) (isClosed_le f.continuous continuous_const) hmem
    have hf0 : f ≠ 0 := by
      rintro rfl
      obtain ⟨c₀, hc₀⟩ := hint
      simpa using hf c₀ hc₀
    refine ⟨(InnerProductSpace.toDual ℝ E).symm f, by simpa using hf0, fun c hc => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply]
    exact hcl c hc
  · have hspan : affineSpan ℝ C ≠ ⊤ := fun h =>
      hint (hC.interior_nonempty_iff_affineSpan_eq_top.mpr h)
    obtain ⟨c₀, hc₀⟩ := hne
    have hc₀' : c₀ ∈ affineSpan ℝ C := subset_affineSpan ℝ C hc₀
    have hdir : (affineSpan ℝ C).direction ≠ ⊤ := fun h =>
      hspan ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨c₀, hc₀'⟩).mp h)
    have hperp : (affineSpan ℝ C).directionᗮ ≠ ⊥ := by
      rwa [Ne, Submodule.orthogonal_eq_bot_iff]
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
    have hconst : ∀ c ∈ C, ⟪w, c⟫ = ⟪w, c₀⟫ := by
      intro c hc
      have hmem : c - c₀ ∈ (affineSpan ℝ C).direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hc) hc₀'
      have := (Submodule.mem_orthogonal' _ _).mp hw _ hmem
      rw [inner_sub_right] at this
      linarith
    by_cases hle : ⟪w, c₀⟫ ≤ ⟪w, a⟫
    · exact ⟨w, hw0, fun c hc => (hconst c hc).le.trans hle⟩
    · refine ⟨-w, neg_ne_zero.mpr hw0, fun c hc => ?_⟩
      rw [inner_neg_left, inner_neg_left, hconst c hc]
      linarith

/-- **Second welfare theorem, quasi-equilibrium form, with consumption sets.** Let the
commodity space be finite-dimensional and let agent `i` have consumption set `X i`. Suppose
each `u i` is quasi-concave on `X i` and locally non-satiated on `X i`. If `x` is an allocation
with `x i ∈ X i` that is weakly Pareto efficient among allocations in the consumption sets,
there is a non-zero price vector `p` such that every bundle of `X i` that agent `i` strictly
prefers to `x i` costs at least as much as `x i`. No continuity is assumed. -/
theorem exists_price_quasiEquilibrium_on (X : ι → Set E) (u : ι → E → ℝ) (x : ι → E)
    (hx : ∀ i, x i ∈ X i)
    (hqc : ∀ i, QuasiconcaveOn ℝ (X i) (u i))
    (hlns : ∀ i, LocallyNonSatiatedOn (X i) (u i))
    (heff : WeaklyParetoEfficientOn X u x) :
    ∃ p : E, p ≠ 0 ∧ ∀ i, ∀ y ∈ X i, u i (x i) < u i y → ⟪p, x i⟫ ≤ ⟪p, y⟫ := by
  classical
  set P : Set E :=
    {a | ∃ y : ι → E, (∀ i, y i ∈ X i ∧ u i (x i) < u i (y i)) ∧ ∑ i, y i = a} with hP
  have hPconv : Convex ℝ P := by
    rintro a ⟨y, hy, rfl⟩ b ⟨z, hz, rfl⟩ s t hs ht hst
    refine ⟨fun i => s • y i + t • z i, fun i => ?_, ?_⟩
    · exact (hqc i).convex_gt (u i (x i)) (hy i) (hz i) hs ht hst
    · rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
  have hnear : ∀ j, ∀ ε > 0, ∃ y' ∈ X j, ‖y' - x j‖ < ε ∧ u j (x j) < u j y' :=
    fun j ε hε => hlns j (x j) (hx j) ε hε
  have hPne : P.Nonempty := by
    choose z hzX _ hz2 using fun j => hnear j 1 one_pos
    exact ⟨_, z, fun i => ⟨hzX i, hz2 i⟩, rfl⟩
  have hxP : (∑ i, x i) ∉ P := by
    rintro ⟨y, hy, hsum⟩
    exact heff ⟨y, fun i => (hy i).1, hsum, fun i => (hy i).2⟩
  obtain ⟨w, hw0, hw⟩ := exists_inner_le_of_convex_of_notMem hPconv hPne hxP
  refine ⟨-w, neg_ne_zero.mpr hw0, fun i y hyX hy => ?_⟩
  have := le_of_aggregate_le (innerSL ℝ w) X u x hnear
    (fun z hzX hz => by
      simpa [inner_sum] using hw _ ⟨z, fun i => ⟨hzX i, hz i⟩, rfl⟩) i y hyX hy
  rw [inner_neg_left, inner_neg_left]
  simpa using this

/-- **Second welfare theorem with consumption sets, interior allocation.** Let the commodity
space be finite-dimensional and let agent `i` have a convex consumption set `X i` on which
`u i` is continuous, quasi-concave and locally non-satiated. If `x` is weakly Pareto efficient
among allocations in the consumption sets and every `x i` lies in the interior of `X i`, there
is a non-zero price vector `p` such that every `x i` maximises `u i` over the budget set
`{y ∈ X i | ⟪p, y⟫ ≤ ⟪p, x i⟫}`. -/
theorem second_welfare_theorem_on (X : ι → Set E) (u : ι → E → ℝ) (x : ι → E)
    (hX : ∀ i, Convex ℝ (X i))
    (hxint : ∀ i, x i ∈ interior (X i))
    (hcont : ∀ i, ContinuousOn (u i) (X i))
    (hqc : ∀ i, QuasiconcaveOn ℝ (X i) (u i))
    (hlns : ∀ i, LocallyNonSatiatedOn (X i) (u i))
    (heff : WeaklyParetoEfficientOn X u x) :
    ∃ p : E, p ≠ 0 ∧ ∀ i, ∀ y ∈ X i, ⟪p, y⟫ ≤ ⟪p, x i⟫ → u i y ≤ u i (x i) := by
  obtain ⟨p, hp, hquasi⟩ := exists_price_quasiEquilibrium_on X u x
    (fun i => interior_subset (hxint i)) hqc hlns heff
  refine ⟨p, hp, fun i y hyX hy => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (x i) (hxint i)
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  set t : ℝ := ε / (2 * ‖p‖) with ht
  have htpos : 0 < t := by positivity
  have hzX : x i - t • p ∈ X i := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg htpos.le, ht]
    have : ε / (2 * ‖p‖) * ‖p‖ = ε / 2 := by field_simp
    rw [this]; linarith
  refine utility_le_of_cheaper_point_on (hX i) (hcont i) (hquasi i) hzX ?_ hyX hy
  rw [inner_sub_right, inner_smul_right]
  have : 0 < ⟪p, p⟫ := real_inner_self_pos.mpr hp
  nlinarith

end ConsumptionSets

end Applied.Economics
