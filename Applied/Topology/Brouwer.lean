import Applied.Topology.SpernerCube

/-!
# Brouwer's fixed point theorem

## Main results

* `brouwer_cube`: a continuous map `g : (Fin m → ℝ) → (Fin m → ℝ)` with values in the cube
  `[0, 1]^m` has a fixed point.
* `brouwer_cube_of_continuousOn`: the usual self-map form: a map that is continuous on the cube
  and maps the cube into itself has a fixed point in the cube.
* `IsCubeRetract X`: `X` is a retract of some cube `[0,1]^M`.
  `IsCubeRetract.exists_fixedPoint`: every continuous self-map of such an `X` has a fixed
  point. `IsCubeRetract.of_retract`, `IsCubeRetract.pi`: closure under retracts and finite
  products.
* `probSimplex α`: the probability simplex on a finite type (equal to Mathlib's `stdSimplex`,
  `probSimplex_eq_stdSimplex`). `isCubeRetract_probSimplex`.
* `brouwer_probSimplex`, `brouwer_stdSimplex`, `brouwer_pi_probSimplex`: Brouwer's theorem for
  the simplex and for finite products of simplices (the form used for Nash equilibria).

## Proof outline

`brouwer_cube`: suppose there is no fixed point; then `dist (g y) y ≥ δ > 0` on the cube.
Choose a grid of mesh `1 / N` fine enough for uniform continuity, label a grid point `x` by a
coordinate `i` with `x i > 0` that `g` does not increase (or by `m` if there is none), check
that the labelling is admissible, and apply Sperner's lemma for the Kuhn triangulation
(`Applied.Topology.Kuhn.exists_full`) to get a small simplex carrying all labels, which
contradicts uniform continuity. No homology or degree theory is used.

## Not in this file

Brouwer's theorem for general compact convex sets (only cubes, simplices, their finite
products and retracts of these); Kakutani's and Schauder's theorems; uniqueness or computation
of fixed points. The one-dimensional case has a direct proof in `BrouwerOneDim`.
-/

-- `stdSimplex` (a `Set`) is deprecated in this Mathlib in favour of `Convexity.StdSimplex`;
-- it is only used to restate `brouwer_probSimplex` in Mathlib's vocabulary.
set_option linter.deprecated false

namespace Applied.Topology

open Set Finset

/-- **Brouwer's fixed point theorem for the cube.** A continuous map of `ℝ^m` whose values lie
in the cube `[0,1]^m` has a fixed point. -/
theorem brouwer_cube {m : ℕ} (g : (Fin m → ℝ) → (Fin m → ℝ)) (hg : Continuous g)
    (hmaps : ∀ y i, g y i ∈ Icc (0 : ℝ) 1) : ∃ y, g y = y := by
  classical
  by_contra hno
  simp only [not_exists] at hno
  set K : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ => Icc (0 : ℝ) 1) with hK
  have hKc : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hKne : K.Nonempty := ⟨fun _ => 0, by simp only [K, Set.mem_pi]; intro i _; simp⟩
  obtain ⟨y0, -, hy0min⟩ :=
    hKc.exists_isMinOn hKne ((hg.dist continuous_id).continuousOn)
  set δ := dist (g y0) y0 with hδdef
  have hδ : 0 < δ := dist_pos.2 (hno y0)
  have hUC := hKc.uniformContinuousOn_of_continuous hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨η, hη, hηg⟩ := hUC (δ / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / η) (2 / δ))
  have hη' : 0 < 1 / η := by positivity
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (le_max_of_le_left hη'.le) hN
  have hNη : 1 / (N : ℝ) < η := by
    rw [div_lt_iff₀ hNpos]
    have := lt_of_le_of_lt (le_max_left _ _) hN
    rw [div_lt_iff₀ hη] at this
    linarith
  have hNδ : 1 / (N : ℝ) < δ / 2 := by
    rw [div_lt_iff₀ hNpos]
    have := lt_of_le_of_lt (le_max_right _ _) hN
    rw [div_lt_iff₀ hδ] at this
    linarith
  -- grid points scaled into the cube
  set p : (Fin m → ℕ) → (Fin m → ℝ) := fun x i => (x i : ℝ) / N with hp
  -- the labelling
  set l : (Fin m → ℕ) → Fin (m + 1) := fun x =>
    if h : ∃ i, 0 < x i ∧ g (p x) i ≤ p x i then (Classical.choose h).castSucc
    else Fin.last m with hl_def
  have hlA : ∀ x i, x i = 0 → l x ≠ i.castSucc := by
    intro x i hx hli
    simp only [hl_def] at hli
    split_ifs at hli with h
    · have := (Classical.choose_spec h).1
      rw [Fin.castSucc_inj.1 hli, hx] at this
      exact lt_irrefl _ this
    · exact Fin.castSucc_ne_last i hli.symm
  have hlB : ∀ x i, x i = N → l x ≠ Fin.last m := by
    intro x i hx hli
    simp only [hl_def] at hli
    split_ifs at hli with h
    · exact Fin.castSucc_ne_last _ hli
    · apply h
      refine ⟨i, ?_, ?_⟩
      · rw [hx]; exact_mod_cast hNpos
      · have : p x i = 1 := by
          simp only [hp, hx]; field_simp
        rw [this]; exact (hmaps _ i).2
  obtain ⟨σ, hσ⟩ := Kuhn.exists_full (N := N) (by exact_mod_cast hNpos) l ⟨hlA, hlB⟩
  have hlab : ∀ c, ∃ k, l (Kuhn.vertex σ k) = c := by
    intro c
    have : c ∈ Finset.univ.image (fun k => l (Kuhn.vertex σ k)) := by
      rw [show Finset.univ.image (fun k => l (Kuhn.vertex σ k)) = Finset.univ from hσ]
      exact Finset.mem_univ c
    simpa using this
  -- the vertices, scaled, lie in the cube and are `1/N`-close
  have hmemK : ∀ k, p (Kuhn.vertex σ k) ∈ K := by
    intro k
    simp only [K, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, hp]
    intro i
    have := Kuhn.vertex_le σ k i
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNpos]; exact_mod_cast this
  have hclose : ∀ k k' i, |p (Kuhn.vertex σ k) i - p (Kuhn.vertex σ k') i| ≤ 1 / N := by
    intro k k' i
    simp only [hp]
    rw [← sub_div, abs_div, abs_of_pos hNpos]
    apply div_le_div_of_nonneg_right _ hNpos.le
    have h1 := Kuhn.vertex_ge σ k i
    have h2 := Kuhn.vertex_le_base σ k i
    have h3 := Kuhn.vertex_ge σ k' i
    have h4 := Kuhn.vertex_le_base σ k' i
    rw [abs_le]
    constructor
    · have : ((Kuhn.vertex σ k' i : ℕ) : ℝ) ≤ (Kuhn.vertex σ k i : ℝ) + 1 := by
        exact_mod_cast (by omega : Kuhn.vertex σ k' i ≤ Kuhn.vertex σ k i + 1)
      linarith
    · have : ((Kuhn.vertex σ k i : ℕ) : ℝ) ≤ (Kuhn.vertex σ k' i : ℝ) + 1 := by
        exact_mod_cast (by omega : Kuhn.vertex σ k i ≤ Kuhn.vertex σ k' i + 1)
      linarith
  have hdist : ∀ k k', dist (p (Kuhn.vertex σ k)) (p (Kuhn.vertex σ k')) < η := by
    intro k k'
    refine lt_of_le_of_lt ?_ hNη
    refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
    rw [Real.dist_eq]; exact hclose k k' i
  -- the vertex with label `last`
  obtain ⟨k0, hk0⟩ := hlab (Fin.last m)
  set a := p (Kuhn.vertex σ k0) with ha
  have hup : ∀ i, a i ≤ g a i := by
    intro i
    simp only [hl_def] at hk0
    split_ifs at hk0 with h
    · exact absurd hk0 (Fin.castSucc_ne_last _)
    · simp only [not_exists, not_and, not_le] at h
      by_cases hx : Kuhn.vertex σ k0 i = 0
      · have : a i = 0 := by simp only [ha, hp, hx]; simp
        rw [this]; exact (hmaps _ i).1
      · exact (h i (Nat.pos_of_ne_zero hx)).le
  have hdown : ∀ i, g a i - a i < δ := by
    intro i
    obtain ⟨ki, hki⟩ := hlab i.castSucc
    set b := p (Kuhn.vertex σ ki) with hb
    have hb_le : g b i ≤ b i := by
      simp only [hl_def] at hki
      split_ifs at hki with h
      · have hi : Classical.choose h = i := Fin.castSucc_inj.1 hki
        have := (Classical.choose_spec h).2
        rw [hi] at this
        exact this
      · exact absurd hki.symm (Fin.castSucc_ne_last _)
    have hgab : dist (g a) (g b) < δ / 2 := hηg a (hmemK k0) b (hmemK ki) (hdist k0 ki)
    have h1 : |g a i - g b i| < δ / 2 :=
      lt_of_le_of_lt (by rw [← Real.dist_eq]; exact dist_le_pi_dist _ _ i) hgab
    have h2 := hclose ki k0 i
    rw [abs_lt] at h1
    rw [abs_le] at h2
    linarith
  have : dist (g a) a < δ := by
    refine (dist_pi_lt_iff hδ).2 fun i => ?_
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [hup i]
    · exact hdown i
  exact absurd (hy0min (hmemK k0)) (not_le.2 this)

/-! ### Retracts of cubes -/

/-- `X` is a retract of a cube: there are continuous maps `e : X → ℝ^M` with values in
`[0,1]^M` and `ρ : ℝ^M → X` with `ρ ∘ e = id`. -/
def IsCubeRetract (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ (M : ℕ) (e : X → (Fin M → ℝ)) (ρ : (Fin M → ℝ) → X), Continuous e ∧ Continuous ρ ∧
    (∀ x i, e x i ∈ Icc (0 : ℝ) 1) ∧ ∀ x, ρ (e x) = x

/-- Brouwer's fixed point theorem for retracts of cubes. -/
theorem IsCubeRetract.exists_fixedPoint {X : Type*} [TopologicalSpace X] (hX : IsCubeRetract X)
    (f : X → X) (hf : Continuous f) : ∃ x, f x = x := by
  obtain ⟨M, e, ρ, he, hρ, hcube, hinv⟩ := hX
  obtain ⟨y, hy⟩ :=
    brouwer_cube (fun y => e (f (ρ y))) (he.comp (hf.comp hρ)) (fun y i => hcube _ i)
  refine ⟨ρ y, ?_⟩
  have : ρ (e (f (ρ y))) = ρ y := by rw [hy]
  rwa [hinv] at this

/-- A retract of a retract of a cube is a retract of a cube. -/
theorem IsCubeRetract.of_retract {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IsCubeRetract X) (i : Y → X) (r : X → Y) (hi : Continuous i) (hr : Continuous r)
    (h : ∀ y, r (i y) = y) : IsCubeRetract Y := by
  obtain ⟨M, e, ρ, he, hρ, hcube, hinv⟩ := hX
  exact ⟨M, e ∘ i, r ∘ ρ, he.comp hi, hr.comp hρ, fun y => hcube (i y),
    fun y => by simp [hinv, h]⟩

/-- A finite product of retracts of cubes is a retract of a cube. -/
theorem IsCubeRetract.pi {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] (h : ∀ i, IsCubeRetract (X i)) :
    IsCubeRetract (∀ i, X i) := by
  classical
  choose M e ρ he hρ hcube hinv using h
  let E := Fintype.equivFin (Σ i, Fin (M i))
  refine ⟨Fintype.card (Σ i, Fin (M i)),
    fun x j => e (E.symm j).1 (x (E.symm j).1) (E.symm j).2,
    fun y i => ρ i (fun k => y (E ⟨i, k⟩)), ?_, ?_, ?_, ?_⟩
  · exact continuous_pi fun j =>
      (continuous_apply _).comp ((he _).comp (continuous_apply _))
  · exact continuous_pi fun i => (hρ i).comp (continuous_pi fun k => continuous_apply _)
  · intro x j; exact hcube _ _ _
  · intro x
    funext i
    have key : ∀ (s : Σ i, Fin (M i)) (i : ι) (k : Fin (M i)), s = ⟨i, k⟩ →
        e s.1 (x s.1) s.2 = e i (x i) k := by
      rintro s i k rfl; rfl
    convert hinv i (x i) using 2
    funext k
    exact key _ i k (E.symm_apply_apply _)

/-! ### The probability simplex -/

/-- The probability simplex on a finite type: non-negative vectors summing to `1`. -/
def probSimplex (α : Type*) [Fintype α] : Set (α → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- Clamp a real number to `[0, 1]`. -/
noncomputable def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

lemma clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

lemma clamp01_of_mem {t : ℝ} (h : t ∈ Icc (0 : ℝ) 1) : clamp01 t = t := by
  unfold clamp01; rw [min_eq_right h.2, max_eq_right h.1]

lemma continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

/-- A retraction of `ℝ^m` onto the corner simplex `{q ≥ 0, ∑ q ≤ 1}`. -/
noncomputable def cornerRetr {m : ℕ} (y : Fin m → ℝ) : Fin m → ℝ :=
  fun i => clamp01 (y i) / max 1 (∑ j, clamp01 (y j))

lemma cornerRetr_nonneg {m : ℕ} (y : Fin m → ℝ) (i : Fin m) : 0 ≤ cornerRetr y i :=
  div_nonneg (clamp01_nonneg _) (le_trans zero_le_one (le_max_left _ _))

lemma sum_cornerRetr_le {m : ℕ} (y : Fin m → ℝ) : ∑ i, cornerRetr y i ≤ 1 := by
  unfold cornerRetr
  rw [← Finset.sum_div]
  exact div_le_one_of_le₀ (le_max_right _ _) (le_trans zero_le_one (le_max_left _ _))

lemma continuous_cornerRetr {m : ℕ} : Continuous (cornerRetr (m := m)) := by
  refine continuous_pi fun i => ?_
  exact (continuous_clamp01.comp (continuous_apply i)).div
    (continuous_const.max (continuous_finsetSum _ fun j _ =>
      continuous_clamp01.comp (continuous_apply j)))
    (fun y => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne')

/-- A retraction of `ℝ^m` onto the simplex `probSimplex (Fin (m + 1))`. -/
noncomputable def simplexRetr {m : ℕ} (y : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (cornerRetr y) (1 - ∑ i, cornerRetr y i)

lemma simplexRetr_mem {m : ℕ} (y : Fin m → ℝ) : simplexRetr y ∈ probSimplex (Fin (m + 1)) := by
  refine ⟨fun k => ?_, ?_⟩
  · induction k using Fin.lastCases with
    | last => simp only [simplexRetr, Fin.snoc_last]; linarith [sum_cornerRetr_le y]
    | cast i => simp only [simplexRetr, Fin.snoc_castSucc]; exact cornerRetr_nonneg y i
  · rw [Fin.sum_univ_castSucc]
    simp only [simplexRetr, Fin.snoc_castSucc, Fin.snoc_last]
    ring

lemma continuous_simplexRetr {m : ℕ} : Continuous (simplexRetr (m := m)) := by
  refine continuous_pi fun k => ?_
  induction k using Fin.lastCases with
  | last =>
    have : (fun y : Fin m → ℝ => simplexRetr y (Fin.last m)) =
        fun y => 1 - ∑ i, cornerRetr y i := funext fun y => by simp [simplexRetr]
    rw [this]
    have hc : ∀ i, Continuous fun y : Fin m → ℝ => cornerRetr y i :=
      fun i => (continuous_apply i).comp continuous_cornerRetr
    have hs : Continuous fun y : Fin m → ℝ => ∑ i, cornerRetr y i :=
      continuous_finsetSum Finset.univ fun i _ => hc i
    exact continuous_const.sub hs
  | cast i =>
    have : (fun y : Fin m → ℝ => simplexRetr y i.castSucc) =
        fun y => cornerRetr y i := funext fun y => by simp [simplexRetr]
    rw [this]
    exact (continuous_apply i).comp continuous_cornerRetr

lemma simplexRetr_castSucc {m : ℕ} (p : Fin (m + 1) → ℝ) (hp : p ∈ probSimplex (Fin (m + 1))) :
    simplexRetr (fun i => p i.castSucc) = p := by
  have hsum := hp.2
  rw [Fin.sum_univ_castSucc] at hsum
  have hlast := hp.1 (Fin.last m)
  have hle : ∀ i : Fin m, p i.castSucc ∈ Icc (0 : ℝ) 1 := by
    intro i
    refine ⟨hp.1 _, ?_⟩
    have := Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i.castSucc)
    rw [hp.2] at this; exact this
  have hs : ∑ j : Fin m, clamp01 (p j.castSucc) = ∑ j : Fin m, p j.castSucc :=
    Finset.sum_congr rfl fun j _ => clamp01_of_mem (hle j)
  have hmax : max 1 (∑ j : Fin m, clamp01 (p j.castSucc)) = 1 := by
    rw [hs]; apply max_eq_left; linarith
  have hc : cornerRetr (fun i => p i.castSucc) = fun i => p i.castSucc := by
    funext i
    simp only [cornerRetr, hmax, div_one, clamp01_of_mem (hle i)]
  funext k
  induction k using Fin.lastCases with
  | last => simp only [simplexRetr, Fin.snoc_last, hc]; linarith
  | cast i => simp only [simplexRetr, Fin.snoc_castSucc, hc]

/-- The simplex `probSimplex (Fin (m + 1))` is a retract of the cube `[0,1]^m`. -/
theorem isCubeRetract_probSimplex_fin (m : ℕ) : IsCubeRetract (probSimplex (Fin (m + 1))) := by
  refine ⟨m, fun p i => p.1 i.castSucc, fun y => ⟨simplexRetr y, simplexRetr_mem y⟩, ?_, ?_, ?_, ?_⟩
  · exact continuous_pi fun i => (continuous_apply _).comp continuous_subtype_val
  · exact continuous_simplexRetr.subtype_mk _
  · intro p i
    refine ⟨p.2.1 _, ?_⟩
    have := Finset.single_le_sum (fun j _ => p.2.1 j) (Finset.mem_univ i.castSucc)
    rw [p.2.2] at this; exact this
  · intro p
    exact Subtype.ext (simplexRetr_castSucc p.1 p.2)

/-- The probability simplex on any non-empty finite type is a retract of a cube. -/
theorem isCubeRetract_probSimplex (α : Type*) [Fintype α] [Nonempty α] :
    IsCubeRetract (probSimplex α) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos (α := α)).ne'
  let E : α ≃ Fin (n + 1) := (Fintype.equivFin α).trans (finCongr hn)
  refine (isCubeRetract_probSimplex_fin n).of_retract
    (fun p => ⟨fun k => p.1 (E.symm k), fun k => p.2.1 _, by
      rw [Equiv.sum_comp E.symm (fun a => p.1 a)]; exact p.2.2⟩)
    (fun q => ⟨fun a => q.1 (E a), fun a => q.2.1 _, by
      rw [Equiv.sum_comp E (fun k => q.1 k)]; exact q.2.2⟩) ?_ ?_ ?_
  · exact Continuous.subtype_mk (continuous_pi fun k =>
      ((continuous_apply (E.symm k)).comp continuous_subtype_val :
        Continuous fun p : probSimplex α => p.1 (E.symm k))) _
  · exact Continuous.subtype_mk (continuous_pi fun a =>
      ((continuous_apply (E a)).comp continuous_subtype_val :
        Continuous fun q : probSimplex (Fin (n + 1)) => q.1 (E a))) _
  · intro p; apply Subtype.ext; funext a; simp

/-- **Brouwer's fixed point theorem for the probability simplex.** Every continuous self-map
of the simplex of probability vectors on a non-empty finite type has a fixed point. -/
theorem brouwer_probSimplex {α : Type*} [Fintype α] [Nonempty α]
    (f : probSimplex α → probSimplex α) (hf : Continuous f) : ∃ p, f p = p :=
  (isCubeRetract_probSimplex α).exists_fixedPoint f hf

/-- **Brouwer's fixed point theorem for finite products of simplices.** -/
theorem brouwer_pi_probSimplex {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    [∀ i, Nonempty (S i)] (f : (∀ i, probSimplex (S i)) → (∀ i, probSimplex (S i)))
    (hf : Continuous f) : ∃ p, f p = p :=
  (IsCubeRetract.pi fun i => isCubeRetract_probSimplex (S i)).exists_fixedPoint f hf

/-- Mathlib's `stdSimplex` is the same set as `probSimplex`. -/
lemma probSimplex_eq_stdSimplex (α : Type*) [Fintype α] :
    probSimplex α = (stdSimplex ℝ α) := rfl

/-- **Brouwer's fixed point theorem for the standard simplex** `stdSimplex ℝ (Fin (n + 1))`. -/
theorem brouwer_stdSimplex {n : ℕ} (f : stdSimplex ℝ (Fin (n + 1)) → stdSimplex ℝ (Fin (n + 1)))
    (hf : Continuous f) : ∃ p, f p = p :=
  brouwer_probSimplex (α := Fin (n + 1)) f hf

/-- **Brouwer's fixed point theorem for the cube, self-map form.** A map that is continuous on
the cube `[0,1]^m` and maps the cube into itself has a fixed point in the cube. This removes
the requirement of `brouwer_cube` that `g` be continuous on all of `ℝ^m`: precompose with the
coordinatewise clamp to `[0, 1]`. -/
theorem brouwer_cube_of_continuousOn {m : ℕ} (g : (Fin m → ℝ) → (Fin m → ℝ))
    (hg : ContinuousOn g (Set.pi Set.univ fun _ => Icc (0 : ℝ) 1))
    (hmaps : MapsTo g (Set.pi Set.univ fun _ => Icc (0 : ℝ) 1)
      (Set.pi Set.univ fun _ => Icc (0 : ℝ) 1)) :
    ∃ y ∈ Set.pi Set.univ (fun _ : Fin m => Icc (0 : ℝ) 1), g y = y := by
  set K : Set (Fin m → ℝ) := Set.pi Set.univ fun _ => Icc (0 : ℝ) 1 with hK
  let c : (Fin m → ℝ) → (Fin m → ℝ) := fun y i => max 0 (min 1 (y i))
  have hc : Continuous c := continuous_pi fun i =>
    continuous_const.max (continuous_const.min (continuous_apply i))
  have hcK : ∀ y, c y ∈ K := fun y => by
    intro i _
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hcid : ∀ y ∈ K, c y = y := by
    intro y hy
    funext i
    have := hy i (Set.mem_univ i)
    simp only [c]
    rw [min_eq_right this.2, max_eq_right this.1]
  have hcont : Continuous (g ∘ c) := hg.comp_continuous hc hcK
  obtain ⟨y, hy⟩ := brouwer_cube (g ∘ c) hcont (fun y i => hmaps (hcK y) i (Set.mem_univ i))
  have hyK : y ∈ K := by rw [← hy]; exact hmaps (hcK y)
  refine ⟨y, hyK, ?_⟩
  have h := hy
  simp only [Function.comp_apply, hcid y hyK] at h
  exact h

end Applied.Topology
