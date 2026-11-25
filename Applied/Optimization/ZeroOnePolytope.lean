import Applied.Optimization.PolytopeGraph
import Mathlib.InformationTheory.Hamming

/-!
# Naddef's theorem: 0/1-polytopes have diameter at most `d`

A *0/1-point* of `ℝ ^ d` is a point all of whose coordinates are `0` or `1`. For a set `S` of
0/1-points, the 0/1-polytope `convexHull ℝ S` has graph diameter at most `d`
(D. Naddef, "The Hirsch conjecture is true for (0,1)-polytopes", Math. Programming 45 (1989)).

* `IsZeroOne x`: every coordinate of `x` is `0` or `1`.
* `isExtreme_convexHull_face`: for a set `S` of 0/1-points, a 0/1-point `u` and a set `J` of
  coordinates (a predicate `p`), the convex hull of `{s ∈ S | s j = u j for all j ∈ J}` is an
  extreme subset (a face) of `convexHull ℝ S`. With `J = {i}` this is the face `x_i = u_i`.
* `AdjVertices.of_isExtreme`: an edge of an extreme subset `B` of `A` is an edge of `A`
  (for any convex sets in any real vector space).
* `mem_extremePoints_convexHull_zeroOne`, `extremePoints_convexHull_zeroOne`: every point of
  `S` is a vertex of `convexHull ℝ S`, and these are all the vertices.
* `isExtreme_segment_zeroOne`: if `u, w ∈ S` and the only points of `S` that agree with `u`
  wherever `w` does are `u` and `w`, then `[u, w]` is an edge of `convexHull ℝ S`.
* `vertexDistLE_hammingDist_zeroOne`: two points `u, v ∈ S` are joined by a walk of at most
  `hammingDist u v` edges of `convexHull ℝ S`.
* `naddef`: two vertices of a 0/1-polytope in `ℝ ^ d` are joined by a walk of at most `d`
  edges.

The proof is Naddef's induction, organised as induction on the Hamming distance with `S` fixed:
among the points `w ≠ u` of `S` that agree with `u` wherever `u` and `v` agree, take one with
`hammingDist w u` minimal. Then `[u, w]` is an edge (an exposed face cut out by the affine
function `faceGap`), and `w` agrees with `v` in one more coordinate than `u` does.
-/

open Set

namespace Applied.Optimization

variable {d : ℕ}

/-- `x` is a 0/1-point: every coordinate is `0` or `1`. -/
def IsZeroOne (x : Fin d → ℝ) : Prop := ∀ j, x j = 0 ∨ x j = 1

/-- The affine function `∑_{j ∈ J} |x j - u j|` (written without absolute values, which is
correct on the cube `[0, 1] ^ d` when `u` is a 0/1-point). -/
private noncomputable def faceGap (p : Fin d → Prop) [DecidablePred p] (u x : Fin d → ℝ) : ℝ :=
  ∑ j, if p j then (1 - 2 * u j) * (x j - u j) else 0

private theorem faceGap_combo (p : Fin d → Prop) [DecidablePred p] (u x y : Fin d → ℝ)
    {a b : ℝ} (hab : a + b = 1) :
    faceGap p u (a • x + b • y) = a * faceGap p u x + b * faceGap p u y := by
  unfold faceGap
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show b = 1 - a by linarith]
    ring
  · simp

private theorem faceGap_term_nonneg {p : Fin d → Prop} [DecidablePred p] {u x : Fin d → ℝ}
    (hu : IsZeroOne u) (hx : IsZeroOne x) (j : Fin d) :
    0 ≤ (if p j then (1 - 2 * u j) * (x j - u j) else 0) := by
  split_ifs
  · rcases hu j with h | h <;> rcases hx j with h' | h' <;> rw [h, h'] <;> norm_num
  · exact le_rfl

private theorem faceGap_nonneg {p : Fin d → Prop} [DecidablePred p] {u x : Fin d → ℝ}
    (hu : IsZeroOne u) (hx : IsZeroOne x) : 0 ≤ faceGap p u x :=
  Finset.sum_nonneg fun j _ => faceGap_term_nonneg hu hx j

private theorem faceGap_pos {p : Fin d → Prop} [DecidablePred p] {u x : Fin d → ℝ}
    (hu : IsZeroOne u) (hx : IsZeroOne x) {j : Fin d} (hj : p j) (hne : x j ≠ u j) :
    0 < faceGap p u x := by
  have h1 : (1 : ℝ) = (if p j then (1 - 2 * u j) * (x j - u j) else 0) := by
    simp only [hj, ↓reduceIte]
    rcases hu j with h | h <;> rcases hx j with h' | h' <;> rw [h, h'] at hne ⊢ <;>
      first | exact absurd rfl hne | norm_num
  have h2 : (if p j then (1 - 2 * u j) * (x j - u j) else 0) ≤ faceGap p u x :=
    Finset.single_le_sum (f := fun j => if p j then (1 - 2 * u j) * (x j - u j) else 0)
      (fun i _ => faceGap_term_nonneg hu hx i) (Finset.mem_univ j)
  linarith

private theorem faceGap_eq_zero {p : Fin d → Prop} [DecidablePred p] {u x : Fin d → ℝ}
    (hx : ∀ j, p j → x j = u j) : faceGap p u x = 0 :=
  Finset.sum_eq_zero fun j _ => by
    split_ifs with h
    · rw [hx j h, sub_self, mul_zero]
    · rfl

/-- **Face lemma.** For a set `S` of 0/1-points, a 0/1-point `u` and a set of coordinates
given by a predicate `p`, the convex hull of the points of `S` that agree with `u` on `p` is an
extreme subset of `convexHull ℝ S`. -/
theorem isExtreme_convexHull_face {S : Set (Fin d → ℝ)} (hS : ∀ s ∈ S, IsZeroOne s)
    (p : Fin d → Prop) [DecidablePred p] {u : Fin d → ℝ} (hu : IsZeroOne u) :
    IsExtreme ℝ (convexHull ℝ S) (convexHull ℝ {s ∈ S | ∀ j, p j → s j = u j}) := by
  set F := {s ∈ S | ∀ j, p j → s j = u j} with hFdef
  have hFS : F ⊆ S := sep_subset _ _
  have hzero : ∀ x ∈ convexHull ℝ F, faceGap p u x = 0 := by
    have hconv : Convex ℝ {x | faceGap p u x = 0} := by
      intro x hx y hy a b _ _ hab
      change faceGap p u x = 0 at hx
      change faceGap p u y = 0 at hy
      change faceGap p u (a • x + b • y) = 0
      rw [faceGap_combo p u x y hab, hx, hy]
      ring
    exact fun x hx => convexHull_min (fun s (hs : s ∈ F) => faceGap_eq_zero hs.2) hconv hx
  set C := {x | 0 < faceGap p u x} ∪ convexHull ℝ F with hCdef
  have hCconv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    have key : ∀ {gx gy : ℝ}, 0 < gx → 0 ≤ gy → 0 < a → 0 < a * gx + b * gy := by
      intro gx gy hgx hgy ha'
      have := mul_pos ha' hgx
      have := mul_nonneg hb hgy
      linarith
    have key' : ∀ {gx gy : ℝ}, 0 ≤ gx → 0 < gy → 0 < b → 0 < a * gx + b * gy := by
      intro gx gy hgx hgy hb'
      have := mul_nonneg ha hgx
      have := mul_pos hb' hgy
      linarith
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · left
      show 0 < faceGap p u (a • x + b • y)
      rw [faceGap_combo p u x y hab]
      rcases ha.eq_or_lt with rfl | ha'
      · exact key' hx.le hy (by linarith)
      · exact key hx hy.le ha'
    · rcases ha.eq_or_lt with rfl | ha'
      · right
        rw [show b = 1 by linarith, zero_smul, one_smul, zero_add]
        exact hy
      · left
        show 0 < faceGap p u (a • x + b • y)
        rw [faceGap_combo p u x y hab]
        exact key hx (hzero y hy).ge ha'
    · rcases hb.eq_or_lt with rfl | hb'
      · right
        rw [show a = 1 by linarith, zero_smul, one_smul, add_zero]
        exact hx
      · left
        show 0 < faceGap p u (a • x + b • y)
        rw [faceGap_combo p u x y hab]
        exact key' (hzero x hx).ge hy hb'
    · right
      exact (convex_convexHull ℝ F) hx hy ha hb hab
  have hSC : S ⊆ C := fun s hs => by
    by_cases h : ∀ j, p j → s j = u j
    · right
      exact subset_convexHull ℝ F ⟨hs, h⟩
    · left
      push Not at h
      obtain ⟨j, hj, hne⟩ := h
      exact faceGap_pos hu (hS s hs) hj hne
  have hhull : convexHull ℝ S ⊆ C := convexHull_min hSC hCconv
  have hnonneg : ∀ x ∈ convexHull ℝ S, 0 ≤ faceGap p u x := fun x hx =>
    (hhull hx).elim (fun h => le_of_lt h) (fun h => (hzero x h).ge)
  refine ⟨convexHull_mono hFS, fun x₁ hx₁ x₂ hx₂ x hx hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  have h0 := hzero _ hx
  rw [faceGap_combo p u x₁ x₂ hab] at h0
  have g1 := hnonneg _ hx₁
  have g2 := hnonneg _ hx₂
  have e1 : ¬ 0 < faceGap p u x₁ := by
    intro hpos
    have := mul_pos ha hpos
    have := mul_nonneg hb.le g2
    linarith
  exact (hhull hx₁).resolve_left e1

/-- An edge of an extreme subset `B` of `A` is an edge of `A`. -/
theorem AdjVertices.of_isExtreme {E : Type*} [AddCommGroup E] [Module ℝ E] {A B : Set E}
    {u v : E} (hAB : IsExtreme ℝ A B) (h : AdjVertices B u v) : AdjVertices A u v :=
  ⟨h.1, hAB.extremePoints_subset_extremePoints h.2.1,
    hAB.extremePoints_subset_extremePoints h.2.2.1, hAB.trans h.2.2.2⟩

/-- If `u, w ∈ S` and the only points of `S` agreeing with `u` on every coordinate where `w`
agrees with `u` are `u` and `w`, then `[u, w]` is an extreme subset of `convexHull ℝ S`. -/
theorem isExtreme_segment_zeroOne {S : Set (Fin d → ℝ)} (hS : ∀ s ∈ S, IsZeroOne s)
    {u w : Fin d → ℝ} (hu : u ∈ S) (hw : w ∈ S)
    (hmin : ∀ s ∈ S, (∀ j, w j = u j → s j = u j) → s = u ∨ s = w) :
    IsExtreme ℝ (convexHull ℝ S) (segment ℝ u w) := by
  classical
  have h := isExtreme_convexHull_face hS (fun j => w j = u j) (hS u hu)
  have hF : {s ∈ S | ∀ j, w j = u j → s j = u j} = {u, w} := by
    ext s
    constructor
    · rintro ⟨hs, h⟩
      rcases hmin s hs h with rfl | rfl
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ (mem_singleton _)
    · rintro (rfl | rfl)
      · exact ⟨hu, fun _ _ => rfl⟩
      · exact ⟨hw, fun _ h => h⟩
  rwa [hF, convexHull_pair] at h

/-- Every point of a set `S` of 0/1-points is an extreme point of `convexHull ℝ S`. -/
theorem mem_extremePoints_convexHull_zeroOne {S : Set (Fin d → ℝ)} (hS : ∀ s ∈ S, IsZeroOne s)
    {u : Fin d → ℝ} (hu : u ∈ S) : u ∈ (convexHull ℝ S).extremePoints ℝ := by
  rw [← isExtreme_singleton, ← segment_same ℝ u]
  exact isExtreme_segment_zeroOne hS hu hu fun s _ h => Or.inl (funext fun j => h j rfl)

/-- The vertices of the 0/1-polytope `convexHull ℝ S` are exactly the points of `S`. -/
theorem extremePoints_convexHull_zeroOne {S : Set (Fin d → ℝ)} (hS : ∀ s ∈ S, IsZeroOne s) :
    (convexHull ℝ S).extremePoints ℝ = S :=
  Subset.antisymm extremePoints_convexHull_subset
    fun _ hu => mem_extremePoints_convexHull_zeroOne hS hu

private theorem eq_of_ne_ne {a b c : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) (hac : a ≠ c) (hbc : b ≠ c) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    first | rfl | exact absurd rfl hac | exact absurd rfl hbc

private theorem vertexDistLE_zeroOne_aux {S : Set (Fin d → ℝ)} (hS : ∀ s ∈ S, IsZeroOne s) :
    ∀ k : ℕ, ∀ u ∈ S, ∀ v ∈ S, hammingDist u v ≤ k → VertexDistLE (convexHull ℝ S) u v k := by
  classical
  intro k
  induction k with
  | zero =>
    intro u _ v _ h
    obtain rfl : u = v := hammingDist_eq_zero.1 (Nat.le_zero.1 h)
    exact VertexDistLE.refl _ _ _
  | succ k ih =>
    intro u hu v hv hk
    by_cases huv : u = v
    · subst huv
      exact VertexDistLE.refl _ _ _
    have hP : ∃ n, ∃ w ∈ S, w ≠ u ∧ (∀ j, u j = v j → w j = u j) ∧ hammingDist w u = n :=
      ⟨_, v, hv, Ne.symm huv, fun j h => h.symm, rfl⟩
    obtain ⟨w, hw, hwu, hwagree, hwk⟩ := Nat.find_spec hP
    have hmin : ∀ s ∈ S, (∀ j, w j = u j → s j = u j) → s = u ∨ s = w := by
      intro s hs hsub
      by_cases hsu : s = u
      · exact Or.inl hsu
      right
      have hs_agree : ∀ j, u j = v j → s j = u j := fun j h => hsub j (hwagree j h)
      have hle : Nat.find hP ≤ hammingDist s u := Nat.find_min' hP ⟨s, hs, hsu, hs_agree, rfl⟩
      have hsubset : (Finset.univ.filter fun j => s j ≠ u j) ⊆
          Finset.univ.filter fun j => w j ≠ u j := by
        intro j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h1 h2
        exact h1 (hsub j h2)
      have heq := Finset.eq_of_subset_of_card_le hsubset (by
        rw [← hwk] at hle
        exact hle)
      funext j
      by_cases hj : s j = u j
      · have : j ∉ Finset.univ.filter fun j => w j ≠ u j := by
          rw [← heq]
          simp [hj]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
        rw [hj, this]
      · have : j ∈ Finset.univ.filter fun j => w j ≠ u j := hsubset (by simp [hj])
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact eq_of_ne_ne (hS s hs j) (hS w hw j) (hS u hu j) hj this
    have hadj : AdjVertices (convexHull ℝ S) u w :=
      ⟨Ne.symm hwu, mem_extremePoints_convexHull_zeroOne hS hu,
        mem_extremePoints_convexHull_zeroOne hS hw, isExtreme_segment_zeroOne hS hu hw hmin⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hwu
    have huvj : u j ≠ v j := fun h => hj (hwagree j h)
    have hwvj : w j = v j :=
      eq_of_ne_ne (hS w hw j) (hS v hv j) (hS u hu j) hj (Ne.symm huvj)
    have hdist : hammingDist w v ≤ k := by
      have hsub : (Finset.univ.filter fun i => w i ≠ v i) ⊆
          (Finset.univ.filter fun i => u i ≠ v i).erase j := by
        intro i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        intro hi
        refine ⟨fun hij => hi (hij ▸ hwvj), fun h => hi ?_⟩
        rw [hwagree i h, h]
      have hjmem : j ∈ Finset.univ.filter fun i => u i ≠ v i := by simp [huvj]
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hjmem] at h1
      have h2 : (Finset.univ.filter fun i => u i ≠ v i).card ≤ k + 1 := hk
      show (Finset.univ.filter fun i => w i ≠ v i).card ≤ k
      omega
    exact (hadj.vertexDistLE.trans (ih w hw v hv hdist)).mono (by omega)

/-- Two points `u, v` of a set `S` of 0/1-points are joined by a walk of at most
`hammingDist u v` edges in the graph of `convexHull ℝ S`. -/
theorem vertexDistLE_hammingDist_zeroOne {S : Set (Fin d → ℝ)} (hS : ∀ s ∈ S, IsZeroOne s)
    {u v : Fin d → ℝ} (hu : u ∈ S) (hv : v ∈ S) :
    VertexDistLE (convexHull ℝ S) u v (hammingDist u v) :=
  vertexDistLE_zeroOne_aux hS _ u hu v hv le_rfl

/-- **Naddef's theorem** (1989). The graph of a 0/1-polytope in `ℝ ^ d` has diameter at most
`d`: any two vertices of `convexHull ℝ S`, `S` a set of 0/1-points, are joined by a walk of at
most `d` edges. -/
theorem naddef {S : Set (Fin d → ℝ)} (hS : ∀ s ∈ S, IsZeroOne s) {u v : Fin d → ℝ}
    (hu : u ∈ (convexHull ℝ S).extremePoints ℝ) (hv : v ∈ (convexHull ℝ S).extremePoints ℝ) :
    VertexDistLE (convexHull ℝ S) u v d := by
  classical
  rw [extremePoints_convexHull_zeroOne hS] at hu hv
  exact (vertexDistLE_hammingDist_zeroOne hS hu hv).mono
    (hammingDist_le_card_fintype.trans (by simp))

end Applied.Optimization
