import Applied.Economics.EFXTwoTypes

/-!
# EFX allocations for three agents with additive valuations

Three agents have additive non-negative valuations over a finite set `G` of indivisible goods.
Then an allocation that is EFX in the strong sense of `Applied.Economics.IsEFX` exists
(`efx_exists_three`, and `efx_exists_card_three` for any type of agents with three elements).
This is the theorem of Chaudhury, Garg and Mehlhorn (EC 2020). The proof below follows the
later, simpler proof of Akrami, Alon, Chaudhury, Garg, Mehlhorn and Mehta (Section 4 of "EFX:
a simpler approach and an (almost) optimal guarantee via rainbow cycle number"), specialised to
additive valuations, with the algorithms replaced by extremal arguments.

* `NoSE u B T`: an agent with valuation `u` holding `B` does not strongly envy the bundle `T`.
* `exists_pr`: for one positive valuation, a partition into bundles indexed by a finite type
  can be replaced by one without strong envy in which every bundle is worth at least the
  former minimum (the statement of the Plaut–Roughgarden lemma used in the paper; the proof
  here takes a partition minimising the sum of squares of the bundle values).
* `Inv a b c X1 X2 X3`: the invariant of the paper: `(X1, X2, X3)` is a partition, the first
  agent does not strongly envy anybody with `X1` or with `X2`, and the second or the third
  agent does not strongly envy anybody with `X3`.
* `step`: from a partition satisfying the invariant one obtains an EFX allocation of the three
  bundles, or another partition satisfying the invariant with a larger value of
  `min (a X1) (a X2)`. Here valuations are positive and the first agent values different sets
  differently.
* `efx3_nondegenerate`: a partition satisfying the invariant with the largest potential gives
  an EFX allocation.
* The general case follows by the perturbation of `EFXTwoTypes.lean`.
-/

open Finset Function

namespace Applied.Economics

variable {G : Type*} [DecidableEq G]

/-- An agent with valuation `u` who holds the bundle `B` does not strongly envy the bundle `T`:
`T` with any one good removed is worth at most `B`. -/
def NoSE (u : G → ℝ) (B T : Finset G) : Prop :=
  ∀ h ∈ T, ∑ x ∈ T.erase h, u x ≤ ∑ x ∈ B, u x

/-- `(X1, X2, X3)` is a partition of all goods: every good lies in exactly one of the sets. -/
def IsPart3 (X1 X2 X3 : Finset G) : Prop :=
  ∀ x, (x ∈ X1 ∧ x ∉ X2 ∧ x ∉ X3) ∨ (x ∉ X1 ∧ x ∈ X2 ∧ x ∉ X3) ∨ (x ∉ X1 ∧ x ∉ X2 ∧ x ∈ X3)

/-- The bundles `(A, B, C)` form a complete allocation to the agents with valuations `a`, `b`,
`c` (in this order) that is EFX in the strong form. -/
def EFX3 (a b c : G → ℝ) (A B C : Finset G) : Prop :=
  IsPart3 A B C ∧ NoSE a A B ∧ NoSE a A C ∧ NoSE b B A ∧ NoSE b B C ∧ NoSE c C A ∧ NoSE c C B

/-- The invariant: `(X1, X2, X3)` is a partition, `X1` and `X2` are both EFX-feasible for the
agent with valuation `a`, and `X3` is EFX-feasible for the agent with valuation `b` or for the
agent with valuation `c`. -/
def Inv (a b c : G → ℝ) (X1 X2 X3 : Finset G) : Prop :=
  IsPart3 X1 X2 X3 ∧ NoSE a X1 X2 ∧ NoSE a X1 X3 ∧ NoSE a X2 X1 ∧ NoSE a X2 X3 ∧
    ((NoSE b X3 X1 ∧ NoSE b X3 X2) ∨ (NoSE c X3 X1 ∧ NoSE c X3 X2))

section basic

variable {u : G → ℝ} {B B' T T' : Finset G}

omit [DecidableEq G] in
lemma IsPart3.swap12 {X1 X2 X3 : Finset G} (h : IsPart3 X1 X2 X3) : IsPart3 X2 X1 X3 :=
  fun x => by have := h x; tauto

omit [DecidableEq G] in
lemma IsPart3.swap23 {X1 X2 X3 : Finset G} (h : IsPart3 X1 X2 X3) : IsPart3 X1 X3 X2 :=
  fun x => by have := h x; tauto

lemma NoSE.of_le (hu : ∀ g, 0 ≤ u g) (h : ∑ x ∈ T, u x ≤ ∑ x ∈ B, u x) : NoSE u B T :=
  fun g _ => (sum_le_sum_of_subset_of_nonneg (erase_subset g T) (fun x _ _ => hu x)).trans h

lemma NoSE.mono (h : NoSE u B T) (hB : ∑ x ∈ B, u x ≤ ∑ x ∈ B', u x) : NoSE u B' T :=
  fun g hg => (h g hg).trans hB

lemma NoSE.subset (hu : ∀ g, 0 ≤ u g) (h : NoSE u B T) (hT : T' ⊆ T) : NoSE u B T' :=
  fun g hg => (sum_le_sum_of_subset_of_nonneg (erase_subset_erase g hT)
    (fun x _ _ => hu x)).trans (h g (hT hg))

lemma lt_of_not_noSE (hu : ∀ g, 0 ≤ u g) (h : ¬ NoSE u B T) :
    ∑ x ∈ B, u x < ∑ x ∈ T, u x := by
  by_contra h'
  exact h (NoSE.of_le hu (not_lt.1 h'))

/-- A set worth more than `t` has a subset worth more than `t` all of whose proper subsets
obtained by removing one good are worth at most `t`. -/
lemma exists_min_subset (u : G → ℝ) (t : ℝ) (S : Finset G) (hS : t < ∑ x ∈ S, u x) :
    ∃ Z ⊆ S, t < ∑ x ∈ Z, u x ∧ ∀ h ∈ Z, ∑ x ∈ Z.erase h, u x ≤ t := by
  have hne' : (S.powerset.filter fun Z => t < ∑ x ∈ Z, u x).Nonempty := ⟨S, by simp [hS]⟩
  obtain ⟨Z, hZ, hZmin⟩ := exists_min_image _ card hne'
  simp only [mem_filter, mem_powerset] at hZ
  refine ⟨Z, hZ.1, hZ.2, fun h hh => ?_⟩
  by_contra hlt
  push Not at hlt
  have := hZmin (Z.erase h) (by simp [hlt, (erase_subset h Z).trans hZ.1])
  have := card_erase_lt_of_mem hh
  omega

/-- If neither `X1` nor `X2` is EFX-feasible for the valuation `u` in `(X1, X2, X3)`, then
`X3` with a suitable good removed is worth more than `X1` and more than `X2`
(Observation 7 of Akrami et al.). -/
lemma exists_good_of_not_feasible (hu : ∀ g, 0 ≤ u g) {X1 X2 X3 : Finset G}
    (h1 : ¬ (NoSE u X1 X2 ∧ NoSE u X1 X3)) (h2 : ¬ (NoSE u X2 X1 ∧ NoSE u X2 X3)) :
    ∃ g ∈ X3, ∑ x ∈ X1, u x < ∑ x ∈ X3.erase g, u x ∧
      ∑ x ∈ X2, u x < ∑ x ∈ X3.erase g, u x := by
  by_contra hno
  push Not at hno
  rcases le_total (∑ x ∈ X1, u x) (∑ x ∈ X2, u x) with h | h
  · refine h2 ⟨NoSE.of_le hu h, fun g hg => ?_⟩
    by_cases h' : ∑ x ∈ X1, u x < ∑ x ∈ X3.erase g, u x
    · exact hno g hg h'
    · exact (not_lt.1 h').trans h
  · refine h1 ⟨NoSE.of_le hu h, fun g hg => ?_⟩
    by_contra h'
    push Not at h'
    exact absurd (hno g hg h') (not_le.2 (lt_of_le_of_lt h h'))

end basic

/-- **Plaut–Roughgarden lemma for one valuation.** Let `u` be positive and let `p` assign the
goods in `S` to bundles indexed by `K`, each bundle worth at least `μ`. Then there is an
assignment `q` in which every bundle is still worth at least `μ` and no bundle, with one of
its goods removed, is worth more than another bundle. -/
lemma exists_pr {K : Type*} [Fintype K] [DecidableEq K] [Fintype G] (u : G → ℝ)
    (hu : ∀ g, 0 < u g) (S : Finset G) (p : G → K) (μ : ℝ)
    (hμ : ∀ k, μ ≤ ∑ x ∈ S with p x = k, u x) :
    ∃ q : G → K, (∀ k, μ ≤ ∑ x ∈ S with q x = k, u x) ∧
      ∀ i j, i ≠ j → ∀ g ∈ S, q g = j →
        ∑ x ∈ S with q x = j, u x - u g ≤ ∑ x ∈ S with q x = i, u x := by
  classical
  have hne : Nonempty {q : G → K // ∀ k, μ ≤ ∑ x ∈ S with q x = k, u x} := ⟨⟨p, hμ⟩⟩
  obtain ⟨⟨q, hq⟩, hmin⟩ := Finite.exists_min
    (fun q : {q : G → K // ∀ k, μ ≤ ∑ x ∈ S with q x = k, u x} =>
      ∑ k, (∑ x ∈ S with q.1 x = k, u x) ^ 2)
  refine ⟨q, hq, fun i j hij g hg hgj => ?_⟩
  by_contra hlt
  push Not at hlt
  set q' := Function.update q g i with hq'
  have hval : ∀ k, ∑ x ∈ S with q' x = k, u x =
      ∑ x ∈ S with q x = k, u x + (if i = k then u g else 0) - (if j = k then u g else 0) := by
    intro k
    rw [sum_filter, sum_filter, ← add_sum_erase _ _ hg, ← add_sum_erase S _ hg]
    have : ∑ x ∈ S.erase g, (if q' x = k then u x else 0) =
        ∑ x ∈ S.erase g, (if q x = k then u x else 0) :=
      sum_congr rfl (fun x hx => by rw [hq', update_of_ne (ne_of_mem_erase hx)])
    rw [this, hq', update_self, hgj]
    ring
  have hi' := hval i
  have hj' := hval j
  simp only [↓reduceIte, hij, Ne.symm hij, add_zero, sub_zero] at hi' hj'
  have hk' : ∀ k, k ≠ i → k ≠ j → ∑ x ∈ S with q' x = k, u x = ∑ x ∈ S with q x = k, u x := by
    intro k hki hkj
    simp only [hval k, Ne.symm hki, Ne.symm hkj, ↓reduceIte, add_zero, sub_zero]
  have hq'μ : ∀ k, μ ≤ ∑ x ∈ S with q' x = k, u x := by
    intro k
    by_cases hki : k = i
    · subst hki
      linarith [hq k, hu g]
    · by_cases hkj : k = j
      · subst hkj
        linarith [hq i]
      · rw [hk' k hki hkj]
        exact hq k
  have h1 := hmin ⟨q', hq'μ⟩
  simp only at h1
  have h2 : ∑ k, ((∑ x ∈ S with q' x = k, u x) ^ 2 - (∑ x ∈ S with q x = k, u x) ^ 2) =
      ((∑ x ∈ S with q' x = i, u x) ^ 2 - (∑ x ∈ S with q x = i, u x) ^ 2) +
      ((∑ x ∈ S with q' x = j, u x) ^ 2 - (∑ x ∈ S with q x = j, u x) ^ 2) :=
    Fintype.sum_eq_add i j hij (fun k hk => by rw [hk' k hk.1 hk.2]; ring)
  rw [sum_sub_distrib, hi', hj'] at h2
  nlinarith [mul_pos (hu g) (sub_pos.2 hlt)]

/-- The Plaut–Roughgarden lemma for partitions of all goods into three bundles. -/
lemma exists_pr3 [Fintype G] (u : G → ℝ) (hu : ∀ g, 0 < u g) {X1 X2 X3 : Finset G}
    (hP : IsPart3 X1 X2 X3) (μ : ℝ) (h1 : μ ≤ ∑ x ∈ X1, u x) (h2 : μ ≤ ∑ x ∈ X2, u x)
    (h3 : μ ≤ ∑ x ∈ X3, u x) :
    ∃ Y1 Y2 Y3, IsPart3 Y1 Y2 Y3 ∧ μ ≤ ∑ x ∈ Y1, u x ∧ μ ≤ ∑ x ∈ Y2, u x ∧
      μ ≤ ∑ x ∈ Y3, u x ∧ NoSE u Y1 Y2 ∧ NoSE u Y1 Y3 ∧ NoSE u Y2 Y1 ∧ NoSE u Y2 Y3 ∧
      NoSE u Y3 Y1 ∧ NoSE u Y3 Y2 := by
  set p : G → Fin 3 := fun x => if x ∈ X1 then 0 else if x ∈ X2 then 1 else 2 with hp
  have e1 : (univ.filter fun x => p x = 0) = X1 := by
    ext x
    have := hP x
    by_cases h1 : x ∈ X1 <;> by_cases h2 : x ∈ X2 <;> simp [hp, h1, h2]
  have e2 : (univ.filter fun x => p x = 1) = X2 := by
    ext x
    have := hP x
    by_cases h1 : x ∈ X1 <;> by_cases h2 : x ∈ X2 <;> simp [hp, h1, h2]
    tauto
  have e3 : (univ.filter fun x => p x = 2) = X3 := by
    ext x
    have := hP x
    by_cases h1 : x ∈ X1 <;> by_cases h2 : x ∈ X2 <;> simp [hp, h1, h2] <;> tauto
  have hall : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  obtain ⟨q, hq, hqe⟩ := exists_pr u hu univ p μ (fun k => by
    rcases hall k with rfl | rfl | rfl
    · rw [e1]; exact h1
    · rw [e2]; exact h2
    · rw [e3]; exact h3)
  have hno : ∀ i j : Fin 3, i ≠ j →
      NoSE u (univ.filter fun x => q x = i) (univ.filter fun x => q x = j) := by
    intro i j hij g hg
    rw [sum_erase_eq_sub hg]
    exact hqe i j hij g (mem_univ _) (mem_filter.1 hg).2
  refine ⟨univ.filter fun x => q x = 0, univ.filter fun x => q x = 1,
    univ.filter fun x => q x = 2, fun x => ?_, hq 0, hq 1, hq 2, hno 0 1 (by decide),
    hno 0 2 (by decide), hno 1 0 (by decide), hno 1 2 (by decide), hno 2 0 (by decide),
    hno 2 1 (by decide)⟩
  rcases hall (q x) with h | h | h <;> simp [h]

/-- The Plaut–Roughgarden lemma for two disjoint bundles. -/
lemma exists_pr2 [Fintype G] (u : G → ℝ) (hu : ∀ g, 0 < u g) {P Q : Finset G}
    (hPQ : Disjoint P Q) (μ : ℝ) (h1 : μ ≤ ∑ x ∈ P, u x) (h2 : μ ≤ ∑ x ∈ Q, u x) :
    ∃ Y Z, Disjoint Y Z ∧ Y ∪ Z = P ∪ Q ∧ μ ≤ ∑ x ∈ Y, u x ∧ μ ≤ ∑ x ∈ Z, u x ∧
      NoSE u Y Z ∧ NoSE u Z Y := by
  set p : G → Bool := fun x => decide (x ∈ P) with hp
  have e1 : ((P ∪ Q).filter fun x => p x = true) = P := by
    ext x
    simp only [hp, mem_filter, mem_union, decide_eq_true_eq]
    tauto
  have e2 : ((P ∪ Q).filter fun x => p x = false) = Q := by
    ext x
    have hd : x ∈ P → x ∉ Q := fun h => disjoint_left.1 hPQ h
    simp only [hp, mem_filter, mem_union, decide_eq_false_iff_not]
    tauto
  obtain ⟨q, hq, hqe⟩ := exists_pr u hu (P ∪ Q) p μ (fun k => by
    cases k
    · rw [e2]; exact h2
    · rw [e1]; exact h1)
  have hno : ∀ i j : Bool, i ≠ j →
      NoSE u ((P ∪ Q).filter fun x => q x = i) ((P ∪ Q).filter fun x => q x = j) := by
    intro i j hij g hg
    rw [sum_erase_eq_sub hg]
    exact hqe i j hij g (mem_filter.1 hg).1 (mem_filter.1 hg).2
  refine ⟨(P ∪ Q).filter fun x => q x = true, (P ∪ Q).filter fun x => q x = false, ?_, ?_,
    hq true, hq false, hno true false (by decide), hno false true (by decide)⟩
  · refine disjoint_left.2 (fun x hx hx' => ?_)
    rw [mem_filter] at hx hx'
    rw [hx.2] at hx'
    exact absurd hx'.2 (by decide)
  · ext x
    simp only [mem_union, mem_filter]
    cases q x <;> simp

/-- From any partition into three bundles, each worth at least `m` to the first agent, one
obtains a partition satisfying the invariant whose first two bundles are worth at least `m` to
the first agent: the first agent re-divides (`exists_pr3`), and the second agent's favourite
bundle is put in third place. -/
lemma exists_inv_of_part [Fintype G] (a b c : G → ℝ) (ha : ∀ g, 0 < a g) (hb : ∀ g, 0 ≤ b g)
    {Z1 Z2 Z3 : Finset G} (hP : IsPart3 Z1 Z2 Z3) (m : ℝ) (h1 : m ≤ ∑ x ∈ Z1, a x)
    (h2 : m ≤ ∑ x ∈ Z2, a x) (h3 : m ≤ ∑ x ∈ Z3, a x) :
    ∃ Y1 Y2 Y3, Inv a b c Y1 Y2 Y3 ∧ m ≤ ∑ x ∈ Y1, a x ∧ m ≤ ∑ x ∈ Y2, a x := by
  obtain ⟨W1, W2, W3, hW, m1, m2, m3, e12, e13, e21, e23, e31, e32⟩ :=
    exists_pr3 a ha hP m h1 h2 h3
  by_cases c3 : ∑ x ∈ W1, b x ≤ ∑ x ∈ W3, b x ∧ ∑ x ∈ W2, b x ≤ ∑ x ∈ W3, b x
  · exact ⟨W1, W2, W3, ⟨hW, e12, e13, e21, e23,
      Or.inl ⟨NoSE.of_le hb c3.1, NoSE.of_le hb c3.2⟩⟩, m1, m2⟩
  by_cases c2 : ∑ x ∈ W1, b x ≤ ∑ x ∈ W2, b x ∧ ∑ x ∈ W3, b x ≤ ∑ x ∈ W2, b x
  · exact ⟨W1, W3, W2, ⟨hW.swap23, e13, e12, e31, e32,
      Or.inl ⟨NoSE.of_le hb c2.1, NoSE.of_le hb c2.2⟩⟩, m1, m3⟩
  have c1 : ∑ x ∈ W2, b x ≤ ∑ x ∈ W1, b x ∧ ∑ x ∈ W3, b x ≤ ∑ x ∈ W1, b x := by
    rw [not_and_or, not_le, not_le] at c3 c2
    constructor
    · rcases c3 with h | h <;> rcases c2 with h' | h' <;> linarith
    · rcases c3 with h | h <;> rcases c2 with h' | h' <;> linarith
  exact ⟨W2, W3, W1, ⟨hW.swap12.swap23, e23, e21, e32, e31,
    Or.inl ⟨NoSE.of_le hb c1.1, NoSE.of_le hb c1.2⟩⟩, m2, m3⟩

/-- **Shrinking step.** Let `(U, P, Q)` be a partition, let `t` be a threshold with
`p0 ≤ t ≤ a U`, `p0 < a U` and `t < a P`, such that `U` with any good removed is worth at most
`t` to the first agent. Let `i` be the second or the third agent, and assume that `i` values
`Q` at least as much as `U` and does not strongly envy `P` when holding `Q`. Then there is a
partition satisfying the invariant whose first two bundles are worth more than `p0` to the
first agent. (`P` is replaced by a smallest subset worth more than `t`, the rest of `P` is
added to `Q`; if the first agent then strongly envies the third bundle, the first agent
re-divides.) -/
lemma exists_inv_shrink [Fintype G] (a b c i : G → ℝ) (ha : ∀ g, 0 < a g) (hb : ∀ g, 0 ≤ b g)
    (hi0 : ∀ g, 0 ≤ i g) (hi : i = b ∨ i = c) {U P Q : Finset G} (hP : IsPart3 U P Q)
    (p0 t : ℝ) (hp0U : p0 < ∑ x ∈ U, a x) (hp0t : p0 ≤ t) (htU : t ≤ ∑ x ∈ U, a x)
    (hUt : ∀ h ∈ U, ∑ x ∈ U.erase h, a x ≤ t) (htP : t < ∑ x ∈ P, a x)
    (hiU : ∑ x ∈ U, i x ≤ ∑ x ∈ Q, i x) (hiP : NoSE i Q P) :
    ∃ Y1 Y2 Y3, Inv a b c Y1 Y2 Y3 ∧ p0 < ∑ x ∈ Y1, a x ∧ p0 < ∑ x ∈ Y2, a x := by
  obtain ⟨P', hP'P, hP't, hP'min⟩ := exists_min_subset a t P htP
  set Q' := Q ∪ (P \ P') with hQ'
  have hPart : IsPart3 U P' Q' := by
    intro x
    have h1 := hP x
    have h2 : x ∈ P' → x ∈ P := fun h => hP'P h
    simp only [hQ', mem_union, mem_sdiff]
    tauto
  have hiQ : ∑ x ∈ Q, i x ≤ ∑ x ∈ Q', i x :=
    sum_le_sum_of_subset_of_nonneg subset_union_left (fun x _ _ => hi0 x)
  have h1 : NoSE a U P' := fun h hh => (hP'min h hh).trans htU
  have h2 : NoSE a P' U := fun h hh => (hUt h hh).trans hP't.le
  have h3 : NoSE i Q' U := (NoSE.of_le hi0 hiU).mono hiQ
  have h4 : NoSE i Q' P' := (hiP.subset hi0 hP'P).mono hiQ
  by_cases hfe : NoSE a U Q' ∧ NoSE a P' Q'
  · refine ⟨U, P', Q', ⟨hPart, h1, hfe.1, h2, hfe.2, ?_⟩, hp0U, lt_of_le_of_lt hp0t hP't⟩
    rcases hi with rfl | rfl
    · exact Or.inl ⟨h3, h4⟩
    · exact Or.inr ⟨h3, h4⟩
  · have ha0 : ∀ g, 0 ≤ a g := fun g => (ha g).le
    have hm : min (∑ x ∈ U, a x) (∑ x ∈ P', a x) ≤ ∑ x ∈ Q', a x := by
      rw [not_and_or] at hfe
      rcases hfe with h | h
      · exact (min_le_left _ _).trans (lt_of_not_noSE ha0 h).le
      · exact (min_le_right _ _).trans (lt_of_not_noSE ha0 h).le
    obtain ⟨Y1, Y2, Y3, hY, hY1, hY2⟩ := exists_inv_of_part a b c ha hb hPart
      (min (∑ x ∈ U, a x) (∑ x ∈ P', a x)) (min_le_left _ _) (min_le_right _ _) hm
    have hlt : p0 < min (∑ x ∈ U, a x) (∑ x ∈ P', a x) :=
      lt_min hp0U (lt_of_le_of_lt hp0t hP't)
    exact ⟨Y1, Y2, Y3, hY, lt_of_lt_of_le hlt hY1, lt_of_lt_of_le hlt hY2⟩

omit [DecidableEq G] in
lemma IsPart3.disjoint12 {X1 X2 X3 : Finset G} (h : IsPart3 X1 X2 X3) : Disjoint X1 X2 :=
  disjoint_left.2 (fun x h1 h2 => by have := h x; tauto)

/-- Moving the good `g` from the third bundle to the first one. -/
lemma IsPart3.move {X1 X2 X3 : Finset G} (hP : IsPart3 X1 X2 X3) {g : G} (hg : g ∈ X3) :
    IsPart3 X2 (insert g X1) (X3.erase g) := by
  intro x
  have h1 := hP x
  have h2 := hP g
  by_cases hx : x = g
  · subst hx
    simp only [mem_insert, mem_erase, true_or, ne_eq, not_true_eq_false, false_and]
    tauto
  · simp only [mem_insert, mem_erase, hx, false_or, ne_eq, not_false_eq_true, true_and]
    tauto

/-- **First case of the step.** If the agent `i` (second or third) values `X3` without `g` at
least as much as `X2` and as `X1` with `g`, the potential can be increased. -/
lemma exists_inv_caseA [Fintype G] (a b c i : G → ℝ) (ha : ∀ g, 0 < a g) (hb : ∀ g, 0 ≤ b g)
    (hi0 : ∀ g, 0 ≤ i g) (hi : i = b ∨ i = c) {X1 X2 X3 : Finset G} (hP : IsPart3 X1 X2 X3)
    (h12 : NoSE a X1 X2) (hlt : ∑ x ∈ X1, a x < ∑ x ∈ X2, a x) {g : G} (hg : g ∈ X3)
    (hi2 : ∑ x ∈ X2, i x ≤ ∑ x ∈ X3.erase g, i x)
    (hi1 : ∑ x ∈ insert g X1, i x ≤ ∑ x ∈ X3.erase g, i x) :
    ∃ Y1 Y2 Y3, Inv a b c Y1 Y2 Y3 ∧ ∑ x ∈ X1, a x < ∑ x ∈ Y1, a x ∧
      ∑ x ∈ X1, a x < ∑ x ∈ Y2, a x := by
  have hgX1 : g ∉ X1 := fun h => by have := hP g; tauto
  exact exists_inv_shrink a b c i ha hb hi0 hi (hP.move hg) _ _ hlt le_rfl hlt.le h12
    (by rw [sum_insert hgX1]; linarith [ha g]) hi2 (NoSE.of_le hi0 hi1)

/-- **Second case of the step.** If the second agent values both `X1` with `g` and `X3`
without `g` more than `X2`, and the third agent values `X1` and `X3` together more than twice
`X2`, then there is an EFX allocation or the potential can be increased. -/
lemma efx_or_inv_caseB [Fintype G] (a b c : G → ℝ) (ha : ∀ g, 0 < a g) (hb : ∀ g, 0 < b g)
    (hc : ∀ g, 0 ≤ c g) {X1 X2 X3 : Finset G} (hP : IsPart3 X1 X2 X3)
    (hlt : ∑ x ∈ X1, a x < ∑ x ∈ X2, a x) {g : G} (hg : g ∈ X3)
    (hb1 : ∑ x ∈ X2, b x < ∑ x ∈ insert g X1, b x)
    (hb3 : ∑ x ∈ X2, b x < ∑ x ∈ X3.erase g, b x)
    (hc2 : 2 * ∑ x ∈ X2, c x < ∑ x ∈ X1, c x + ∑ x ∈ X3, c x) :
    (∃ A B C, EFX3 a b c A B C) ∨ ∃ Y1 Y2 Y3, Inv a b c Y1 Y2 Y3 ∧
      ∑ x ∈ X1, a x < ∑ x ∈ Y1, a x ∧ ∑ x ∈ X1, a x < ∑ x ∈ Y2, a x := by
  have ha0 : ∀ g, 0 ≤ a g := fun g => (ha g).le
  have hb0 : ∀ g, 0 ≤ b g := fun g => (hb g).le
  have hgX1 : g ∉ X1 := fun h => by have := hP g; tauto
  have hmove := hP.move hg
  have hdisj : Disjoint (insert g X1) (X3.erase g) :=
    disjoint_left.2 (fun x h1 h2 => by have := hmove x; tauto)
  obtain ⟨Y, Z, hYZ, hU, hμY, hμZ, hYZe, hZYe⟩ := exists_pr2 b hb hdisj
    (min (∑ x ∈ insert g X1, b x) (∑ x ∈ X3.erase g, b x)) (min_le_left _ _) (min_le_right _ _)
  have hbY : ∑ x ∈ X2, b x < ∑ x ∈ Y, b x := lt_of_lt_of_le (lt_min hb1 hb3) hμY
  have hbZ : ∑ x ∈ X2, b x < ∑ x ∈ Z, b x := lt_of_lt_of_le (lt_min hb1 hb3) hμZ
  have hcsum : ∑ x ∈ Y, c x + ∑ x ∈ Z, c x = ∑ x ∈ X1, c x + ∑ x ∈ X3, c x := by
    rw [← sum_union hYZ, hU, sum_union hdisj, sum_insert hgX1, sum_erase_eq_sub hg]
    ring
  have hPart : IsPart3 X2 Y Z := by
    intro x
    have h1 := hmove x
    have h2 : x ∈ Y ∨ x ∈ Z ↔ x ∈ insert g X1 ∨ x ∈ X3.erase g := by
      rw [← mem_union, ← mem_union, hU]
    have h3 : x ∈ Y → x ∉ Z := fun h => disjoint_left.1 hYZ h
    tauto
  -- `Y2` goes to the second agent, `Y3` to the third agent
  have key : ∀ Y2 Y3 : Finset G, IsPart3 X2 Y2 Y3 → ∑ x ∈ X2, b x < ∑ x ∈ Y2, b x →
      NoSE b Y2 Y3 → ∑ x ∈ Y2, c x ≤ ∑ x ∈ Y3, c x → ∑ x ∈ X2, c x < ∑ x ∈ Y3, c x →
      (∃ A B C, EFX3 a b c A B C) ∨ ∃ Y1 Y2 Y3, Inv a b c Y1 Y2 Y3 ∧
        ∑ x ∈ X1, a x < ∑ x ∈ Y1, a x ∧ ∑ x ∈ X1, a x < ∑ x ∈ Y2, a x := by
    intro Y2 Y3 hPt hbY2 hb23 hc23 hcX
    have hUt : ∀ h ∈ X2, ∑ x ∈ X2.erase h, a x ≤ ∑ x ∈ X2, a x := fun h _ =>
      sum_le_sum_of_subset_of_nonneg (erase_subset h X2) (fun x _ _ => ha0 x)
    by_cases h2 : NoSE a X2 Y2
    · by_cases h3 : NoSE a X2 Y3
      · exact Or.inl ⟨X2, Y2, Y3, hPt, h2, h3, NoSE.of_le hb0 hbY2.le, hb23,
          NoSE.of_le hc hcX.le, NoSE.of_le hc hc23⟩
      · exact Or.inr (exists_inv_shrink a b c b ha hb0 hb0 (Or.inl rfl) hPt.swap23 _ _ hlt
          hlt.le le_rfl hUt (lt_of_not_noSE ha0 h3) hbY2.le hb23)
    · exact Or.inr (exists_inv_shrink a b c c ha hb0 hc (Or.inr rfl) hPt _ _ hlt
        hlt.le le_rfl hUt (lt_of_not_noSE ha0 h2) hcX.le (NoSE.of_le hc hc23))
  rcases le_total (∑ x ∈ Y, c x) (∑ x ∈ Z, c x) with h | h
  · exact key Y Z hPart hbY hYZe h (by linarith)
  · exact key Z Y hPart.swap23 hbZ hZYe h (by linarith)

/-- The step, when the second agent finds `X3` EFX-feasible and the first agent values `X1` at
most as much as `X2`. -/
lemma step_wlog [Fintype G] (a b c : G → ℝ) (ha : ∀ g, 0 < a g) (hb : ∀ g, 0 < b g)
    (hc : ∀ g, 0 < c g)
    (hnd : ∀ S T : Finset G, S ≠ T → ∑ x ∈ S, a x ≠ ∑ x ∈ T, a x) {X1 X2 X3 : Finset G}
    (hP : IsPart3 X1 X2 X3) (a12 : NoSE a X1 X2) (a13 : NoSE a X1 X3) (a21 : NoSE a X2 X1)
    (a23 : NoSE a X2 X3) (b31 : NoSE b X3 X1) (b32 : NoSE b X3 X2)
    (hle : ∑ x ∈ X1, a x ≤ ∑ x ∈ X2, a x) :
    (∃ A B C, EFX3 a b c A B C) ∨ ∃ Y1 Y2 Y3, Inv a b c Y1 Y2 Y3 ∧
      ∑ x ∈ X1, a x < ∑ x ∈ Y1, a x ∧ ∑ x ∈ X1, a x < ∑ x ∈ Y2, a x := by
  have ha0 : ∀ g, 0 ≤ a g := fun g => (ha g).le
  have hb0 : ∀ g, 0 ≤ b g := fun g => (hb g).le
  have hc0 : ∀ g, 0 ≤ c g := fun g => (hc g).le
  -- the third agent finds `X2` or `X1` EFX-feasible
  by_cases hc2 : NoSE c X2 X1 ∧ NoSE c X2 X3
  · exact Or.inl ⟨X1, X3, X2, hP.swap23, a13, a12, b31, b32, hc2.1, hc2.2⟩
  by_cases hc1 : NoSE c X1 X2 ∧ NoSE c X1 X3
  · exact Or.inl ⟨X2, X3, X1, hP.swap12.swap23, a23, a21, b32, b31, hc1.1, hc1.2⟩
  obtain ⟨gc, hgc, hgc1, hgc2⟩ := exists_good_of_not_feasible hc0 hc1 hc2
  have hcer : ∑ x ∈ X3.erase gc, c x ≤ ∑ x ∈ X3, c x :=
    sum_le_sum_of_subset_of_nonneg (erase_subset gc X3) (fun x _ _ => hc0 x)
  -- the second agent finds `X2` or `X1` EFX-feasible: the third agent takes `X3`
  by_cases hb2 : NoSE b X2 X1 ∧ NoSE b X2 X3
  · exact Or.inl ⟨X1, X2, X3, hP, a12, a13, hb2.1, hb2.2, NoSE.of_le hc0 (by linarith),
      NoSE.of_le hc0 (by linarith)⟩
  by_cases hb1 : NoSE b X1 X2 ∧ NoSE b X1 X3
  · exact Or.inl ⟨X2, X1, X3, hP.swap12, a21, a23, hb1.1, hb1.2, NoSE.of_le hc0 (by linarith),
      NoSE.of_le hc0 (by linarith)⟩
  obtain ⟨gb, hgb, hgb1, hgb2⟩ := exists_good_of_not_feasible hb0 hb1 hb2
  -- the first agent values `X1` strictly less than `X2`
  have hlt : ∑ x ∈ X1, a x < ∑ x ∈ X2, a x := by
    refine lt_of_le_of_ne hle (hnd _ _ (fun h12 => ?_))
    have hne : (X3.erase gb).Nonempty := by
      by_contra hem
      rw [not_nonempty_iff_eq_empty] at hem
      rw [hem, sum_empty] at hgb1
      exact absurd (sum_nonneg (fun x _ => hb0 x)) (not_le.2 hgb1)
    obtain ⟨h, hh⟩ := hne
    have h1 : a h ≤ ∑ x ∈ X3.erase gb, a x := single_le_sum (fun x _ => ha0 x) hh
    have h2 := a13 gb hgb
    have hX1 : X1.Nonempty := by
      by_contra hem
      rw [not_nonempty_iff_eq_empty] at hem
      rw [hem, sum_empty] at h2
      linarith [ha h]
    obtain ⟨x, hx⟩ := hX1
    have := hP x
    rw [← h12] at this
    tauto
  have hgbX1 : gb ∉ X1 := fun h => by have := hP gb; tauto
  have hgcX1 : gc ∉ X1 := fun h => by have := hP gc; tauto
  by_cases hAb : ∑ x ∈ insert gb X1, b x ≤ ∑ x ∈ X3.erase gb, b x
  · exact Or.inr (exists_inv_caseA a b c b ha hb0 hb0 (Or.inl rfl) hP a12 hlt hgb hgb2.le hAb)
  by_cases hAc : ∑ x ∈ insert gc X1, c x ≤ ∑ x ∈ X3.erase gc, c x
  · exact Or.inr (exists_inv_caseA a b c c ha hb0 hc0 (Or.inr rfl) hP a12 hlt hgc hgc2.le hAc)
  rw [not_le] at hAb hAc
  refine efx_or_inv_caseB a b c ha hb hc0 hP hlt hgb (hgb2.trans hAb) hgb2 ?_
  rw [sum_insert hgcX1] at hAc
  have := sum_erase_eq_sub (f := c) hgc
  linarith

lemma EFX3.swap {a b c : G → ℝ} {A B C : Finset G} (h : EFX3 a c b A B C) :
    EFX3 a b c A C B :=
  ⟨h.1.swap23, h.2.2.1, h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, h.2.2.2.1, h.2.2.2.2.1⟩

/-- **The step.** From a partition satisfying the invariant one obtains an EFX allocation, or
a partition satisfying the invariant with a larger potential `min (a X1) (a X2)`. -/
lemma step [Fintype G] (a b c : G → ℝ) (ha : ∀ g, 0 < a g) (hb : ∀ g, 0 < b g)
    (hc : ∀ g, 0 < c g)
    (hnd : ∀ S T : Finset G, S ≠ T → ∑ x ∈ S, a x ≠ ∑ x ∈ T, a x) {X1 X2 X3 : Finset G}
    (hI : Inv a b c X1 X2 X3) :
    (∃ A B C, EFX3 a b c A B C) ∨ ∃ Y1 Y2 Y3, Inv a b c Y1 Y2 Y3 ∧
      min (∑ x ∈ X1, a x) (∑ x ∈ X2, a x) < min (∑ x ∈ Y1, a x) (∑ x ∈ Y2, a x) := by
  -- the step when the agent with valuation `b'` finds `X3` EFX-feasible
  have hstep : ∀ b' c' : G → ℝ, (∀ g, 0 < b' g) → (∀ g, 0 < c' g) → NoSE b' X3 X1 →
      NoSE b' X3 X2 → (∃ A B C, EFX3 a b' c' A B C) ∨ ∃ Y1 Y2 Y3, Inv a b' c' Y1 Y2 Y3 ∧
        min (∑ x ∈ X1, a x) (∑ x ∈ X2, a x) < min (∑ x ∈ Y1, a x) (∑ x ∈ Y2, a x) := by
    intro b' c' hb' hc' b31 b32
    obtain ⟨hP, a12, a13, a21, a23, -⟩ := hI
    rcases le_total (∑ x ∈ X1, a x) (∑ x ∈ X2, a x) with hle | hle
    · rcases step_wlog a b' c' ha hb' hc' hnd hP a12 a13 a21 a23 b31 b32 hle with h | h
      · exact Or.inl h
      · obtain ⟨Y1, Y2, Y3, hY, h1, h2⟩ := h
        refine Or.inr ⟨Y1, Y2, Y3, hY, ?_⟩
        rw [min_eq_left hle]
        exact lt_min h1 h2
    · rcases step_wlog a b' c' ha hb' hc' hnd hP.swap12 a21 a23 a12 a13 b32 b31 hle with h | h
      · exact Or.inl h
      · obtain ⟨Y1, Y2, Y3, hY, h1, h2⟩ := h
        refine Or.inr ⟨Y1, Y2, Y3, hY, ?_⟩
        rw [min_eq_right hle]
        exact lt_min h1 h2
  rcases hI.2.2.2.2.2 with h | h
  · exact hstep b c hb hc h.1 h.2
  · rcases hstep c b hc hb h.1 h.2 with h' | h'
    · obtain ⟨A, B, C, hE⟩ := h'
      exact Or.inl ⟨A, C, B, hE.swap⟩
    · obtain ⟨Y1, Y2, Y3, hY, hlt⟩ := h'
      exact Or.inr ⟨Y1, Y2, Y3, ⟨hY.1, hY.2.1, hY.2.2.1, hY.2.2.2.1, hY.2.2.2.2.1,
        hY.2.2.2.2.2.symm⟩, hlt⟩

/-- **EFX for three agents, non-degenerate case.** If the three valuations are positive and
the first agent values different sets of goods differently, the goods can be divided into
three bundles `A`, `B`, `C` for the three agents such that the allocation is EFX. -/
theorem efx3_nondegenerate [Fintype G] (a b c : G → ℝ) (ha : ∀ g, 0 < a g)
    (hb : ∀ g, 0 < b g) (hc : ∀ g, 0 < c g)
    (hnd : ∀ S T : Finset G, S ≠ T → ∑ x ∈ S, a x ≠ ∑ x ∈ T, a x) :
    ∃ A B C, EFX3 a b c A B C := by
  have hb0 : ∀ g, 0 ≤ b g := fun g => (hb g).le
  obtain ⟨Z1, Z2, Z3, hZ, -, -⟩ := exists_inv_of_part a b c ha hb0
    (Z1 := univ) (Z2 := ∅) (Z3 := ∅) (fun x => by simp) 0
    (sum_nonneg (fun x _ => (ha x).le)) (by simp) (by simp)
  have hne : Nonempty {t : Finset G × Finset G × Finset G // Inv a b c t.1 t.2.1 t.2.2} :=
    ⟨⟨(Z1, Z2, Z3), hZ⟩⟩
  obtain ⟨⟨⟨X1, X2, X3⟩, hX⟩, hmax⟩ := Finite.exists_max
    (fun t : {t : Finset G × Finset G × Finset G // Inv a b c t.1 t.2.1 t.2.2} =>
      min (∑ x ∈ t.1.1, a x) (∑ x ∈ t.1.2.1, a x))
  rcases step a b c ha hb hc hnd hX with h | h
  · exact h
  · obtain ⟨Y1, Y2, Y3, hY, hlt⟩ := h
    exact absurd (hmax ⟨(Y1, Y2, Y3), hY⟩) (not_le.2 hlt)

end Applied.Economics
