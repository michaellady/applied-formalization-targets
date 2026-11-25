import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic

/-!
# Arrow's impossibility theorem

Voters `V` (finitely many) and alternatives `X` (at least three; `X` may be infinite). Every
voter has a strict preference over `X`, a linear order; a *profile* is a function
`P : V → LinearOrder X`, and `(P i).lt x y` means that voter `i` ranks `y` strictly above `x`.
A *social welfare function* `F` maps every profile to a linear order on `X` (unrestricted
domain; the social ranking is strict).

* `Unanimity F` (weak Pareto): if every voter ranks `y` above `x`, so does society.
* `IIA F` (independence of irrelevant alternatives): if two profiles agree, voter by voter, on
  how `x` and `y` compare, then society compares `x` and `y` in the same way in both.
* `IsDictator F d`: whenever voter `d` ranks `y` above `x`, so does society.

`arrow`: a social welfare function for finitely many voters and at least three alternatives
that satisfies unanimity and IIA has a dictator. `dictator_unique` shows the dictator is
unique (when there are at least two alternatives), and `dictator_unanimity`, `dictator_iia`
that a dictatorship (the projection to a voter) does satisfy the two axioms.

Proof (decisive coalitions form an ultrafilter). For `x ≠ y` say that a set `S` of voters
*wins* `(x, y)` if society ranks `y` above `x` in every profile in which `S` is exactly the set
of voters who do. Using three alternatives, unanimity and IIA: a superset of a winning set for
`(x, y)` wins every other pair (`Wins.transfer`); if `S` does not win `(x, y)` then its
complement wins `(y, x)`; and the intersection of two winning sets wins. The empty set does not
win. So the winning sets form an ultrafilter on the finite set `V`, which is principal: some
singleton `{d}` wins, and `d` is a dictator.
-/

open Function

namespace Applied.Economics.Arrow

variable {V X : Type*}

/-- A preference profile: a strict linear preference for each voter. -/
abbrev Profile (V X : Type*) := V → LinearOrder X

/-- Unanimity (weak Pareto): if all voters rank `y` above `x`, so does society. -/
def Unanimity (F : Profile V X → LinearOrder X) : Prop :=
  ∀ (P : Profile V X) (x y : X), (∀ i, (P i).lt x y) → (F P).lt x y

/-- Independence of irrelevant alternatives: the social comparison of `x` and `y` depends only
on the voters' comparisons of `x` and `y`. -/
def IIA (F : Profile V X → LinearOrder X) : Prop :=
  ∀ (P P' : Profile V X) (x y : X), (∀ i, (P i).lt x y ↔ (P' i).lt x y) →
    ((F P).lt x y ↔ (F P').lt x y)

/-- Voter `d` is a dictator: society ranks `y` above `x` whenever `d` does. -/
def IsDictator (F : Profile V X → LinearOrder X) (d : V) : Prop :=
  ∀ (P : Profile V X) (x y : X), (P d).lt x y → (F P).lt x y

section Orders

private lemma lo_asymm (r : LinearOrder X) {x y : X} (h : r.lt x y) : ¬ r.lt y x := by
  let _ := r
  exact lt_asymm h

private lemma lo_trans (r : LinearOrder X) {x y z : X} (h1 : r.lt x y) (h2 : r.lt y z) :
    r.lt x z := by
  let _ := r
  exact lt_trans h1 h2

private lemma lo_total (r : LinearOrder X) {x y : X} (h : x ≠ y) : r.lt x y ∨ r.lt y x := by
  let _ := r
  exact lt_or_gt_of_ne h

private lemma lo_irrefl (r : LinearOrder X) (x : X) : ¬ r.lt x x := by
  let _ := r
  exact lt_irrefl x

private lemma lo_iff (r : LinearOrder X) {x y : X} {p : Prop} (h1 : p → r.lt x y)
    (h2 : ¬ p → r.lt y x) : r.lt x y ↔ p :=
  ⟨fun h => by_contra fun hp => lo_asymm r h (h2 hp), h1⟩

/-- The linear order that ranks by the score `s` and breaks ties by the order `base`. -/
@[reducible] private def scoreOrder (base : LinearOrder X) (s : X → ℕ) : LinearOrder X :=
  letI := base
  LinearOrder.lift' (fun u => toLex (s u, u)) fun u v h => by
    have := congrArg (fun p => (ofLex p).2) h
    simpa using this

private lemma scoreOrder_lt (base : LinearOrder X) (s : X → ℕ) {u v : X} (h : s u < s v) :
    (scoreOrder base s).lt u v := by
  let _ := base
  change toLex (s u, u) < toLex (s v, v)
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

open Classical in
/-- For distinct `x`, `y`, `z` and arbitrary scores `a i`, `b i`, `c i` there is a profile in
which every voter `i` ranks `x`, `y`, `z` according to these scores. -/
private lemma exists_profile (base : LinearOrder X) {x y z : X} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (a b c : V → ℕ) :
    ∃ Q : Profile V X, ∀ i,
      (a i < b i → (Q i).lt x y) ∧ (b i < a i → (Q i).lt y x) ∧
      (b i < c i → (Q i).lt y z) ∧ (c i < b i → (Q i).lt z y) ∧
      (a i < c i → (Q i).lt x z) ∧ (c i < a i → (Q i).lt z x) := by
  let s : V → X → ℕ := fun i u => if u = x then a i else if u = y then b i else if u = z then c i
    else 0
  have sx : ∀ i, s i x = a i := fun i => by simp [s]
  have sy : ∀ i, s i y = b i := fun i => by simp [s, hxy.symm]
  have sz : ∀ i, s i z = c i := fun i => by simp [s, hxz.symm, hyz.symm]
  refine ⟨fun i => scoreOrder base (s i), fun i => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> intro h <;>
    apply scoreOrder_lt <;> simp only [sx, sy, sz] <;> exact h

end Orders

/-- The set `S` of voters wins the pair `(x, y)`: society ranks `y` above `x` in every profile
in which `S` is exactly the set of voters ranking `y` above `x`. -/
private def Wins (F : Profile V X → LinearOrder X) (x y : X) (S : Set V) : Prop :=
  ∀ P : Profile V X, (∀ i, (P i).lt x y ↔ i ∈ S) → (F P).lt x y

section Proof

variable {F : Profile V X → LinearOrder X}

open Classical in
private lemma Wins.right (hU : Unanimity F) (hI : IIA F) (base : LinearOrder X) {x y z : X}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {S T : Set V} (hST : S ⊆ T)
    (h : Wins F x y S) : Wins F x z T := by
  intro P hP
  -- `S`: x < y < z;  `T \ S`: y < x < z;  outside `T`: y < z < x
  obtain ⟨Q, hQ⟩ := exists_profile base hxy hxz hyz
    (fun i => if i ∈ S then 1 else if i ∈ T then 2 else 3)
    (fun i => if i ∈ S then 2 else 1)
    (fun i => if i ∈ S then 3 else if i ∈ T then 3 else 2)
  have h1 : ∀ i, (Q i).lt x y ↔ i ∈ S := fun i =>
    lo_iff _ (fun hi => (hQ i).1 (by simp [hi]))
      (fun hi => (hQ i).2.1 (by split_ifs <;> omega))
  have h2 : ∀ i, (Q i).lt y z := fun i =>
    (hQ i).2.2.1 (by split_ifs <;> omega)
  have h3 : ∀ i, (Q i).lt x z ↔ i ∈ T := fun i =>
    lo_iff _ (fun hi => (hQ i).2.2.2.2.1 (by split_ifs <;> omega))
      (fun hi => (hQ i).2.2.2.2.2 (by
        have : i ∉ S := fun hS => hi (hST hS)
        simp [hi, this]))
  have h4 : (F Q).lt x z := lo_trans _ (h Q h1) (hU Q y z h2)
  exact (hI P Q x z fun i => (hP i).trans (h3 i).symm).2 h4

open Classical in
private lemma Wins.left (hU : Unanimity F) (hI : IIA F) (base : LinearOrder X) {x y z : X}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {S T : Set V} (hST : S ⊆ T)
    (h : Wins F x y S) : Wins F z y T := by
  intro P hP
  -- `S`: z < x < y;  `T \ S`: z < y < x;  outside `T`: y < z < x
  obtain ⟨Q, hQ⟩ := exists_profile base hxy hxz hyz
    (fun i => if i ∈ S then 2 else 3)
    (fun i => if i ∈ S then 3 else if i ∈ T then 2 else 1)
    (fun i => if i ∈ S then 1 else if i ∈ T then 1 else 2)
  have h1 : ∀ i, (Q i).lt x y ↔ i ∈ S := fun i =>
    lo_iff _ (fun hi => (hQ i).1 (by simp [hi]))
      (fun hi => (hQ i).2.1 (by split_ifs <;> omega))
  have h2 : ∀ i, (Q i).lt z x := fun i =>
    (hQ i).2.2.2.2.2 (by split_ifs <;> omega)
  have h3 : ∀ i, (Q i).lt z y ↔ i ∈ T := fun i =>
    lo_iff _ (fun hi => (hQ i).2.2.2.1 (by split_ifs <;> omega))
      (fun hi => (hQ i).2.2.1 (by
        have : i ∉ S := fun hS => hi (hST hS)
        simp [hi, this]))
  have h4 : (F Q).lt z y := lo_trans _ (hU Q z x h2) (h Q h1)
  exact (hI P Q z y fun i => (hP i).trans (h3 i).symm).2 h4

/-- A superset of a winning set for one pair wins every pair. -/
private lemma Wins.transfer (hU : Unanimity F) (hI : IIA F) (base : LinearOrder X)
    (hX : ∀ x y : X, ∃ z, z ≠ x ∧ z ≠ y) {x y u v : X} (hxy : x ≠ y) (huv : u ≠ v)
    {S T : Set V} (hST : S ⊆ T) (h : Wins F x y S) : Wins F u v T := by
  by_cases hux : u = x
  · subst hux
    by_cases hvy : v = y
    · subst hvy
      obtain ⟨z, hzu, hzv⟩ := hX u v
      have h1 : Wins F u z S := h.right hU hI base hxy hzu.symm hzv.symm subset_rfl
      exact h1.right hU hI base hzu.symm hxy hzv hST
    · exact h.right hU hI base hxy huv (Ne.symm hvy) hST
  · by_cases hvy : v = y
    · subst hvy
      exact h.left hU hI base hxy (Ne.symm hux) (Ne.symm huv) hST
    · by_cases huy : u = y
      · subst huy
        by_cases hvx : v = x
        · subst hvx
          obtain ⟨z, hzv, hzu⟩ := hX v u
          have h1 : Wins F v z S := h.right hU hI base hxy hzv.symm hzu.symm subset_rfl
          have h2 : Wins F u z S := h1.left hU hI base hzv.symm hxy hzu subset_rfl
          exact h2.right hU hI base hzu.symm huv hzv hST
        · have h1 : Wins F x v S := h.right hU hI base hxy (Ne.symm hvx) huv subset_rfl
          exact h1.left hU hI base (Ne.symm hvx) hxy (Ne.symm huv) hST
      · by_cases hvx : v = x
        · subst hvx
          have h1 : Wins F u y S := h.left hU hI base hxy (Ne.symm huv) (Ne.symm huy)
            subset_rfl
          exact h1.right hU hI base huy huv (Ne.symm hxy) hST
        · have h1 : Wins F x v S := h.right hU hI base hxy (Ne.symm hvx) (Ne.symm hvy)
            subset_rfl
          exact h1.left hU hI base (Ne.symm hvx) (Ne.symm hux) (Ne.symm huv) hST

private lemma Wins.compl (hI : IIA F) {x y : X} (hxy : x ≠ y) {S : Set V}
    (h : ¬ Wins F x y S) : Wins F y x Sᶜ := by
  rw [Wins, not_forall] at h
  obtain ⟨P, hP'⟩ := h
  obtain ⟨hP, hnot⟩ := Classical.not_imp.1 hP'
  intro P' hP'
  have hagree : ∀ i, (P i).lt x y ↔ (P' i).lt x y := by
    intro i
    rw [hP i]
    constructor
    · intro hi
      rcases lo_total (P' i) hxy with h' | h'
      · exact h'
      · exact absurd hi ((hP' i).1 h')
    · intro h'
      by_contra hi
      exact lo_asymm _ h' ((hP' i).2 hi)
  have hnot' : ¬ (F P').lt x y := fun h' => hnot ((hI P P' x y hagree).2 h')
  exact (lo_total (F P') hxy).resolve_left hnot'

open Classical in
private lemma Wins.inter (hI : IIA F) (base : LinearOrder X) {x y z : X}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {S T : Set V}
    (hS : Wins F x y S) (hT : Wins F y z T) : Wins F x z (S ∩ T) := by
  intro P hP
  -- `S ∩ T`: x < y < z;  `S \ T`: z < x < y;  `T \ S`: y < z < x;  neither: z < y < x
  obtain ⟨Q, hQ⟩ := exists_profile base hxy hxz hyz
    (fun i => if i ∈ S then (if i ∈ T then 1 else 2) else 3)
    (fun i => if i ∈ S then (if i ∈ T then 2 else 3) else (if i ∈ T then 1 else 2))
    (fun i => if i ∈ S then (if i ∈ T then 3 else 1) else (if i ∈ T then 2 else 1))
  have h1 : ∀ i, (Q i).lt x y ↔ i ∈ S := fun i =>
    lo_iff _ (fun hi => (hQ i).1 (by split_ifs <;> omega))
      (fun hi => (hQ i).2.1 (by split_ifs <;> omega))
  have h2 : ∀ i, (Q i).lt y z ↔ i ∈ T := fun i =>
    lo_iff _ (fun hi => (hQ i).2.2.1 (by split_ifs <;> omega))
      (fun hi => (hQ i).2.2.2.1 (by split_ifs <;> omega))
  have h3 : ∀ i, (Q i).lt x z ↔ i ∈ S ∩ T := fun i =>
    lo_iff _ (fun hi => (hQ i).2.2.2.2.1 (by
        obtain ⟨hi1, hi2⟩ := hi
        simp [hi1, hi2]))
      (fun hi => (hQ i).2.2.2.2.2 (by
        have hi' : i ∈ S → i ∉ T := fun h1 h2 => hi ⟨h1, h2⟩
        split_ifs <;> first | omega | (exfalso; tauto)))
  have h4 : (F Q).lt x z := lo_trans _ (hS Q h1) (hT Q h2)
  exact (hI P Q x z fun i => (hP i).trans (h3 i).symm).2 h4

private lemma not_wins_empty (hU : Unanimity F) (base : LinearOrder X) {x y : X}
    (hX : ∀ x y : X, ∃ z, z ≠ x ∧ z ≠ y) (hxy : x ≠ y) : ¬ Wins F x y (∅ : Set V) := by
  intro h
  obtain ⟨z, hzx, hzy⟩ := hX x y
  obtain ⟨Q, hQ⟩ := exists_profile (V := V) base hxy hzx.symm hzy.symm (fun _ => 1) (fun _ => 0)
    (fun _ => 2)
  have h1 : ∀ i, (Q i).lt y x := fun i => (hQ i).2.1 (by norm_num)
  have h2 : (F Q).lt x y := h Q fun i =>
    ⟨fun hi => absurd (h1 i) (lo_asymm _ hi), fun hi => absurd hi (Set.notMem_empty i)⟩
  exact lo_asymm _ h2 (hU Q y x h1)

end Proof

/-- **Arrow's impossibility theorem.** With finitely many voters and at least three
alternatives, every social welfare function (from profiles of linear orders to linear orders)
that satisfies unanimity and independence of irrelevant alternatives is dictatorial. -/
theorem arrow [Finite V] (hX : ∃ x y z : X, x ≠ y ∧ x ≠ z ∧ y ≠ z)
    (F : Profile V X → LinearOrder X) (hU : Unanimity F) (hI : IIA F) :
    ∃ d : V, IsDictator F d := by
  classical
  obtain ⟨base, -⟩ := exists_wellFoundedLT X
  obtain ⟨x₀, y₀, z₀, hxy₀, hxz₀, hyz₀⟩ := hX
  have hX' : ∀ x y : X, ∃ z, z ≠ x ∧ z ≠ y := by
    intro x y
    by_cases h1 : x₀ ≠ x ∧ x₀ ≠ y
    · exact ⟨x₀, h1⟩
    by_cases h2 : y₀ ≠ x ∧ y₀ ≠ y
    · exact ⟨y₀, h2⟩
    refine ⟨z₀, ?_, ?_⟩
    · rintro rfl
      by_cases h3 : x₀ = y
      · subst h3; exact h2 ⟨hyz₀, Ne.symm hxy₀⟩
      · exact h3 (by_contra fun h => h1 ⟨hxz₀, h⟩)
    · rintro rfl
      by_cases h3 : x₀ = x
      · subst h3; exact h2 ⟨Ne.symm hxy₀, hyz₀⟩
      · exact h1 ⟨h3, hxz₀⟩
  -- the winning sets for the pair `(x₀, y₀)` form an ultrafilter
  have hmono : ∀ {S T : Set V}, S ⊆ T → Wins F x₀ y₀ S → Wins F x₀ y₀ T := fun hST h =>
    h.transfer hU hI base hX' hxy₀ hxy₀ hST
  have hcompl : ∀ S : Set V, ¬ Wins F x₀ y₀ S → Wins F x₀ y₀ Sᶜ := fun S h =>
    (Wins.compl hI hxy₀ h).transfer hU hI base hX' (Ne.symm hxy₀) hxy₀ subset_rfl
  have hinter : ∀ S T : Set V, Wins F x₀ y₀ S → Wins F x₀ y₀ T → Wins F x₀ y₀ (S ∩ T) := by
    intro S T hS hT
    have hT' : Wins F y₀ z₀ T := hT.transfer hU hI base hX' hxy₀ hyz₀ subset_rfl
    exact (Wins.inter hI base hxy₀ hxz₀ hyz₀ hS hT').transfer hU hI base hX' hxz₀ hxy₀
      subset_rfl
  have hempty : ¬ Wins F x₀ y₀ (∅ : Set V) := not_wins_empty hU base hX' hxy₀
  -- on a finite set it is principal
  have hprinc : ∃ d : V, Wins F x₀ y₀ {d} := by
    by_contra hcon
    push Not at hcon
    cases nonempty_fintype V
    have hall : ∀ s : Finset V, Wins F x₀ y₀ (↑s : Set V)ᶜ := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have := hcompl ∅ hempty
        simpa using this
      | insert d s _ ih =>
        have h1 := hinter _ _ (hcompl {d} (hcon d)) ih
        have h2 : ({d} : Set V)ᶜ ∩ (↑s : Set V)ᶜ = (↑(insert d s) : Set V)ᶜ := by
          ext i; simp
        rwa [h2] at h1
    have := hall Finset.univ
    rw [Finset.coe_univ, Set.compl_univ] at this
    exact hempty this
  obtain ⟨d, hd⟩ := hprinc
  refine ⟨d, fun P x y hdxy => ?_⟩
  have hxy : x ≠ y := fun h => lo_irrefl (P d) y (h ▸ hdxy)
  have hS : Wins F x y {i | (P i).lt x y} :=
    hd.transfer hU hI base hX' hxy₀ hxy (Set.singleton_subset_iff.2 hdxy)
  exact hS P fun i => Iff.rfl

/-- A dictatorship (society adopts the ranking of voter `d`) satisfies unanimity. -/
theorem dictator_unanimity (d : V) : Unanimity (fun P : Profile V X => P d) :=
  fun _ _ _ h => h d

/-- A dictatorship satisfies independence of irrelevant alternatives. -/
theorem dictator_iia (d : V) : IIA (fun P : Profile V X => P d) :=
  fun _ _ _ _ h => h d

/-- With at least two alternatives, a social welfare function has at most one dictator. -/
theorem dictator_unique (hX : ∃ x y : X, x ≠ y) (F : Profile V X → LinearOrder X) {d d' : V}
    (hd : IsDictator F d) (hd' : IsDictator F d') : d = d' := by
  classical
  by_contra hne
  obtain ⟨base, -⟩ := exists_wellFoundedLT X
  obtain ⟨x, y, hxy⟩ := hX
  -- `d` ranks `y` above `x`, everybody else ranks `x` above `y`
  let P : Profile V X := fun i =>
    scoreOrder base fun u => if i = d then (if u = y then 1 else 0) else (if u = x then 1 else 0)
  have h1 : (P d).lt x y := scoreOrder_lt base _ (by simp [hxy])
  have h2 : (P d').lt y x := scoreOrder_lt base _ (by simp [Ne.symm hne, hxy.symm])
  exact lo_asymm _ (hd P x y h1) (hd' P y x h2)

end Applied.Economics.Arrow
