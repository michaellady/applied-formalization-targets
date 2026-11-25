import Applied.Economics.Arrow
import Mathlib.Tactic

/-!
# The Gibbard–Satterthwaite theorem

Voters `V` (finitely many) and alternatives `X` (at least three; `X` may be infinite). As in
`Applied.Economics.Arrow`, a profile `P : V → LinearOrder X` gives every voter a strict
preference, and `(P i).lt x y` means that voter `i` ranks `y` strictly above `x`. A *social
choice function* `f` maps every profile to one alternative.

* `StrategyProof f`: no voter can obtain a strictly preferred outcome by reporting a different
  preference, whatever the others report.
* `IsDictatorial f d`: the outcome is always (weakly) the best alternative for voter `d`.

`gibbard_satterthwaite`: a strategy-proof and onto social choice function for finitely many
voters and at least three alternatives is dictatorial.

Proof (reduction to Arrow's theorem). Strategy-proofness gives monotonicity (`monotone`): if
the outcome at `P` is `a` and in `P'` nothing is ranked above `a` that was not already ranked
above `a` in `P`, the outcome at `P'` is `a`. With surjectivity this gives a Pareto property
(`pareto`). For a profile `P` and `x ≠ y` let `P` with `x`, `y` moved to the top be the
profile in which every voter keeps the internal ranking of `{x, y}` and of its complement but
ranks `x`, `y` above everything else; society ranks `y` above `x` when the outcome at that
profile is `y`. This is a linear order (transitivity uses three alternatives moved to the top)
and the resulting social welfare function satisfies unanimity and independence of irrelevant
alternatives, so it has a dictator by `Arrow.arrow`, who is then a dictator for `f`.
-/

open Function

namespace Applied.Economics.GibbardSatterthwaite

open Applied.Economics.Arrow

variable {V X : Type*}

open Classical in
/-- Strategy-proofness: for every profile `P`, voter `i` and alternative report `r`, voter `i`
(whose true preference is `P i`) does not strictly prefer the outcome after misreporting `r`
to the outcome under truthful reporting. -/
def StrategyProof (f : Profile V X → X) : Prop :=
  ∀ (P : Profile V X) (i : V) (r : LinearOrder X), ¬ (P i).lt (f P) (f (Function.update P i r))

/-- Voter `d` is a dictator for the social choice function `f`: no alternative is ranked by
`d` strictly above the outcome. -/
def IsDictatorial (f : Profile V X → X) (d : V) : Prop :=
  ∀ (P : Profile V X) (y : X), ¬ (P d).lt (f P) y

section Orders

private lemma lo_asymm (r : LinearOrder X) {x y : X} (h : r.lt x y) : ¬ r.lt y x := by
  let _ := r
  exact lt_asymm h

private lemma lo_total (r : LinearOrder X) {x y : X} (h : x ≠ y) : r.lt x y ∨ r.lt y x := by
  let _ := r
  exact lt_or_gt_of_ne h

private lemma lo_irrefl (r : LinearOrder X) (x : X) : ¬ r.lt x x := by
  let _ := r
  exact lt_irrefl x

/-- The linear order that ranks by the score `s` (higher is better) and breaks ties by `r`. -/
@[reducible] private def lift (r : LinearOrder X) (s : X → ℕ) : LinearOrder X :=
  letI := r
  LinearOrder.lift' (fun u => toLex (s u, u)) fun u v h => by
    have := congrArg (fun p => (ofLex p).2) h
    simpa using this

private lemma lift_lt_iff (r : LinearOrder X) (s : X → ℕ) {u v : X} :
    (lift r s).lt u v ↔ s u < s v ∨ (s u = s v ∧ r.lt u v) := by
  let _ := r
  change toLex (s u, u) < toLex (s v, v) ↔ _
  rw [Prod.Lex.toLex_lt_toLex]

/-- A linear order from a strict total order relation. -/
@[reducible] private noncomputable def ofStrict (R : X → X → Prop) (irr : ∀ x, ¬ R x x)
    (tr : ∀ x y z, R x y → R y z → R x z) (tot : ∀ x y, x ≠ y → R x y ∨ R y x) :
    LinearOrder X where
  le x y := x = y ∨ R x y
  lt := R
  le_refl x := Or.inl rfl
  le_trans x y z := by
    rintro (rfl | h1) (rfl | h2)
    · exact Or.inl rfl
    · exact Or.inr h2
    · exact Or.inr h1
    · exact Or.inr (tr _ _ _ h1 h2)
  lt_iff_le_not_ge x y := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (rfl | h')
      · exact irr _ h
      · exact irr _ (tr _ _ _ h h')
    · rintro ⟨rfl | h, h'⟩
      · exact absurd (Or.inl rfl) h'
      · exact h
  le_antisymm x y := by
    rintro (rfl | h1) (h | h2)
    · rfl
    · rfl
    · exact h.symm
    · exact absurd (tr _ _ _ h1 h2) (irr _)
  le_total x y := by
    by_cases h : x = y
    · exact Or.inl (Or.inl h)
    · exact (tot x y h).imp Or.inr Or.inr
  toDecidableLE := Classical.decRel _

end Orders

section Monotone

variable {f : Profile V X → X}

open Classical in
/-- Monotonicity, one voter: if the outcome is `a` and voter `i` changes to a preference in
which everything above `a` was already above `a`, the outcome stays `a`. -/
private lemma monotone_one (hsp : StrategyProof f) (P : Profile V X) (i : V)
    (r : LinearOrder X) (a : X) (ha : f P = a) (h : ∀ c, r.lt a c → (P i).lt a c) :
    f (Function.update P i r) = a := by
  have h1 := hsp P i r
  have h2 := hsp (Function.update P i r) i (P i)
  rw [Function.update_idem, Function.update_eq_self, Function.update_self] at h2
  rw [ha] at h1 h2
  by_contra hne
  rcases lo_total r hne with h3 | h3
  · exact h2 h3
  · exact h1 (h _ h3)

/-- **Monotonicity** (Maskin monotonicity of strategy-proof rules): if the outcome at `P` is
`a` and at `P'` every voter ranks above `a` only alternatives that were already above `a`,
then the outcome at `P'` is `a`. -/
private lemma monotone [Finite V] (hsp : StrategyProof f) (P P' : Profile V X) (a : X)
    (ha : f P = a) (h : ∀ i c, (P' i).lt a c → (P i).lt a c) : f P' = a := by
  classical
  have := Fintype.ofFinite V
  have key : ∀ T : Finset V, f (fun i => if i ∈ T then P' i else P i) = a := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using ha
    | insert j T hj ih =>
      have e : (fun i => if i ∈ insert j T then P' i else P i) =
          Function.update (fun i => if i ∈ T then P' i else P i) j (P' j) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
      rw [e]
      refine monotone_one hsp _ j (P' j) a ih fun c hc => ?_
      have e' : (if j ∈ T then P' j else P j) = P j := by simp [hj]
      rw [e']
      exact h j c hc
  simpa using key Finset.univ

open Classical in
/-- **Pareto property.** If every voter ranks `a` above `b`, the outcome is not `b`. -/
private lemma pareto [Finite V] (hsp : StrategyProof f) (honto : Surjective f)
    (P : Profile V X) {a b : X} (hab : a ≠ b) (h : ∀ i, (P i).lt b a) : f P ≠ b := by
  intro hb
  obtain ⟨P0, hP0⟩ := honto a
  set Q : Profile V X := fun i => lift (P0 i) (fun u => if u = a then 1 else 0) with hQ
  have hfQ : f Q = a := by
    refine monotone hsp P0 Q a hP0 fun i c hc => ?_
    rcases (lift_lt_iff (P0 i) _).1 hc with hc | ⟨-, hc⟩
    · exfalso
      simp only [↓reduceIte] at hc
      split_ifs at hc <;> omega
    · exact hc
  set s2 : X → ℕ := fun u => if u = a then 2 else if u = b then 1 else 0 with hs2
  set P' : Profile V X := fun i => lift (P i) s2 with hP'
  have hfa : f P' = a := by
    refine monotone hsp Q P' a hfQ fun i c hc => ?_
    exfalso
    rcases (lift_lt_iff (P i) s2).1 hc with hc | ⟨hc1, hc2⟩
    · simp only [hs2, ↓reduceIte] at hc
      split_ifs at hc <;> omega
    · have : c = a := by
        by_contra hca
        simp only [hs2, ↓reduceIte, hca] at hc1
        split_ifs at hc1; omega
      subst this
      exact lo_irrefl _ _ hc2
  have hfb : f P' = b := by
    refine monotone hsp P P' b hb fun i c hc => ?_
    rcases (lift_lt_iff (P i) s2).1 hc with hc | ⟨-, hc⟩
    · have : c = a := by
        by_contra hca
        simp only [hs2, hab.symm, ↓reduceIte, hca] at hc
        split_ifs at hc <;> omega
      subst this
      exact h i
    · exact hc
  exact hab (hfa.symm.trans hfb)

end Monotone

section Social

variable (f : Profile V X → X)

open Classical in
/-- The profile `P` with the alternatives in `S` moved to the top: every voter ranks the
members of `S` above all other alternatives and otherwise keeps their ranking. -/
@[reducible] private noncomputable def top (P : Profile V X) (S : Set X) : Profile V X :=
  fun i => lift (P i) (fun u => if u ∈ S then 1 else 0)

private lemma top_lt_iff (P : Profile V X) (S : Set X) (i : V) {u v : X} :
    (top P S i).lt u v ↔ (u ∉ S ∧ v ∈ S) ∨ ((u ∈ S ↔ v ∈ S) ∧ (P i).lt u v) := by
  classical
  unfold top
  rw [lift_lt_iff]
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]

variable {f}

/-- With `S` moved to the top, the outcome lies in `S`. -/
private lemma top_mem [Finite V] (hsp : StrategyProof f) (honto : Surjective f)
    (P : Profile V X) {S : Set X} {a : X} (ha : a ∈ S) : f (top P S) ∈ S := by
  by_contra hb
  have hab : a ≠ f (top P S) := fun h => hb (h ▸ ha)
  exact pareto hsp honto (top P S) hab (fun i => (top_lt_iff P S i).2 (Or.inl ⟨hb, ha⟩)) rfl

/-- If the outcome with `S` moved to the top is `a` and `a ∈ T ⊆ S`, the outcome with `T`
moved to the top is `a`. -/
private lemma top_subset [Finite V] (hsp : StrategyProof f) (P : Profile V X) {S T : Set X}
    (hTS : T ⊆ S) {a : X} (haT : a ∈ T) (ha : f (top P S) = a) : f (top P T) = a := by
  refine monotone hsp _ _ a ha fun i c hc => ?_
  rw [top_lt_iff] at hc ⊢
  rcases hc with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact absurd haT h1
  · have hcT : c ∈ T := h1.1 haT
    exact Or.inr ⟨⟨fun _ => hTS hcT, fun _ => hTS haT⟩, h2⟩

/-- Society ranks `y` above `x`: with `x`, `y` moved to the top, the outcome is `y`. -/
private def socialLt (f : Profile V X → X) (P : Profile V X) (x y : X) : Prop :=
  x ≠ y ∧ f (top P {x, y}) = y

private lemma socialLt_total [Finite V] (hsp : StrategyProof f) (honto : Surjective f)
    (P : Profile V X) (x y : X) (hxy : x ≠ y) : socialLt f P x y ∨ socialLt f P y x := by
  have hmem := top_mem hsp honto P (S := {x, y}) (a := x) (by simp)
  rcases hmem with h | h
  · right
    refine ⟨hxy.symm, ?_⟩
    rw [Set.pair_comm]
    exact h
  · exact Or.inl ⟨hxy, h⟩

private lemma socialLt_trans [Finite V] (hsp : StrategyProof f) (honto : Surjective f)
    (P : Profile V X) (x y z : X) (h1 : socialLt f P x y) (h2 : socialLt f P y z) :
    socialLt f P x z := by
  have hxz : x ≠ z := by
    rintro rfl
    have := h2.2
    rw [Set.pair_comm, h1.2] at this
    exact h1.1 this.symm
  refine ⟨hxz, ?_⟩
  have hmem := top_mem hsp honto P (S := {x, y, z}) (a := x) (by simp)
  rcases hmem with h | h | h
  · have := top_subset hsp P (S := {x, y, z}) (T := {x, y}) (by intro u; simp; tauto)
      (by simp) h
    rw [h1.2] at this
    exact absurd this.symm h1.1
  · have := top_subset hsp P (S := {x, y, z}) (T := {y, z}) (by intro u; simp; tauto)
      (by simp) h
    rw [h2.2] at this
    exact absurd this.symm h2.1
  · exact top_subset hsp P (S := {x, y, z}) (T := {x, z}) (by intro u; simp; tauto)
      (by simp) h

/-- The social welfare function induced by a strategy-proof onto social choice function. -/
@[reducible] private noncomputable def social [Finite V] (hsp : StrategyProof f) (honto : Surjective f)
    (P : Profile V X) : LinearOrder X :=
  ofStrict (socialLt f P) (fun _ h => h.1 rfl) (socialLt_trans hsp honto P)
    (socialLt_total hsp honto P)

end Social

/-- **Gibbard–Satterthwaite theorem.** With finitely many voters and at least three
alternatives, every strategy-proof social choice function that is onto is dictatorial. -/
theorem gibbard_satterthwaite [Finite V] (hX : ∃ x y z : X, x ≠ y ∧ x ≠ z ∧ y ≠ z)
    (f : Profile V X → X) (hsp : StrategyProof f) (honto : Surjective f) :
    ∃ d, IsDictatorial f d := by
  have hun : Unanimity (social hsp honto) := by
    intro P x y h
    change socialLt f P x y
    have hxy : x ≠ y := by
      rintro rfl
      obtain ⟨i⟩ : Nonempty V := by
        by_contra hV
        rw [not_nonempty_iff] at hV
        obtain ⟨a, b, -, hab, -, -⟩ := hX
        obtain ⟨Pa, hPa⟩ := honto a
        obtain ⟨Pb, hPb⟩ := honto b
        exact hab (by rw [← hPa, ← hPb, Subsingleton.elim Pa Pb])
      exact lo_irrefl _ _ (h i)
    rcases socialLt_total hsp honto P x y hxy with h' | h'
    · exact h'
    · exfalso
      refine pareto hsp honto (top P {y, x}) hxy.symm (fun i => ?_) h'.2
      rw [top_lt_iff]
      exact Or.inr ⟨by simp, h i⟩
  have hiia : IIA (social hsp honto) := by
    have key : ∀ (P P' : Profile V X) (x y : X), (∀ i, (P i).lt x y ↔ (P' i).lt x y) →
        socialLt f P x y → socialLt f P' x y := by
      intro P P' x y h hs
      refine ⟨hs.1, monotone hsp _ _ y hs.2 fun i c hc => ?_⟩
      rw [top_lt_iff] at hc ⊢
      rcases hc with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact absurd (by simp) h1
      · refine Or.inr ⟨h1, ?_⟩
        have hc : c = x ∨ c = y := h1.1 (by simp)
        rcases hc with rfl | rfl
        · by_contra hcon
          rcases lo_total (P i) hs.1 with h3 | h3
          · exact lo_asymm _ ((h i).1 h3) h2
          · exact hcon h3
        · exact absurd h2 (lo_irrefl _ _)
    intro P P' x y h
    exact ⟨key P P' x y h, key P' P x y fun i => (h i).symm⟩
  obtain ⟨d, hd⟩ := arrow hX (social hsp honto) hun hiia
  refine ⟨d, fun P y hy => ?_⟩
  have hs : socialLt f P (f P) y := hd P (f P) y hy
  have : f (top P {f P, y}) = f P := by
    refine monotone hsp P _ (f P) rfl fun i c hc => ?_
    rw [top_lt_iff] at hc
    rcases hc with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (by simp) h1
    · exact h2
  rw [hs.2] at this
  exact hs.1 this.symm

/-- A dictatorship is strategy-proof: if the outcome is always a best alternative of voter `d`
then no voter can gain by misreporting, provided the outcome depends only on `d`'s report. -/
theorem strategyProof_of_dictatorial (f : Profile V X → X) (d : V) (hd : IsDictatorial f d)
    (hdep : ∀ P P' : Profile V X, P d = P' d → f P = f P') : StrategyProof f := by
  classical
  intro P i r
  by_cases hi : i = d
  · subst hi
    exact hd P _
  · rw [hdep (Function.update P i r) P (Function.update_of_ne (Ne.symm hi) _ _)]
    exact lo_irrefl _ _

end Applied.Economics.GibbardSatterthwaite
