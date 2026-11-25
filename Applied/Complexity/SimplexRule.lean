import Applied.Complexity.PolyTime
import Applied.Optimization.Simplex

/-!
# Polynomial-time pivot rules

A pivot rule (`Applied.Optimization.PivotRule ℚ`) is a function of a rational linear program
and the list of bases visited so far. This file says when such a rule is computable in
polynomial time by a Turing machine.

* `RuleInput`: a rational program in standard form together with a history of bases.
* `RuleInput.encode`: its encoding as a bit string (numbers in binary); `encode_injective`.
* `encBasis B`: a basis as the string of its `n` membership bits.
* `bitSize P`: the length of the encoding of the program `P`; `add_le_bitSize`.
* `PivotRule.IsPolyTime R`: the map `(program, history) ↦ membership bits of the next basis` is
  polynomial-time computable.
-/

open Applied.Optimization

namespace Applied.Complexity

/-- The single bit `b` as a one-letter code word. -/
def encBit (b : Bool) : List Bool := [b]

/-- A single bit is a prefix-free code. -/
theorem prefixFree_encBit : PrefixFree encBit := by
  intro a a' r r' h
  simpa [encBit] using h

/-- An input of a pivot rule: the dimensions, a rational program in standard form and the list
of bases visited so far (current basis first). -/
structure RuleInput where
  /-- number of constraints -/
  m : ℕ
  /-- number of variables -/
  n : ℕ
  /-- the program -/
  P : StdLP ℚ m n
  /-- the bases visited so far, most recent first -/
  hist : List (Finset (Fin n))

/-- A set of column indices as its vector of membership bits. -/
def memVec {n : ℕ} (B : Finset (Fin n)) : Fin n → Bool := fun j => decide (j ∈ B)

/-- A set of column indices is determined by its vector of membership bits. -/
theorem memVec_injective {n : ℕ} : Function.Injective (memVec : Finset (Fin n) → Fin n → Bool) :=
  by
  intro B B' h
  ext j
  have := congrFun h j
  simpa [memVec] using this

/-- A basis written as its `n` membership bits (bit `j` is `1` iff `j` is in the basis). -/
def encBasis {n : ℕ} (B : Finset (Fin n)) : List Bool := List.ofFn (memVec B)

/-- The bit string of a rule input: `m` and `n` in binary; the entries of `A` row by row, then
`b`, then `c`, each rational as numerator and denominator in binary; then the history, each
basis as its membership bits. All parts are self-delimiting (see `encNat`, `encRat`, `encVec`,
`encList`). The length is linear in the total number of binary digits of the data. -/
def RuleInput.encode (I : RuleInput) : List Bool :=
  encNat I.m ++ (encNat I.n ++ (encVec (encVec encRat) (fun i j => I.P.A i j) ++
    (encVec encRat I.P.b ++ (encVec encRat I.P.c ++
      encList (encVec encBit) (I.hist.map memVec)))))

/-- Distinct inputs (program and history) have distinct encodings. -/
theorem RuleInput.encode_injective : Function.Injective RuleInput.encode := by
  rintro ⟨m, n, ⟨A, b, c⟩, h⟩ ⟨m', n', ⟨A', b', c'⟩, h'⟩ heq
  simp only [RuleInput.encode] at heq
  obtain ⟨rfl, h1⟩ := prefixFree_encNat _ _ _ _ heq
  obtain ⟨rfl, h2⟩ := prefixFree_encNat _ _ _ _ h1
  obtain ⟨hA, h3⟩ := (prefixFree_encRat.vec n).vec m _ _ _ _ h2
  obtain ⟨rfl, h4⟩ := prefixFree_encRat.vec m _ _ _ _ h3
  obtain ⟨rfl, h5⟩ := prefixFree_encRat.vec n _ _ _ _ h4
  have h6 := (prefixFree_encBit.vec n).list.injective h5
  have h7 : h = h' := List.map_injective_iff.2 memVec_injective h6
  have hA' : A = A' := by
    ext i j
    exact congrFun (congrFun hA i) j
  subst h7 hA'
  rfl

/-- An encoded list is longer than the number of its entries. -/
theorem length_encList_ge {α : Type*} (e : α → List Bool) (l : List α) :
    l.length + 1 ≤ (encList e l).length := by
  induction l with
  | nil => simp [encList]
  | cons a l ih => simp only [encList, List.length_cons, List.length_append]; omega

/-- The bit size of a rational program: the length of its encoding (with empty history). -/
def bitSize {m n : ℕ} (P : StdLP ℚ m n) : ℕ := (RuleInput.encode ⟨m, n, P, []⟩).length

/-- The bit size is at least the number of constraints plus the number of variables. -/
theorem add_le_bitSize {m n : ℕ} (P : StdLP ℚ m n) : m + n ≤ bitSize P := by
  have h1 := length_encList_ge encRat (List.ofFn P.b)
  have h2 := length_encList_ge encRat (List.ofFn P.c)
  simp only [List.length_ofFn] at h1 h2
  simp only [bitSize, RuleInput.encode, encVec, List.length_append]
  omega

end Applied.Complexity

namespace Applied.Optimization.PivotRule

open Applied.Complexity

/-- The pivot rule `R` on rational programs is computable in polynomial time: a Turing machine
(Mathlib's `FinTM2`) maps the encoding of the program and of the history to the membership bits
of the next basis, in time polynomial in the length of the encoding. -/
def IsPolyTime (R : PivotRule ℚ) : Prop :=
  PolyTimeComputable RuleInput.encode (id : List Bool → List Bool)
    (fun I : RuleInput => encBasis (R I.m I.n I.P I.hist))

end Applied.Optimization.PivotRule
