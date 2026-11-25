import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Polynomial-time decision problems on bit strings

Mathlib has a Turing-machine notion of polynomial-time computability,
`Turing.TM2ComputableInPolyTime ea eb f`: a multi-stack machine (`Turing.FinTM2`) with finitely
many stacks, labels and internal states which, started with the encoding `ea a` on its input
stack, halts with `eb (f a)` on its output stack (all other stacks empty) after at most
`p (ea a).length` steps, for a fixed polynomial `p` with natural coefficients. This file turns
that into a class of languages and fixes concrete binary encodings.

* `PolyTimeComputable ea eb f`: a `Turing.TM2ComputableInPolyTime ea eb f` exists.
* `InP L`: the language `L : List Bool → Prop` is decidable in polynomial time: there is a total
  function `f : List Bool → Bool` with `f w = true ↔ L w` that is polynomial-time computable,
  the input being the bit string itself and the output a single bit.
* `DecidableInPolyTime enc L`: for a problem `L : α → Prop` on mathematical objects and an
  encoding `enc : α → List Bool`, the language `{enc a | L a}` is in `P`. Strings that encode no
  instance are no-instances.
* `inP_const`, `inP_univ`, `inP_empty`: the two trivial languages are in `P` (an explicit
  machine that empties its input stack and writes the answer, in `|w| + 1` steps).
* Encodings: `sd` (self-delimiting form of a bit string), `encNat`, `encInt`, `encRat`,
  `encList`, `encVec`, and `PrefixFree`, the property that makes concatenations of codes uniquely
  decodable; all the encodings are proved prefix-free, hence injective.

Nothing else is proved: Mathlib has no composition of machines, no closure properties and no
simulation results for `FinTM2`, so even "the complement of a language in `P` is in `P`" would
need a machine construction from scratch.
-/

open Turing Computability

namespace Applied.Complexity

/-! ### Polynomial time -/

/-- `f` is computable in polynomial time by a multi-stack Turing machine, with respect to the
encodings `ea` of inputs and `eb` of outputs as bit strings. Time is measured in the length of
the encoded input. -/
def PolyTimeComputable {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) :
    Prop :=
  Nonempty (TM2ComputableInPolyTime ea eb f)

/-- The language `L` over the alphabet `Bool` is in the class `P`: its characteristic function is
computable in polynomial time. The input is the string itself and the output is one bit. -/
def InP (L : List Bool → Prop) : Prop :=
  ∃ f : List Bool → Bool, (∀ w, f w = true ↔ L w) ∧ PolyTimeComputable id encodeBool f

/-- The decision problem `L` on objects of type `α`, with instances written as bit strings by
`enc`, is decidable in polynomial time: the language of encodings of yes-instances is in `P`.
This is only meaningful when `enc` is injective. -/
def DecidableInPolyTime {α : Type} (enc : α → List Bool) (L : α → Prop) : Prop :=
  InP fun w => ∃ a, enc a = w ∧ L a

/-- Membership in `P` only depends on the language up to pointwise equivalence. -/
theorem InP.congr {L L' : List Bool → Prop} (h : InP L) (hL : ∀ w, L w ↔ L' w) : InP L' := by
  obtain ⟨f, hf, hc⟩ := h
  exact ⟨f, fun w => (hf w).trans (hL w), hc⟩

/-- `DecidableInPolyTime enc` only depends on the problem up to pointwise equivalence. -/
theorem DecidableInPolyTime.congr {α : Type} {enc : α → List Bool} {L L' : α → Prop}
    (h : DecidableInPolyTime enc L) (hL : ∀ a, L a ↔ L' a) : DecidableInPolyTime enc L' :=
  InP.congr h fun _ => ⟨fun ⟨a, ha, h'⟩ => ⟨a, ha, (hL a).1 h'⟩,
    fun ⟨a, ha, h'⟩ => ⟨a, ha, (hL a).2 h'⟩⟩

/-! ### A machine for constant functions -/

/-- A one-stack machine that pops its whole input and then pushes the bit `c`. The internal state
is one bit recording whether the last pop found a symbol. -/
def constTM (c : Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := .pop () (fun _ o => o.isSome)
    (.branch id (.goto fun _ => ()) (.push () (fun _ => c) .halt))

/-- The run of `constTM c` on an input `l`: after `|l| + 1` steps it has halted with exactly
`[c]` on its stack. -/
theorem constTM_run (c : Bool) (l : List Bool) (v : Bool) :
    (flip bind (constTM c).step)^[l.length + 1]
        (some (⟨some (), v, fun _ => l⟩ : (constTM c).Cfg)) =
      some (⟨none, false, fun _ => [c]⟩ : (constTM c).Cfg) := by
  induction l generalizing v with
  | nil =>
    simp only [List.length_nil, zero_add, Function.iterate_one, flip, FinTM2.step]
    show some _ = some _
    congr 1
  | cons a t ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have : flip bind (constTM c).step (some (⟨some (), v, fun _ => a :: t⟩ : (constTM c).Cfg))
        = some (⟨some (), true, fun _ => t⟩ : (constTM c).Cfg) := by
      simp only [flip, FinTM2.step]
      show some _ = some _
      congr 1
    exact (congrArg _ this).trans (ih true)

/-- Every constant function with values in `Bool` is computable in polynomial time, for any
encoding `ea` of the inputs (in fact in `|ea a| + 1` steps). -/
noncomputable def constComputableInPolyTime {α : Type} (ea : α → List Bool) (c : Bool) :
    TM2ComputableInPolyTime ea encodeBool (fun _ : α => c) where
  tm := constTM c
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun a :=
    { steps := (ea a).length + 1
      evals_in_steps := by
        have h := constTM_run c (ea a) false
        have e1 : initList (constTM c) (List.map (Equiv.refl Bool).invFun (ea a)) =
            (⟨some (), false, fun _ => ea a⟩ : (constTM c).Cfg) := by
          simp [initList, constTM]
          rfl
        have e2 : Option.map (haltList (constTM c))
            (some (List.map (Equiv.refl Bool).invFun (encodeBool c))) =
            some (⟨none, false, fun _ => [c]⟩ : (constTM c).Cfg) := by
          simp [haltList, constTM, encodeBool]
          rfl
        rw [e1, e2]
        exact h
      steps_le_m := by simp }

/-- Constant Boolean functions are polynomial-time computable, for every input encoding. -/
theorem polyTimeComputable_const {α : Type} (ea : α → List Bool) (c : Bool) :
    PolyTimeComputable ea encodeBool (fun _ : α => c) :=
  ⟨constComputableInPolyTime ea c⟩

/-- A language that does not depend on its input is in `P`. -/
theorem inP_const (p : Prop) : InP fun _ => p := by
  classical
  exact ⟨fun _ => decide p, fun _ => by simp, polyTimeComputable_const id _⟩

/-- The language of all strings is in `P`. -/
theorem inP_univ : InP fun _ => True := inP_const True

/-- The empty language is in `P`. -/
theorem inP_empty : InP fun _ => False := inP_const False

/-- A problem whose answer is the same for every instance and every non-instance, namely "no",
is decidable in polynomial time. -/
theorem decidableInPolyTime_false {α : Type} (enc : α → List Bool) :
    DecidableInPolyTime enc fun _ => False :=
  inP_empty.congr fun _ => by simp

/-! ### Self-delimiting binary encodings -/

/-- A code is prefix-free in the strong sense used here: a code word followed by arbitrary bits
determines both the encoded object and the remaining bits. Concatenations of such codes can be
decoded uniquely. -/
def PrefixFree {α : Type*} (e : α → List Bool) : Prop :=
  ∀ a a' r r', e a ++ r = e a' ++ r' → a = a' ∧ r = r'

/-- A prefix-free code is injective. -/
theorem PrefixFree.injective {α : Type*} {e : α → List Bool} (h : PrefixFree e) :
    Function.Injective e := fun a a' hh =>
  (h a a' [] [] (by simpa using hh)).1

/-- Precomposing a prefix-free code with an injective map gives a prefix-free code. -/
theorem PrefixFree.comp {α β : Type*} {e : α → List Bool} (h : PrefixFree e) {g : β → α}
    (hg : Function.Injective g) : PrefixFree (e ∘ g) := fun _ _ r r' hh =>
  let ⟨h1, h2⟩ := h _ _ r r' hh
  ⟨hg h1, h2⟩

/-- Concatenating two prefix-free codes gives a prefix-free code for pairs. -/
theorem PrefixFree.prod {α β : Type*} {ea : α → List Bool} {eb : β → List Bool}
    (ha : PrefixFree ea) (hb : PrefixFree eb) :
    PrefixFree fun p : α × β => ea p.1 ++ eb p.2 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ r r' hh
  simp only [List.append_assoc] at hh
  obtain ⟨rfl, h2⟩ := ha _ _ _ _ hh
  obtain ⟨rfl, h3⟩ := hb _ _ _ _ h2
  exact ⟨rfl, h3⟩

/-- Self-delimiting form of a bit string: every bit `b` becomes the two bits `1 b`, and the
string is closed by a single `0`. The length is `2 |w| + 1`. -/
def sd : List Bool → List Bool
  | [] => [false]
  | b :: w => true :: b :: sd w

/-- The self-delimiting form of `w` has length `2 |w| + 1`. -/
@[simp] theorem length_sd (w : List Bool) : (sd w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [sd, ih]; ring

/-- The self-delimiting form of bit strings is a prefix-free code. -/
theorem prefixFree_sd : PrefixFree sd := by
  intro w
  induction w with
  | nil =>
    intro w' r r' h
    cases w' with
    | nil => simpa [sd] using h
    | cons b w' => simp [sd] at h
  | cons b w ih =>
    intro w' r r' h
    cases w' with
    | nil => simp [sd] at h
    | cons b' w' =>
      simp only [sd, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, h2⟩ := h
      obtain ⟨rfl, h3⟩ := ih _ _ _ h2
      exact ⟨rfl, h3⟩

/-- Binary encoding of a natural number, least significant bit first (Mathlib's `encodeNat`), in
self-delimiting form. Its length is `2 * (number of binary digits) + 1`. -/
def encNat (n : ℕ) : List Bool := sd (encodeNat n)

/-- The binary encoding of natural numbers is prefix-free. -/
theorem prefixFree_encNat : PrefixFree encNat :=
  prefixFree_sd.comp fun a b h => by
    have := congrArg decodeNat h
    simpa using this

/-- An integer: a sign bit (`1` for negative) followed by the absolute value. -/
def encInt (z : ℤ) : List Bool := decide (z < 0) :: encNat z.natAbs

/-- The encoding of integers is prefix-free. -/
theorem prefixFree_encInt : PrefixFree encInt := by
  intro a a' r r' h
  simp only [encInt, List.cons_append, List.cons.injEq, decide_eq_decide] at h
  obtain ⟨hs, h⟩ := h
  obtain ⟨hn, hr⟩ := prefixFree_encNat _ _ _ _ h
  refine ⟨?_, hr⟩
  omega

/-- A rational number: numerator and denominator of the reduced fraction, in binary. -/
def encRat (q : ℚ) : List Bool := encInt q.num ++ encNat q.den

/-- The encoding of rationals is prefix-free. -/
theorem prefixFree_encRat : PrefixFree encRat := by
  have h := (prefixFree_encInt.prod prefixFree_encNat).comp
    (g := fun q : ℚ => (q.num, q.den)) (fun a b hab => by
      simp only [Prod.mk.injEq] at hab
      exact Rat.ext hab.1 hab.2)
  exact h

/-- A list: every element is preceded by a `1`, and the list is closed by a `0`. -/
def encList {α : Type*} (e : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: l => true :: (e a ++ encList e l)

/-- Lists of code words of a prefix-free code form a prefix-free code. -/
theorem PrefixFree.list {α : Type*} {e : α → List Bool} (h : PrefixFree e) :
    PrefixFree (encList e) := by
  intro l
  induction l with
  | nil =>
    intro l' r r' hh
    cases l' with
    | nil => simpa [encList] using hh
    | cons b l' => simp [encList] at hh
  | cons b l ih =>
    intro l' r r' hh
    cases l' with
    | nil => simp [encList] at hh
    | cons b' l' =>
      simp only [encList, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at hh
      obtain ⟨rfl, h2⟩ := h _ _ _ _ hh
      obtain ⟨rfl, h3⟩ := ih _ _ _ h2
      exact ⟨rfl, h3⟩

/-- A vector `Fin n → α`, encoded as the list of its entries. -/
def encVec {α : Type*} {n : ℕ} (e : α → List Bool) (f : Fin n → α) : List Bool :=
  encList e (List.ofFn f)

/-- Vectors `Fin n → α` of code words of a prefix-free code form a prefix-free code. -/
theorem PrefixFree.vec {α : Type*} {e : α → List Bool} (h : PrefixFree e) (n : ℕ) :
    PrefixFree (encVec e : (Fin n → α) → List Bool) :=
  h.list.comp List.ofFn_injective

end Applied.Complexity
