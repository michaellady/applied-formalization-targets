import Applied.Complexity.PolyTime

/-!
# Polynomial-time decidable languages (Turing machines) and binary encodings

- id: complexity-polytime-languages
- area: complexity
- status: formalized
- source: standard definition of the class P, e.g. M. Sipser, "Introduction to the Theory of Computation", Chapter 7 (to be confirmed); machine model and time bound from Mathlib, `Mathlib/Computability/TuringMachine/Computable.lean` (P. Spelier, D. van Gent)
- used-in: stating open problems about polynomial-time algorithms (`Targets/Complexity/SDPFeasibility.lean`, `Targets/Complexity/PlantedClique.lean`, `Targets/Optimization/PolynomialPivotRule.lean`)
- prerequisites: `Turing.FinTM2`, `Turing.TM2ComputableInPolyTime`, `Computability.encodeNat` (Mathlib)
- formalized-elsewhere: not checked
- statement-review: unreviewed

Informal statement. A language `L ⊆ {0,1}*` is in P (`InP L`) if some total function
`f : {0,1}* → {0,1}` with `f(w) = 1 ⟺ w ∈ L` is computed by a deterministic multi-stack Turing
machine in a number of steps bounded by a polynomial in `|w|`. A decision problem on
mathematical objects with a binary encoding `enc` is decidable in polynomial time
(`DecidableInPolyTime enc L`) if the language `{enc a | L a}` is in P.

What is proved.
* `inP_const`: for every proposition `p`, the language `{w | p}` is in P; in particular the
  full language and the empty language (`inP_univ`, `inP_empty`). The machine pops its input
  and pushes the answer, in `|w| + 1` steps (`constTM`, `constTM_run`). More generally every
  constant function to `Bool` is polynomial-time computable for every input encoding
  (`polyTimeComputable_const`).
* `InP.congr`: the class depends only on the language as a set.
* `decidableInPolyTime_false`: the problem with no yes-instances is decidable in polynomial
  time for every encoding.
* The encodings `encNat`, `encInt`, `encRat`, `encList e`, `encVec e` are prefix-free in the
  sense of `PrefixFree` (a code word followed by arbitrary bits determines the object and the
  rest), hence injective, when `e` is (`prefixFree_encNat`, `prefixFree_encInt`,
  `prefixFree_encRat`, `PrefixFree.list`, `PrefixFree.vec`, `PrefixFree.prod`,
  `PrefixFree.injective`).

Not proved, and what is missing in Mathlib: there is no construction of machines beyond the
identity machine (no composition, no simulation of one machine by another, no loops with
verified running time other than the one built here), so no closure property of P (complement,
union, composition with polynomial-time maps) and no non-trivial member of P is available.
Consequently nothing here shows that the class is the usual P beyond the definition itself.

Review notes (modelling choices to check).
* Machine model: Mathlib's `Turing.FinTM2`: finitely many stacks, finitely many labels and
  finitely many internal states; each label carries a statement built from push, peek, pop,
  load, branch, goto, halt. One step executes a whole statement (a bounded number of
  elementary operations), so step counts agree with elementary-operation counts up to a
  constant factor depending on the machine. Only the input stack's alphabet is required to be
  finite by `FinTM2`; other stacks may have infinite alphabets, but since the internal state
  set is finite each push statement can write only finitely many distinct symbols, so this
  gives no extra power (not formalized).
* Acceptance convention (Mathlib's `TM2OutputsInTime`): the machine starts with the input on
  the input stack (first symbol on top) and all other stacks empty; it must halt with exactly
  the output on the output stack, all other stacks empty and the internal state reset to the
  initial one.
* Time bound: a polynomial with natural-number coefficients evaluated at the length of the
  encoded input.
* `InP` uses the identity encoding of `List Bool` on the input side and `encodeBool` (a single
  bit) on the output side.
* `DecidableInPolyTime enc L` is the language of encodings of yes-instances; strings that are
  not encodings are no-instances, so the machine must also recognize well-formedness. It is
  meaningful only for injective `enc`; injectivity is not part of the definition and is proved
  separately for each encoding used.
* Number encoding: binary, least significant bit first (`Computability.encodeNat`), made
  self-delimiting by doubling (`sd`: each bit `b` becomes `1 b`, terminated by `0`). Integers:
  sign bit then absolute value. Rationals: reduced numerator and denominator. Lists: each
  element preceded by `1`, terminated by `0`. All lengths are linear in the usual bit length.
-/

namespace Targets.Complexity

alias inP_const := Applied.Complexity.inP_const

alias inP_univ := Applied.Complexity.inP_univ

alias inP_empty := Applied.Complexity.inP_empty

alias polyTimeComputable_const := Applied.Complexity.polyTimeComputable_const

alias decidableInPolyTime_false := Applied.Complexity.decidableInPolyTime_false

alias prefixFree_encRat := Applied.Complexity.prefixFree_encRat

end Targets.Complexity
