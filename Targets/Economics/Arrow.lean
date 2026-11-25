import Applied.Economics.Arrow

/-!
# Arrow's impossibility theorem

- id: econ-arrow-impossibility
- area: economics
- status: formalized
- source: K. J. Arrow, "A difficulty in the concept of social welfare", J. Political Economy 58 (1950); K. J. Arrow, "Social Choice and Individual Values" (2nd ed. 1963), Chapter VIII (theorem numbering to be confirmed); the proof via decisive coalitions forming an ultrafilter follows A. P. Kirman, D. Sondermann, J. Econ. Theory 5 (1972) (attribution to be confirmed)
- used-in: social choice theory, voting rules, preference and rank aggregation
- prerequisites: linear orders; Mathlib has no social choice theory (no `Arrow`, `dictator` or `SocialChoice` declarations found)
- formalized-elsewhere: atlas-lean `MathlibExt/GameTheory/SocialChoice/Arrow.lean` :: `arrow_impossibility` (strict-order social welfare functions as here; equivalent); econcslib-bei `EconCSLib/SocialChoice/Voting/Arrow.lean` :: `arrow_impossibility` (social output a weak preference: a larger class of rules, so a stronger theorem than the one here); elazarg/GameTheory `GameTheory/Core/Arrow.lean`. Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Let `V` be a finite set of voters and `X` a set of at least three
alternatives (`∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z`; `X` may be infinite). A profile assigns to
every voter a strict linear order on `X` (`Profile V X = V → LinearOrder X`;
`(P i).lt x y` means voter `i` ranks `y` strictly above `x`). A social welfare function `F`
assigns to every profile a linear order on `X`. Suppose

* unanimity (weak Pareto, `Unanimity F`): if every voter ranks `y` above `x` then so does
  `F P`; and
* independence of irrelevant alternatives (`IIA F`): if profiles `P`, `P'` satisfy
  `(P i).lt x y ↔ (P' i).lt x y` for every voter `i`, then
  `(F P).lt x y ↔ (F P').lt x y`.

Then (`arrow`) there is a dictator: a voter `d` such that for every profile `P` and all
`x`, `y`, if `d` ranks `y` above `x` then so does `F P` (`IsDictator F d`).

Also proved: the dictator is unique if there are at least two alternatives
(`arrow_dictator_unique`), and the projection to a voter satisfies unanimity and IIA
(`dictator_unanimity`, `dictator_iia`), so the hypotheses are consistent.

Scope of this version. Individual and social preferences are strict (linear orders), and the
domain is all profiles of linear orders. Arrow's original statement allows indifference (weak
orders) for individuals and for society; the strict version here is the common textbook
variant and is neither a special case nor a generalisation of the weak-order one in an obvious
way (smaller domain, but also a smaller codomain). With no voters (`V` empty) unanimity fails
when `X` is nonempty, so the theorem is vacuous there. The case of exactly two alternatives
(where majority rule is a non-dictatorial example) is excluded by hypothesis.

Not covered: weak-order preferences, infinitely many voters (where non-principal ultrafilters
give non-dictatorial rules). The Gibbard–Satterthwaite theorem, derived from this one, is in
`Targets/Economics/GibbardSatterthwaite.lean`.
-/

namespace Targets.Economics

alias arrow := Applied.Economics.Arrow.arrow

alias arrow_dictator_unique := Applied.Economics.Arrow.dictator_unique

alias dictator_unanimity := Applied.Economics.Arrow.dictator_unanimity

alias dictator_iia := Applied.Economics.Arrow.dictator_iia

end Targets.Economics
