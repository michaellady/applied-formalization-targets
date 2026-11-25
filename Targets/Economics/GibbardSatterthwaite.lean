import Applied.Economics.GibbardSatterthwaite

/-!
# Gibbard–Satterthwaite theorem

- id: econ-gibbard-satterthwaite
- area: economics
- status: formalized
- source: A. Gibbard, "Manipulation of voting schemes: a general result", Econometrica 41 (1973); M. A. Satterthwaite, "Strategy-proofness and Arrow's conditions", J. Econ. Theory 10 (1975) (theorem numbering to be confirmed); the reduction to Arrow's theorem follows the textbook route (e.g. N. Nisan et al., "Algorithmic Game Theory", Section 9.2.4, to be confirmed)
- used-in: voting theory, mechanism design without money, impossibility results for strategy-proof rules
- prerequisites: `Applied.Economics.Arrow` (Arrow's theorem for strict preferences); Mathlib has no social choice theory
- formalized-elsewhere: atlas-lean `MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean` :: `gibbard_satterthwaite` (onto and strategy-proof, as here; equivalent); econcslib-bei `EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean` (resolute, unanimous, set-valued rules; equivalent by the standard reduction, not formalized); elazarg/GameTheory `GameTheory/Core/GibbardSatterthwaite.lean` :: `impossibility`. Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Let `V` be a finite set of voters and `X` a set of at least three
alternatives. (The Lean statement does not require `X` to be finite, but for infinite `X` its
hypotheses cannot all hold, so the result has content only for finite `X`; see below.) A profile gives every voter a strict linear order on `X`
(`(P i).lt x y`: voter `i` ranks `y` above `x`). A social choice function `f` maps every
profile to an alternative. Suppose `f` is

* strategy-proof (`StrategyProof f`): for every profile `P`, voter `i` and linear order `r`,
  voter `i` does not rank `f (P with i's order replaced by r)` strictly above `f P` in the
  order `P i`; and
* onto (`Function.Surjective f`): every alternative is the outcome at some profile.

Then (`gibbard_satterthwaite`) some voter `d` is a dictator (`IsDictatorial f d`): for every
profile `P`, no alternative is ranked by `d` strictly above `f P`.

Also proved: a rule that depends only on voter `d`'s report and always picks a `d`-best
alternative is strategy-proof (`strategyProof_of_dictatorial`).

Differences from textbook statements and edge cases. Preferences are strict (linear orders)
and the domain is all profiles, as in the textbook version. The classical hypothesis "the
range of `f` has at least three elements" is replaced by the stronger "`f` is onto and `X` has
at least three elements"; the range version follows by restricting `X` to the range only when
preferences are restricted accordingly, which is not done here. For infinite `X` the theorem is vacuous: some profile gives the would-be dictator an order with
no best element, where no outcome can satisfy the dictatorship condition, so no rule is both
strategy-proof and onto in the sense required. In that case a
voter's order need not have a best element, and "dictator" means that nothing is ranked above
the outcome by `d` (so the outcome is `d`'s maximum, which must then exist at every profile).
With no voters there is a single profile, so `f` cannot be onto and the theorem is vacuous.
`StrategyProof` is stated with `Function.update` using classical decidable equality on `V`.

Not covered: weak preferences (indifference), restricted domains (single-peaked etc.),
randomised rules (Gibbard 1977), infinitely many voters.
-/

namespace Targets.Economics

alias gibbard_satterthwaite := Applied.Economics.GibbardSatterthwaite.gibbard_satterthwaite

alias strategyProof_of_dictatorial :=
  Applied.Economics.GibbardSatterthwaite.strategyProof_of_dictatorial

end Targets.Economics
