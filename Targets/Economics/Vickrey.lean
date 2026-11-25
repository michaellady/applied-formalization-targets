import Applied.Economics.Vickrey

/-!
# Truthfulness of the second-price (Vickrey) auction

- id: econ-vickrey-truthful
- area: economics
- status: formalized
- source: W. Vickrey, "Counterspeculation, auctions, and competitive sealed tenders", J. Finance 16 (1961); textbook form: T. Roughgarden, "Twenty Lectures on Algorithmic Game Theory", Lecture 2 (theorem number to be confirmed)
- used-in: auction design, ad auctions, mechanism design (base case of VCG)
- prerequisites: finite suprema only
- formalized-elsewhere: econcslib-bei `EconCSLib/MechanismDesign/Auction/Vickrey.lean` :: `mechanism_isDSIC`; elazarg/GameTheory `Mechanism/Auction.lean` (equivalent). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Finitely many, at least two, bidders submit real bids for one item. A
highest bidder wins and pays the highest bid among the other bidders; all others pay nothing
and get utility zero. Ties are broken by an arbitrary rule `win` that always selects a highest
bidder (`IsHighestBidRule win`); the theorems hold for every such rule. Then for every bidder
`i` with value `v i`, every profile of the others' bids and every alternative bid `x`, bidding
`v i` gives `i` at least the utility of bidding `x` (`vickrey_truthful`), and a truthful bidder
never has negative utility (`vickrey_truthful_utility_nonneg`). `vickrey_truthful_fin` is the
special case of bidders `Fin n` with `2 ≤ n`.

Not covered: the single-bidder case (no "other" bid exists; no reserve price is modelled), the
fact that truthful bidding is the *only* weakly dominant strategy, welfare maximisation of the
outcome, and randomised tie-breaking.
-/

namespace Targets.Economics

alias vickrey_truthful := Applied.Economics.vickrey_truthful

alias vickrey_truthful_utility_nonneg := Applied.Economics.vickrey_truthful_utility_nonneg

alias vickrey_truthful_fin := Applied.Economics.vickrey_truthful_fin

alias exists_isHighestBidRule := Applied.Economics.exists_isHighestBidRule

end Targets.Economics
