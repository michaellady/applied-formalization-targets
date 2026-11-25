import Applied.Economics.MulticommodityFlow

/-!
# Open (partial, routing side only): the Li–Li multiple-unicast network coding conjecture

- id: netinfo-li-li-routing-side
- area: network-information-theory
- status: open
- source: Z. Li, B. Li, "Network coding: the case of multiple unicast sessions", Allerton Conference 2004 (exact wording to be confirmed); see also N. Harvey, R. Kleinberg, A. Lehman, "On the capacity of information networks", IEEE Trans. Inform. Theory 52 (2006) (to be confirmed); PROBLEMS.md #342
- used-in: network information theory, limits of network coding in undirected networks
- prerequisites: for the routing side only finite sums; the coding side needs a definition of network codes (or an entropy-based characterisation) for undirected capacitated graphs, which neither Mathlib nor this project has
- statement-review: unreviewed

Informal statement of the conjecture. In an undirected capacitated network with several
unicast sessions (source–sink pairs), every rate vector achievable with network coding is
achievable by fractional routing, i.e. by a fractional multicommodity flow.

THIS FILE DOES NOT STATE THE CONJECTURE. It contains only the routing side: the definition of
the routable rate region (`Routable G σ r`, from `Applied/Economics/MulticommodityFlow.lean`),
and basic proved facts about it. No `Prop` named after the conjecture is defined, because the
network-coding rate region is not defined.

What is missing to state the conjecture. A faithful definition of "the rate vector `r` is
achievable with network coding in the undirected network `G`": this needs (i) how the capacity
of an undirected edge may be shared between its two directions (per use, or by time sharing);
(ii) block codes: message alphabets, block length, encoding functions at the vertices
respecting causality (the graph has cycles, so a time-expanded or otherwise ordered model is
needed), decoding at the sinks, and whether a vanishing error probability is allowed;
(iii) achievability as a limit over block lengths. The conjecture would then read
`∀ G σ r, CodingAchievable G σ r → Routable G σ r` (possibly with the closure of the regions).
These choices were not made here to avoid guessing.

Review notes (modelling choices of the routing side).
* Network: finite vertex type `V`; capacities `cap : V → V → ℝ`, symmetric and non-negative;
  `cap u v = 0` encodes "no edge". Parallel edges are merged (capacities add). Loops `cap u u`
  are allowed and irrelevant.
* Sessions: an arbitrary finite index type `K`; each session has a source and a different
  sink. Different sessions may share sources or sinks.
* Flow: session `i` has a non-negative flow `f i u v` in the direction `u → v` for every
  ordered pair, with conservation at every vertex other than its source and sink; the rate of
  the session is the net outflow at its source (no separate constraint at the sink: it follows
  from conservation and finiteness). Flow circulations are allowed.
* Capacity: for every unordered pair, the flows of all sessions in both directions add up to
  at most the capacity (`∑ i, (f i u v + f i v u) ≤ cap u v`); opposite flows do not cancel.
* Rates are a vector `r : K → ℝ` (not a single common rate); negative entries are not
  excluded by the definition but force a net inflow at the source.
* The rate region is the set of exactly achievable vectors (the rate constraint is an
  equality and negative entries are not excluded), so it is NOT closed under lowering a
  coordinate. A faithful statement of the conjecture would use the downward closure within
  the non-negative orthant, or an inequality in the rate constraint.

What is proved (`Applied/Economics/MulticommodityFlow.lean`): the zero vector is routable
(`routable_zero`); the routable region is convex and closed under scaling by `t ∈ [0, 1]`
(`convex_routable`, `routable_smul`); the rate of a session is at most the total capacity at
its source (`routable_rate_le_source_cap`).
-/

namespace Targets.Economics

alias routable_zero := Applied.Economics.MulticommodityFlow.routable_zero

alias convex_routable := Applied.Economics.MulticommodityFlow.convex_routable

alias routable_smul := Applied.Economics.MulticommodityFlow.Routable.smul

alias routable_rate_le_source_cap :=
  Applied.Economics.MulticommodityFlow.Routable.rate_le_source_cap

end Targets.Economics
