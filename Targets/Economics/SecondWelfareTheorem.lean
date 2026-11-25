import Applied.Economics.SecondWelfare

/-!
# Second fundamental theorem of welfare economics (exchange economy)

- id: econ-second-welfare-theorem
- area: economics
- status: formalized
- source: K. J. Arrow, "An extension of the basic theorems of classical welfare economics" (1951); G. Debreu, "Theory of Value" (1959); textbook form: Mas-Colell, Whinston, Green, "Microeconomic Theory" (1995), Section 16.D (proposition numbering to be confirmed)
- used-in: the case for lump-sum redistribution plus markets; decentralisation of efficient allocations; planning problems in macroeconomics
- prerequisites: Mathlib's geometric Hahn–Banach theorem (`geometric_hahn_banach_open_point`), quasi-concave functions, Fréchet–Riesz representation, interiors of convex sets in finite dimension; Mathlib has no welfare theorems (searched for `Pareto`, `Walras`, `welfare`)
- statement-review: unreviewed

Informal statement. Pure exchange, finitely many agents `i : ι`, commodity space a real inner
product space `E`, utilities `u i : E → ℝ`, no production. A reallocation `y` of an allocation
`x` is any `y : ι → E` with `∑ i, y i = ∑ i, x i`. Local non-satiation means: arbitrarily close
to every bundle there is a strictly better one. Quasi-concavity is Mathlib's `QuasiconcaveOn`:
upper contour sets `{y | r ≤ u i y}` are convex.

A. Consumption sets equal to the whole space; `E` complete (any Hilbert space, in particular
any finite-dimensional space). Assume every `u i` is continuous, quasi-concave on `E` and
locally non-satiated, and `x` is weakly Pareto efficient (no reallocation makes *every* agent
strictly better off). Then

* `second_welfare_quasiEquilibrium`: there is a price vector `p ≠ 0` such that for every agent
  `i` and bundle `y`, `u i y > u i (x i)` implies `⟪p, y⟫ ≥ ⟪p, x i⟫` (price quasi-equilibrium);
* `second_welfare_theorem`: there is `p ≠ 0` such that for every `i`, `x i` maximises `u i` on
  the budget set `{y | ⟪p, y⟫ ≤ ⟪p, x i⟫}`. This is the equilibrium-with-transfers statement:
  `second_welfare_theorem_transfers` restates it as the existence of `p ≠ 0` and redistributed
  endowments `ω'` with the same total as given endowments `ω` (assuming `∑ x = ∑ ω`) for which
  `x` is affordable, clears markets and is utility-maximising — the hypotheses of the first
  welfare theorem in this project. The redistributed endowments are simply `ω' = x`;
* `paretoEfficient_iff_exists_supporting_price`: with at least one agent, `x` is Pareto
  efficient (no reallocation makes all weakly and one strictly better off) iff such a
  supporting `p ≠ 0` exists;
* `weaklyParetoEfficient_iff_paretoEfficient`: with at least one agent, under these hypotheses
  weak and strong Pareto efficiency coincide.

In setting A no interiority or "cheaper point" assumption appears, because with consumption
set `E` the bundle `x i - p` is always available and strictly cheaper than `x i`.

B. Consumption sets `X i ⊆ E`; `E` finite-dimensional. Efficiency (`WeaklyParetoEfficientOn`)
is among allocations `y` with `y i ∈ X i` and the same total; local non-satiation
(`LocallyNonSatiatedOn`) is within `X i`.

* `second_welfare_quasiEquilibrium_on`: if `x i ∈ X i`, each `u i` is quasi-concave on `X i`
  (in Mathlib's sense, which makes the upper contour sets within `X i` convex) and locally
  non-satiated on `X i`, and `x` is weakly Pareto efficient, there is `p ≠ 0` with
  `⟪p, y⟫ ≥ ⟪p, x i⟫` for every `y ∈ X i` with `u i y > u i (x i)`. No continuity and no
  convexity of `X i` beyond that implied by quasi-concavity is assumed. This is only a
  quasi-equilibrium.
* `second_welfare_cheaper_point`: for one agent, if `X` is convex, `u` is continuous on `X`,
  the quasi-equilibrium condition holds at `x` and some `z ∈ X` has `⟪p, z⟫ < ⟪p, x⟫`, then
  `u y ≤ u x` for all `y ∈ X` with `⟪p, y⟫ ≤ ⟪p, x⟫`.
* `second_welfare_theorem_on`: if moreover every `X i` is convex, every `u i` is continuous on
  `X i` and every `x i` is in the interior of `X i`, there is `p ≠ 0` such that each `x i`
  maximises `u i` over `{y ∈ X i | ⟪p, y⟫ ≤ ⟪p, x i⟫}`.

Auxiliary result of independent use: `exists_inner_le_of_convex_of_notMem`, weak separation of
a point from an arbitrary non-empty convex set in a finite-dimensional inner product space.

Differences from textbook statements and edge cases. Preferences are represented by utility
functions. The hypothesis is weak Pareto efficiency, which is implied by the usual (strong)
notion when there is at least one agent (`ParetoEfficient.weakly`, proved for setting A), so
the theorems are, if anything, stronger. With no agents, weak Pareto efficiency is false (the
empty reallocation vacuously makes "every agent" better off) and the statements hold
vacuously; the content is for at least one agent. Prices are not shown to be non-negative (that needs
monotonicity, which is not assumed). In setting B the passage from quasi-equilibrium to
equilibrium is proved only under interiority of every `x i`, not under the weaker textbook
condition that each agent has a cheaper point in `X i` at the supporting prices (the one-agent
lemma `second_welfare_cheaper_point` covers that step once such a point is given).

Not covered: production, existence of Pareto-efficient allocations or of Walrasian equilibria,
infinite-dimensional commodity spaces with consumption sets (setting B is finite-dimensional),
economies with infinitely many agents.
-/

namespace Targets.Economics

alias second_welfare_quasiEquilibrium := Applied.Economics.exists_price_quasiEquilibrium

alias second_welfare_theorem := Applied.Economics.second_welfare_theorem

alias second_welfare_theorem_transfers := Applied.Economics.second_welfare_theorem_transfers

alias paretoEfficient_iff_exists_supporting_price :=
  Applied.Economics.paretoEfficient_iff_exists_supporting_price

alias weaklyParetoEfficient_iff_paretoEfficient :=
  Applied.Economics.weaklyParetoEfficient_iff_paretoEfficient

alias second_welfare_quasiEquilibrium_on := Applied.Economics.exists_price_quasiEquilibrium_on

alias second_welfare_cheaper_point := Applied.Economics.utility_le_of_cheaper_point_on

alias second_welfare_theorem_on := Applied.Economics.second_welfare_theorem_on

alias exists_inner_le_of_convex_of_notMem := Applied.Economics.exists_inner_le_of_convex_of_notMem

end Targets.Economics
