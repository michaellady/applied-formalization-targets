import Applied.Economics.EFXOrdered
import Targets.Economics.EFX

/-!
# EFX allocations exist when all agents rank the goods in the same order (additive case)

- id: econ-efx-common-ranking
- area: economics
- status: formalized
- source: B. Plaut, T. Roughgarden, "Almost envy-freeness with general valuations", SODA 2018 / SIAM J. Discrete Math. 34 (2020) (EFX for additive valuations with identical ordinal rankings of the goods, via a modified envy-cycle procedure; theorem number and the exact form of EFX used there to be confirmed)
- used-in: fair division of indivisible goods; partial result towards `Targets.Economics.EFXExists`
- prerequisites: finite sums, finite maxima
- statement-review: unreviewed

Informal statement. `n ≥ 1` agents have additive valuations `v i g ≥ 0` (real-valued) over
`m` indivisible goods. Suppose there is a ranking `r : Fin m → ℕ` of the goods such that for
every agent `i` and goods `g, g'`, `r g ≤ r g'` implies `v i g' ≤ v i g` (all agents weakly
prefer a better-ranked good; goods with equal rank must then have equal value to every agent).
Then there is a complete allocation `a : Fin m → Fin n` that is EFX in the strong form
`Targets.Economics.IsEFX`: no agent values another agent's bundle with *any* single good
removed (including goods they value at zero) more than their own bundle
(`efx_exists_common_ranking`).

The library theorem `Applied.Economics.efx_exists_of_common_ranking` is stated for any finite
nonempty type of agents, any finite type of goods and a ranking into any linear order.

Differences from the textbook statement. Plaut and Roughgarden state the identical-ranking
result as part of a paper on general (monotone) valuations; here only additive valuations are
treated. The ranking is given as a function into `ℕ` (equivalently, a common weak order that
each agent's valuation respects); this is the usual "identical ordering" hypothesis. The proof
is a non-algorithmic version of the envy-cycle argument: goods are added best-first, each to
an agent envied by nobody, and an unenvied agent is found in a welfare-maximising EFX
allocation of the goods added so far (rotating bundles along an envy cycle would raise
welfare). No algorithm or running time is formalized.

Not covered: non-additive valuations; chores or mixed goods and chores; any statement about
efficiency (for example Pareto optimality) of the allocation; the general case without a
common ranking, which remains open (`Targets.Economics.EFXExists`). This strictly generalises
`Targets.Economics.efx_exists_identical` (identical valuations admit a common ranking), but
that corollary is not re-derived in Lean here.
-/

namespace Targets.Economics

/-- EFX allocations exist for `n ≥ 1` agents with additive non-negative valuations that all
respect a common ranking `r` of the goods. -/
theorem efx_exists_common_ranking {n m : ℕ} (hn : 0 < n) (v : Fin n → Fin m → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (r : Fin m → ℕ) (hr : ∀ i g g', r g ≤ r g' → v i g' ≤ v i g) :
    ∃ a : Fin m → Fin n, IsEFX v a :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  Applied.Economics.efx_exists_of_common_ranking v hv r hr

alias efx_exists_of_common_ranking := Applied.Economics.efx_exists_of_common_ranking

end Targets.Economics
