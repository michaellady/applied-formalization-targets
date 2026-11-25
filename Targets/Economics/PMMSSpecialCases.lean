import Applied.Economics.PMMS
import Targets.Economics.PMMS

/-!
# PMMS allocations exist for two agents and for identical valuations (additive case)

- id: econ-pmms-two-agents-identical
- area: economics
- status: formalized
- source: I. Caragiannis, D. Kurokawa, H. Moulin, A. D. Procaccia, N. Shah, J. Wang, "The unreasonable fairness of maximum Nash welfare", EC 2016 / ACM Trans. Econ. Comput. 7(3) (2019) (PMMS; the two-agent case is the classical cut-and-choose argument). For identical valuations, existence via a leximin-type argument is folklore to our knowledge; a precise citation is to be confirmed
- used-in: partial results towards `Targets.Economics.PMMSExists`
- prerequisites: finite sums, finite maxima, finite minima
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md)
- statement-review: unreviewed

Informal statement. Agents have additive real valuations over `m` indivisible goods; PMMS is
`Targets.Economics.IsPMMS` (`Targets/Economics/PMMS.lean`).

* `pmms_exists_two`: for two agents with arbitrary additive real valuations `v : Fin 2 → Fin m →
  ℝ` (no sign condition), a complete PMMS allocation exists. Proof: agent `0` splits the goods by
  a split attaining their maximin share, agent `1` takes the part they value more.
* `pmms_exists_identical`: if `n ≥ 1` agents all have the same additive real valuation
  `u : Fin m → ℝ` (no sign condition), a complete PMMS allocation exists. Proof: an allocation
  minimising the sum over agents of the squared bundle values is PMMS (if a pair violated PMMS,
  re-splitting their goods by a maximin split would lower the sum of squares).

The library theorems `Applied.Economics.pmms_exists_two` (any finite type of goods) and
`Applied.Economics.pmms_exists_identical` (any finite nonempty type of agents, any finite type of
goods) are the general versions.

Differences from the textbook statement. Usually stated for non-negative valuations; the proofs
here need no sign condition, so the theorems are stated without one (they include the
non-negative case). For two agents PMMS coincides with each agent receiving at least their
maximin share of all goods. The allocation for identical valuations minimises a sum of squares
rather than being leximin-optimal.

Not covered: three or more agents with different valuations (open, `PMMSExistsThree`,
`PMMSExists`); approximate PMMS guarantees for general `n`; non-additive valuations; chores.
-/

namespace Targets.Economics

/-- PMMS allocations exist for two agents with additive valuations. -/
theorem pmms_exists_two {m : ℕ} (v : Fin 2 → Fin m → ℝ) : ∃ a : Fin m → Fin 2, IsPMMS v a :=
  Applied.Economics.pmms_exists_two v

/-- PMMS allocations exist for `n ≥ 1` agents with identical additive valuations. -/
theorem pmms_exists_identical {n m : ℕ} (hn : 0 < n) (u : Fin m → ℝ) :
    ∃ a : Fin m → Fin n, IsPMMS (fun _ : Fin n => u) a :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  Applied.Economics.pmms_exists_identical u

end Targets.Economics
