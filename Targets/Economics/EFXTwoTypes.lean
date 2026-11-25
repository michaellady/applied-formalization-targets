import Applied.Economics.EFXTwoTypes
import Targets.Economics.EFX

/-!
# EFX allocations exist when every agent has one of two additive valuations

- id: econ-efx-two-types
- area: economics
- status: formalized
- source: R. Mahara, "Existence of EFX for two additive valuations", arXiv:2008.08798 (2020; v4 2025, Theorem 1) / Discrete Appl. Math. 340 (2023) (journal details to be confirmed); the paper's Definition 2 is the strong form of EFX ("for all g ∈ A_j")
- used-in: partial result towards `Targets.Economics.EFXExists`
- prerequisites: finite sums, finite maxima, permutations of a finite type, binary expansions (`Finset.geomSum_injective`)
- statement-review: unreviewed

Informal statement. `n ≥ 1` agents have additive valuations `v i g ≥ 0` (real-valued) over
`m` indivisible goods, and there are two functions `va vb : Fin m → ℝ` such that for every
agent `i`, `v i = va` or `v i = vb` (agents are of one of two types; one type may be empty,
and `va = vb` is allowed). Then there is a complete allocation `a : Fin m → Fin n` that is EFX
in the strong form `Targets.Economics.IsEFX` (removing *any* single good, including goods
valued at zero) (`efx_exists_two_types`).

The library theorem `Applied.Economics.efx_exists_two_types` is stated for any finite
non-empty type of agents and finite type of goods.

Proof. If only one type occurs this is the identical-valuations case. Otherwise the
valuations are perturbed by `ε · 2^k` on the `k`-th good (as in Chaudhury–Garg–Mehlhorn and
in Mahara's paper), which makes all values positive and all subset sums of each valuation
pairwise different, and EFX for the perturbed valuations implies EFX for the original ones.
A partial EFX allocation of maximal welfare is then shown to be complete, following Mahara's
argument: champions and envy-cycle rotations exclude every configuration except the one in
which the poorest agent of each type is envied by nobody, and in that configuration the two
poorest agents exchange parts of their bundles (Mahara's Section 3.1) and then shrink their
bundles (Section 3.2) to a partial EFX allocation of larger welfare.

Differences from the textbook statement. Mahara's proof is algorithmic (a sequence of Pareto
improvements); here it is replaced by a maximal-welfare argument, so no algorithm or running
time is formalized. Mahara's general champion lemma (Chaudhury et al.) along envy paths is
replaced by one rotation lemma that combines envy edges with a single "champion" edge
(`exists_perm_of_forall_rel` applied to the whole set of agents), and Mahara's reduction step
in Section 3.2 (shrinking to a minimum preferred set relative to the second-poorest agent) is
replaced by shrinking to a subset of smallest size that the agent still prefers to their old
bundle; both changes are ours and are checked here, not claimed to appear in the paper.
Only additive valuations are treated, as in the paper.

Not covered: three or more types; two general (non-additive) monotone valuations; chores;
efficiency of the allocation; the general case (`Targets.Economics.EFXExists`, open).
-/

namespace Targets.Economics

/-- EFX allocations exist for `n ≥ 1` agents with additive non-negative valuations when every
agent's valuation is one of two functions `va`, `vb`. -/
theorem efx_exists_two_types {n m : ℕ} (hn : 0 < n) (v : Fin n → Fin m → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (va vb : Fin m → ℝ) (htype : ∀ i, v i = va ∨ v i = vb) :
    ∃ a : Fin m → Fin n, IsEFX v a :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  Applied.Economics.efx_exists_two_types v hv va vb htype

end Targets.Economics
