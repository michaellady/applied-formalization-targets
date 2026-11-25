import Applied.Economics.EFXThree
import Targets.Economics.EFXTwoTypes

/-!
# EFX allocations exist for three agents with additive valuations

- id: econ-efx-three-agents
- area: economics
- status: formalized
- source: B. R. Chaudhury, J. Garg, K. Mehlhorn, "EFX exists for three agents", EC 2020; arXiv:2002.05119v3, Theorem 20 (read at source); journal version J. ACM 71(1), 2024 (volume not verified at source); proof followed here: H. Akrami, N. Alon, B. R. Chaudhury, J. Garg, K. Mehlhorn, R. Mehta, arXiv:2205.07638v2, "EFX Allocations: Simplifications and Improvements", Section 4, Theorem 10 (read at source; the EC 2023 / journal version carries the title "EFX: a simpler approach and an (almost) optimal guarantee via rainbow cycle number", not verified at source)
- used-in: partial result towards `Targets.Economics.EFXExists`; it is the proposition `Targets.Economics.EFXExistsThree`
- prerequisites: finite sums, finite maxima and minima, binary expansions (through the perturbation lemma of `EFXTwoTypes.lean`)
- formalized-elsewhere: not found in the searches recorded in `PRIOR-ART-VERIFICATION-2.md` (two-agent EFX exists elsewhere; three agents does not)
- statement-review: unreviewed

Informal statement. Three agents have additive valuations `v i g ≥ 0` (real-valued) over `m`
indivisible goods (`m = 0` allowed). Then there is a complete allocation `a : Fin m → Fin 3`
that is EFX in the strong form `Targets.Economics.IsEFX`: for all agents `i`, `j` and every
good `g` in `j`'s bundle (including goods that `i` values at zero), agent `i` values `j`'s
bundle without `g` at most as much as their own bundle (`efx_exists_three`, which is a proof
of the proposition `EFXExistsThree` of `EFX.lean`).

* `efx_exists_le_three`: the same for `n` agents, `1 ≤ n ≤ 3`.
* `efx_exists_card_three` (library, alias): the same for any finite type of agents with
  exactly three elements and any finite type of goods.
* `efx3_nondegenerate` (library, alias): the core statement. Hypotheses: `G` is a finite type
  of goods; three valuations `a b c : G → ℝ` are strictly positive on every good; the first
  one takes different values on different sets of goods. Conclusion: there are sets
  `A`, `B`, `C` such that every good lies in exactly one of them (`IsPart3`) and nobody
  strongly envies anybody when the agents with valuations `a`, `b`, `c` receive `A`, `B`, `C`
  (`EFX3`, six conditions `NoSE`).
* `exists_pr` (library, alias): the form of the Plaut–Roughgarden lemma that the proof uses,
  for one strictly positive additive valuation `u`, a finite set `S` of goods and bundles
  indexed by a finite type `K` (given by a map `p : G → K`; only goods in `S` count): if every
  bundle is worth at least `μ`, there is an assignment `q` in which every bundle is still
  worth at least `μ` and, for all bundles `i ≠ j` and every good `g ∈ S` of bundle `j`, bundle
  `j` without `g` is worth at most bundle `i`.

Proof. Valuations are perturbed as in `EFXTwoTypes.lean` (`exists_pos_nondegenerate`, in the
shared library file `Applied/Economics/FairDivisionBasic.lean`), so that
they are positive and non-degenerate and EFX for the perturbed valuations implies EFX for the
original ones. For the perturbed instance we follow Akrami et al.: among all partitions
`(X1, X2, X3)` such that `X1` and `X2` are EFX-feasible for the first agent and `X3` is
EFX-feasible for the second or the third agent (`Inv`), take one maximising
`min (v₁ X1) (v₁ X2)`. The lemma `step` shows that such a partition either gives an EFX
allocation of its three bundles or can be replaced by one with a larger potential, by the case
analysis of Section 4.1 of the paper.

Differences from the textbook statement. (1) The source theorem of Chaudhury–Garg–Mehlhorn is
for additive valuations, as here; Akrami et al. prove more (two agents with general monotone
valuations and one with an MMS-feasible valuation), and that generality is NOT formalized:
all three valuations are additive here, and additivity of the third agent's valuation is used
where the paper uses MMS-feasibility. (2) The papers give algorithms; here the potential
argument is replaced by taking a partition of maximal potential, so no algorithm or running
time is formalized. (3) The Plaut–Roughgarden lemma is proved differently: instead of the
paper's reallocation procedure (for which the strict increase of the minimum seems to need
an extra argument when two bundles are empty; this remark is ours), we take a partition minimising the sum of the squares of the bundle values among
those whose bundles are worth at least `μ`; this needs positivity but not non-degeneracy.
(4) The two sub-cases "the first agent strongly envies both / exactly one of the new bundles"
and the first case of the paper are all derived from one lemma (`exists_inv_shrink`); the
choice of `g_i` as the least valuable good of `X3` for agent `i` is replaced by any good `g`
with `X3 \ g` worth more than `X1` and `X2`. (5) Non-degeneracy is only assumed for the first
agent in `efx3_nondegenerate`. These rearrangements are ours and are checked by Lean; they are
not claimed to appear in the papers. The definition of EFX in both papers is the strong form
used here (removing any good); this was read in the arXiv texts (Chaudhury–Garg–Mehlhorn,
arXiv:2002.05119v3: "`i` strongly envies `S` if `X_i <_i S \ g` for some `g ∈ S`"; Akrami et
al., arXiv:2205.07638v2, Section 2). Both papers compare distinct agents; `IsEFX` also
contains the case `i = j`, which is automatic for non-negative valuations (see `EFX.lean`).

Not covered: four or more agents (`Targets.Economics.EFXExists`, open); non-additive
valuations (general monotone, MMS-feasible, nice-cancelable); chores; any efficiency or
welfare guarantee; computation of the allocation.
-/

namespace Targets.Economics

/-- **EFX exists for three agents** with additive non-negative valuations
(Chaudhury–Garg–Mehlhorn). This proves the proposition `EFXExistsThree`. -/
theorem efx_exists_three : EFXExistsThree :=
  fun _ v hv => Applied.Economics.efx_exists_three v hv

/-- EFX allocations exist for `n` agents with additive non-negative valuations when
`1 ≤ n ≤ 3`. -/
theorem efx_exists_le_three {n m : ℕ} (hn : 0 < n) (hn3 : n ≤ 3) (v : Fin n → Fin m → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) : ∃ a : Fin m → Fin n, IsEFX v a := by
  obtain rfl | rfl | rfl : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  · exact efx_exists_two_types hn v hv (v 0) (v 0) (fun i => Or.inl (by rw [Subsingleton.elim i 0]))
  · exact Applied.Economics.efx_exists_two v hv
  · exact efx_exists_three m v hv

alias efx_exists_card_three := Applied.Economics.efx_exists_card_three
alias efx3_nondegenerate := Applied.Economics.efx3_nondegenerate
alias exists_pr := Applied.Economics.exists_pr

end Targets.Economics
