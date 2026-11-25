import Applied.Economics.EFXBinary
import Targets.Economics.EFX

/-!
# EFX allocations exist for binary additive valuations

- id: econ-efx-binary
- area: economics
- status: formalized
- source: G. Amanatidis, G. Birmpas, A. Filos-Ratsikas, A. Hollender, A. A. Voudouris, "Maximum Nash welfare and other stories about EFX", IJCAI 2020 / Theor. Comput. Sci. 863 (2021) (EFX for binary and bi-valued additive valuations); M. Babaioff, T. Ezra, U. Feige, "Fair and truthful mechanisms for dichotomous valuations", AAAI 2021 (matroid-rank valuations); which of these state the strong form (any good removed, all goods allocated) to be confirmed
- used-in: partial result towards `Targets.Economics.EFXExists`
- prerequisites: finite sums, finite minima
- statement-review: unreviewed

Informal statement. `n ≥ 1` agents have additive valuations with every `v i g ∈ {0, 1}`
(real-valued, `v i g = 0 ∨ v i g = 1`) over `m` indivisible goods. Then there is a complete
allocation `a : Fin m → Fin n` that is EFX in the strong form `Targets.Economics.IsEFX`
(removing *any* single good, including goods valued at zero) (`efx_exists_binary`).

The library theorem `Applied.Economics.efx_exists_binary` is stated for finite types of agents
(nonempty) and goods; `Applied.Economics.efx_exists_binary_nat` is the same result for
natural-number valuations bounded by `1`.

Proof: among *clean* allocations (every good that someone values is held by an agent who
values it), take one minimising the sum of squares of the agents' own values; then give every
good nobody values to an agent with the smallest own value.

Differences from the textbook statement. The cited works prove EFX for binary valuations
(Amanatidis et al. for the maximum Nash welfare allocation, also for bi-valued valuations;
Babaioff et al. for matroid-rank valuations). Here the allocation is a minimum-sum-of-squares
clean allocation, not necessarily one of maximum Nash welfare, and only binary additive
valuations are treated. The theorem gives the strong form with all goods allocated, including
goods nobody values; we have not confirmed that this exact form is stated in the cited works.

Not covered: bi-valued valuations (`v i g ∈ {a, b}`); matroid-rank valuations; maximum Nash
welfare or Pareto optimality of the allocation; truthfulness; the general case
(`Targets.Economics.EFXExists`, open).
-/

namespace Targets.Economics

/-- EFX allocations exist for `n ≥ 1` agents whose additive valuations take only the values
`0` and `1`. -/
theorem efx_exists_binary {n m : ℕ} (hn : 0 < n) (v : Fin n → Fin m → ℝ)
    (hv : ∀ i g, v i g = 0 ∨ v i g = 1) : ∃ a : Fin m → Fin n, IsEFX v a :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  Applied.Economics.efx_exists_binary v hv

alias efx_exists_binary_nat := Applied.Economics.efx_exists_binary_nat

end Targets.Economics
