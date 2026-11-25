import Applied.Economics.Kelly

/-!
# The Kelly criterion for a repeated binary bet

- id: econ-kelly-criterion
- area: economics
- status: formalized
- source: J. L. Kelly Jr., "A new interpretation of information rate", Bell System Technical Journal 35 (1956); textbook form to be confirmed (e.g. T. Cover, J. Thomas, "Elements of Information Theory", chapter on gambling)
- used-in: bet sizing, portfolio growth-optimal strategies, information-theoretic gambling
- prerequisites: the real logarithm and `log x ≤ x - 1`
- statement-review: unreviewed

Informal statement. A bet pays net odds `b > 0` with probability `p` (`0 < p < 1`) and loses
the stake otherwise. Staking a fraction `f` of wealth with `0 ≤ f < 1` gives expected log
growth `g f = p log (1 + b f) + (1 - p) log (1 - f)` (`kellyGrowth p b f`). Let
`f⋆ = (p (b + 1) - 1) / b = p - (1 - p) / b` (`kellyFraction p b`). Then:

* `kellyGrowth_le`: `g f ≤ g f⋆` for all `f ∈ [0, 1)`;
* `kellyGrowth_lt`: `g f < g f⋆` for all `f ∈ [0, 1)` with `f ≠ f⋆`;
* `kellyFraction_mem`: if the bet is favourable, `p (b + 1) > 1`, then `0 < f⋆ < 1`;
* `kellyGrowth_isMaxOn_iff`: for a favourable bet, `f ∈ [0, 1)` maximises `g` over `[0, 1)` if
  and only if `f = f⋆`;
* `kellyGrowth_kellyFraction`: `g f⋆ = p log (p (b + 1)) + (1 - p) log ((1 - p) (b + 1) / b)`.

The two inequalities do not assume `p (b + 1) > 1`: they compare `g f` with the value of the
formula `g` at `f⋆` even when `f⋆ ≤ 0` (where `f⋆` is not an admissible stake, but `1 + b f⋆`
and `1 - f⋆` are still positive). The favourability assumption is used only to place `f⋆` in
`(0, 1)`.

Not covered: the endpoint `f = 1` (where the true growth rate is `-∞` but Lean's `Real.log 0`
is `0`), the probabilistic statement that wealth grows almost surely at rate `g f` (law of
large numbers) and that the Kelly strategy asymptotically dominates any other, several
simultaneous or multi-outcome bets, and the unfavourable case `p (b + 1) ≤ 1` (optimal stake
`0`).
-/

namespace Targets.Economics

alias kellyGrowth := Applied.Economics.kellyGrowth

alias kellyFraction := Applied.Economics.kellyFraction

alias kellyGrowth_le := Applied.Economics.kellyGrowth_le

alias kellyGrowth_lt := Applied.Economics.kellyGrowth_lt

alias kellyFraction_mem := Applied.Economics.kellyFraction_mem

alias kellyGrowth_isMaxOn_iff := Applied.Economics.kellyGrowth_isMaxOn_iff

alias kellyGrowth_kellyFraction := Applied.Economics.kellyGrowth_kellyFraction

end Targets.Economics
