import Applied.Statistics.InverseNormalCombination

/-!
# Inverse-normal combination test with pre-fixed weights (Lehmacher-Wassmer; Cui-Hung-Wang)

- id: stat-inverse-normal-combination
- area: statistics
- status: formalized
- source: W. Lehmacher, G. Wassmer, "Adaptive sample size calculations in group sequential trials", Biometrics 55 (1999) 1286-1290; L. Cui, H. M. J. Hung, S.-J. Wang, "Modification of sample size in group sequential clinical trials", Biometrics 55 (1999) 853-857. Page ranges confirmed at Crossref. The places of the statements in the papers are to be confirmed: only the abstracts were read, and the papers were not consulted while formalizing.
- used-in: sample-size re-estimation and other data-driven second-stage changes in confirmatory adaptive trials; the weighted statistic with pre-specified weights is the method implemented in adaptive-design software (rpact, ADDPLAN, East; to be confirmed)
- prerequisites: `Targets/Statistics/CombinationTests.lean` (lower-set bound), sums of independent normal variables, absolute continuity of the normal law with respect to Lebesgue measure in both directions
- formalized-elsewhere: not found in the Lean repositories searched (NEXT-TARGETS.md, 25 Nov 2026)
- statement-review: unreviewed

Informal statement. `Φ` is the standard normal distribution function and
`normalTail z = 1 - Φ(z)`. `P` is a probability measure, `m1` a sub-σ-algebra (interim
information), `p1` an `m1`-measurable valid p-value, and `p2` a real function that is
conditionally valid given `m1` (for all `u ≥ 0` and `m1`-measurable `A`,
`P(A ∩ {p2 ≤ u}) ≤ u · P(A)`), as in `Targets/Statistics/CombinationTests.lean`.
The weights `w₁, w₂` are real constants with `w₁ ≥ 0`, `w₂ ≥ 0`, `w₁² + w₂² = 1`, and `z` is
any real critical value.

The rejection region is defined without the quantile function:
`invNormalRegion w₁ w₂ z` is the set of pairs `(x, y)` for which there are reals `z₁, z₂` with
`x ≤ 1 - Φ(z₁)`, `y ≤ 1 - Φ(z₂)` and `w₁ z₁ + w₂ z₂ ≥ z`.

(1) `inverse_normal_region_iff`: for `w₁, w₂ ≥ 0` and reals `Z₁, Z₂`, the pair
`(1 - Φ(Z₁), 1 - Φ(Z₂))` lies in the region if and only if `w₁ Z₁ + w₂ Z₂ ≥ z`.

(2) `inverse_normal_level`: `P((p1, p2) ∈ invNormalRegion w₁ w₂ z) ≤ 1 - Φ(z)`.

(3) `weighted_z_level`: if `Z₁, Z₂` are real functions such that `1 - Φ(Z₁)` is
`m1`-measurable and valid and `1 - Φ(Z₂)` is conditionally valid given `m1`, then
`P(w₁ Z₁ + w₂ Z₂ ≥ z) ≤ 1 - Φ(z)`.

(4) `adaptive_weighted_z_level`: let `Z₁` be `m1`-measurable with standard normal law; for
each `d` in a countable set let `Z₂ d` be measurable with standard normal law and independent
of `m1`; let `D` be a choice of design with every event `{D = d}` `m1`-measurable. Then
`P(w₁ Z₁ + w₂ Z₂(D) ≥ z) ≤ 1 - Φ(z)`.

(5) `inverse_normal_exact`: if `p1, p2` are measurable, independent, and exactly uniform
(`P(pᵢ ≤ t) = t` for all `t ∈ [0, 1]`), then
`P((p1, p2) ∈ invNormalRegion w₁ w₂ z) = 1 - Φ(z)`. (No σ-algebra `m1` appears here.)

(6) `normal_tail_uniform`: the image of the standard normal law under `z ↦ 1 - Φ(z)` is
Lebesgue measure on `[0, 1]`; `normal_cdf_strictMono`: `Φ` is strictly increasing.

Differences from the textbook statement. The weights must be fixed in advance: they are
constants in the Lean statements and may not depend on interim data (on paper, data-dependent
weights can inflate the level; no Lean statement about that case is given). There is no early stopping: one interim
look, one final test. The textbook region `w₁ Φ⁻¹(1 - p1) + w₂ Φ⁻¹(1 - p2) ≥ z` is replaced
by `invNormalRegion`; by (1) the two agree whenever both p-values are of the form `1 - Φ(Z)`,
that is, lie strictly between `0` and `1`. At the boundary the Lean region uses these
conventions: a pair with `p1 ≥ 1` or `p2 ≥ 1` is never in the region (even if the
corresponding weight is `0`), and a coordinate `≤ 0` imposes no restriction on its `zᵢ`.
The level is stated as `1 - Φ(z)` for an arbitrary real `z`; that every `α ∈ (0, 1)` equals
`1 - Φ(z)` for some `z` is not proved here. In (4) each fixed-design statistic `Z₂ d` is
assumed exactly standard normal and independent of all interim information; this is the
null distribution of a z-statistic computed from second-stage data only.

Not covered: group-sequential versions with early rejection or futility stops; more than two
stages; data-dependent weights; the conditional-power rule for choosing the second-stage
sample size; t-statistics or other non-normal stage-wise statistics (only through their
p-values, via (2)); an explicit probability model of a two-stage trial satisfying the
hypotheses of (4); equality in (2) beyond the independent uniform case.
-/

namespace Targets.Statistics

alias inverse_normal_region_iff := Applied.CombinationTests.mem_invNormalRegion_normalTail_iff
alias inverse_normal_level := Applied.CombinationTests.measure_inverseNormal_le
alias weighted_z_level := Applied.CombinationTests.measure_weightedZ_le
alias adaptive_weighted_z_level := Applied.CombinationTests.measure_adaptive_weightedZ_le
alias inverse_normal_exact := Applied.CombinationTests.measure_inverseNormal_eq
alias normal_tail_uniform := Applied.CombinationTests.map_normalTail
alias normal_cdf_strictMono := Applied.CombinationTests.cdf_gaussianReal_strictMono

end Targets.Statistics
