# Review packet G: Frank–Wolfe, online gradient descent, AdaBoost, Johnson–Lindenstrauss, null space property and restricted isometry

**Reviewer profile:** this block spans three areas. It can be split between an optimizer
(G1–G3), a learning theorist (G4) and a signal-processing / compressed-sensing person (G5–G7).
Each needs to read Lean 4 signatures over real inner-product spaces.
**Estimated time:** 60 minutes in total (about 20 per sub-area).
**Registry files:** `Targets/Optimization/FrankWolfeRate.lean`, `Targets/Optimization/OnlineGradientRegret.lean`,
`Targets/Optimization/ProjectedOnlineGradientRegret.lean`, `Targets/Learning/AdaBoost.lean`,
`Targets/SignalProcessing/JohnsonLindenstrauss.lean`, `Targets/SignalProcessing/NullSpaceProperty.lean`,
`Targets/SignalProcessing/RestrictedIsometry.lean`.
**Library files:** `Applied/Optimization/FrankWolfe.lean`, `Applied/Optimization/OnlineGradient.lean`,
`Applied/Optimization/ProjectedOnlineGradient.lean`, `Applied/Learning/AdaBoost.lean`,
`Applied/SignalProcessing/JohnsonLindenstrauss.lean`, `Applied/SignalProcessing/NullSpaceProperty.lean`.

Line numbers are those at the time of writing (commit `fbba0ff` on `par-econ`) and will drift.

## Summary

These are classical, widely used guarantees: the `O(1/k)` rate of the Frank–Wolfe
(conditional gradient) method, the `O(√T)`-type regret bound of (projected) online gradient
descent, the AdaBoost training-error bound, the Johnson–Lindenstrauss lemma, and the two
basic facts of compressed sensing (the null space property is equivalent to exact `ℓ¹`
recovery of all `s`-sparse vectors; a restricted isometry constant `δ₂ₛ < 1/3` implies it).
**None of these is new.** `NOVELTY.md` listed several as "nowhere found", but the later
code-level search of 22 public Lean 4 repositories (25 November 2026; see `review/README.md`)
**found** all of them: Frank–Wolfe in Garg's EconCSLib (`ConditionalGradient.lean`, repository
head dated September 2026, before this project); online and projected gradient descent in
`atlas-lean`, cslib-frontier and LMLExplore; the AdaBoost bound in `atlas-lean`;
Johnson–Lindenstrauss in `atlas-lean`, tCSlib and cslib-frontier; RIP ⇒ NSP in `atlas-lean`
(with `δ₂ₛ < √2 − 1`) and in lean-CKSD (with `δ < 1/3`, the same constant as here). This packet
is therefore only about fidelity of these particular statements, which other parts of the
project use.

---

## G1: Frank–Wolfe rate

Aliases `frank_wolfe_rate`, `frank_wolfe_step` (`Targets/Optimization/FrankWolfeRate.lean:29–30`).
The theorem uses section variables, `Applied/Optimization/FrankWolfe.lean:51–52`:

```lean
variable (K : Set E) (hK : Convex ℝ K) (x s : ℕ → E) (hx0 : x 0 ∈ K) (hs : ∀ k, s k ∈ K)
  (hstep : ∀ k : ℕ, x (k + 1) = x k + (2 / ((k : ℝ) + 2)) • (s k - x k))
```

and `Applied/Optimization/FrankWolfe.lean:77`:

```lean
theorem frank_wolfe_rate (f : E → ℝ) (L : ℝ≥0) (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (hlip : LipschitzWith L (gradient f))
    (D : ℝ) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D)
    (hmin : ∀ k, ∀ v ∈ K, ⟪gradient f (x k), s k⟫ ≤ ⟪gradient f (x k), v⟫)
    (u : E) (hu : u ∈ K) (k : ℕ) (hk : 1 ≤ k) :
    f (x k) - f u ≤ 2 * L * D ^ 2 / (k + 2) := by
```

(`E` is a real Hilbert space: `InnerProductSpace ℝ E`, `CompleteSpace E`.)

**Math.** `f` convex and differentiable on all of `E` with `L`-Lipschitz gradient; `K` convex
with diameter `≤ D`; `x₀ ∈ K`; `sₖ ∈ argmin_{v ∈ K} ⟨∇f(xₖ), v⟩`;
`xₖ₊₁ = xₖ + (2/(k+2))(sₖ − xₖ)`. Then `f(xₖ) − f(u) ≤ 2LD²/(k+2)` for all `u ∈ K`, `k ≥ 1`.

**Source (from memory — reviewer please check).** Jaggi (ICML 2013), Theorem 1:
`f(xₖ) − f* ≤ 2C_f/(k+2)` with curvature constant `C_f ≤ L·diam(K)²`. Frank & Wolfe (1956)
for the method.

**Differences.** `C_f` replaced by its upper bound `LD²`. Convexity/smoothness on the whole
space rather than on `K`. Existence of `sₖ` is a hypothesis. `k = 0` excluded (with `x₀`
arbitrary in `K` the bound can fail at `k = 0`).

**Edge cases.** `L = 0` (affine `f`): bound `0`, i.e. `x₁ = s₀` and all later iterates are
minimisers over `K`. `K` a single point: `D ≥ 0`, everything constant. `k = 1`: bound
`2LD²/3`.

## G2: online gradient descent (unconstrained, fixed step)

Alias `ogd_regret` (`Targets/Optimization/OnlineGradientRegret.lean:25`).
`Applied/Optimization/OnlineGradient.lean:56`:

```lean
theorem ogd_regret (f : ℕ → E → ℝ) (hconv : ∀ t, ConvexOn ℝ Set.univ (f t))
    (hdiff : ∀ t, Differentiable ℝ (f t)) (η G : ℝ) (hη : 0 < η)
    (x : ℕ → E) (hstep : ∀ t, x (t + 1) = x t - η • gradient (f t) (x t))
    (T : ℕ) (hG : ∀ t < T, ‖gradient (f t) (x t)‖ ≤ G) (u : E) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ ‖x 0 - u‖ ^ 2 / (2 * η) + η * G ^ 2 * T / 2 := by
```

**Math.** Convex differentiable losses, `xₜ₊₁ = xₜ − η∇fₜ(xₜ)`, `‖∇fₜ(xₜ)‖ ≤ G` for `t < T`.
Then `∑_{t<T} fₜ(xₜ) − fₜ(u) ≤ ‖x₀ − u‖²/(2η) + ηG²T/2` for every `u`.

**Source (from memory — reviewer please check).** Zinkevich (ICML 2003), Theorem 1, is for
projected OGD with decreasing steps `ηₜ = 1/√t` and bound `D²√T/2 + (√T − 1/2)G²`. The
fixed-step bound is the standard textbook variant (Hazan, *Introduction to Online Convex
Optimization*, Ch. 3; Shalev-Shwartz's survey; numbers to be confirmed).

**Differences.** Unconstrained, fixed step, differentiable losses (no subgradients). The
`O(√T)` tuned form is not stated (choose `η = ‖x₀−u‖/(G√T)` by hand). The citation of
Zinkevich Theorem 1 is to a different (projected, decreasing-step) statement; the header
says so.

**Edge cases.** `T = 0`: `0 ≤ ‖x₀−u‖²/(2η)`. `u = x₀`: bound `ηG²T/2`. `G < 0` is only
possible when `T = 0`.

## G3: projected online gradient descent

Aliases `projected_ogd_regret`, `projected_ogd_regret_of_diam`, `exists_projected_ogd`
(`Targets/Optimization/ProjectedOnlineGradientRegret.lean:28–30`).
`Applied/Optimization/ProjectedOnlineGradient.lean:48`, `:93`, `:108`:

```lean
theorem projected_ogd_regret (f : ℕ → E → ℝ) (hconv : ∀ t, ConvexOn ℝ Set.univ (f t))
    (hdiff : ∀ t, Differentiable ℝ (f t)) (η G : ℝ) (hη : 0 < η)
    (K : Set E) (hK : Convex ℝ K) (x : ℕ → E) (hmem : ∀ t, x (t + 1) ∈ K)
    (hstep : ∀ t, ‖x t - η • gradient (f t) (x t) - x (t + 1)‖
      = ⨅ w : K, ‖x t - η • gradient (f t) (x t) - w‖)
    (T : ℕ) (hG : ∀ t < T, ‖gradient (f t) (x t)‖ ≤ G) (u : E) (hu : u ∈ K) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ ‖x 0 - u‖ ^ 2 / (2 * η) + η * G ^ 2 * T / 2 := by
```

```lean
theorem projected_ogd_regret_of_diam (f : ℕ → E → ℝ) (hconv : ∀ t, ConvexOn ℝ Set.univ (f t))
    (hdiff : ∀ t, Differentiable ℝ (f t)) (η G : ℝ) (hη : 0 < η)
    (K : Set E) (hK : Convex ℝ K) (D : ℝ) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D)
    (x : ℕ → E) (hx0 : x 0 ∈ K) (hmem : ∀ t, x (t + 1) ∈ K)
    (hstep : ∀ t, ‖x t - η • gradient (f t) (x t) - x (t + 1)‖
      = ⨅ w : K, ‖x t - η • gradient (f t) (x t) - w‖)
    (T : ℕ) (hG : ∀ t < T, ‖gradient (f t) (x t)‖ ≤ G) (u : E) (hu : u ∈ K) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ D ^ 2 / (2 * η) + η * G ^ 2 * T / 2 := by
```

```lean
theorem exists_projected_ogd (f : ℕ → E → ℝ) (η : ℝ) (K : Set E) (hne : K.Nonempty)
    (hcl : IsClosed K) (hK : Convex ℝ K) (x₀ : E) :
    ∃ x : ℕ → E, x 0 = x₀ ∧ ∀ t, x (t + 1) ∈ K ∧
      ‖x t - η • gradient (f t) (x t) - x (t + 1)‖
        = ⨅ w : K, ‖x t - η • gradient (f t) (x t) - w‖ := by
```

**Math.** `xₜ₊₁` a nearest point of `K` to `xₜ − η∇fₜ(xₜ)`; same bound for `u ∈ K`; with
`x₀ ∈ K` and `diam K ≤ D`, the bound `D²/(2η) + ηG²T/2`; iterates exist for nonempty closed
convex `K` in a Hilbert space.

**Source.** Zinkevich (2003) Theorem 1 with fixed steps; textbook variant (see G2).

**Differences.** Losses convex on the whole space (not only on `K`); fixed step; the
projection is characterised by "distance equals infimum", which for convex `K` determines it
uniquely. `x₀` need not lie in `K` in the first theorem.

**Edge cases.** `K = E`: projection is the identity; reduces to G2. `T = 0`. `η` very large:
the bound is dominated by `ηG²T/2`.

## G4: AdaBoost training error

Aliases in `Targets/Learning/AdaBoost.lean:32–35`. Definitions,
`Applied/Learning/AdaBoost.lean:38`, `:44`, `:48`, `:53`:

```lean
noncomputable def adaDist (y : ι → ℝ) (h : ℕ → ι → ℝ) (α : ℕ → ℝ) : ℕ → ι → ℝ
  | 0, _ => 1 / Fintype.card ι
  | t + 1, i => adaDist y h α t i * Real.exp (-α t * y i * h t i) /
      ∑ j, adaDist y h α t j * Real.exp (-α t * y j * h t j)
```

```lean
noncomputable def adaZ (y : ι → ℝ) (h : ℕ → ι → ℝ) (α : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ j, adaDist y h α t j * Real.exp (-α t * y j * h t j)
```

```lean
noncomputable def adaScore (h : ℕ → ι → ℝ) (α : ℕ → ℝ) (T : ℕ) (i : ι) : ℝ :=
  ∑ t ∈ range T, α t * h t i
```

```lean
noncomputable def adaErr (y : ι → ℝ) (h : ℕ → ι → ℝ) (α : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i with h t i ≠ y i, adaDist y h α t i
```

Theorems, `AdaBoost.lean:115`, `:139`, `:176`, `:218` (all with `[Nonempty ι]`):

```lean
theorem adaboost_training_error (T : ℕ) :
    ((univ.filter fun i => y i * adaScore h α T i ≤ 0).card : ℝ) / Fintype.card ι
      ≤ ∏ t ∈ range T, adaZ y h α t := by
```

```lean
theorem adaboost_training_error_sign (hy : ∀ i, y i = 1 ∨ y i = -1) (T : ℕ) :
    ((univ.filter fun i => Real.sign (adaScore h α T i) ≠ y i).card : ℝ) / Fintype.card ι
      ≤ ∏ t ∈ range T, adaZ y h α t := by
```

```lean
theorem adaZ_optimal (hy : ∀ i, y i = 1 ∨ y i = -1) (hh : ∀ t i, h t i = 1 ∨ h t i = -1)
    (t : ℕ) (h0 : 0 < adaErr y h α t) (h1 : adaErr y h α t < 1)
    (hα : α t = 1 / 2 * Real.log ((1 - adaErr y h α t) / adaErr y h α t)) :
    adaZ y h α t = 2 * Real.sqrt (adaErr y h α t * (1 - adaErr y h α t)) := by
```

```lean
theorem adaboost_training_error_exp (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hh : ∀ t i, h t i = 1 ∨ h t i = -1) (T : ℕ)
    (h0 : ∀ t < T, 0 < adaErr y h α t) (h1 : ∀ t < T, adaErr y h α t < 1)
    (hα : ∀ t < T, α t = 1 / 2 * Real.log ((1 - adaErr y h α t) / adaErr y h α t)) :
    ((univ.filter fun i => Real.sign (adaScore h α T i) ≠ y i).card : ℝ) / Fintype.card ι
      ≤ Real.exp (-2 * ∑ t ∈ range T, (1 / 2 - adaErr y h α t) ^ 2) := by
```

**Math.** For any real labels, predictions and votes: fraction of non-positive margins
`≤ ∏ Zₜ`. For `±1` labels: misclassification fraction (score `0` counts as an error)
`≤ ∏ Zₜ`. For `±1` predictions and `αₜ = ½ log((1−εₜ)/εₜ)` with `εₜ ∈ (0,1)`:
`Zₜ = 2√(εₜ(1−εₜ))` and training error `≤ exp(−2∑(½−εₜ)²)`.

**Source (from memory — reviewer please check).** Freund & Schapire (1997, JCSS 55),
Theorem 6: training error `≤ ∏ 2√(εₜ(1−εₜ)) ≤ exp(−2∑γₜ²)`, `γₜ = ½ − εₜ`. Schapire & Singer
(1999) for the `∏ Zₜ` form.

**Differences / things to check.**
- The weak hypotheses `h` are an arbitrary fixed sequence; in AdaBoost `hₜ` is chosen
  depending on `Dₜ`. Since the bound holds for every sequence, this covers adaptive choice.
- `εₜ > 1/2` is allowed (then `αₜ < 0`); the bound still holds.
- **Name vs content.** The alias `adaboost_normaliser_optimal` (for `adaZ_optimal`) computes
  `Zₜ` at the stated `αₜ`; it does **not** prove that this `αₜ` minimises `Zₜ`, and the header
  explicitly lists that minimisation as "not covered". The alias name could mislead.

**Edge cases.** `T = 0`: bound `1`. `εₜ = 1/2`: `αₜ = 0`, `Zₜ = 1`. One sample point: the
fraction is `0` or `1`. `εₜ ∈ {0, 1}` excluded (log of `0` or division by `0`).

## G5: Johnson–Lindenstrauss

`Targets/SignalProcessing/JohnsonLindenstrauss.lean:31` (proved by the library theorem at
`Applied/SignalProcessing/JohnsonLindenstrauss.lean:244`, same statement):

```lean
theorem johnsonLindenstrauss {d k : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d)))
    (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hk : 24 * Real.log S.card ≤ ε ^ 2 * k) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      ∀ x ∈ S, ∀ y ∈ S,
        (1 - ε) * ‖x - y‖ ^ 2 ≤ ‖f x - f y‖ ^ 2 ∧ ‖f x - f y‖ ^ 2 ≤ (1 + ε) * ‖x - y‖ ^ 2 := by
```

**Math.** For `N` points in `ℝᵈ`, `0 < ε < 1`, `k ≥ 24 ln N / ε²`, there is a linear
`f : ℝᵈ → ℝᵏ` with `(1−ε)‖x−y‖² ≤ ‖fx−fy‖² ≤ (1+ε)‖x−y‖²` for all pairs.

**Source (from memory — reviewer please check).** Dasgupta & Gupta (2003), Theorem 2.1 (number
to be confirmed): `k ≥ 4(ε²/2 − ε³/3)⁻¹ ln N`. Since `ε²/2 − ε³/3 ≥ ε²/6` on `(0,1)`, `24/ε²` is a
valid (weaker) constant.

**Differences.** Existence only (not "with high probability" for a random projection);
squared distances; natural log; constant `24` instead of Dasgupta–Gupta's.

**Edge cases.** `N ≤ 1`: `log N ≤ 0`, any `k` (including `0`); zero map. `k ≥ d`: still
fine. `ε → 1`: lower bound `0`.

## G6: null space property ⟺ exact ℓ¹ recovery

Aliases in `Targets/SignalProcessing/NullSpaceProperty.lean:36–42`. Definitions,
`Applied/SignalProcessing/NullSpaceProperty.lean:39`, `:81`, `:87`:

```lean
def IsSparse (s : ℕ) (x : ι → ℝ) : Prop :=
  (univ.filter fun i => x i ≠ 0).card ≤ s
```

```lean
def NullSpaceProperty (A : (ι → ℝ) →ₗ[ℝ] F) (s : ℕ) : Prop :=
  ∀ v : ι → ℝ, A v = 0 → v ≠ 0 → ∀ S : Finset ι, S.card ≤ s →
    ∑ i ∈ S, |v i| < ∑ i ∈ Sᶜ, |v i|
```

```lean
def ExactRecovery (A : (ι → ℝ) →ₗ[ℝ] F) (s : ℕ) : Prop :=
  ∀ x : ι → ℝ, IsSparse s x → ∀ z : ι → ℝ, A z = A x → z ≠ x → ∑ i, |x i| < ∑ i, |z i|
```

Theorem, `NullSpaceProperty.lean:91` (matrix version at `:542`):

```lean
theorem nullSpaceProperty_iff_exactRecovery (A : (ι → ℝ) →ₗ[ℝ] F) (s : ℕ) :
    NullSpaceProperty A s ↔ ExactRecovery A s := by
```

**Math.** For a linear map `A` on `ℝⁿ`: `‖v_S‖₁ < ‖v_{Sᶜ}‖₁` for all `v ∈ ker A ∖ {0}`, `|S| ≤ s`
⟺ every `s`-sparse `x` is the unique minimiser of `‖z‖₁` subject to `Az = Ax`.

**Source (from memory — reviewer please check).** Foucart & Rauhut (2013), Theorem 4.5
(number to be confirmed); Cohen, Dahmen, DeVore (2009); also Donoho–Huo, Gribonval–Nielsen.

**Differences.** None of substance; real scalars only; codomain any real vector space.

**Edge cases.** `s = 0`: NSP always holds; recovery concerns only `x = 0`. `s ≥ n`: both sides
say `A` is injective. `ker A = 0`: both hold for all `s`.

## G7: restricted isometry ⇒ null space property (δ₂ₛ < 1/3)

Aliases in `Targets/SignalProcessing/RestrictedIsometry.lean:36–43`. Definition,
`NullSpaceProperty.lean:242`:

```lean
def RestrictedIsometry (A : (ι → ℝ) →ₗ[ℝ] F) (k : ℕ) (δ : ℝ) : Prop :=
  ∀ x : ι → ℝ, IsSparse k x →
    (1 - δ) * ∑ i, x i ^ 2 ≤ ‖A x‖ ^ 2 ∧ ‖A x‖ ^ 2 ≤ (1 + δ) * ∑ i, x i ^ 2
```

Theorems, `NullSpaceProperty.lean:439`, `:528`, `:562`, `:578`:

```lean
theorem RestrictedIsometry.nullSpaceProperty {A : (ι → ℝ) →ₗ[ℝ] F} {s : ℕ} {δ : ℝ}
    (hA : RestrictedIsometry A (2 * s) δ) (hδ : δ < 1 / 3) : NullSpaceProperty A s := by
```

```lean
theorem RestrictedIsometry.exactRecovery {A : (ι → ℝ) →ₗ[ℝ] F} {s : ℕ} {δ : ℝ}
    (hA : RestrictedIsometry A (2 * s) δ) (hδ : δ < 1 / 3) : ExactRecovery A s :=
```

```lean
theorem matrix_exactRecovery_of_restrictedIsometry (A : Matrix κ ι ℝ) (s : ℕ) (δ : ℝ)
    (hδ : δ < 1 / 3)
    (hA : ∀ x : ι → ℝ, IsSparse (2 * s) x →
      (1 - δ) * ∑ i, x i ^ 2 ≤ ∑ j, A.mulVec x j ^ 2 ∧
        ∑ j, A.mulVec x j ^ 2 ≤ (1 + δ) * ∑ i, x i ^ 2)
    (x : ι → ℝ) (hx : IsSparse s x) (z : ι → ℝ) (hz : A.mulVec z = A.mulVec x) (hne : z ≠ x) :
    ∑ i, |x i| < ∑ i, |z i| := by
```

```lean
theorem restrictedIsometry_one (k : ℕ) :
    RestrictedIsometry (matrixEuclideanMap (1 : Matrix ι ι ℝ)) k 0 := by
```

**Math.** If `(1−δ)‖x‖₂² ≤ ‖Ax‖² ≤ (1+δ)‖x‖₂²` for all `2s`-sparse `x` and `δ < 1/3`, then NSP of
order `s`, hence exact `ℓ¹` recovery. The identity satisfies RIP with `δ = 0` (non-vacuity).

**Source (from memory — reviewer please check).** Foucart & Rauhut (2013), Theorem 6.9
(`δ₂ₛ < 1/3`), with sharper constants later in the same chapter; Candès & Tao (2005) for RIP
and recovery under a different condition (numbers to be confirmed).

**Differences.** `δ` need not be the smallest constant and may be negative (then the
hypothesis can only hold if there is no nonzero `2s`-sparse vector, i.e. `s = 0` or `ι`
empty — harmless). The constant `1/3` is not optimal. Codomain: any real inner product space.

**Edge cases.** `s = 0`: conclusion trivially true. `δ = 1/3` exactly: excluded. Identity
matrix: RIP with `δ = 0` for every order; recovery is trivial since `A` is injective.

---

## Lean conventions that matter in this block

- **`gradient`** is Mathlib's Riesz-represented derivative; `Differentiable ℝ f` is assumed,
  so `gradient` is the true gradient everywhere.
- **`⨅ w : K, …`** over a subtype: if `K` were empty this would be `0`, but `hmem` forces `K`
  nonempty.
- **`Real.log` of `0` is `0`**; relevant for `S.card = 0` in JL (then `k` is arbitrary) and for
  `εₜ = 0` in AdaBoost (excluded by hypothesis).
- **`Real.sign 0 = 0`**, so a zero score counts as a misclassification.
- **`1 / Fintype.card ι`** in `adaDist 0`; `[Nonempty ι]` is assumed so it is not `1/0`.

## Reviewer checklist

- [ ] Definitions match (iterations; `IsSparse`, NSP, exact recovery, RIP; AdaBoost
      distribution and normaliser)
- [ ] Hypotheses match (convexity/smoothness domain; step sizes; `±1` labels; `εₜ ∈ (0,1)`)
- [ ] Conclusions match (rates, regret bounds, error bounds, JL distortion, NSP/recovery)
- [ ] Constants match (`2LD²/(k+2)`; `‖x₀−u‖²/(2η) + ηG²T/2`; `24`; `1/3`)
- [ ] Citations correct (Jaggi Thm 1; Zinkevich Thm 1 vs textbook fixed-step variant;
      Freund–Schapire Thm 6; Dasgupta–Gupta; Foucart–Rauhut Thms 4.5 / 6.9)

## Known doubts (from file headers, `REVIEW.md` and the prior-art verification)

- Theorem numbers in Jaggi (2013), Hazan, Freund–Schapire, Foucart–Rauhut are "to be
  confirmed" in the headers.
- OGD: the cited Zinkevich theorem has decreasing steps and projection; the formalized
  statements are the fixed-step textbook variant (headers).
- AdaBoost: the alias `adaboost_normaliser_optimal` does not prove optimality (observation
  made while writing this packet).
- `NOVELTY.md` called Frank–Wolfe, online gradient descent, AdaBoost and Johnson–Lindenstrauss
  "nowhere found". The code-level verification found all of them (and RIP ⇒ NSP) in other
  Lean repositories; `NOVELTY.md` is out of date on these points. Do not cite any of them as a
  first.

## Recording the outcome

For each registry file you checked, open a pull request changing
`statement-review: unreviewed` to `statement-review: reviewed`, run
`python3 scripts/check_targets.py --write`, and say what you checked. If the block is split
between reviewers, one pull request per sub-area is fine.
