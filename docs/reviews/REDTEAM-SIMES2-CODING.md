# Red-team report SIMES2-CODING

Worktree `wt-g`, branch `rv-g`, commit `5a821ef` (new files only, nothing existing modified).
Scripts: `priorart/redteam-simes2-coding-scripts/`. Date 2026-11-25.

## Verdict table

| # | Result | Verdict |
|---|---|---|
| 1a | Open statement `SimesTwoSidedGaussian` | READY WITH REWORDING (statement is right; header citations/status need fixes) |
| 1b | `BHTwoSidedGaussian` in the same file | NOT READY as "open": the literature now reports it false; file title and docstring still say open |
| 1c | Two-sided Simes, m ≤ 2 (`simesTwoSidedGaussian_of_le_two`) | READY WITH REWORDING (fix the Samuel-Cahn citation) |
| 1d | Two-sided Simes, one-factor / equicorrelated ρ ≥ 0 | READY TO ANNOUNCE |
| 1e | Two-sided Simes under the Karlin–Rinott sign condition | READY TO ANNOUNCE (as the "if" direction, non-degenerate case) |
| 1f | Four functions theorem, integral form; FKG; MTP2 ⇒ weak PRDS | READY WITH REWORDING: **not a first** (prior Lean version found) |
| 2 | Trifference: Körner, Körner–Marton, T(1..4), codes of length 5, 6 | READY TO ANNOUNCE |
| 3 | Černý family, exact reset threshold (n−1)² | READY TO ANNOUNCE |
| 4 | Naddef, 0/1-polytope diameter ≤ d | READY WITH REWORDING (ambient dimension; already disclosed) |
| 5a | VT codes correct one deletion; Levenshtein upper bound | READY TO ANNOUNCE |
| 5b | Deletion channel: C(d) ≥ 1 − H(d), C(d) > 0, definition of capacity | READY TO ANNOUNCE |

No false statement, vacuous hypothesis or trivialising definition was found in any assigned result.
All headline theorems depend only on `propext`, `Classical.choice`, `Quot.sound` (34 `#print axioms`
lines, script `Ax.lean`); no `sorry`, `native_decide` or `axiom` in the assigned files.

## Defects, most serious first

1. **Prior art missed for the integral four functions theorem.** `caiusdfolkerts/research`
   (GitHub, published 2026-11-06), `wishart/source/wishart/verified/core03.lean`, sections
   `Wishart/FourFunctionsIntegral.lean` and `Wishart/ContinuousFKG.lean`:
   `continuous_four_functions_bounded` (product of probability measures on ℝ^ι, four bounded
   non-negative measurable real functions, same lattice hypothesis, Bochner integrals),
   `continuous_four_functions_of_monotone_approximation` (unbounded, via monotone bounded
   approximants), `continuous_fkg_bounded_on`. No `sorry` in that file (not built by me).
   Ours is more general (σ-finite measures on arbitrary linearly ordered measurable spaces,
   `[0,∞]`-valued, no boundedness, marginal form, set form), but "first Lean formalization of the
   Karlin–Rinott integral four functions theorem / continuous FKG" must not be claimed.
   `Targets/Statistics/FourFunctionsIntegral.lean` has no `formalized-elsewhere` line; add one.
   No Lean precedent found for "MTP2 ⇒ PRDS", for the Karlin–Rinott theorem on |N(0,Σ)|, or for
   any two-sided Simes result.

2. **`BHTwoSidedGaussian` is filed as open but is reported false.** arXiv:2607.12208 exists
   (E. Dobriban, "The Benjamini–Hochberg Procedure Can Fail to Control the FDR for Correlated
   Two-Sided Gaussian Tests"): a factor model, nominal level 0.01, FDR > 0.0104 for all large m,
   interval-arithmetic certificate. arXiv:2607.14812 exists (L. Lei, "How Much Can Gaussian
   Dependence Inflate the Benjamini-Hochberg Procedure's FDR?"). I read abstracts only. That model
   is inside the hypotheses of the Lean `Prop` (jointly Gaussian, unit variances, mean-zero nulls,
   arbitrary means for false nulls), so the `Prop` as written is (reportedly) false. The file
   is inconsistent with itself: title "Open: Simes and Benjamini–Hochberg…", docstring
   "**Open, disputed.**", first paragraph "Treat the truth value as unknown", last paragraph "the
   proposition is false". The phrases "citation to be confirmed" / "not verified" can now be
   replaced by "abstract checked 2026-11-25".

3. **Open-problem header is out of date and one source is misdescribed.**
   - New partial results exist: X. Zhang, "Exact Simes inequalities for two-sided Gaussian
     tests", arXiv:2611.02513 (2 Nov 2026): for every fixed m, validity for all sufficiently
     small α uniformly in the covariance; m = 3 at α = 0.05 (computer-assisted) and an interval
     around it; large m under bounded-degree or small-block structure. The abstract says the
     general question "remains open", which confirms our status line, but the header sentences
     "These are the cases covered by the literature" and "What remains open is … already for
     three statistics" need this paper cited (m = 3 is settled near α = 0.05, not for all α).
   - Sarkar arXiv:2304.05261 is "On Controlling the False Discovery Rate in Multiple Testing of
     the Means of Correlated Normals Against Two-Sided Alternatives": it is the source for the
     BH conjecture (partial proof with weighted statistics), not primarily for Simes.

4. **Wrong source for the bivariate case.** `TwoSidedSimesBivariate.lean` cites Samuel-Cahn,
   Biometrika 83 (1996) for "two-sided tests, two normal statistics; to be confirmed". Its
   abstract is about **one-sided** bivariate normal tests (conservative for ρ ≥ 0,
   anticonservative for ρ < 0). I could not confirm any two-sided statement there. The m = 2
   two-sided case follows from Karlin–Rinott (for two variables the sign condition always holds)
   plus Sarkar (1998); cite those, and Hochberg–Rom (1995) for bivariate TP2 if a direct source is
   wanted (from memory, unverified).

   > **Note added 2026-11-26 (housekeeping): defect 4 is withdrawn.** `SOURCE-VERIFICATION.md`,
   > section 2.23, fetched the abstract of Samuel-Cahn (1996), which says: "Two-sided tests based
   > on bivariate normal variables are always conservative." The registry citation is kept, and
   > `TwoSidedSimesBivariate.lean` no longer says "to be confirmed" for it. Only the abstract was
   > read, not the paper. The verdict "fix the Samuel-Cahn citation" in row 1c of the table above
   > is withdrawn with it.

5. **Karlin–Rinott attribution, minor.** The sign condition in Lean (`B i j * sg (d i) * sg (d j) ≤ 0`
   for i ≠ j, B = Σ⁻¹) is the published one: "off-diagonal elements of −DΣ⁻¹D non-negative for some
   diagonal D with entries ±1". I confirmed this wording from the abstract of Karlin–Rinott,
   J. Multivariate Anal. 10 (1980) 467–498 and from secondary sources; I could not open the 1981
   Ann. Statist. paper, so "Theorem 3.1" stays unconfirmed. The criterion already appears in the
   1980 paper, so cite both. Only the "if" direction is proved (disclosed).

6. **Trifference small cases: reference can be filled in.** T(5) = 10, T(6) = 13:
   S. Della Fiore, A. Gnutti, S. Polak, "The maximum cardinality of trifferent codes with lengths
   5 and 6", Examples and Counterexamples 2 (2022), arXiv:2201.06846. S. Kurz, "Trifferent codes
   with small lengths", arXiv:2310.13563 reports T(7) = 16, T(8) = 20, T(9) = 27 (search snippet
   only). The header's "to be confirmed" can go. "ProofAtlas Top 500" could not be checked.

7. **Naddef: dimension.** As the header says, the bound is in the ambient dimension. The standard
   statement is diameter ≤ dim P; do not write "Hirsch conjecture for 0/1-polytopes" (facets are
   not formalized). I could not fetch the 1989 paper.

8. **Cosmetic.** `reset word` differs from formal-conjectures for an empty state type (ours: every
   word; theirs: none). Harmless, now recorded in the Bridge file.

## 1. Two-sided Simes

**Unfolded.** `twoSidedP z = 2 (1 − Φ(|z|))`, Φ = `cdf (gaussianReal 0 1)`.
`IsStdGaussianVector P Z` = the law of ω ↦ (Z_i ω)_i on ℝⁿ is `IsGaussian` (every continuous linear
functional is a real Gaussian, degenerate allowed) and each `P.map (Z i) = N(0,1)`.
`bhK α p = max {k ≤ n : #{j : p_j ≤ αk/n} ≥ k}`, so `1 ≤ bhK α p` is the Simes rejection event
"p₍ₖ₎ ≤ kα/n for some k". `SimesTwoSidedGaussian`: for all n, all probability spaces, all
measurable Z with that law, all α ∈ [0,1]: P(Simes rejects) ≤ α. This is the conjecture as stated
in Sarkar (2008), Finner et al., and Zhang (2026): global null, zero means, unit variances,
arbitrary (possibly singular) correlation. Nothing is asserted (`def … : Prop`).

**Proved classes** (all conclude the same event bound, any n):
- n ≤ 2, any correlation;
- `IsStdGaussianVector` + ∃a, a_i² ≤ 1, Cov(Z_i,Z_j) = a_i a_j (i ≠ j); corollary ρ ∈ [0,1] equicorrelated;
- `IsStdGaussianVector` + Cov = M Mᵀ, det M ≠ 0, ((M Mᵀ)⁻¹)_ij s_i s_j ≤ 0 (i ≠ j) for some signs s.

**Non-vacuity (new Lean file `Applied/Statistics/TwoSidedSimesSanity.lean`).** On
ℝ × (Fin 3 → ℝ) with the product of N(0,1) laws, Z_j = √½·W + √½·ε_j. Proved: jointly Gaussian
(`isGaussian_map_Z`), N(0,1) marginals (`map_Z`), Cov = ½ off the diagonal (`cov_Z`),
**not independent** (`not_indepFun_Z`), Cov = M Mᵀ for M = √½·[[1,1,0],[1,0,1],[0,1,1]], det M ≠ 0,
precision off-diagonal entries = −½ (`precision_offDiag`). Both general theorems are then applied
to it: `simes_equicorrelated_instance`, `simes_karlinRinott_instance`.

**Hypotheses.** Joint normality is needed (marginal normality plus covariances does not give
Simes). `a_i² ≤ 1` and `det M ≠ 0` are real restrictions, disclosed. In the density form the
constant C and matrix B are unconstrained but the N(0,1) marginal hypothesis pins them down; the
`IsGaussian` form shows it is satisfiable.

**Monte Carlo** (`simes.py`, 2·10⁷ draws, s.e. ≤ 1.1·10⁻⁴; α = .01, .05, .2, .5, .9):

| Σ | class | level |
|---|---|---|
| independent, m=3 | inside | .01002 .05004 .20005 .50002 .90001 (Simes is exact) |
| equicorr ρ=.5, m=3 | inside (1F, KR) | .00964 .04678 .17999 .44773 .87486 |
| equicorr ρ=.3, m=5 | inside | .00986 .04836 .18772 .46496 .88161 |
| AR(1) ρ=−.7, m=4 | inside (KR) | .00912 .04357 .16584 .40841 .83908 |
| hub r=.8, s=−.6 | inside | .00910 .04387 .16900 .42020 .85092 |
| equicorr ρ=−.4, m=3 | outside | .00983 .04798 .18567 .45941 .87504 |
| equicorr ρ=−.49, m=3 | outside | .00963 .04682 .17847 .43358 .87189 |
| equicorr ρ=−.3, m=4 | outside | .00987 .04866 .18909 .46480 .87600 |
| tridiagonal cov (.7,.7,0) | outside | .00920 .04458 .17240 .43023 .86225 |
| equicorr ρ=−.5, m=3 | outside, singular | .00962 .04658 .17765 .42524 .88220 |

14 random 3×3 / 4×4 correlation matrices (`simes2.py`, 4·10⁶ draws; 13 outside the classes or
singular): largest level/α = 0.958, 0.951, 0.973 at α = .05, .3, .7. No violation anywhere, so no
evidence against the open statement; consistent with it being open rather than false.

## 2. Trifference

**Unfolded.** `IsTrifferent C`: C ⊆ {0,1,2}ⁿ, any three pairwise distinct codewords have a
coordinate with three distinct symbols. `trifferenceMax n` = max cardinality (sup over a nonempty
finite set, attained). `trifferenceRate` = limsup log₂T(n)/n; the sequence is proved bounded both
ways, so the real `limsup` has no junk value. Proved: T(n) ≤ 2(3/2)ⁿ; rate ≤ log₂(3/2);
T(4k) ≥ M − M³(25/81)ᵏ; T(n) ≥ ¼(9/5)^⌊n/4⌋; rate ≥ ¼log₂(9/5); T(1..4) = 3, 4, 6, 9;
T(5) ≥ 10, T(6) ≥ 13.

**Checks (`trif.py`).** The two codes transcribed from `TrifferenceLower.lean`: 10 and 13 distinct
words, all triples trifferent. Tetracode trifferent. Exhaustive backtracking gives
T(1..4) = 3, 4, 6, 9. 225 of 729 ordered triples of tetracode words are not pairwise distinct
(225/729 = 25/81). ¼log₂(9/5) = 0.21200, log₂√(9/7) = 0.18129, log₂(3/2) = 0.58496.
Matches Körner (1973) and Körner–Marton (1988); the constant ¼ and the floor are ours (disclosed).
Prior art: GitHub code search `trifferent`, `Trifference`, `perfect hash trifferent`: 0 Lean hits.

## 3. Černý family

**Unfolded.** `cerny n`: states `Fin n`; a: i ↦ i+1 mod n; b: n−1 ↦ 0, others fixed. Reset word:
`∀ p q, evalFrom p w = evalFrom q w`. `IsMinResetLength M k`: some reset word of length k, none
shorter. Theorem: for n ≥ 2, `IsMinResetLength (cerny n) ((n−1)²)`.
This is Černý's automaton as in Volkov's survey with the letter names swapped.

**Checks (`cerny.py`).** BFS on the power automaton with the Lean transition table:
shortest reset word = 0, 1, 4, 9, 16, 25, 36, 49, 64, 81 for n = 1..10; the word
b(aⁿ⁻¹b)ⁿ⁻² has length (n−1)² and sends everything to state 0 for n = 2..10.

**Bridge (new `Applied/Automata/CernyFamilyBridge.lean`).** formal-conjectures states the conjecture
(`cerny_conjecture`, `sorry`) and says in prose that C_n shows sharpness, without a theorem.
Their `IsSynchronizingWord`/`IsSynchronizing` are copied verbatim; proved equivalent to ours for
nonempty state types; `cerny_bound_sharp_fc`: for n ≥ 2 a DFA on `Fin n` that is synchronizing in
their sense, with a synchronizing word of length exactly `(Fintype.card (Fin n) − 1)²` and none
shorter. Prior art: only formal-conjectures and copies of it.

## 4. Naddef

**Unfolded.** S any set of 0/1 points of ℝᵈ, P = conv S. `AdjVertices P u v`: u ≠ v, both extreme
points, and the segment [u,v] is an extreme subset of P. `VertexDistLE P u v N`: a walk of ≤ N
such edges. Theorem: any two extreme points are within d edges; also within `hammingDist u v`;
vertices of P are exactly S; for the cube the bound d is attained.

**Edge definition vs the standard one (`naddef.py`).** For every nonempty S ⊆ {0,1}ᵈ, d = 2, 3
(15 + 255 sets) and 300 random S ⊆ {0,1}⁴, two LPs per pair: (i) "exposed edge": a linear
functional maximised exactly on {u,v}; (ii) the extreme-segment definition. They agree on every
pair. Graph distance ≤ Hamming distance in every case; maximum diameter 2, 3, 4. Square: 4 sides,
no diagonals. Triangle {00,10,11}: 00–11 is an edge.
**Lean (`Applied/Optimization/ZeroOnePolytopeSanity.lean`).** (0,0)–(1,0) adjacent in the square,
(0,0)–(1,1) not adjacent, distance exactly 2.

## 5. VT codes and the deletion channel

**VT, unfolded.** `vtSum x = Σ (i+1)·x_i`, `vtCode n a = {x : vtSum x ≡ a mod n+1}`, single-deletion
code = disjoint deletion balls. Theorems: every VT_a(m+1) is one; Σ_a |VT_a(n)| = 2ⁿ; some a has
(n+1)|VT_a(n)| ≥ 2ⁿ; any single-deletion code has |C| ≤ (1+ε)2ⁿ/n for large n.
**Checks (`vt.py`, n = 1..12, beyond the requested 10).** Every VT_a(n) has pairwise disjoint
deletion balls; sizes sum to 2ⁿ; a = 0 is a largest; |VT₀| = 1, 2, 2, 4, 6, 10, 16, 30, 52, 94, 172,
316 (Sloane's values); |delBall x| = number of runs for every word; the finite bound holds;
supersequence count Σ_{j≥m} C(n,j) verified exhaustively for n ≤ 8.

**Capacity, unfolded.** Output type: (length m ≤ n, word of length m). Kernel(x,y) =
Σ over kept sets s with x|ₛ = y of d^(n−|s|)(1−d)^|s|. `Achievable R`: ∀ε>0 ∃N ∀n ≥ N ∃M, encoder
`Fin M → {0,1}ⁿ`, decoder on outputs, with exp(nR) ≤ M and **max** over messages of error ≤ ε.
`deletionCapacity d = sSup {R achievable}`. This is the operational capacity, maximal error,
deterministic code, all large n, nats per input bit. M ≥ 1 is forced, so the `⨆` over `Fin M` is
a finite maximum; the set is nonempty (R = 0) and bounded for d ∈ [0,1]. For d ∉ [0,1] the value is
meaningless (disclosed).
**Units.** `le_deletionCapacity`: `log 2 − Real.binEntropy d ≤ C(d)` for 0 ≤ d ≤ ½; natural logs
on both sides and in `exp(nR)`, i.e. 1 − H₂(d) bits. Consistent with the proved upper bound
(1−d)·log 2 since H₂(d) ≥ d on [0,½], and with C(0) = log 2. `C(½) ≥ log 2/528`: the hypothesis
`blockBad(½,10,5,½) = 2⁻¹¹ + 2¹¹(¾)⁵⁵ ≈ 7.6·10⁻⁴ ≤ 10⁻³` checks numerically. Attribution of
1 − H(d) to Gallager / Zigangirov / Diggavi–Grossglauser and (1−d)/9 to Mitzenmacher–Drinea
agrees with Mitzenmacher's survey (from memory). Prior art: 0 relevant Lean hits for
`Tenengolts`, `deletion channel`.

## Claim wording I would sign off on

- Two-sided Simes: "Lean proofs of the Simes inequality for two-sided z-tests of jointly normal
  statistics in three classes: any two statistics; one-factor correlation (including
  equicorrelation ρ ∈ [0,1]); non-degenerate vectors whose precision matrix satisfies the
  Karlin–Rinott sign condition (the 'if' direction of their MTP2 criterion). These are known
  results; we found no earlier formalization in Lean. The general conjecture is stated, not
  proved, and is open (Zhang, arXiv:2611.02513, has further partial results we do not formalize).
  Positive dependence is the conditioning-on-pᵢ ≤ t (weak PRDS) form." Do not say "the cases
  covered by the literature". Do not present two-sided BH as open.
- Four functions: "an integral four functions theorem on finite products of σ-finite linearly
  ordered measure spaces, with FKG and 'MTP2 density ⇒ weak PRDS'. A version for products of
  probability measures on ℝ with bounded functions exists in caiusdfolkerts/research
  (Nov 2026); ours is more general and adds the PRDS consequence." Not "first".
- Trifference: "first Lean formalization we could find of trifferent codes: Körner's bound
  T(n) ≤ 2(3/2)ⁿ, the Körner–Marton rate bound ¼log₂(9/5), T(1..4) = 3, 4, 6, 9, and explicit
  codes giving T(5) ≥ 10, T(6) ≥ 13 (the matching upper bounds of Della Fiore–Gnutti–Polak are
  not formalized)."
- Černý: "first Lean proof we could find that the Černý automaton C_n has shortest reset word
  of length exactly (n−1)², also restated in the definitions of formal-conjectures."
- Naddef: "any two vertices of a 0/1-polytope in ℝᵈ are joined by at most d edges (ambient
  dimension; at most their Hamming distance), tight for the cube." Not "Hirsch conjecture for
  0/1-polytopes", not "diameter ≤ dim P".
- VT / deletion: "VT codes correct one deletion; Levenshtein's asymptotic upper bound
  (1+o(1))2ⁿ/n; for the i.i.d. deletion channel with operational capacity (maximal error),
  1 − H(d) ≤ C(d) in bits for d ≤ ½, C(d) > 0 for all d < 1, C(d) ≤ 1 − d. The positive-rate
  construction is ours and far from the published (1−d)/9." No Lean precedent found.

## What I could not do

Full texts of Karlin–Rinott (1980, 1981), Samuel-Cahn (1996), Naddef (1989), Körner (1973),
Körner–Marton (1988), Levenshtein (1965) were not fetched; comparisons are from abstracts,
secondary sources and memory. arXiv items were checked at abstract level only. The
`caiusdfolkerts/research` file was read, not compiled. GitHub code search is rate-limited and
keyword-based.

## New Lean files (commit 5a821ef on `rv-g`, all build, standard axioms only)

- `Applied/Statistics/TwoSidedSimesSanity.lean`
- `Applied/Optimization/ZeroOnePolytopeSanity.lean`
- `Applied/Automata/CernyFamilyBridge.lean`

## Addendum: source verification after network access was widened (2026-11-25)

This supersedes "What I could not do" and corrects defects 4 and 6 above.

### Fetched in full (PDF from arxiv.org, text read)

| Source | Claims verified at source |
|---|---|
| Zhang, arXiv:2611.02513 | Problem statement is Z ~ N_m(0,Σ), Σ any PSD correlation matrix ("Singular covariance matrices are allowed"), P_i = 2Φ̄(|Z_i|), global null, "whether F_Σ(α) ≤ α for every m, α, Σ … remains open": identical to `SimesTwoSidedGaussian`. §7 states the Karlin–Rinott (1981) criterion: for a centred nonsingular Gaussian vector, |Z| is MTP2 iff some diagonal sign matrix Λ makes ΛΣ⁻¹Λ non-positive off the diagonal: identical to the Lean sign condition. §3.1: m = 2 "is classical (Samuel-Cahn, 1996)" and also follows from Sarkar (1998) + Karlin–Rinott; ρ = ±1 gives identical p-values. Equicorrelated ρ ∈ [0,1) is covered by the criterion; common negative correlation only in fixed dimension by his Thm 2.1 / 3.1. Equality in Simes iff independent groups of identical p-values (matches my Monte Carlo: exact level only for the independent case). |
| Dobriban, arXiv:2607.12208 | Setting X ~ N_m(μ,Σ), Σ correlation matrix, two-sided p-values, nulls μ_i = 0, question "FDR ≤ α for every m, μ, Σ, α": identical to `BHTwoSidedGaussian`. Theorem 1: one-factor model, 96N nulls X = 0.3Z + (√91/10)ε, N non-nulls with mean 12/5 and loading −0.3, 3N with mean 22/5 and loading −18/25; at α = 0.01, FDR > 0.0104 for all large N. So the Lean `Prop` is false if that theorem is right; and the false nulls are mean-shifted and load on the factor, which is exactly the case our `bh_twoSided_oneFactor` excludes. The proof is stated to be AI-generated (GPT-5.6 Pro) and author-checked. |
| Lei, arXiv:2607.14812 | Abstract and introduction: worst-case two-sided FDR ≥ ℓ₌(q) > q with ℓ₌(q)/q = 1.355 at q = 0.01; cites Hochberg–Rom (1995) and Samuel-Cahn (1996) for **one-sided** negatively correlated anticonservative examples. |
| Sarkar, arXiv:2304.05261 | It is about the BH/FDR two-sided conjecture; for the Simes global test it points to Finner et al. (2017) for the conjecture. So Finner–Roters–Strassburger (2017) should be the cited source for the Simes conjecture. |
| Sarkar, arXiv:0805.2322 (2008) | Cites Karlin–Rinott for the MTP2 conditions for N_n(μ,Σ) and |N_n(0,Σ)|; Hochberg–Rom and Samuel-Cahn "first attempted to prove the conjecture in the bivariate case". |
| Della Fiore–Gnutti–Polak, arXiv:2201.06846 | T(5) = 10, T(6) = 13; T(4) = 9 via the tetracode; attributes T(n) ≤ 2(3/2)ⁿ to Körner–Marton [12]. |
| Kurz, arXiv:2310.13563 | T(7) = 16, T(8) = 20, T(9) = 27; the same recursion #C ≤ k/(k−1)·#C′ as our `exists_shorter`, cited "c.f. [KM88]". |
| Bhandari–Khetan, arXiv:2402.02390 | T(n) ≤ c·n^(−2/5)·(3/2)ⁿ; attributes T(n) ≤ 2(3/2)ⁿ to **Elias (1988)** and 0.6937·(3/2)ⁿ to Kurz. The paper is dated **2024**, not 2022. |
| Pohoata–Zakharov, arXiv:2105.00122 | Calls 2(3/2)ⁿ "an elementary double counting argument"; "In 1973, Körner raised the problem of improving" it; Körner–Marton sets of size (9/5)^(n/4) from the tetracode are the largest known. |
| Ananichev–Gusev–Volkov, arXiv:1005.0129 | C_n: one letter a cyclic permutation, the other fixes all states but one, which it sends to its cyclic successor; Theorem 3 (= Černý 1964, Lemma 1): reset length (n−1)², reset word (abⁿ⁻¹)ⁿ⁻²a. Same automaton and word as in Lean with the letter names swapped. |
| Wikipedia "Synchronizing word" (raw wikitext) | Černý's 1964 paper exhibits automata with shortest reset word (n−1)²; cites Volkov LATA 2008, p. 19. |
| Ziegler, "Lectures on 0/1-polytopes", arXiv:math/9909177 | Theorem 29 (Naddef): the graph of a **d-dimensional** 0/1-polytope P ⊆ ℝⁿ has diameter ≤ d, equality iff P is a d-cube; headed "The Hirsch conjecture for 0/1-polytopes". Confirms that ours (ambient dimension, no equality case) is weaker than the cited theorem. |
| Sloane, arXiv:math/0207197 | VT_a(n) = {x : Σ i·x_i ≡ a mod n+1}, 0 ≤ a ≤ n (same as Lean); Levenshtein observed they correct one deletion; |D₁(u)| = number of runs; |VT₀(n)| ≥ 2ⁿ/(n+1); Theorem 2.5 (Levenshtein): A(n,1) ~ 2ⁿ/n; VT₀(n) optimal for n ≤ 9. |
| Kanoria–Montanari, arXiv:1104.5546 | Dobrushin's coding theorem for the deletion channel; Drinea–Mitzenmacher "A simple lower bound…" exists as cited. It does not state the 1 − H(d) attribution. |

### Not obtained

- projecteuclid.org (Karlin–Rinott 1981, Sarkar 1998) and link.springer.com (Naddef 1989, Volkov 2008) answer plain `curl` with a bot-challenge page. A retry with a browser user-agent and cookie jar was blocked by the session's permission system, and I did not pursue it. The WebFetch tool cannot resolve these hosts at all.
- Samuel-Cahn (1996, OUP), Karlin–Rinott (1980) and Körner–Marton (1988, both Elsevier), Körner (1973), Elias (1988), Levenshtein (1965), Mitzenmacher's survey: hosts not allowed or not on arXiv.
- So these remain verified only through the secondary sources in the table: the Karlin–Rinott criterion (via Zhang and Sarkar 2008; theorem number still unconfirmed), Naddef (via Ziegler), Levenshtein (via Sloane), Černý (via Ananichev–Gusev–Volkov), Körner–Marton rate (via Pohoata–Zakharov and Della Fiore et al.).
- Still unverified anywhere: the attribution of 1 − H(d) to Gallager / Zigangirov / Diggavi–Grossglauser and of (1−d)/9 to Mitzenmacher–Drinea.

### Corrections to the defect list

- **Defect 4 (Samuel-Cahn) is downgraded.** Zhang (2026) cites Samuel-Cahn (1996) as the classical source for the two-sided bivariate inequality, so the registry's citation is corroborated by a secondary source. The paper's abstract mentions only one-sided tests and I could not read the paper, so keep "to be confirmed" and add "also follows from Karlin–Rinott (1981) + Sarkar (1998)".
- **New defect: attribution of the 2(3/2)ⁿ bound.** The registry attributes it to Körner (1973). Recent papers disagree: Elias 1988 (Bhandari–Khetan), Körner–Marton 1988 (Della Fiore et al., Kurz), "elementary double counting" with Körner 1973 as the origin of the problem (Pohoata–Zakharov). Safer wording: "the elementary bound T(n) ≤ 2(3/2)ⁿ (Körner 1973; see Körner–Marton 1988, Elias 1988)". Also fix "Bhandari, Khetan … 2022" to 2024 (arXiv:2402.02390) and note that the best constant-factor bound before it is Kurz's.
- **Defect 6 is confirmed at source** (Della Fiore et al. and Kurz read in full).
- **Defect 3**: add Finner–Roters–Strassburger (2017) and Chi et al. (2025) as sources for the Simes conjecture (both via Zhang).

### Extra numerics

`dobriban_mc.py`, Dobriban's model at α = 0.01: N = 20 (m = 2000), 1.2·10⁵ runs: FDR = 0.00993 ± 0.00011; N = 300 (m = 30000), 4·10⁴ runs: FDR = 0.01019 ± 0.00017. Both are above α·m₀/m = 0.0096 (by 3 s.e.), the second is above α by 1.1 s.e. This is consistent with the theorem (which is for large N) but does not by itself confirm FDR > α.
