# Source verification of the registry citations (2026-11-25, unrestricted network)

Scope. The five red-team reports (`REDTEAM-{LOVASZ,MULTIPLE-TESTING,REGULATORY,ECON,SIMES2-CODING}.md`)
list source claims they could not check. This file records, per source, what could be opened now,
each claim checked against it, and the registry sentence that should change. Repository:
`applied-formalization-targets`, branch `main` at `ba30357`; file paths below are
relative to it. Nothing in the repository was edited.

> **Note added 2026-11-26 (housekeeping).** This is a copy of the report as written. Its line
> numbers refer to `main` at `ba30357`. The "registry change" column was applied to the registry
> headers afterwards, on branch `housekeeping-1`; items marked STILL UNVERIFIED keep their hedges.
> The fetching and reading were done by a machine (Claude), not by a person.

Verdicts: **CONFIRMED** (at the source, or — where marked "(secondary)" — by a fetched paper that
quotes the statement with its number), **CORRECTED** (the registry or a red-team report says
something the source contradicts; the right value is given), **STILL UNVERIFIED**.

Quotes are verbatim from the fetched text, at most 25 words. Greek letters lost by `pdftotext`
are restored in brackets where the surrounding text fixes them.

## 0. What was reachable

| Route | Result |
|---|---|
| Publisher sites: `academic.oup.com`, `onlinelibrary.wiley.com`, `www.tandfonline.com`, `www.sciencedirect.com`, `dl.acm.org`, `epubs.siam.org`, `gallica.bnf.fr` | HTTP 403 to `curl` (bot wall). Not bypassed. |
| `projecteuclid.org` (also its open-access PDFs), `www.jstor.org`, `link.springer.com` (also its open-access PDFs), `repository.lib.ncsu.edu` | Bot-challenge page (Incapsula / JS challenge / Anubis). Not bypassed. |
| `ieeexplore.ieee.org` | HTTP 202, empty body. |
| `web.cs.elte.hu` (Lovász's page), `web.archive.org`, `www2.math.uu.se` | Connection reset / tunnel closed by the egress proxy on every attempt. |
| `apps.dtic.mil` | "Under maintenance" page. |
| `infoscience.epfl.ch`, `api.core.ac.uk`, `archive.org/wayback/available` | HTTP 429 on almost every request. |
| Works: `api.unpaywall.org`, `api.crossref.org`, `api.openalex.org`, `www.ebi.ac.uk/europepmc` (REST and full-text XML), `arxiv.org`, author and course pages (`math.tau.ac.il`, `eecs.harvard.edu`, `cs.cornell.edu`, `cs.toronto.edu`, `mwarmuth.bitbucket.io`, `sci2s.ugr.es`, `math.utoronto.ca`, `cs.rit.edu`), `zenodo.org`, `authors.library.caltech.edu`, `drops.dagstuhl.de`, `cran.r-project.org` | Used below. |
| `WebFetch` tool | Cannot resolve any of these hosts in this session; everything was fetched with `curl` and read with `pdftotext` / `tesseract`. |

"Abstract only" below means the publisher abstract as served by OpenAlex / Europe PMC / Crossref;
page ranges are from Crossref and OpenAlex. Copies marked "course-hosted" are JSTOR- or
publisher-stamped scans placed on a university course page; they are the published text, but not
an official open-access copy.

## 1. Shannon capacity (REDTEAM-LOVASZ)

### 1.1 L. Lovász, "On the Shannon capacity of a graph", IEEE Trans. Inform. Theory 25(1) (1979) 1–7
Obtained: **nothing of the paper itself** (author page: TLS reset; Wayback: tunnel closed; IEEE: empty
202; Unpaywall, OpenAlex, Semantic Scholar: closed; a `cocalc.com` share link serves only a
JavaScript shell). Bibliographic data from Crossref. Secondary source newly fetched in full:
S. Hu, I. Tamo, O. Shayevitz, "A bound on the Shannon capacity via a linear programming variation",
arXiv:1804.05529, which quotes Lovász's statements with their numbers ([13] is the 1979 paper).

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Vol. 25, pp. 1–7, 1979 | Crossref / OpenAlex: 25 (1), 1–7, 1979 | CONFIRMED | none |
| Theorem 1 is `Θ(G) ≤ ϑ(G)` | arXiv:1804.05529 §2: "Theorem 2. [13, Theorem 1] Θ(G) ≤ ϑ(G)." (second independent secondary, after Wikipedia) | CONFIRMED (secondary) | `Targets/InformationTheory/LovaszThetaBound.lean:10`: "Theorem 1 (`Θ(G) ≤ ϑ(G)`; numbering to be confirmed)" → drop "numbering to be confirmed" for Theorem 1 |
| Corollary 5 is `ϑ(Cₙ) = n cos(π/n)/(1+cos(π/n))`, odd `n` | arXiv:1804.05529 §2: "Proposition 1. [13, Corollary 5] For odd n, ϑ(Cn) = n cos(π/n) / (1 + cos(π/n))" | CONFIRMED (secondary; agrees with formal-conjectures' "[La79, Corollary 5]") | `Targets/InformationTheory/LovaszOddCycle.lean:10` and `LovaszThetaBound.lean:10`: drop "numbering to be confirmed" after "Corollary 5" |
| Theorem 2 is `Θ(C₅) = √5` | no fetched source gives the number. arXiv:1804.05529 says only "for the pentagon graph, Lovász proved that Θ(C5) ≤ ϑ(C5) = √5" | STILL UNVERIFIED | `Targets/InformationTheory/ShannonCapacityC5.lean:9`: keep "Theorem 2 (numbering to be confirmed)" or cite without number |
| "Lemmas 1–3" lead to Theorem 1 | not checkable (Wikipedia cites only "Lemma 2") | STILL UNVERIFIED | `LovaszThetaBound.lean:10`: "Lemmas 1–3" stays unconfirmed; safest wording "the lemmas preceding Theorem 1" |
| Lovász's own wording of the product, of Θ, of orthonormal representations | paper not opened | STILL UNVERIFIED | none (the conventions are confirmed through Polak–Schrijver and Wikipedia, see REDTEAM-LOVASZ) |

Also seen in arXiv:1804.05529 (not used by the registry): "[13, Theorem 5]" (dual formula for ϑ),
"[13, Theorem 7] ϑ(G ⊠ H) = ϑ(G)·ϑ(H)".

### 1.2 Baumert, McEliece, Rodemich, Rumsey, Stanley, Taylor, "A combinatorial packing problem" (1971)
Obtained: nothing (AMS proceedings volume; no open copy found). Secondary, fetched in full:
Mathew–Östergård, arXiv:1504.01472 (= Des. Codes Cryptogr. 84 (2017) 13–22); Polak–Schrijver,
published version (Inform. Process. Lett. 143 (2019) 37–40, course-hosted copy at `cs.rit.edu`).

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| `α(C₇^⊠3) = 33` is Baumert et al. | Mathew–Östergård §1: "Baumert et al. [4] used exhaustive search to show that G(3, 7) = 33"; Polak–Schrijver Table 1 note d | CONFIRMED (two secondaries) | none |
| `α(C₇^⊠2) = 10` has a citation | Polak–Schrijver Table 1 note a: "α(C_n²) = ⌊(n² − n)/4⌋ [3, Theorem 2]" | CONFIRMED (secondary) | `Targets/InformationTheory/ShannonCapacityC7Lower.lean:9`: "`α(C₇^{⊠2}) = 10` is classical" → "… is Baumert et al. 1971, Theorem 2 (as cited by Polak–Schrijver)" |
| `α(C₇^⊠4) ≥ 108`: Vesel–Žerovnik 2002 | Crossref: A. Vesel, J. Žerovnik, "Improved lower bound on the Shannon capacity of C7", Inform. Process. Lett. 81 (5) (2002) 277–282; Mathew–Östergård §1: "Vesel and Žerovnik [25] proved that G(4, 7) ≥ 108 with simulated annealing" | CONFIRMED (bibliography at Crossref; statement secondary) | `ShannonCapacityC7Lower.lean:9`: "(A. Vesel, J. Žerovnik, 2002, to be confirmed)" → "A. Vesel, J. Žerovnik, Inform. Process. Lett. 81 (2002) 277–282" |
| `α(C₇^⊠5) ≥ 350`: Mathew–Östergård 2017 | arXiv:1504.01472 abstract: "α(C₇⁵) ≥ 350"; "c(C7) ≥ 350^{1/5} > 3.2271" (primary, arXiv version) | CONFIRMED | none |
| Baumert et al.: exact statements at source, page range 97–108 | pages only as cited by Polak–Schrijver | STILL UNVERIFIED | none |

## 2. Multiple testing (REDTEAM-MULTIPLE-TESTING, REDTEAM-REGULATORY)

### 2.1 Benjamini–Yekutieli, Ann. Statist. 29(4) (2001) 1165–1188
Obtained: **full text**, author-hosted PDF
`https://www.math.tau.ac.il/~ybenja/MyPapers/benjamini_yekutieli_ANNSTAT2001.pdf` (24 pages, the
journal typesetting with page numbers).

| Claim | Quote and location | Verdict | Registry change |
|---|---|---|---|
| Journal data | header: "2001, Vol. 29, No. 4, 1165–1188" | CONFIRMED | none |
| PRDS is defined in "Section 2.1" | It is not. §1.3 "The problem", p. 1168: "Property PRDS. For any increasing set D, and for each i ∈ I0, P(X ∈ D ∣ Xi = x) is nondecreasing in x." §2.1 is "The FDR criterion"; §2.2 "Positive dependency" compares PRDS with other notions | **CORRECTED** | `Targets/Statistics/ClassicalPRDS.lean:9`: "Section 2.1 (definition of PRDS)" → "Section 1.3 (Property PRDS, p. 1168; compared with other notions in Section 2.2)" |
| Theorem 1.2 | §1.4, p. 1168: "If the joint distribution of the test statistics is PRDS on the subset of test statistics corresponding to true null hypotheses", BH "controls the FDR" at level `≤ (m0/m) q` | CONFIRMED | none (`PositiveDependence.lean:9`, `PRDSGaussian.lean:9`) |
| Theorem 1.3 | §1.4, p. 1169: "When the Benjamini Hochberg procedure is conducted with q/(Σ 1/i) taking the place of q in (1), it always controls the FDR" | CONFIRMED | none (`BenjaminiYekutieli.lean:9`) |
| §3.1 Case 1 = multivariate normal; hypothesis | §3.1, p. 1172: "Case 1 (Multivariate normal test statistics)"; "Assume that for each i ∈ I0, and for each j ≠ i, σij ≥ 0, then the distribution of X is PRDS over I0." One-sided tests, `µi = 0` vs `µi > 0`. p. 1173: "the intercorrelations among the test statistics corresponding to the false null hypotheses need not be nonnegative" | CONFIRMED — the hypothesis is exactly the one in `PRDSGaussian` (true-null coordinates have non-negative covariance with every coordinate) | `Targets/Statistics/BHOneFactor.lean:9`: "(… case number to be confirmed)" → "Case 1"; `BHEquicorrelated.lean:11`: "(… section number to be confirmed)" → "Section 3.1, Case 1; the equicorrelated case is the simulation setting named in Section 1.3"; `PRDSCommonFactor.lean:9`: "case number to be confirmed" → "Case 1 (normal statistics); latent-variable structures are Case 2" |
| Other cases of §3.1 | Case 2 "Latent variable models" (unidimensional latent variable ⇒ PRDS on any subset), Case 3 "Absolute values of multivariate normal and t", Case 4 "Studentized multivariate normal" (not PRDS; FDR control for q < 1/2 via Remark 4.2) | CONFIRMED | — |
| Many-to-one comparisons are an example "in Section 3.1" | They are in **§3.2 "Applied problems", "Problem 3 (Many-to-one comparisons in clinical trials)"**, p. 1175: "(Yi − Y0)/ci is multivariate normal with ρij > 0, hence PRDS, thus according to Case 4, X is PRDS" (Studentized) | **CORRECTED** | `Targets/Statistics/ManyToOneControl.lean:9`: "Section 3.1 (comparisons of several treatments with a common control … exact location to be confirmed)" → "Section 3.2, Problem 3 (p. 1175; Studentized statistics, through Case 4 of Section 3.1)"; `ManyToOneGaussian.lean:9`: "that comparisons with a common control are named there as an example is to be confirmed" → "they are, in Section 3.2, Problem 3" |
| "Independence is a special case of PRDS" is "a remark" | Not a numbered remark. §3.1 Case 3, p. 1174: "If Σ = I, the components of Y are independent and thus PRDS over any subset." | CONFIRMED (location supplied) | `Targets/Statistics/PRDSIndependent.lean:9`: "stated as a remark … (exact location to be confirmed)" → "stated in passing in Section 3.1, Case 3 (p. 1174)" |
| Equality `FDR = m₀q/m` for independent continuous statistics | §5, p. 1180: Theorem 5.1: for independent test statistics the procedure controls the FDR at `(m0/m) q`, and "If the test statistics are also continuous, the FDR is exactly (m0/m) q." | CONFIRMED; number is **Theorem 5.1**. Their hypothesis is joint independence ("If the test statistics are jointly independent"); ours (each null p-value independent of the others) is weaker | `Targets/Statistics/BHExact.lean:9`: "Y. Benjamini, D. Yekutieli, Ann. Statist. 29 (2001) … (exact statements to be confirmed)" → "… Theorem 5.1" |
| A block structure is discussed in §3.1 | No. Nearest: Case 3, last paragraph (a dependent subset and independent components), and §3.2 Problem 1 (subgroup analysis) | **CORRECTED** (answer is no) | `Targets/Statistics/PRDSGroupFactor.lean:9`: "(… whether a block structure is discussed there is to be confirmed)" → "(a block structure is not discussed there)" |
| The two facts of `PRDSExamples` are "stated there in this form" | No. §2.2 only notes invariance under "comonotone transformations in each of the coordinates" | **CORRECTED** (answer is no) | `Targets/Statistics/PRDSExamples.lean:9`: "(whether these two facts are stated there in this form is to be confirmed)" → "(not stated there; they are elementary consequences of the definition in Section 1.3)" |

Two further sentences worth carrying into the registry: §1.2, p. 1167, restates the procedure as
"k = max{i : p(i) ≤ (i/m) q}" (non-strict, largest index); and §2.3, p. 1171: "the result had
already been proved by Seeger (1968)" — the Simes equality has an earlier source than Simes (1986)
(`Targets/Statistics/SimesIdentity.lean:9` could add "first proved by Seeger (1968) according to
Benjamini–Yekutieli (2001), Section 2.3").

### 2.2 Benjamini–Hochberg, J. R. Statist. Soc. B 57(1) (1995) 289–300
Obtained: **full text**, author-hosted JSTOR scan
`https://www.math.tau.ac.il/~ybenja/MyPapers/benjamini_hochberg1995.pdf`, read by OCR.

| Claim | Quote and location | Verdict | Registry change |
|---|---|---|---|
| Theorem 1, pp. 289–300 | §3.1, p. 293: "Theorem 1. For independent test statistics and for any configuration of false null hypotheses, the above procedure controls the FDR at q*." The Lemma under it gives the bound `(m0/m) q*` | CONFIRMED | none (`BenjaminiHochberg.lean:9`) |
| Hypotheses on the false nulls | p. 293: "Note that the independence of the test statistics corresponding to the false null hypotheses is not needed for the proof of the theorem." | CONFIRMED — same shape as the registry's hypothesis | `BHExact.lean` may cite this Remark for the inequality |
| Sorted rule and tie convention | procedure (1), p. 293 (OCR damaged at the inequality sign); BY 2001 p. 1167 restates it as `k = max{i : p(i) ≤ (i/m) q}` | CONFIRMED (through BY's restatement) | `Targets/Statistics/SortedProcedures.lean:9`: for BH, "(exact wording and tie conventions to be confirmed)" can go |

### 2.3 Simes, Biometrika 73(3) (1986) 751–754
Obtained: **abstract only** (OUP 403, JSTOR bot wall).

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 73 (3), 751–754 | CONFIRMED | none |
| Equality under independence is Simes's result | abstract: "For independent tests the procedure has type I error probability equal to α."; Hommel 1988 p. 383: "he proved that the level is exactly equal to α if the test statistics are independent" | CONFIRMED | none |
| Theorem number | not visible in any fetched text | STILL UNVERIFIED | `Targets/Statistics/SimesIdentity.lean:9`: keep "(theorem numbering to be confirmed)" or write "the main result" only |

### 2.4 Hochberg, Biometrika 75(4) (1988)
Obtained: **abstract only** (the course-hosted copy at `www2.math.uu.se` is unreachable through the proxy).

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Pages | Crossref and OpenAlex: 800–**802**; Wright's 1992 abstract cites "Biometrika 75, 800-802" | CONFIRMED 800–802. REDTEAM-MULTIPLE-TESTING §C ("800–803 (R help; I wrote 800–802 from memory)") has it backwards | registry gives no pages; if added, use 800–802 |
| Step-up rule | abstract: "The new procedure rejects all hypotheses with smaller or equal p-values to that of any one found less than its critical value." | CONFIRMED in prose | — |
| Exact wording and tie convention (`≤` or `<`) | not in the abstract | STILL UNVERIFIED | `Targets/Statistics/SortedProcedures.lean:9`: keep the caveat for Hochberg |

### 2.5 Hommel, Biometrika 75(2) (1988) 383–386
Obtained: **full text**, course-hosted JSTOR scan `https://sci2s.ugr.es/keel/pdf/algorithm/articulo/1988-Hommel-BIO.pdf`.

| Claim | Quote and location | Verdict | Registry change |
|---|---|---|---|
| Journal data | cover: "Vol. 75, No. 2 (Jun., 1988), pp. 383-386" | CONFIRMED | none |
| "Hommel's procedure" is the closed test with Simes local tests | Summary: "It is based on the principle of closed test procedures (Marcus, Peritz & Gabriel, 1976) and controls the multiple level α."; §2: "When all overall tests are tests as proposed by Simes, the arising multiple test procedure …" | CONFIRMED **at source**. REDTEAM-MULTIPLE-TESTING defect 3 ("the closed Simes test, not Hommel's 1988 stagewise algorithm") should be reworded: the 1988 paper *defines* the procedure as the closure of Simes tests and then gives a rule to carry it out | `Targets/Statistics/HommelAdjusted.lean:9` and the Hommel headers: may say "defined in Hommel (1988), Section 2, as the closed test procedure with Simes tests" |
| The shortcut rule (not formalized) | §2, p. 384: "compute j = max{i ∈ {1,…,n}: P(n−i+k) > kα/i for k = 1,…,i}"; if no such `i` exists reject all, "otherwise reject all Hi with Pi ≤ α/j." | CONFIRMED (wording and tie convention: strict `>` in the definition of `j`, `≤` for rejection) | announcement wording: "Hommel's shortcut (1988, Section 2) is not formalized" |
| Validity condition | §2: "controls the multiple level α provided each of Simes's tests for HI is a level α test"; in particular when "the n tests are independent." | CONFIRMED | — |
| Hommel 1983: level-α version with `Cₙ = 1 + 1/2 + … + 1/n` | §1, p. 383: "reject H0, if P(k) ≤ kα/(nCn) for at least one k (1 ≤ k ≤ n)", with `Cn = 1 + 1/2 + … + 1/n` | CONFIRMED (as quoted by Hommel himself) | see 2.6 |

### 2.6 Hommel, Biometrical J. 25(5) (1983) 423–430
Obtained: **abstract only**.

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 25 (5), 423–430 (DOI 10.1002/bimj.19830250502) | CONFIRMED | none |
| The bound and its attainment | abstract: "Admitted are arbitrary dependences among the tests; for each method sharp upper bounds for the error probability are obtained."; Samuel-Cahn 1996 abstract: "He gave an attainable upper bound for its anticonservativeness." | CONFIRMED (abstracts) | — |
| Statement number | not visible | STILL UNVERIFIED | `Targets/Statistics/SimesSharp.lean:9`: keep "statement number to be confirmed" |

### 2.7 Holm, Scand. J. Statist. 6 (1979) 65–70
Obtained: **abstract only** (JSTOR bot wall; the copy at `ime.usp.br` returns 403).

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal data | OpenAlex: vol. 6, 65–70; Wright's abstract: "Scandinavian Journal of Statistic 6, 65-70" | CONFIRMED | none |
| Result | abstract: "It is shown that the test has a prescribed level of significance protection against error of the first kind for any combination of true hypotheses." | CONFIRMED | — |
| Exact wording, tie convention | not in the abstract | STILL UNVERIFIED | `SortedProcedures.lean:9`: keep the caveat for Holm |

### 2.8 Šidák, J. Amer. Statist. Assoc. 62(318) (1967) 626–633
Obtained: **full text**, course-hosted publisher PDF `https://www.math.utoronto.ca/mccann/assignments/477/Sidak67.pdf`.

| Claim | Quote and location | Verdict | Registry change |
|---|---|---|---|
| Journal data | cover page: "62:318, 626-633" | CONFIRMED | none |
| What the paper proves | Corollary 1 (§2, p. 628): `P(∣X1∣ ≤ c1, …, ∣Xk∣ ≤ ck) ≥ ∏ P(∣Xi∣ ≤ ci)` for centred normal vectors (inequality (4)) | CONFIRMED — it is the rectangle inequality, as REDTEAM-MULTIPLE-TESTING says | none |
| The `1 − (1 − α)^{1/k}` threshold | §3, p. 629: `c_α` chosen "to satisfy Φ(c_α) = ½[1 + (1 − α)^{1/k}]"; "we may always act as if all coordinates of the vectors Y_ν were independent" | CONFIRMED | — |
| Exactness under independence "stated in the literature" there | Not stated as a result. The independent case is the calibration: p. 632, "the confidence rectangle must be chosen to be valid in particular for independent variables". No multiple-testing statement in the paper | **CORRECTED** (the question in the header is answered: not in this paper) | `Targets/Statistics/SidakExact.lean:9`: "(where it is stated in the literature: to be confirmed)" → "(not stated in Šidák 1967, which uses the independent case only to calibrate the rectangle, Section 3, p. 629)" |

### 2.9 Sarkar, Ann. Statist. 26(2) (1998) 494–504
Obtained: **abstract only** (Project Euclid's open PDF is behind a bot challenge). Secondary, full
text: S. K. Sarkar, "On the Simes inequality and its generalization", arXiv:0805.2322.

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 26 (2), 494–504 | CONFIRMED | none |
| Hypothesis is MTP2 | abstract: "probability inequalities involving the ordered components of an MTP2 random vector … provide an analytical proof of an important conjecture" | CONFIRMED | `BHOneFactor.lean:9`: "exact hypotheses to be confirmed" → "MTP2" |
| Theorem number | Sarkar 2008, §1: "Theorem 3.1 in Sarkar [22] establishing the Simes conjecture" | CONFIRMED (secondary, same author): **Theorem 3.1** | `Targets/Statistics/PRDSGaussian.lean:9`: "theorem numbers to be confirmed" → "Sarkar (1998), Theorem 3.1" (the 2002 number stays open) |
| Caveat | Sarkar 2008, §1: "while the main theorem is correct, there is a flaw in his proof of the corollary" (Corollary 3.1, multivariate t) | new information | do not cite Sarkar (1998) Corollary 3.1 for Studentized statistics |

### 2.10 Bretz, Maurer, Brannath, Posch, Statist. Med. 28(4) (2009) 586–604
Obtained: **abstract only** (Wiley 403; the Vienna preprint URL is 404; no open copy at Unpaywall/OpenAlex/Europe PMC).

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 28 (4), 586–604 | CONFIRMED | none |
| "Algorithm 1" is in the 2009 paper; order-independence is proved there | Bretz et al. 2011 (full text, §2): "tailoring Algorithm 1 in Bretz et al. (2009)"; "As shown by Bretz et al. (2009), the weights wj(J), j ∈ J are unique." | CONFIRMED (through the 2011 paper) | none |
| Statement number of the theorem; section and figure numbers of the Holm / fixed-sequence / fallback examples | not visible | STILL UNVERIFIED | `Targets/Statistics/GraphicalApproach.lean:9` and `GraphicalInstances.lean:9`: keep the caveats |

### 2.11 Bretz, Posch, Glimm, Klinglmueller, Maurer, Rohmeyer, Biometrical J. 53(6) (2011) 894–913
Obtained: **full text** (Europe PMC XML, PMC3427907).

| Claim | Quote and location | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 53 (6), 894–913 | CONFIRMED | none |
| Simes-based graphical tests: section | section title "3.3 Weighted Simes tests" | CONFIRMED: **Section 3.3** | `Targets/Statistics/WeightedSimes.lean:9`: "(Simes-based graphical closed tests; section to be confirmed)" → "Section 3.3" |
| Worked example p-values | §3.1: "the unadjusted p-values p1 = 0.01, p2 = 0.005, p3 = 0.1, and p4 = 0.5. Then we can reject both H1 and H2" | CONFIRMED | — |
| Level of the example | Table 2 caption: "for the example from Figure 1 and α = 0.025"; the level of Figure 3 itself is in the image | CONFIRMED that `α = 0.025` is the level this paper uses with this graph (Table 2, Example 3); not for Figure 3 specifically | sanity docstring may say "α = 0.025 as in Table 2 of Bretz et al. (2011)" |
| Closed test = sequentially rejective procedure | §3.1: "a closed weighted Bonferroni test procedure using the weights from Algorithm 1 leads to exactly the same test decisions as" the sequentially rejective procedure of Algorithm 2 | CONFIRMED | — |

### 2.12 Wright, Biometrics 48(4) (1992) 1005–1013
Obtained: **abstract only**.

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Contains Holm-, Hochberg- and Hommel-adjusted p-values and closed tests in general; not BH | abstract: "adjusted P-values based on the Bonferroni procedure and modifications of that procedure by Holm (1979 …), Hochberg (1988 …), and Hommel (1988 …)"; "a procedure is outlined for obtaining adjusted P-values for any closed test procedure" | CONFIRMED | `Targets/Statistics/StepUpAdjusted.lean:9`: cite Wright for the Hochberg-adjusted p-value only; the BH-adjusted p-value is not in Wright (1992) |
| Formulas and statement numbers; last page 1013 | Crossref has only the first page 1005 | STILL UNVERIFIED | keep caveats in `HolmAdjusted.lean:9`, `HolmAdjustedSorted.lean:9`, `HommelAdjusted.lean:9`, `StepUpAdjusted.lean:9` |

### 2.13 Finner–Roters, Biometrical J. 43(8) (2001) 985–1005
Obtained: **abstract only**. The abstract speaks of "some bounds for the FDR and the EER" and does
not mention the exact equality. Verdict on "equality … Finner–Roters (2001)": STILL UNVERIFIED at
source (supported only by Finner–Dickhaus–Roters 2009, see REDTEAM-MULTIPLE-TESTING). Registry:
`BHExact.lean:9` — keep "(exact statements to be confirmed)" for this reference only.

### 2.14 Maurer–Bretz, Stat. Biopharm. Res. 5(4) (2013) 311–320
Obtained: **abstract only** (T&F 403).

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 5 (4), 311–320 | CONFIRMED | none |
| Main result | abstract: "Under mild monotonicity conditions on the error spending functions, this allows the use of sequentially rejective graphical procedures in group sequential trials." | CONFIRMED | — |
| Section and page numbers | not visible | STILL UNVERIFIED | `Targets/Statistics/GroupSequentialGraphical.lean:9`: keep |
| Jennison–Turnbull 1989 page range "305-361" | Crossref (DOI 10.1111/j.2517-6161.1989.tb01433.x): J. R. Statist. Soc. B 51 (3), **305–334** | **CORRECTED** per Crossref (305–334 is the paper; any discussion pages after it were not checked) | `GroupSequentialGraphical.lean:9`: "51 (1989) 305-361 (to be confirmed)" → "51 (1989) 305–334" |

### 2.15 Strassburger–Bretz, Statist. Med. 27(24) (2008) 4914–4927
Obtained: **abstract only**. Secondary, full text: Brannath, Kluge, Scharpenberg, "Informative
simultaneous confidence intervals for graphical test procedures", arXiv:2402.13719.

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 27 (24), 4914–4927 | CONFIRMED | none |
| Scope | abstract: "simultaneous confidence intervals that are compatible with a certain class of closed test procedures using weighted Bonferroni tests for each intersection hypothesis" | CONFIRMED | — |
| Bounds of rejected hypotheses when not all are rejected | arXiv:2402.13719 §3.1: "the bounds for rejected hypotheses are only informative if all hypotheses are rejected"; §4: "would give e.g. L1 = −δ1 if HE1 is rejected but not HE2" | CONFIRMED (secondary) for that part of `compatible_bounds_sequential` | — |
| "Theorem 1"; exact form of the all-rejected case | not visible | STILL UNVERIFIED | `Targets/Statistics/CompatibleBounds.lean:9`: keep the caveat |

### 2.16 Hsu–Berger, J. Amer. Statist. Assoc. 94(446) (1999) 468–482
Obtained: **abstract only** (the NC State technical-report copy is behind a bot wall). Journal data
CONFIRMED (Crossref). Method (abstract): "a fundamentally different, confidence set-based
justification by partitioning the parameter space" — CONFIRMED. Theorem number: STILL UNVERIFIED
(`CompatibleBounds.lean:9`, keep).

### 2.17 Two-stage adaptive designs
Obtained: **abstracts only** for all six papers. Secondary, raw full text (Europe PMC XML, not a
model summary): Bauer, Bretz, Dragalin, König, Wassmer, Stat. Med. 35 (2016), PMC6680191; Edwards
et al., Trials 21 (2020), PMC7718653.

| Source and claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Bauer–Köhne, Biometrics 50(4) (1994) 1029–1041: product test, early stopping | abstract: "Stopping rules for Fisher's product criterion in terms of critical limits for the p-value in the first subsample are introduced, including early stopping" | CONFIRMED (content). First page 1029 at Crossref; last page 1041 and the place of `α₁ + c(ln α₀ − ln α₁)` not visible | `Targets/Statistics/CombinationTests.lean:9`: keep "places of the formulas … to be confirmed" — STILL UNVERIFIED |
| Lehmacher–Wassmer, Biometrics 55(4) (1999) 1286–1290 | Crossref pages; abstract: "based on the inverse normal method for combining the results of the separate stages" | CONFIRMED (pages, method) | `Targets/Statistics/InverseNormalCombination.lean:9`: "Page numbers … to be confirmed" → pages confirmed; places of statements STILL UNVERIFIED |
| Cui–Hung–Wang, Biometrics 55(3) (1999) 853–857 | Crossref pages; abstract: "developed by modifying the weights used in the traditional repeated significance two-sample mean test" | CONFIRMED (pages, method) | same line |
| Brannath–Posch–Bauer, JASA 97(457) (2002) 236–244 | Crossref pages; abstract: "a recursive application of the two-stage combination tests for p values" | CONFIRMED (pages, content). The term "p-clud" is not in the abstract nor in the 2016 review | `CombinationTests.lean:9`: "(the "p-clud" condition …)" — STILL UNVERIFIED for the term |
| Müller–Schäfer, Biometrics 57(3) (2001) 886–891; Stat. Med. 23(16) (2004) 2497–2508 | Crossref pages; 2004 abstract: "It is based on the conditional rejection probability of a decision variable." | CONFIRMED | `Targets/Statistics/ConditionalError.lean:9`: the sentence "Titles, page, theorem and equation numbers are from m[emory]" → titles and pages confirmed for Müller–Schäfer, Chen–DeMets–Lan, Mehta–Pocock, Cui–Hung–Wang, Lehmacher–Wassmer, Proschan–Hunsberger (Biometrics 51 (1995) 1315–1324, per the 2016 review's reference list), Gao–Ware–Mehta (J. Biopharm. Stat. 18 (6) (2008) 1184–1196, Crossref); theorem and equation numbers STILL UNVERIFIED |
| Chen–DeMets–Lan, Stat. Med. 23(7) (2004) 1023–1038: the 50 % rule | abstract: "The unblinded interim result is considered promising if the conditional power is greater than 50 per cent"; "increasing the sample size when the unblinded interim result is promising will not inflate the type I error rate" | CONFIRMED (primary abstract). Abstract says "greater than"; Lean has `≥` | — |
| Mehta–Pocock, Stat. Med. 30(28) (2011) 3267–3284 | abstract: "we here define those promising circumstances in which a conventional final inference can be performed while preserving the overall type-1 error" | CONFIRMED (pages, content) | — |
| Conditional validity of the second-stage p-value | Bauer et al. 2016: "the conditional distribution of the second stage p-value q, given the first stage data, is under H stochastically larger or equal to the uniform distribution" | CONFIRMED (secondary, now quoted from the raw text) | — |

### 2.18 Dunnett, J. Amer. Statist. Assoc. 50(272) (1955) 1096–1121
Obtained: **nothing** (T&F 403, JSTOR bot wall; the copy at `edisciplinas.usp.br` is behind a login).
Journal data CONFIRMED (Crossref). Section numbers and the estimated-variance setting: STILL
UNVERIFIED (`Targets/Statistics/Dunnett.lean:9`, keep "section numbers to be confirmed"). Other
entries of that source line, from Crossref: Marcus–Peritz–Gabriel, Biometrika 63 (3) (1976)
655–660 — CONFIRMED; Dunnett–Tamhane, Stat. Med. 10 (6) (1991) 939–947 — CONFIRMED (drop "to be
confirmed" for the bibliographic data).

### 2.19 Berger, Technometrics 24(4) (1982) 295–300; Berger–Hsu, Statist. Sci. 11(4) (1996) 283–319
Obtained: **abstracts only** (the Florida State technical report at DTIC: site under maintenance).

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 24 (4), 295–300; 11 (4), 283–319; Morikawa–Yoshida, J. Biopharm. Stat. 5 (3) (1995) 297–306 | CONFIRMED | `Targets/Statistics/IntersectionUnion.lean:9`: "(page numbers to be confirmed)" can go |
| Level and size results | 1982 abstract: "attaining exactly a prespecified consumer's risk"; "more general hypothesis-testing results concerning null hypotheses consisting of the unions of sets" | CONFIRMED (content) | — |
| "Theorems 1 and 2" in both papers | not visible | STILL UNVERIFIED | `IntersectionUnion.lean:9`, `CombinedPValues.lean:9`: keep |

### 2.20 Schuirmann, J. Pharmacokin. Biopharm. 15(6) (1987) 657–680
Obtained: **full text** (Zenodo record 1232484, listed by Unpaywall).
Journal data CONFIRMED (header "Vol. 15, No. 6, 1987"). t-test version CONFIRMED (the paper works
with 40 degrees of freedom etc.). On the level, p. 669: "The true level never exceeds the nominal level". Registry (`IntersectionUnion.lean:67`, "Schuirmann's paper treats the
t-test version") is accurate; no change.

### 2.21 Karlin–Rinott, Ann. Statist. 9(5) (1981) 1035–1049
Obtained: **abstract only** (Project Euclid bot challenge). Secondary, full text: Genest–Ouimet,
arXiv:2112.12283; Sarkar, arXiv:0805.2322.

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 9 (5), 1035–1049 | CONFIRMED | none |
| Necessary and sufficient condition | abstract: "we determine necessary and sufficient conditions for total positivity of absolute value multinormal variables" | CONFIRMED | — |
| It is Theorem 3.1; sign condition | Genest–Ouimet §2: "Theorem 3.1 of Karlin and Rinott [8] finds an equivalence between Condition (I) and the requirement" that "There exists a signature matrix D ∈ R^{d×d} such that var(DX)^{-1} has nonpositive off-diagonal elements"; Sarkar 2008 §2: "the off-diagonals of −DΣ^{-1}D are non-negative for some diagonal matrix D with diagonal entries ±1" | CONFIRMED (secondary): **Theorem 3.1**, and the statement is the registry's `B i j d i d j ≤ 0` | `Targets/Statistics/TwoSidedKarlinRinott.lean:10`: drop "statement and number to be confirmed"; `TwoSidedOneFactor.lean:10`: "(… theorem number to be confirmed)" → "Theorem 3.1" |

### 2.22 Karlin–Rinott, J. Multivariate Anal. 10(4) (1980) 467–498
Obtained: **nothing** (ScienceDirect 403; no copy at CORE). Journal data CONFIRMED (Crossref).
"Theorem 2.1 (integral form)" and "absolute values of a bivariate normal vector are MTP2":
STILL UNVERIFIED at source (`FourFunctionsIntegral.lean:9`, `TwoSidedSimesBivariate.lean:10`,
keep). Sarkar 2008 cites "[12, 13]" (the 1980 and 1981 papers) jointly for the two MTP2 criteria,
which supports citing both.

### 2.23 Samuel-Cahn, Biometrika 83(4) (1996) 928–933
Obtained: **abstract only**.

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 83 (4), 928–933 | CONFIRMED | none |
| The paper has the two-sided bivariate normal case | abstract: "Two-sided tests based on bivariate normal variables are always conservative." | CONFIRMED. **REDTEAM-SIMES2-CODING defect 4 is wrong** ("I could not confirm any two-sided statement there"; "Wrong source for the bivariate case"): the abstract states it in so many words, after the one-sided sentences | `Targets/Statistics/TwoSidedSimesBivariate.lean:10`: "(two-sided tests, two normal statistics; to be confirmed)" → "(abstract: two-sided tests based on bivariate normal variables are always conservative)". Keep this citation; do not replace it by Hochberg–Rom |

## 3. Economics (REDTEAM-ECON)

### 3.1 Caragiannis, Kurokawa, Moulin, Procaccia, Shah, Wang, ACM Trans. Econ. Comput. 7(3) (2019), Article 12
Obtained: **full text** of the journal version, author-hosted `https://www.cs.toronto.edu/~nisarg/papers/mnw.pdf`
(32 pages, running head "Vol. 7, No. 3, Article 12. Publication date: September 2019").

| Claim | Quote and location | Verdict | Registry change |
|---|---|---|---|
| Journal data | running head; Crossref 7 (3), 1–32 | CONFIRMED | none |
| Definition of PMMS | "Definition 4.3 (α-Pairwise Maximin Share Guarantee)": `v_i(A_i) ≥ α · max_{B ∈ Π₂(A_i ∪ A_j)} min{v_i(B₁), v_i(B₂)}` for all `i, j` | CONFIRMED — same as `IsApproxPMMS` | `Targets/Economics/PMMS.lean:13`: add "Definition 4.3" |
| Their EFX | Definition 4.5 (EFX): "∀ i, j ∈ N, ∀ g ∈ A_j such that v_i(g) > 0, v_i(A_i) ≥ v_i(A_j \ {g})" | CONFIRMED: the **positive-goods form** | — |
| PMMS ⇒ EFX: exact statement and number | Theorem 4.6: for additive valuations "the pairwise maximin share guarantee is implied by envy freeness (EF), and implies 1/2-maximin share guarantee, envy freeness up to the least-valued good (EFX)" | CONFIRMED: **Theorem 4.6**, with EFX of Definition 4.5 | `Targets/Economics/PMMSEFX.lean:11`: "(… exact statement and numbering to be confirmed)" → "Theorem 4.6, with EFX as in Definition 4.5 (goods of positive value)". `PMMSEFX.lean:42–45` ("Caragiannis et al. state that PMMS implies EFX for additive valuations; the strict positivity hypothesis … is needed …, as `not_isPMMS_imp_isEFX` shows") must be rewritten: their EFX removes only positively valued goods, so their Theorem 4.6 is `efx_of_isPMMS_of_pos`, and the counterexample concerns only the strong form used in this library |
| Existence of PMMS is open | §4.2: "We do not know whether a pairwise MMS allocation always exists (under the constraint that all goods must be allocated)." | CONFIRMED as stated in 2019; the present status for `n = 3` was not checked | `PMMS.lean:13`: "is our understanding of the literature and is to be confirmed" → "left open by Caragiannis et al. (2019), Section 4.2; later status not checked" |
| EFX existence posed there | §4.2: "we were not able to settle the question of whether an EFX allocation always exists … and leave it as an enigmatic open question" | CONFIRMED | `EFX.lean:11` fine |

### 3.2 Chaudhury–Garg–Mehlhorn, "EFX exists for three agents"
Obtained: arXiv:2002.05119 (full). The J. ACM version is not reachable (`dl.acm.org` 403).

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal volume | Crossref: J. ACM 71 (1), pp. 1–27, published 2024-02-11 | CONFIRMED | `Targets/Economics/EFXThreeAgents.lean:10`: "(the theorem; volume and theorem number to be confirmed)" → volume confirmed |
| Theorem number | arXiv version: "Theorem 20. For any instance I = ⟨[3], M, V⟩ where all vi ∈ V are additive, an EFX allocation" [exists] | CONFIRMED for arXiv; number in the J. ACM version STILL UNVERIFIED | cite "Theorem 20 in arXiv:2002.05119" |
| Their EFX is the strong form | arXiv §1: "vi(Xi) ≥ vi(Xj \ g) for all g ∈ Xj" | CONFIRMED (arXiv version) | `Targets/Economics/EFX.lean:47–51`: "flagged as uncertain … to be confirmed against the J. ACM version" → "confirmed in the arXiv version (Section 1); the J. ACM text was not opened" |

### 3.3 Babaioff–Immorlica–Kleinberg, SODA 2007, pp. 434–443
Obtained: **full text**, author-hosted `https://www.cs.cornell.edu/~rdk/papers/matsec.pdf`.

| Claim | Quote and location | Verdict | Registry change |
|---|---|---|---|
| "The conjecture" and its wording | The paper poses a **question**, not a conjecture. Abstract/§1: "We leave open the question of whether there is a constant-competitive secretary algorithm for general matroids." §3: "our hypothesis is that any matroid domain has a constant-competitive algorithm. Question 1. Is there an algorithm which is constant competitive for every matroid domain?" | **CORRECTED** | `Targets/Economics/MatroidSecretary.lean:9`: "(the conjecture; exact wording and numbering to be confirmed)" → "(posed as Question 1 in Section 3, with the authors' "hypothesis" that the answer is yes; called a conjecture in later papers, e.g. Im–Wang 2011, Jaillet–Soto–Zenklusen 2013)" |
| Model: matroid known in advance | §2: "an algorithm which given the matroid structure (U, I) (but not the weights w(i)) selects online an independent set"; "over a uniform random ordering of elements" | CONFIRMED — the registry's known-matroid, random-order model is the paper's | `MatroidSecretary.lean:36–37` ("the version here is the one most favourable to the algorithm, hence the weakest conjecture. To be confirmed"): the known-matroid model is the one of the 2007 paper itself; that the question is open in the other variants was not checked |
| Graphic matroids: constant 16 | §5: "Theorem 5.1. For any graphic matroid the algorithm is a 16-approximation." | CONFIRMED | `Targets/Economics/MatroidSecretaryGraphic.lean:10`: "(constant `1/16`, to be confirmed)" → "Theorem 5.1" |
| Partition matroids: where, which constant | §6: "partition matroids have an e-competitive algorithm (run an independent copy of the original secretary algorithm on each piece of the partition)" | CONFIRMED: a one-line remark in Section 6, constant `e` | `Targets/Economics/MatroidSecretaryPartition.lean:11`: "(whether and where … to be confirmed)" → "(remark in Section 6, before Theorem 6.1; constant e)" |
| Closure under direct sums and restriction: citable statement | Not in the paper. The only closure result is truncation: "Theorem 6.1. Let M = (U, I) be a matroid. If ALG is a c-competitive algorithm for the M-secretary problem, then" [a constant-competitive algorithm exists for any truncation] | **CORRECTED** (answer: no such statement there) | `Targets/Economics/MatroidSecretaryDirectSum.lean:10`: "(… a citable statement, with theorem number, to be confirmed)" → "(not stated in that paper, whose closure result is for truncations, Theorem 6.1)" |

### 3.4 Im–Wang, SODA 2011, pp. 1265–1274; Jaillet–Soto–Zenklusen, IPCO 2013
Obtained: Im–Wang **abstract only** (SIAM 403); Jaillet–Soto–Zenklusen **full text** (arXiv:1207.1333).

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Im–Wang: first constant for all laminar matroids | abstract: "we give the first constant-competitive algorithm" | CONFIRMED | — |
| Im–Wang constant `3/16000` | JSZ abstract: "a clever but rather involved method and analysis [13] that leads to a competitive ratio of 16000/3" | CONFIRMED (secondary) | `Targets/Economics/MatroidSecretaryLaminar.lean:10`: "constant `3/16000` as far as we recall, to be confirmed" → "constant 3/16000 (ratio 16000/3 as reported by Jaillet–Soto–Zenklusen)" |
| JSZ constant `1/(3√3 e) ≈ 1/14.12` | JSZ abstract: "a considerably simpler and stronger 3√3e ≈ 14.12-competitive procedure" | CONFIRMED | same line: drop "to be confirmed" |
| Korula–Pál `1/(2e)`, ICALP 2009 | arXiv:0807.1139: "Theorem 5.2 There is a 2e-competitive algorithm for the graphic matroid secretary problem." | CONFIRMED (already in REDTEAM-ECON) | `MatroidSecretaryGraphic.lean:10`: "exact statement and numbering to be confirmed" → "Theorem 5.2 (arXiv:0807.1139)" |
| Babaioff–Immorlica–Kempe–Kleinberg, APPROX 2007: `e`-competitive for `k`-uniform | not opened | STILL UNVERIFIED | `MatroidSecretaryUniform.lean:10`, `MatroidSecretaryUniformTop.lean:10`: keep |

## 4. Coding, optimization, learning (REDTEAM-SIMES2-CODING and the priority list)

### 4.1 Trifference: Körner 1973, Körner–Marton 1988, small cases
Obtained: neither primary paper (Körner 1973 is a conference volume; Körner–Marton is on
ScienceDirect, 403). Full texts: Della Fiore–Gnutti–Polak, arXiv:2201.06846; Kurz,
arXiv:2310.13563; Guruswami–Riazanov, arXiv:1805.04151.

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Körner–Marton journal data | Crossref: European J. Combin. 9 (6) (1988) 523–530 | CONFIRMED | none |
| The elementary bound `T(n) ≤ 2 (3/2)ⁿ` and its general-`k` form are "Körner (1973)" | Both recent papers attribute the elementary bound to **Körner–Marton 1988**: DFGP §1: "An elementary double counting argument, as shown in [12], gives the following bound" `∣C∣ ≤ (k − 1)(k/(k − 1))ⁿ` ([12] = Körner–Marton); Kurz §1: the same bound, "for every k ≥ 3, c.f. [KM88]". Guruswami–Riazanov say only "(which is called the trifference problem by Körner)". No fetched source cites the 1973 paper for the bound | **CORRECTED** (attribution, on two secondaries; the 1973 paper was not opened) | `Targets/Coding/PerfectHash.lean:9`: "attribution of the general-`k` elementary bound to be confirmed" → "stated for general `k` in Körner–Marton (1988), as cited by Della Fiore–Gnutti–Polak (2022) and Kurz (2023)". `Targets/Coding/Trifference.lean:9`, `TrifferenceOpen.lean:9`, `TrifferenceSmall.lean:9`: cite Körner–Marton (1988) for the bound; keep Körner (1973) only as the origin of the problem, marked "not consulted" |
| Rate lower bound `(1/4) log₂(9/5)` is in Körner–Marton; theorem number | not visible in any fetched text | STILL UNVERIFIED | `Targets/Coding/TrifferenceKornerMarton.lean:9`: keep |
| `T(1..4) = 3, 4, 6, 9`: reference | DFGP §1: "it is easy to verify that T(1) = 3, T(2) = 4 and T(3) = 6", and Körner–Marton give a trifferent code of length 4 and size 9, so "T(4) = 9" | CONFIRMED (secondary) | `Targets/Coding/TrifferenceSmall.lean:9`: "(exact reference to be confirmed)" → "Della Fiore–Gnutti–Polak (2022), Section 1; the length-4 code of size 9 is from Körner–Marton (1988)" |
| `T(5) = 10`, `T(6) = 13`; `T(7), T(8), T(9) = 16, 20, 27` | DFGP abstract: "we use an optimized search algorithm to show that T(5) = 10 and T(6) = 13" (Examples and Counterexamples 2 (2022) 100051, Crossref); Kurz abstract: "we determine T(7) = 16, T(8) = 20, and T(9) = 27" | CONFIRMED (full texts; REDTEAM-SIMES2-CODING had a search snippet for Kurz) | — |

### 4.2 Fredman–Komlós 1984; Hansel 1964
Obtained: Fredman–Komlós **abstract only** (SIAM 403); Hansel nothing (Gallica 403).

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Fredman–Komlós journal data | Crossref: SIAM J. Algebraic Discrete Methods 5 (1) (1984) 61–68 | CONFIRMED | none |
| Rate bound `k!/k^{k−1}` | Guruswami–Riazanov eq. (1): "Rk ≤ k!/k^{k−1}", "the 1984 paper of Fredman and Komlós"; DFGP eq. (2): `∣C∣ ≤ (2^{k!/k^{k−1}})ⁿ` "for every k ≥ 4 and sufficiently large n" | CONFIRMED (secondary) | — |
| Exact finite form in the 1984 paper | not visible | STILL UNVERIFIED | `Targets/Coding/FredmanKomlos.lean:9`: keep for the finite form |
| Körner 1986 | Guruswami–Riazanov ref. [4]: SIAM J. Algebraic Discrete Methods 7 (4) (1986) 560–570 | CONFIRMED | `FredmanKomlos.lean:9`: that secondary reference is confirmed |
| Hansel: C. R. Acad. Sci. Paris 258 (1964) 6037–6040 | Guruswami–Riazanov ref. [7]: "C. R. Acad. Sci. Paris, pp. 6037–6040, 1964" (no volume) | pages CONFIRMED (secondary); volume 258, Katona–Szemerédi and Radhakrishnan's survey STILL UNVERIFIED | `Targets/Coding/Hansel.lean:9`: keep |

### 4.3 Levenshtein 1965/66, Varshamov–Tenengolts 1965
Obtained: neither. Secondary, full text: N. J. A. Sloane, "On single-deletion-correcting codes", arXiv:math/0207197.

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Levenshtein: Doklady 163 (1965) 845–848; Soviet Phys. Dokl. 10 (1966) 707–710 | Sloane ref. [Lev65]: "Doklady Akademii Nauk SSSR, 163 (No. 4, 1965), 845–848. English translation in Soviet Physics Dokl., 10 (No. 8, 1966), 707–710." | CONFIRMED (secondary) | none |
| Varshamov–Tenengolts: Avtomatika i Telemekhanika 26 (1965) 288–292 | Sloane ref. [VT65]: "26 (No. 2, 1965), 288–292" | CONFIRMED (secondary) | none |
| VT codes correct one deletion: Levenshtein | Sloane §2: "Levenshtein [Lev65], [Lev65a] observed that the Varshamov-Tenengolts codes could be used for correcting single deletions" | CONFIRMED (secondary) | `Targets/Coding/VarshamovTenengolts.lean:9`: "(details to be confirmed)" can go for these three items |
| Asymptotic bound `2ⁿ/n` is Levenshtein's | Sloane: "Theorem 2.5 ([Lev65]). A(n, 1) ∼ 2ⁿ/n, as n → ∞." with the run-counting proof "Following Levenshtein" | CONFIRMED (secondary) | `Targets/Coding/SingleDeletionUpperBound.lean:9`: "(… details to be confirmed)" → "(Sloane, Theorem 2.5)" |
| Sloane's survey appeared in "Codes and Designs, Ohio State Univ. Math. Res. Inst. Publ. 10" | the arXiv version does not say where it appeared | STILL UNVERIFIED | cite as arXiv:math/0207197 if a checked reference is wanted |

### 4.4 Deletion channel: Gallager 1961, Zigangirov 1969, Diggavi–Grossglauser 2006, Mitzenmacher–Drinea 2006, survey
Obtained: Mitzenmacher–Drinea **full text** (author-hosted `…/~michaelm/postscripts/toit2006b.pdf`);
Diggavi–Grossglauser **abstract only**; Mitzenmacher's survey as the author's **draft**
(`…/postscripts/DelSurvey.pdf`; the Probability Surveys version is behind Project Euclid's challenge).

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Mitzenmacher–Drinea: `C ≥ (1 − d)/9`, IEEE Trans. Inform. Theory 52(10) (2006) 4657–4660 | abstract: "the capacity of the binary independent and identically distributed (i.i.d.) deletion channel … is at least (1 − d)/9" | CONFIRMED | `Targets/InformationTheory/DeletionPositiveCapacity.lean:9`: "(attributions and constants to be confirmed)" → confirmed for Mitzenmacher–Drinea |
| Diggavi–Grossglauser: journal data | Crossref: 52 (3) (2006) 1226–1237 | CONFIRMED | none |
| Diggavi–Grossglauser give `C ≥ 1 − H(d)` | abstract: with i.i.d. input codebooks "the achievable rate in deletion channels differs from that of erasure channels by at most H0(pd) − pd log K/(K − 1) bits" — for `K = 2`: `(1 − p_d) − H(p_d) + p_d = 1 − H(p_d)` | CONFIRMED (abstract; the binary bound follows by putting `K = 2`) | `Targets/InformationTheory/DeletionLowerBound.lean:9`: Diggavi–Grossglauser confirmed |
| The same bound is due to Gallager (1961) and Zigangirov (1969); theorem numbers | the draft survey lists both in its references but its §3.1 says only that the i.i.d. codebook argument gives "a very weak lower bound", "non-zero only when p < 0.5" | STILL UNVERIFIED | `DeletionLowerBound.lean:9`: keep "(exact statements and theorem numbers to be confirmed)" for Gallager and Zigangirov |
| Erasure upper bound `1 − d` is in the survey | draft, section on upper bounds: "the trivial upper bound from the erasure channel of 1 − p" | CONFIRMED in the draft; location in the published version not checked | `Targets/InformationTheory/DeletionErasureBound.lean:9`: "(location in the survey to be confirmed)" → "(stated in the section on upper bounds of the author's draft)" |
| Survey journal data | Crossref: Probability Surveys 6 (2009) 1–33 | CONFIRMED | none |
| Chvátal–Sankoff supersequence count | not opened (Crossref returns only the conference abstract in Adv. Appl. Probab. 7 (2), p. 253) | STILL UNVERIFIED | keep |

### 4.5 Naddef, Math. Programming 45 (1989) 109–110
Obtained: **nothing** of the paper (Springer bot wall). Secondary, full text: G. M. Ziegler,
"Lectures on 0/1-polytopes", arXiv:math/9909177.

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 45 (1–3), 109–110, DOI 10.1007/BF01589099 | CONFIRMED | none |
| Ambient dimension or dimension of the polytope | Ziegler: Theorem 29 ("The Hirsch conjecture for 0/1-polytopes: Naddef [48]"): "The diameter of the graph of a d-dimensional 0/1-polytope P ⊆ Rⁿ is at most … d", with equality only for the `d`-cube | CONFIRMED (secondary): the standard statement is with the **dimension of the polytope**, hence stronger than the registry's ambient-dimension bound | `Targets/Optimization/ZeroOnePolytopeDiameter.lean:9`: "whether the paper states the bound with the ambient dimension or the dimension of the polytope is to be confirmed" → "as restated by Ziegler (Lectures on 0/1-polytopes, Theorem 29) the bound is `dim P`; the paper itself was not opened; the theorem here is the weaker ambient-dimension form" |

### 4.6 Klee–Minty 1972; Chvátal 1983
Obtained: nothing (book chapters; the DTIC report copy is on a site under maintenance; a Johns
Hopkins course copy returns 403). Pages 159–175 and the wording of Chvátal's Chapter 4:
STILL UNVERIFIED (`Targets/Optimization/KleeMintyDantzig.lean:9`,
`PolynomialPivotRule.lean:10`, keep). Klee, Canad. J. Math. 16 (1964) 602–614 — CONFIRMED at
Crossref (`PolytopeGraphDimOne.lean:9`, bibliographic data only).

### 4.7 Eisenbrand–Hähnle–Razborov–Rothvoß, Math. Oper. Res. 35(4) (2010) 786–794
Obtained: the authors' **extended abstract** (Dagstuhl Seminar Proceedings 10211, 5 pages, full
text). The full paper at EPFL Infoscience answers 429.

| Claim | Evidence | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 35 (4), 786–794 | CONFIRMED | none |
| The abstraction and the bound | "For each u, v ∈ V there exists a path connecting u and v whose intermediate vertices all contain u ∩ v"; "the bound of Kalai and Kleitman [13], ∆u(d, n) ≤ n^{1+log d} … continue to hold in the base abstraction" | CONFIRMED (extended abstract: graph form of the abstraction; the connected-layer-family form is one of the "three different descriptions that all turn out to be pairwise equivalent") | — |
| Theorem numbers | not in the extended abstract | STILL UNVERIFIED | `Targets/Optimization/ConnectedLayerFamilyBound.lean:9`: keep |

### 4.8 Floyd–Warmuth, Machine Learning 21(3) (1995) 269–304
Obtained: **full text**, author-hosted `https://mwarmuth.bitbucket.io/pubs/J30.pdf` (journal pages).

| Claim | Quote and location | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 21 (3), 269–304 | CONFIRMED | none |
| Maximum classes have schemes of size `d`: number | §6.1: Theorem 10: for a maximum class of VC dimension `d` on a finite domain, each concept has "a compression set A± of exactly d elements"; "Theorem 11. … the VC Compression Scheme is a sample compression scheme of size d for C." (possibly infinite domain) | CONFIRMED: **Theorems 10 and 11** | `Targets/Learning/CompressionMaximum.lean:9`: "(… theorem number to be confirmed)" → "Theorems 10 and 11" |
| Welzl's restriction and reduction facts appear there | §6: "Theorem 9 (Welzl, 1987)", "Corollary 1 (Welzl, 1987)", "Corollary 2 (Welzl, 1987)" | CONFIRMED | same line: "(exact location to be confirmed)" → "Theorem 9 and Corollaries 1, 2 (Section 6)" |
| Halving scheme of size `log₂ ∣C∣` | §4.1: Theorem 4: for a finite class, the One-Pass Compression Scheme with the Halving algorithm "gives a sample compression scheme of size at most log ∣C∣ for the class C." | CONFIRMED: **Theorem 4**, Section 4.1 | `Targets/Learning/CompressionHalving.lean:9` and `CompressionLogBound.lean:9`: "(exact location to be confirmed)" → "Theorem 4" |
| Counting lower bound: the constant | §6.4: Theorem 14: "For an arbitrary concept class C of VC dimension d, there is no sample compression scheme of size at most d/5" | CONFIRMED: **Theorem 14**, and the constant is **5**, the same as the registry's (theirs is strict: size `> d/5`; ours `vcDim ≤ 5k`) | `Targets/Learning/CompressionLowerBound.lean:9`: "(counting argument; the constant proved there to be confirmed)" → "Theorem 14 (Section 6.4): no scheme of size at most d/5" |
| Intervals and rectangles as examples: location | §3 "Sample compression schemes": "Example: rectangles." ("this compression function saves at most four points"); "Example: intervals on the line." ("At most 2n examples are saved.") | CONFIRMED: Section 3 | `Targets/Learning/CompressionRectangles.lean:9`, `CompressionIntervals.lean:9`, `CompressionThresholds.lean:9`: "(location to be confirmed)" → "Section 3 (examples)"; thresholds are not a named example there |
| Littlestone–Warmuth generalization bound as stated there | §5: "Theorem 5 (Littlestone and Warmuth, 1986)", and "Theorem 6" for classes with a scheme | CONFIRMED | `Targets/Learning/CompressionGeneralization.lean:9`: may add "Floyd–Warmuth, Theorems 5 and 6" |
| "the question whether every class of VC dimension `d` embeds into a maximum class of dimension `O(d)` is raised there" | It is not. §7: "Every class C of VC dimension d on a finite set X can be embedded in a maximal class of VC dimension d". §9.1: "The main open question of this paper is whether there is a sample compression scheme of size d, or of size O(d)" for every class | **CORRECTED** | `Targets/Learning/CompressionMaximumEmbedding.lean:10`: replace that clause by "Floyd–Warmuth note only the embedding into a *maximal* class of the same dimension (Section 7); embedding into *maximum* classes is the approach of Rubinstein–Rubinstein–Bartlett" |
| Rubinstein–Rubinstein–Bartlett | arXiv:1401.7388 abstract: "embedding general VC classes into maximum classes without super-linear increase to their VC dimensions"; "VC-d classes that cannot be embedded in any maximum class of VC dimension lower than 2d" | CONFIRMED (arXiv version; the book chapter data not checked) | same line: drop "(to be confirmed)" for the content |

### 4.9 Ben-David–Litman, Discrete Appl. Math. 86(1) (1998) 3–25
Obtained: **nothing** (ScienceDirect 403). Journal data CONFIRMED (Crossref). "classes of VC
dimension 1 have labelled schemes of size 1; exact statement and location": STILL UNVERIFIED
(`Targets/Learning/CompressionVCOne.lean:9`, keep).

### 4.10 Goldreich–Karloff–Schulman–Trevisan
Obtained: **full text of the CCC 2002 version** (Caltech repository
`https://authors.library.caltech.edu/27595/1/GOLaccc02.pdf`, listed by Unpaywall). The journal
version (Comput. Complexity 15 (3) (2006) 263–296, Crossref) was not opened; numbers below are
those of the conference version. Greek letters are lost in the extracted text; the exponents are
fixed by the proof text quoted.

| Claim | Quote and location | Verdict | Registry change |
|---|---|---|---|
| Journal data | Crossref: 15 (3), 263–296 | CONFIRMED | none |
| "their constants differ" | For the statement actually formalized they do **not**. Lemma 3.3 (Combinatorial Lemma): vectors `a1, …, am ∈ {0,1}ⁿ`, and "for every i ∈ [n] there is a set Mi of at least [γ]m disjoint pairs of indices {j1, j2} such that ei = aj1 ⊕ aj2. Then m ≥ 2^{2[γ]n}." The lemma adds that the average condition `(1/n) Σ ∣Mi∣ ≥ γm` suffices. Proof, §3.3: "This gives a total of at least [γ]mn edges, but this number has to be no more than ½ m log₂ m". This is `linear_two_query_ldc_four_rpow_le` (`4^{δk} ≤ m`) with the same constant | **CORRECTED** | `Targets/Coding/LinearTwoQueryLDCLowerBound.lean:9`: "(exponential lower bound for linear 2-query LDCs; their constants differ, to be confirmed)" → "(the matching-form statement here is their Combinatorial Lemma, Lemma 3.3 of the CCC 2002 version, with the same bound `m ≥ 2^{2δk}`; their Theorem 1.3 for (2, δ, ε)-locally decodable linear codes is `m ≥ 2^{εδn/8}`)" |
| The isoperimetric inequality used | Lemma 3.5: "the number of edges of the hypercube having both endpoints in S is at most ½ ∣S∣ log₂ ∣S∣." | CONFIRMED | may be cited next to Harper / Bernstein / Hart |
| The decoder of `LinearTwoQueryLDCDecoder` | not checked against the text | STILL UNVERIFIED | `Targets/Coding/LinearTwoQueryLDCDecoder.lean:9`: keep |

## 5. Bibliographic data confirmed at Crossref / OpenAlex only (no text opened)

Hochberg–Liberman, Statist. Probab. Lett. 21 (2) (1994) 101–105; Benjamini–Hochberg, Scand. J.
Statist. 24 (3) (1997) 407–418; Wiens, Pharmaceut. Statist. 2 (3) (2003) 211–215;
Hommel–Bretz–Maurer, Statist. Med. 26 (22) (2007) 4063–4073; Pocock, Biometrika 64 (2) (1977)
191–199; Lan–DeMets, Biometrika 70 (3) (1983), first page 659; Guilbaud, Biometrical J. 50 (5)
(2008) 678–692; Finner–Strassburger, Ann. Statist. 30 (4) (2002) 1194–1213; Sarkar, Ann.
Statist. 30 (1) (2002) 239–257; Yekutieli–Benjamini, J. Statist. Plann. Inference 82 (1999)
171–196; Tang–Geller, Biometrics 55 (4) (1999) 1188–1192; Glimm–Maurer–Bretz, Statist. Med.
29 (2) (2010) 219–228; Guo–Rao, J. Statist. Plann. Inference 138 (10) (2008) 3176–3188;
Ginibre, Comm. Math. Phys. 16 (4) (1970) 310–328; Ahlswede–Daykin, Z. Wahrsch. Verw. Gebiete
43 (3) (1978) 183–185; Massart, Ann. Fac. Sci. Toulouse Math. 9 (2) (2000) 245–303;
Dvir–Shpilka, SIAM J. Comput. 36 (5) (2007) 1404–1434; Polak–Schrijver, Inform. Process. Lett.
143 (2019) 37–40; Korula–Pál, ICALP 2009, LNCS pp. 508–520; Amanatidis–Birmpas–Markakis,
IJCAI 2018, pp. 42–48. Registry lines that carry "(to be confirmed)" only for such data
(`WeightedSimes.lean:9` for Hochberg–Liberman; `TwoSidedKarlinRinott.lean:10` for Ginibre) can
drop it for the bibliographic part; statement and lemma numbers inside these papers remain
unchecked.

## 6. Totals

Counted per claim (142 table rows plus 19 claims in the prose paragraphs 2.13, 2.16, 2.18,
2.20, 2.22, 4.6, 4.9; a row with a confirmed part and an open part is counted by its first
verdict; the bibliographic block of §5 is not counted).

| Verdict | Count |
|---|---|
| CONFIRMED | 121 |
| — of which only through a secondary source that quotes the statement with its number | 19 |
| — the others: full text of the source, or its publisher abstract / Crossref record, as marked in each row | 102 |
| CORRECTED (registry sentence contradicted by the source) | 11 |
| STILL UNVERIFIED | 29 |

Full text of the primary source was read for 14 of the papers on the priority list:
Benjamini–Yekutieli 2001, Benjamini–Hochberg 1995, Hommel 1988, Šidák 1967, Bretz et al. 2011,
Schuirmann 1987, Caragiannis et al. 2019, Chaudhury–Garg–Mehlhorn (arXiv version),
Babaioff–Immorlica–Kleinberg 2007, Jaillet–Soto–Zenklusen (arXiv version), Mitzenmacher–Drinea
2006, Floyd–Warmuth 1995, Goldreich–Karloff–Schulman–Trevisan (CCC 2002 version),
Eisenbrand et al. (extended abstract only). Abstract only: Simes 1986, Hochberg 1988, Holm 1979,
Hommel 1983, Sarkar 1998, Bretz et al. 2009, Maurer–Bretz 2013, Strassburger–Bretz 2008,
Hsu–Berger 1999, Bauer–Köhne 1994, Lehmacher–Wassmer 1999, Cui–Hung–Wang 1999,
Brannath–Posch–Bauer 2002, Müller–Schäfer 2001 and 2004, Chen–DeMets–Lan 2004, Mehta–Pocock
2011, Berger 1982, Karlin–Rinott 1981, Samuel-Cahn 1996, Fredman–Komlós 1984,
Diggavi–Grossglauser 2006, Im–Wang 2011, Wright 1992, Finner–Roters 2001. Nothing of the text:
Lovász 1979, Dunnett 1955, Karlin–Rinott 1980, Körner 1973, Körner–Marton 1988, Naddef 1989,
Levenshtein 1965/66, Hansel 1964, Baumert et al. 1971, Klee–Minty 1972, Chvátal 1983,
Ben-David–Litman 1998, Gallager 1961.

### Corrected items

1. BY 2001: PRDS is defined in Section 1.3 ("Property PRDS", p. 1168), not Section 2.1 — `Targets/Statistics/ClassicalPRDS.lean:9`.
2. BY 2001: many-to-one comparisons are Section 3.2, Problem 3 (p. 1175, via Case 4), not Section 3.1 — `ManyToOneControl.lean:9`, `ManyToOneGaussian.lean:9`.
3. BY 2001: no block structure in Section 3.1 — `PRDSGroupFactor.lean:9`.
4. BY 2001: the two facts of `PRDSExamples` are not stated there — `PRDSExamples.lean:9`.
5. Šidák 1967 does not state exactness under independence (only the calibration `Φ(c_α) = ½[1 + (1 − α)^{1/k}]`, Section 3) — `SidakExact.lean:9`.
6. Jennison–Turnbull 1989: pages 305–334 at Crossref, not 305–361 — `GroupSequentialGraphical.lean:9`.
7. Babaioff–Immorlica–Kleinberg 2007 pose a question ("Question 1", Section 3) and a "hypothesis", not a conjecture — `MatroidSecretary.lean:9`.
8. Babaioff–Immorlica–Kleinberg 2007 have no direct-sum or restriction statement (only truncation, Theorem 6.1) — `MatroidSecretaryDirectSum.lean:10`.
9. The elementary trifference / perfect-hash bound is attributed to Körner–Marton 1988 by Della Fiore–Gnutti–Polak and by Kurz, not to Körner 1973 — `Trifference.lean:9`, `TrifferenceOpen.lean:9`, `TrifferenceSmall.lean:9`, `PerfectHash.lean:9`.
10. Floyd–Warmuth 1995 do not raise the embedding-into-maximum-classes question (they embed into maximal classes, Section 7) — `CompressionMaximumEmbedding.lean:10`.
11. Goldreich–Karloff–Schulman–Trevisan: the constants do not differ; the formalized statement is their Lemma 3.3 with `m ≥ 2^{2γn}` — `LinearTwoQueryLDCLowerBound.lean:9`.

Corrections to the red-team reports themselves (the registry is right in these three places):

- REDTEAM-SIMES2-CODING defect 4 ("Wrong source for the bivariate case") is to be withdrawn.
  Samuel-Cahn's abstract says "Two-sided tests based on bivariate normal variables are always
  conservative." `TwoSidedSimesBivariate.lean:10` keeps the citation and drops "to be confirmed".
- REDTEAM-MULTIPLE-TESTING defect 3: Hommel (1988) itself defines the procedure as the closure of
  Simes tests (Section 2); the part not formalized is his rule
  `j = max{i : P(n−i+k) > kα/i, k = 1..i}`, reject `Pi ≤ α/j`.
- REDTEAM-MULTIPLE-TESTING §C: Hochberg's pages are 800–802 (Crossref), not 800–803.

Numbers newly available for "to be confirmed" notes: Lovász Corollary 5 and Theorem 1
(secondary); BY Theorem 5.1 and Case 1; BH95 Remark after Theorem 1; Sarkar 1998 Theorem 3.1
(secondary); Karlin–Rinott 1981 Theorem 3.1 (secondary); Bretz 2011 Section 3.3; Caragiannis
Definition 4.3, Definition 4.5, Theorem 4.6; BIK Theorem 5.1 and the Section 6 remark;
Korula–Pál Theorem 5.2; Floyd–Warmuth Theorems 4, 10, 11, 14 and Section 3; GKST Lemmas 3.3,
3.5 and Theorem 1.3 (CCC version); Sloane Theorem 2.5; Baumert et al. Theorem 2 (secondary);
Ziegler Theorem 29 for Naddef.

### Still unverified, and why

| Item | Why |
|---|---|
| Lovász 1979: "Theorem 2" for `Θ(C₅) = √5`, "Lemmas 1–3", his wording of the definitions | paper not obtainable: author page and Wayback unreachable through the proxy, IEEE empty response, no open copy indexed; no secondary gives these numbers |
| Baumert et al. 1971 at source | AMS proceedings volume, no open copy |
| Simes 1986 theorem number; Hochberg 1988 and Holm 1979 exact wording and tie convention | OUP 403, JSTOR bot wall; only abstracts |
| Hommel 1983 statement number | Wiley 403; abstract only |
| Wright 1992 formulas, last page; Finner–Roters 2001 theorem for the equality | abstracts only |
| Bretz et al. 2009: number of the theorem behind Algorithm 1; section and figure numbers of the examples | Wiley 403; no preprint found |
| Maurer–Bretz 2013 section and page numbers | T&F 403 |
| Strassburger–Bretz 2008 "Theorem 1" and the all-rejected form; Hsu–Berger 1999 theorem number | Wiley / T&F 403; NC State copy behind a bot wall |
| Bauer–Köhne 1994 place of the level formula and last page; Lehmacher–Wassmer, Cui–Hung–Wang places of statements; the term "p-clud" in Brannath–Posch–Bauer 2002; theorem and equation numbers in Müller–Schäfer, Chen–DeMets–Lan, Mehta–Pocock | abstracts only |
| Dunnett 1955 (everything but the page range) | T&F 403, JSTOR bot wall, course copy behind a login |
| Berger 1982 and Berger–Hsu 1996 "Theorems 1 and 2" | abstracts only; DTIC under maintenance; Project Euclid challenge |
| Karlin–Rinott 1980 "Theorem 2.1" and the bivariate MTP2 statement | ScienceDirect 403 |
| Sarkar 2002 theorem numbers | Project Euclid challenge |
| CGM theorem number in the J. ACM version | `dl.acm.org` 403 (arXiv: Theorem 20) |
| Babaioff–Immorlica–Kempe–Kleinberg APPROX 2007 (`e`-competitive, `k`-uniform); Bateni et al. | not opened |
| Körner 1973 (whether it contains the bound at all); Körner–Marton `(1/4) log₂(9/5)` and its number | conference volume; ScienceDirect 403 |
| Fredman–Komlós exact finite form; Hansel volume number; Katona–Szemerédi; Radhakrishnan's survey | SIAM 403, Gallica 403 |
| Levenshtein 1965/66 at source; venue of Sloane's survey | no legitimate copy reachable (checked through Sloane, arXiv) |
| Gallager 1961, Zigangirov 1969 for `1 − H(d)`; Chvátal–Sankoff; published survey's section numbers | report / journal not reachable; Project Euclid challenge |
| Naddef 1989 at source | Springer bot wall (checked through Ziegler) |
| Klee–Minty 1972 pages; Chvátal 1983 Chapter 4 | book chapters; DTIC under maintenance |
| Eisenbrand–Hähnle–Razborov–Rothvoß theorem numbers | only the Dagstuhl extended abstract; EPFL copy answers 429 |
| Ben-David–Litman 1998 VC-1 statement | ScienceDirect 403 |
| GKST journal-version numbering; the decoder statement | journal version not opened |

Hosts a person with library access would need: `academic.oup.com`, `www.jstor.org`,
`onlinelibrary.wiley.com`, `www.tandfonline.com`, `www.sciencedirect.com`, `projecteuclid.org`,
`ieeexplore.ieee.org`, `link.springer.com`, `epubs.siam.org`, `dl.acm.org`; for Lovász's own scan,
`web.cs.elte.hu` must be reachable from the session's egress.

Downloaded files and scripts are in the session scratchpad
(`<session scratchpad>/src/<key>/doc[.txt]`
and `<session scratchpad>/scripts/`); they are
not in the repository.
