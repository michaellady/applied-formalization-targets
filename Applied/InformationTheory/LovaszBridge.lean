import Applied.InformationTheory.LovaszOddCycle
import Applied.InformationTheory.ShannonCapacityC7
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Bridges from the library's `Θ(C₇)` bounds to statements of other projects

The library proves `367^{1/5} ≤ Θ(C₇) ≤ 7 cos(π/7)/(1 + cos(π/7))` for
`Θ = shannonCapacity (SimpleGraph.cycleGraph 7)` (`ShannonCapacityC7.lean`,
`LovaszOddCycle.lean`). Two other projects state the same facts, without proof, in the
"difference set" model: words over `ℤ/7`, a code being a set `A` with
`(A - A) ∩ {-1, 0, 1}ⁿ = {0}`. This file copies their definitions verbatim (in sub-namespaces,
so that no dependency is added) and proves their statements from the library's theorems.

* **formal-conjectures** (github.com/google-deepmind/formal-conjectures, Apache 2.0),
  `FormalConjectures/GreensOpenProblems/38.lean` and
  `FormalConjecturesForMathlib/Data/ZMod/Fp.lean`: the definitions in `namespace Green38` below
  are copied from there. Proved here: `green_38_variants_best_upper` (their
  `green_38.variants.best_upper`, a `sorry` upstream) and `green_38_variants_best_lower` (their
  `green_38.variants.best_lower`, a `sorry` upstream).
* **atlas-lean** (github.com/facebookresearch/atlas-lean, see its LICENSE),
  `MathlibExt/Combinatorics/Coding/CycleCode.lean` and
  `WantedExt/Combinatorics/Coding/CycleShannonBoundsWanted.lean`: the definitions in
  `namespace CycleGraphCode` below are copied from there. Proved here: `lovasz1979UpperBound`,
  `polakSchrijverLowerBound`, `polakSchrijverRateLowerBound`, `veselZerovnik2002LowerBound`,
  `mathewOstergard2017LowerBound` (all `theorem_wanted` upstream), and the identification
  `shannonCapacityCycle_seven_eq`: their `shannonCapacityCycle 7 : ENNReal` is
  `ENNReal.ofReal (shannonCapacity (cycleGraph 7))`.

* **formal-conjectures, open pull request #5321** ("feat(Wikipedia): shannon capacity of C7",
  opened 2026-09-07, not merged on 2026-11-25; files `FormalConjectures/Wikipedia/Shannon.lean`
  and `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Shannon.lean` of that branch): the
  definitions in `namespace PR5321` below are copied from there (with `α(G)` written out as
  `G.indepNum`). Its `strongPow` is defined by recursion through the binary strong product;
  `PR5321.strongPow_eq` and `PR5321.shannonCapacity_eq` show that it and its `shannonCapacity`
  are equal to the library's. Proved here: `PR5321.shannonCapacityC5`,
  `PR5321.threesixseven_le_indepNum_pow_five`, `PR5321.root_367_le_shannonCapacityC7` (the
  first two are `sorry` there) and the known half `PR5321.shannonCapacityC7_le` of its open
  problem `shannonCapacityC7`.

The bridge itself is `intersectsOnlyAtZero_iff` / `isCycleCode_iff`: a finite set of words over
`ZMod 7` satisfies the difference condition iff it is an independent set of
`strongPow (cycleGraph 7) n` (`ZMod 7` is definitionally `Fin 7`), hence
`largestAdmissibleCardinality_eq`: `LargestAdmissibleCardinality n = α(C₇^{⊠n})`.

Two general facts are added because the bridges need them:
`indepNum_strongPow_le_pow_of_shannonCapacity_le` (`Θ(G) ≤ M → α(G^{⊠k}) ≤ Mᵏ`) and
`indepNum_strongPow_add_ge` (`α(G^{⊠m}) α(G^{⊠n}) ≤ α(G^{⊠(m+n)})`).
-/

open Filter Set
open scoped Pointwise

namespace Applied.InformationTheory.LovaszBridge

/-! ### Definitions copied verbatim from formal-conjectures -/

namespace Green38

/-- Copied from formal-conjectures, `FormalConjecturesForMathlib/Data/ZMod/Fp.lean`. -/
abbrev 𝔽 (p n : ℕ) := Fin n → ZMod p

/-- Copied from formal-conjectures, `FormalConjecturesForMathlib/Data/ZMod/Fp.lean`. -/
abbrev 𝔽₇ (n : ℕ) := 𝔽 7 n

/-- $A - A$ intersects $\{-1, 0, 1\}^n$ only at $0$.
(Copied from formal-conjectures, `GreensOpenProblems/38.lean`.) -/
def IntersectsOnlyAtZero {n : ℕ} (A : Finset (𝔽₇ n)) : Prop :=
  ∀ a ∈ A - A, (∀ i, a i ∈ ({-1, 0, 1} : Finset (ZMod 7))) → a = 0

/-- The set of cardinalities of all subsets A where A - A intersects {-1, 0, 1}^n only at 0.
(Copied from formal-conjectures, `GreensOpenProblems/38.lean`.) -/
def ValidCardinalities (n : ℕ) : Set ℕ :=
  { (A.card) | (A : Finset (𝔽₇ n)) (_ : IntersectsOnlyAtZero A) }

/-- The largest subset $A \subset \mathbb{F}_7^n$ for which $A - A$ intersects $\{-1, 0, 1\}^n$
only at $0$. (Copied from formal-conjectures, `GreensOpenProblems/38.lean`.) -/
noncomputable def LargestAdmissibleCardinality : ℕ → ℝ := fun n ↦
  (sSup (ValidCardinalities n) : ℕ)

/-- The lower bound constant $C_1 \approx 3.2578$ from [Po20].
(Copied from formal-conjectures, `GreensOpenProblems/38.lean`.) -/
noncomputable def C₁ : ℝ := (367 : ℝ) ^ (5⁻¹ : ℝ)

/-- The upper bound constant $C_2 \approx 3.3177$ from [La79].
(Copied from formal-conjectures, `GreensOpenProblems/38.lean`.) -/
noncomputable def C₂ : ℝ := (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7))

end Green38

/-! ### Definitions copied verbatim from atlas-lean -/

namespace CycleGraphCode

/-- Positive block lengths. (Copied from atlas-lean,
`MathlibExt/Combinatorics/Coding/CycleCode.lean`.) -/
abbrev PositiveNat := {n : ℕ // 1 ≤ n}

/-- Independent codes for the modular cycle. (Copied from atlas-lean,
`MathlibExt/Combinatorics/Coding/CycleCode.lean`.) -/
def IsCycleCode (q : ℕ) {n : ℕ} (A : Finset (Fin n → ZMod q)) : Prop :=
  ∀ (x : Fin n → ZMod q),
    (∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ - a₂ = x) →
    (∀ i : Fin n, x i = -1 ∨ x i = 0 ∨ x i = 1) →
    x = 0

/-- Cycle codes. (Copied from atlas-lean, `MathlibExt/Combinatorics/Coding/CycleCode.lean`.) -/
abbrev CycleCode (q n : ℕ) := {A : Finset (Fin n → ZMod q) // IsCycleCode q A}

/-- Rate of a cycle code. (Copied from atlas-lean,
`MathlibExt/Combinatorics/Coding/CycleCode.lean`.) -/
noncomputable def cycleCodeRate (q : ℕ) (n : PositiveNat) (A : CycleCode q n.1) : ENNReal :=
  ENNReal.rpow (A.1.card : ENNReal) ((n.1 : ℝ)⁻¹)

/-- Shannon capacity of the modular cycle. (Copied from atlas-lean,
`MathlibExt/Combinatorics/Coding/CycleCode.lean`.) -/
noncomputable def shannonCapacityCycle (q : ℕ) : ENNReal :=
  ⨆ (n : PositiveNat) (A : CycleCode q n.1), cycleCodeRate q n A

/-- Lovász's theta value for the 7-cycle. (Copied from atlas-lean,
`WantedExt/Combinatorics/Coding/CycleShannonBoundsWanted.lean`.) -/
noncomputable def lovaszThetaCycleSeven : ENNReal :=
  ENNReal.ofReal (7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7)))

end CycleGraphCode

/-! ### The dictionary: difference condition ⟺ independent set of the strong power -/

/-- The 7-cycle with vertex type written `ZMod 7` (definitionally `Fin 7`). -/
abbrev C7z : SimpleGraph (ZMod 7) := SimpleGraph.cycleGraph 7

/-- A difference in `ℤ/7` lies in `{-1, 0, 1}` iff the letters are equal or adjacent in `C₇`. -/
lemma small_iff : ∀ a b : ZMod 7,
    (a - b = -1 ∨ a - b = 0 ∨ a - b = 1) ↔ (a = b ∨ C7z.Adj a b) := by
  have h : ∀ a b : Fin 7, (a - b = -1 ∨ a - b = 0 ∨ a - b = 1) ↔
      (a = b ∨ (a - b = 1 ∨ b - a = 1)) := by decide
  exact h

/-- Independent sets of `C₇^{⊠n}`, in difference form. -/
lemma isIndepSet_iff {n : ℕ} (A : Finset (Fin n → ZMod 7)) :
    (strongPow C7z n).IsIndepSet (A : Set (Fin n → ZMod 7)) ↔
      ∀ a ∈ A, ∀ b ∈ A, (∀ i, a i - b i = -1 ∨ a i - b i = 0 ∨ a i - b i = 1) → a = b := by
  constructor
  · intro h a ha b hb hs
    by_contra hne
    exact h (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hne
      ⟨hne, fun i => (small_iff _ _).1 (hs i)⟩
  · intro h a ha b hb hne hadj
    exact hne (h a (Finset.mem_coe.1 ha) b (Finset.mem_coe.1 hb)
      fun i => (small_iff _ _).2 (hadj.2 i))

/-- formal-conjectures' `IntersectsOnlyAtZero` is independence in `C₇^{⊠n}`. -/
theorem intersectsOnlyAtZero_iff {n : ℕ} (A : Finset (Green38.𝔽₇ n)) :
    Green38.IntersectsOnlyAtZero A ↔
      (strongPow C7z n).IsIndepSet (A : Set (Fin n → ZMod 7)) := by
  rw [isIndepSet_iff]
  constructor
  · intro h a ha b hb hs
    refine sub_eq_zero.1 (h (a - b) (Finset.sub_mem_sub ha hb) fun i => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton, Pi.sub_apply]
    exact hs i
  · intro h x hx hs
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.1 hx
    rw [h a ha b hb (fun i => by simpa using hs i), sub_self]

/-- atlas-lean's `IsCycleCode 7` is independence in `C₇^{⊠n}`. -/
theorem isCycleCode_iff {n : ℕ} (A : Finset (Fin n → ZMod 7)) :
    CycleGraphCode.IsCycleCode 7 A ↔
      (strongPow C7z n).IsIndepSet (A : Set (Fin n → ZMod 7)) := by
  rw [isIndepSet_iff]
  constructor
  · intro h a ha b hb hs
    exact sub_eq_zero.1 (h (a - b) ⟨a, ha, b, hb, rfl⟩ hs)
  · rintro h x ⟨a, ha, b, hb, rfl⟩ hs
    rw [h a ha b hb hs, sub_self]

/-- The two upstream predicates agree. -/
theorem isCycleCode_iff_intersectsOnlyAtZero {n : ℕ} (A : Finset (Fin n → ZMod 7)) :
    CycleGraphCode.IsCycleCode 7 A ↔ Green38.IntersectsOnlyAtZero A :=
  (isCycleCode_iff A).trans (intersectsOnlyAtZero_iff A).symm

/-- The independence number does not see the renaming `Fin 7 = ZMod 7`. -/
lemma indepNum_C7z (n : ℕ) :
    (strongPow C7z n).indepNum = (strongPow (SimpleGraph.cycleGraph 7) n).indepNum := rfl

/-- `α(C₇^{⊠n})` is the largest valid cardinality of formal-conjectures. -/
theorem isGreatest_validCardinalities (n : ℕ) :
    IsGreatest (Green38.ValidCardinalities n)
      (strongPow (SimpleGraph.cycleGraph 7) n).indepNum := by
  constructor
  · obtain ⟨s, hs⟩ := (strongPow C7z n).exists_isNIndepSet_indepNum
    exact ⟨s, (intersectsOnlyAtZero_iff s).2 hs.isIndepSet, hs.card_eq⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact ((intersectsOnlyAtZero_iff A).1 hA).card_le_indepNum

/-- **The bridge to formal-conjectures.** Their `LargestAdmissibleCardinality n` is the
independence number of the `n`-th strong power of the 7-cycle (for every `n`, including `0`). -/
theorem largestAdmissibleCardinality_eq (n : ℕ) :
    Green38.LargestAdmissibleCardinality n =
      ((strongPow (SimpleGraph.cycleGraph 7) n).indepNum : ℝ) := by
  unfold Green38.LargestAdmissibleCardinality
  rw [(isGreatest_validCardinalities n).csSup_eq]

/-! ### General facts about strong powers used by the bridges -/

/-- An upper bound on the Shannon capacity bounds every strong power:
`Θ(G) ≤ M → α(G^{⊠k}) ≤ Mᵏ` (also for `k = 0`). -/
theorem indepNum_strongPow_le_pow_of_shannonCapacity_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) {M : ℝ} (hM : shannonCapacity G ≤ M) (k : ℕ) :
    ((strongPow G k).indepNum : ℝ) ≤ M ^ k := by
  cases k with
  | zero =>
    have h := indepNum_strongPow_le G 0
    have h' : ((strongPow G 0).indepNum : ℝ) ≤ 1 := by exact_mod_cast h
    simpa using h'
  | succ k =>
    have h := (le_shannonCapacity G k).trans hM
    have h0 : (0 : ℝ) ≤ ((strongPow G (k + 1)).indepNum : ℝ) := Nat.cast_nonneg _
    have h2 := pow_le_pow_left₀ (Real.rpow_nonneg h0 _) h (k + 1)
    rwa [Real.rpow_inv_natCast_pow h0 (Nat.succ_ne_zero k)] at h2

/-- Concatenating codes: `α(G^{⊠m}) · α(G^{⊠n}) ≤ α(G^{⊠(m+n)})`. -/
theorem indepNum_strongPow_add_ge {V : Type*} [Fintype V] (G : SimpleGraph V) (m n : ℕ) :
    (strongPow G m).indepNum * (strongPow G n).indepNum ≤ (strongPow G (m + n)).indepNum := by
  classical
  obtain ⟨s, hs⟩ := (strongPow G m).exists_isNIndepSet_indepNum
  obtain ⟨t, ht⟩ := (strongPow G n).exists_isNIndepSet_indepNum
  let φ : (Fin m → V) × (Fin n → V) → (Fin (m + n) → V) := fun p => Fin.append p.1 p.2
  have hφ : Function.Injective φ := by
    rintro ⟨f, g⟩ ⟨f', g'⟩ h
    have h1 : f = f' := funext fun i => by simpa [φ] using congrFun h (Fin.castAdd n i)
    have h2 : g = g' := funext fun i => by simpa [φ] using congrFun h (Fin.natAdd m i)
    rw [h1, h2]
  have hind : (strongPow G (m + n)).IsIndepSet (((s ×ˢ t).image φ : Finset _) : Set _) := by
    intro x hx y hy hxy hadj
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product] at hx hy
    obtain ⟨⟨f, g⟩, ⟨hf, hg⟩, rfl⟩ := hx
    obtain ⟨⟨f', g'⟩, ⟨hf', hg'⟩, rfl⟩ := hy
    by_cases h1 : f = f'
    · subst h1
      have h2 : g ≠ g' := fun h => hxy (by rw [h])
      refine ht.isIndepSet (Finset.mem_coe.2 hg) (Finset.mem_coe.2 hg') h2 ⟨h2, fun i => ?_⟩
      simpa [φ] using hadj.2 (Fin.natAdd m i)
    · refine hs.isIndepSet (Finset.mem_coe.2 hf) (Finset.mem_coe.2 hf') h1 ⟨h1, fun i => ?_⟩
      simpa [φ] using hadj.2 (Fin.castAdd n i)
  have := hind.card_le_indepNum
  rwa [Finset.card_image_of_injective _ hφ, Finset.card_product, hs.card_eq, ht.card_eq] at this

/-- A single word is a code: `1 ≤ α(G^{⊠k})` when `G` has a vertex. -/
theorem one_le_indepNum_strongPow {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (k : ℕ) : 1 ≤ (strongPow G k).indepNum := by
  classical
  have hind : (strongPow G k).IsIndepSet
      (({fun _ => Classical.arbitrary V} : Finset (Fin k → V)) : Set (Fin k → V)) := by
    simp [SimpleGraph.IsIndepSet]
  simpa using hind.card_le_indepNum

/-- Repeating a code: `α(G^{⊠k})^q ≤ α(G^{⊠(k q)})`. -/
theorem pow_indepNum_strongPow_le {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (k q : ℕ) : (strongPow G k).indepNum ^ q ≤ (strongPow G (k * q)).indepNum := by
  induction q with
  | zero => simpa using one_le_indepNum_strongPow G 0
  | succ q ih =>
    calc (strongPow G k).indepNum ^ (q + 1)
        = (strongPow G k).indepNum ^ q * (strongPow G k).indepNum := pow_succ _ _
      _ ≤ (strongPow G (k * q)).indepNum * (strongPow G k).indepNum :=
          Nat.mul_le_mul_right _ ih
      _ ≤ (strongPow G (k * q + k)).indepNum := indepNum_strongPow_add_ge G _ _
      _ = (strongPow G (k * (q + 1))).indepNum := by rw [Nat.mul_succ]

/-- `367^{⌊n/5⌋} ≤ α(C₇^{⊠n})` for every `n`. -/
theorem pow_div_five_le_indepNum (n : ℕ) :
    367 ^ (n / 5) ≤ (strongPow (SimpleGraph.cycleGraph 7) n).indepNum := by
  have h1 := pow_indepNum_strongPow_le (SimpleGraph.cycleGraph 7) 5 (n / 5)
  have h2 := one_le_indepNum_strongPow (SimpleGraph.cycleGraph 7) (n % 5)
  have h3 := indepNum_strongPow_add_ge (SimpleGraph.cycleGraph 7) (5 * (n / 5)) (n % 5)
  rw [Nat.div_add_mod] at h3
  calc 367 ^ (n / 5)
      ≤ (strongPow (SimpleGraph.cycleGraph 7) 5).indepNum ^ (n / 5) :=
        Nat.pow_le_pow_left threeHundredSixtySeven_le_indepNum_strongPow_five _
    _ ≤ (strongPow (SimpleGraph.cycleGraph 7) (5 * (n / 5))).indepNum * 1 := by
        rw [mul_one]; exact h1
    _ ≤ _ := (Nat.mul_le_mul_left _ h2).trans h3

/-! ### formal-conjectures: `green_38.variants.best_upper` and `best_lower` -/

lemma C₂_nonneg : 0 ≤ Green38.C₂ :=
  le_trans (by norm_num) (three_le_shannonCapacity_cycleGraph_seven.trans
    shannonCapacity_cycleGraph_seven_le_lovaszTheta)

/-- The bound without `ε` and for every `n`: `LargestAdmissibleCardinality n ≤ C₂ⁿ`. -/
theorem largestAdmissibleCardinality_le_pow (n : ℕ) :
    Green38.LargestAdmissibleCardinality n ≤ Green38.C₂ ^ n := by
  rw [largestAdmissibleCardinality_eq]
  exact indepNum_strongPow_le_pow_of_shannonCapacity_le _
    shannonCapacity_cycleGraph_seven_le_lovaszTheta n

/-- **formal-conjectures `green_38.variants.best_upper`** (`sorry` upstream), statement copied
verbatim: `|A| ≤ (C₂ + o(1))ⁿ` with `C₂ = 7 cos(π/7)/(1 + cos(π/7))`. It follows from
`shannonCapacity_cycleGraph_seven_le_lovaszTheta`; in fact the bound holds with `ε = 0` and
for every `n` (`largestAdmissibleCardinality_le_pow`). -/
theorem green_38_variants_best_upper :
    ∀ ε > 0, ∀ᶠ n in atTop, Green38.LargestAdmissibleCardinality n ≤ (Green38.C₂ + ε) ^ n := by
  intro ε hε
  refine Eventually.of_forall fun n => ?_
  exact (largestAdmissibleCardinality_le_pow n).trans
    (pow_le_pow_left₀ C₂_nonneg (by linarith) n)

/-- `367^{⌊n/5⌋} ≤ LargestAdmissibleCardinality n`. -/
theorem pow_div_five_le_largestAdmissibleCardinality (n : ℕ) :
    (367 : ℝ) ^ (n / 5) ≤ Green38.LargestAdmissibleCardinality n := by
  rw [largestAdmissibleCardinality_eq]
  exact_mod_cast pow_div_five_le_indepNum n

/-- **formal-conjectures `green_38.variants.best_lower`** (`sorry` upstream), statement copied
verbatim: `(C₁ - o(1))ⁿ ≤ |A|` with `C₁ = 367^{1/5}`. It follows from
`threeHundredSixtySeven_le_indepNum_strongPow_five` by concatenating codes. -/
theorem green_38_variants_best_lower :
    ∀ ε ∈ Set.Ioo (0 : ℝ) Green38.C₁, ∀ᶠ n in atTop,
      (Green38.C₁ - ε) ^ n ≤ Green38.LargestAdmissibleCardinality n := by
  rintro ε ⟨hε, hεC⟩
  have hC1 : (1 : ℝ) ≤ Green38.C₁ := Real.one_le_rpow (by norm_num) (by norm_num)
  have hC0 : (0 : ℝ) < Green38.C₁ := by linarith
  have hC5 : Green38.C₁ ^ 5 = 367 := by
    unfold Green38.C₁
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have ha0 : 0 < Green38.C₁ - ε := sub_pos.2 hεC
  have hr : (Green38.C₁ - ε) / Green38.C₁ < 1 := (div_lt_one hC0).2 (by linarith)
  have hr0 : 0 ≤ (Green38.C₁ - ε) / Green38.C₁ := by positivity
  have hev : ∀ᶠ n : ℕ in atTop,
      ((Green38.C₁ - ε) / Green38.C₁) ^ n < (Green38.C₁ ^ 4)⁻¹ :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).eventually
      (eventually_lt_nhds (by positivity))
  filter_upwards [hev] with n hn
  have hpow : Green38.C₁ ^ n ≤ Green38.C₁ ^ (5 * (n / 5)) * Green38.C₁ ^ 4 := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hC1 (by omega)
  calc (Green38.C₁ - ε) ^ n
      = ((Green38.C₁ - ε) / Green38.C₁) ^ n * Green38.C₁ ^ n := by
        rw [div_pow]; field_simp
    _ ≤ (Green38.C₁ ^ 4)⁻¹ * (Green38.C₁ ^ (5 * (n / 5)) * Green38.C₁ ^ 4) :=
        mul_le_mul hn.le hpow (by positivity) (by positivity)
    _ = (367 : ℝ) ^ (n / 5) := by
        rw [pow_mul, hC5]; field_simp
    _ ≤ Green38.LargestAdmissibleCardinality n :=
        pow_div_five_le_largestAdmissibleCardinality n

/-! ### atlas-lean: `lovasz1979UpperBound` and the lower-bound requests -/

open CycleGraphCode

/-- Every atlas-lean cycle code of length `n` has at most `α(C₇^{⊠n})` words. -/
lemma card_cycleCode_le {n : ℕ} (A : CycleCode 7 n) :
    A.1.card ≤ (strongPow (SimpleGraph.cycleGraph 7) n).indepNum :=
  ((isCycleCode_iff A.1).1 A.2).card_le_indepNum

/-- An upper bound on the library's `Θ(C₇)` bounds atlas-lean's `shannonCapacityCycle 7`. -/
theorem shannonCapacityCycle_seven_le_of_le {M : ℝ}
    (hM : shannonCapacity (SimpleGraph.cycleGraph 7) ≤ M) :
    shannonCapacityCycle 7 ≤ ENNReal.ofReal M := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) (three_le_shannonCapacity_cycleGraph_seven.trans hM)
  refine iSup_le fun n => iSup_le fun A => ?_
  have hcard : (A.1.card : ℝ) ≤ M ^ n.1 :=
    (Nat.cast_le.2 (card_cycleCode_le A)).trans
      (indepNum_strongPow_le_pow_of_shannonCapacity_le _ hM n.1)
  have hn : n.1 ≠ 0 := by have := n.2; omega
  show (A.1.card : ENNReal) ^ ((n.1 : ℝ)⁻¹) ≤ ENNReal.ofReal M
  rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (A.1.card : ℝ) ^ ((n.1 : ℝ)⁻¹)
      ≤ (M ^ n.1) ^ ((n.1 : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hcard (by positivity)
    _ = M := Real.pow_rpow_inv_natCast hM0 hn

/-- **atlas-lean `lovasz1979UpperBound`** (`theorem_wanted` upstream), statement copied
verbatim. -/
theorem lovasz1979UpperBound : shannonCapacityCycle 7 ≤ lovaszThetaCycleSeven :=
  shannonCapacityCycle_seven_le_of_le shannonCapacity_cycleGraph_seven_le_lovaszTheta

/-- A lower bound on `α(C₇^{⊠n})` gives an atlas-lean cycle code of exactly that size. -/
theorem exists_cycleCode_of_le_indepNum {n M : ℕ}
    (h : M ≤ (strongPow (SimpleGraph.cycleGraph 7) n).indepNum) :
    ∃ A : Finset (Fin n → ZMod 7), IsCycleCode 7 A ∧ A.card = M := by
  obtain ⟨s, hs⟩ := (strongPow C7z n).exists_isNIndepSet_indepNum
  obtain ⟨A, hAs, hA⟩ := Finset.exists_subset_card_eq (s := s) (n := M) (by rw [hs.card_eq]; exact h)
  exact ⟨A, (isCycleCode_iff A).2 (hs.isIndepSet.mono (Finset.coe_subset.2 hAs)), hA⟩

/-- A lower bound on `α(C₇^{⊠n})`, `n ≥ 1`, gives a lower bound on `shannonCapacityCycle 7`. -/
theorem rpow_le_shannonCapacityCycle_seven {n M : ℕ} (hn : 1 ≤ n)
    (h : M ≤ (strongPow (SimpleGraph.cycleGraph 7) n).indepNum) :
    ENNReal.rpow (M : ENNReal) ((n : ℝ)⁻¹) ≤ shannonCapacityCycle 7 := by
  obtain ⟨A, hA, rfl⟩ := exists_cycleCode_of_le_indepNum h
  exact le_iSup_of_le (⟨n, hn⟩ : PositiveNat)
    (le_iSup (cycleCodeRate 7 (⟨n, hn⟩ : PositiveNat)) ⟨A, hA⟩)

/-- **atlas-lean `polakSchrijverLowerBound`** (`theorem_wanted` upstream), statement copied
verbatim. The code is the library's 367-word independent set (found by our own search; see
`Targets/InformationTheory/ShannonCapacityC7Lower.lean`), not the Polak–Schrijver set itself. -/
theorem polakSchrijverLowerBound :
    ∃ A : Finset (Fin 5 → ZMod 7), IsCycleCode 7 A ∧ A.card = 367 :=
  exists_cycleCode_of_le_indepNum threeHundredSixtySeven_le_indepNum_strongPow_five

/-- **atlas-lean `polakSchrijverRateLowerBound`** (`theorem_wanted` upstream), statement copied
verbatim. -/
theorem polakSchrijverRateLowerBound :
    ENNReal.rpow 367 ((5 : ℝ)⁻¹) ≤ shannonCapacityCycle 7 := by
  simpa using rpow_le_shannonCapacityCycle_seven (n := 5) (M := 367) (by norm_num)
    threeHundredSixtySeven_le_indepNum_strongPow_five

/-- **atlas-lean `mathewOstergard2017LowerBound`** (`theorem_wanted` upstream), statement copied
verbatim (implied by the 367-word code). -/
theorem mathewOstergard2017LowerBound :
    ENNReal.rpow 350 ((5 : ℝ)⁻¹) ≤ shannonCapacityCycle 7 := by
  simpa using rpow_le_shannonCapacityCycle_seven (n := 5) (M := 350) (by norm_num)
    (le_trans (by norm_num) threeHundredSixtySeven_le_indepNum_strongPow_five)

/-- **atlas-lean `veselZerovnik2002LowerBound`** (`theorem_wanted` upstream), statement copied
verbatim. -/
theorem veselZerovnik2002LowerBound :
    ENNReal.rpow 108 ((4 : ℝ)⁻¹) ≤ shannonCapacityCycle 7 := by
  simpa using rpow_le_shannonCapacityCycle_seven (n := 4) (M := 108) (by norm_num)
    oneHundredEight_le_indepNum_strongPow_four

/-- atlas-lean's capacity of the 7-cycle is finite. -/
lemma shannonCapacityCycle_seven_ne_top : shannonCapacityCycle 7 ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top lovasz1979UpperBound

/-- **The bridge to atlas-lean.** Their `shannonCapacityCycle 7 : ENNReal` is the library's
real number `shannonCapacity (cycleGraph 7)`. -/
theorem shannonCapacityCycle_seven_eq :
    shannonCapacityCycle 7 = ENNReal.ofReal (shannonCapacity (SimpleGraph.cycleGraph 7)) := by
  refine le_antisymm (shannonCapacityCycle_seven_le_of_le le_rfl) ?_
  rw [← ENNReal.ofReal_toReal shannonCapacityCycle_seven_ne_top]
  refine ENNReal.ofReal_le_ofReal (ciSup_le fun k => ?_)
  have h := rpow_le_shannonCapacityCycle_seven (n := k + 1)
    (M := (strongPow (SimpleGraph.cycleGraph 7) (k + 1)).indepNum) (by omega) le_rfl
  have h' : ENNReal.ofReal
      (((strongPow (SimpleGraph.cycleGraph 7) (k + 1)).indepNum : ℝ) ^ (((k + 1 : ℕ) : ℝ)⁻¹)) ≤
      shannonCapacityCycle 7 := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity),
      ENNReal.ofReal_natCast]
    exact h
  exact (ENNReal.ofReal_le_iff_le_toReal shannonCapacityCycle_seven_ne_top).1 h'

/-! ### cslib-frontier and shannon-capacity-lean: the same supremum, other spellings

Both projects define the strong power with the adjacency
`x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)`, word for word the library's `strongPow`, and the
Shannon capacity as a supremum over `k + 1`; only the exponent is spelled differently. -/

/-- The exponent spelling of cslib-frontier
(`CslibFrontier/Foundations/Combinatorics/SimpleGraph/ShannonCapacity.lean`):
`⨆ k, α(G^{⊠(k+1)}) ^ ((k + 1 : ℝ)⁻¹)`. -/
theorem shannonCapacity_eq_cslibFrontier_form {V : Type*} (G : SimpleGraph V) :
    shannonCapacity G = ⨆ k : ℕ, ((strongPow G (k + 1)).indepNum : ℝ) ^ ((k + 1 : ℝ)⁻¹) := by
  simp [shannonCapacity]

/-- The exponent spelling of spectra-research/shannon-capacity-lean (`ShannonBounds/Defs.lean`):
`⨆ n, α(G^{⊠(n+1)}) ^ (1 / (n + 1 : ℝ))`. -/
theorem shannonCapacity_eq_shannonBounds_form {V : Type*} (G : SimpleGraph V) :
    shannonCapacity G = ⨆ n : ℕ, ((strongPow G (n + 1)).indepNum : ℝ) ^ (1 / (n + 1 : ℝ)) := by
  simp [shannonCapacity]

/-! ### formal-conjectures pull request #5321: the recursive strong power -/

namespace PR5321

universe u

variable {α β : Type u}

open SimpleGraph

/-- Tensor product of simple graphs. (Copied from formal-conjectures PR #5321,
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Shannon.lean`.) -/
def tensorProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm.symm x y h := by rwa [adj_comm G, adj_comm H]

/-- Strong product of simple graphs. (Copied from formal-conjectures PR #5321.) -/
def strongProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) :=
  boxProd G H ⊔ tensorProd G H

/-- The power of a simple graph w. r. t. the strong product. (Copied from formal-conjectures
PR #5321.) -/
def strongPow (G : SimpleGraph α) : (n : ℕ) → SimpleGraph (Fin n → α)
  | 0 => completeGraph _
  | n + 1 => (Fin.succFunEquiv α n).symm.simpleGraph <| strongProd (strongPow G n) G

/-- The Shannon capacity of a graph. (Copied from formal-conjectures PR #5321, with their
notation `α(G)` written as `G.indepNum`.) -/
noncomputable def shannonCapacity (G : SimpleGraph α) : ℝ :=
  sSup {((strongPow G n).indepNum : ℝ) ^ (↑n : ℝ)⁻¹ | n > 0}

/-- The recursive strong power has the coordinatewise adjacency of the library's `strongPow`. -/
theorem strongPow_adj (G : SimpleGraph α) (n : ℕ) (f g : Fin n → α) :
    (strongPow G n).Adj f g ↔ f ≠ g ∧ ∀ i, f i = g i ∨ G.Adj (f i) (g i) := by
  induction n with
  | zero => simp [strongPow]
  | succ n ih =>
    have hne : f = g ↔
        (∀ i : Fin n, f i.castSucc = g i.castSucc) ∧ f (Fin.last n) = g (Fin.last n) := by
      rw [funext_iff, Fin.forall_fin_succ']
    rw [Fin.forall_fin_succ', Ne, hne]
    simp only [strongPow, strongProd, Equiv.simpleGraph_apply, Equiv.symm_symm, comap_adj,
      sup_adj, boxProd_adj, tensorProd, ih, Fin.succFunEquiv_apply, funext_iff]
    have h1 : ∀ i : Fin n, Fin.castAdd 1 i = i.castSucc := fun _ => rfl
    have h2 : Fin.natAdd n (0 : Fin 1) = Fin.last n := rfl
    simp only [h1, h2, ne_eq, funext_iff]
    have hl : G.Adj (f (Fin.last n)) (g (Fin.last n)) → f (Fin.last n) ≠ g (Fin.last n) :=
      fun h => h.ne
    have hPQ : (∀ i : Fin n, f i.castSucc = g i.castSucc) →
        ∀ i : Fin n, f i.castSucc = g i.castSucc ∨ G.Adj (f i.castSucc) (g i.castSucc) :=
      fun h i => Or.inl (h i)
    tauto

/-- **The bridge to PR #5321**: its strong power is the library's. -/
theorem strongPow_eq (G : SimpleGraph α) (n : ℕ) :
    strongPow G n = Applied.InformationTheory.strongPow G n := by
  ext f g
  exact strongPow_adj G n f g

/-- **The bridge to PR #5321**: its Shannon capacity is the library's (for every graph; the
supremum over `n > 0` is the library's supremum over `k + 1`). -/
theorem shannonCapacity_eq (G : SimpleGraph α) :
    shannonCapacity G = Applied.InformationTheory.shannonCapacity G := by
  unfold shannonCapacity Applied.InformationTheory.shannonCapacity
  rw [iSup]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_range, strongPow_eq]
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, Nat.succ_pos k, rfl⟩

/-- **PR #5321 `shannonCapacityC5`** (`sorry` there), statement copied verbatim. -/
theorem shannonCapacityC5 : shannonCapacity (cycleGraph 5) = √5 := by
  rw [shannonCapacity_eq]; exact shannonCapacity_cycleGraph_five

/-- **PR #5321 `threesixseven_le_indepNum_pow_five`** (`sorry` there), statement copied
verbatim. -/
theorem threesixseven_le_indepNum_pow_five : 367 ≤ indepNum (strongPow (cycleGraph 7) 5) := by
  rw [strongPow_eq]; exact threeHundredSixtySeven_le_indepNum_strongPow_five

/-- **PR #5321 `root_367_le_shannonCapacityC7`**, statement copied verbatim (proved there
modulo two `sorry`s). -/
theorem root_367_le_shannonCapacityC7 :
    (367 : ℝ) ^ (5 : ℝ)⁻¹ ≤ shannonCapacity (cycleGraph 7) := by
  rw [shannonCapacity_eq]
  have h := rpow_threeHundredSixtySeven_le_shannonCapacity_cycleGraph_seven
  rwa [one_div] at h

/-- The known half of PR #5321's open problem `shannonCapacityC7`
(`answer(sorry) ↔ shannonCapacity (cycleGraph 7) = 7 cos(π/7)/(1 + cos(π/7))`). -/
theorem shannonCapacityC7_le :
    shannonCapacity (cycleGraph 7) ≤
      (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7)) := by
  rw [shannonCapacity_eq]; exact shannonCapacity_cycleGraph_seven_le_lovaszTheta

end PR5321

end Applied.InformationTheory.LovaszBridge
