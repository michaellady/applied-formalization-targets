import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic

/-!
# The matroid secretary problem: the model

This is the model file for all `MatroidSecretary*.lean` and `Secretary*.lean` files. It
contains the definitions and the two trivial algorithms; nothing here depends on the structure
of a particular matroid.

## Model

* The ground set is a finite type `E` with `n = Fintype.card E` elements, carrying a matroid
  `M : Matroid E` (Mathlib's matroids) and a weight function `w : E → ℝ`.
* An *arrival order* is a bijection `σ : Fin n ≃ E` (`ArrivalOrder E`); `σ i` is the element
  arriving at time `i` (times are `0, …, n - 1`). There are `n!` arrival orders.
* An *online algorithm* (`OnlineAlg E`) is a decision function: for every `k` and every
  sequence `h : Fin (k + 1) → E × ℝ` of the first `k + 1` arrivals, each with its weight, it
  says whether the last of them, `h (Fin.last k)`, is accepted. The decision is irrevocable
  because it is made once, at the arrival of the element, as a function of what has been
  revealed up to that time only. Earlier decisions need not be passed explicitly: they are
  functions of shorter prefixes of the same sequence.
* `Accepts A σ w e`: the algorithm `A` accepts the element `e` when the arrival order is `σ`
  and the weights are `w`. `selected A σ w` is the set of accepted elements.
* `IsFeasible M A`: for every arrival order and every non-negative weight function the set of
  accepted elements is independent in `M`.
* `expWeight A w`: the average over all `n!` arrival orders of the total weight of the
  accepted set.
* `IsCompetitive M A c`: for all non-negative weights and every independent set `I`,
  `c * w(I) ≤ expWeight A w`.
* `HasCompetitiveRandomized M c`: there is a probability space `(Ω, P)` and a family of
  feasible online algorithms `A ω` such that for all non-negative weights and every
  independent set `I`, `c * w(I) ≤ ∫ ω, expWeight (A ω) w ∂P`.

## Results

* `never_isFeasible`, `expWeight_never`: accepting nothing is a feasible online algorithm of
  expected weight `0`.
* `card_mul_sum_orders_apply`: under a uniformly random arrival order the element arriving
  at a fixed time is uniformly distributed.
* `firstNonloop_isFeasible`, `firstNonloop_isCompetitive`: for every matroid on `n` elements,
  "accept the first arrival if it is not a loop, and nothing else" is feasible and
  `1/n`-competitive.
* `IsCompetitive.hasCompetitiveRandomized`: a deterministic competitive algorithm is a
  randomized one.

## Where the other results are

| File | Content |
|---|---|
| `MatroidSecretary.lean` | threshold rule, classical secretary with constant `1/4`, rank-one matroid |
| `SecretaryOneOverE.lean` | exact success probability of threshold rules, constant `1/e` |
| `SecretaryRankOptimal.lean`, `SecretaryArrivalOptimal.lean` | optimality of threshold rules |
| `MatroidSecretaryDirectSum.lean` | direct sums, restriction, partition matroids |
| `MatroidSecretaryUniform.lean`, `MatroidSecretaryUniformTop.lean` | uniform matroids, `e⁻²` and `(1 - 1/e)/e` |
| `MatroidSecretaryGraphic.lean` | graphic matroids |
| `MatroidSecretaryLaminar.lean` | laminar matroids of bounded depth |

## Not in this file

Algorithms with internal randomness are modelled only through `HasCompetitiveRandomized`
(a probability space of deterministic algorithms). Weights are revealed exactly; there is no
adversarial-order or free-order model. The matroid secretary conjecture itself (a constant
valid for all matroids) is open and is not proved anywhere in the library.
-/

open Finset Function

open scoped Nat

open Classical

noncomputable section

namespace Applied.Economics.MatroidSecretary

variable {E : Type*} [Fintype E]

/-- An arrival order: `σ i` is the element arriving at time `i`. -/
abbrev ArrivalOrder (E : Type*) [Fintype E] := Fin (Fintype.card E) ≃ E

/-- A (deterministic) online algorithm: given the first `k + 1` arrivals with their weights,
decide whether to accept the last one. -/
def OnlineAlg (E : Type*) := (k : ℕ) → (Fin (k + 1) → E × ℝ) → Prop

/-- The first `i + 1` arrivals, with their weights, under the arrival order `σ`. -/
def arrivals (σ : ArrivalOrder E) (w : E → ℝ) (i : Fin (Fintype.card E)) :
    Fin (i + 1) → E × ℝ :=
  fun j => (σ (Fin.castLE i.isLt j), w (σ (Fin.castLE i.isLt j)))

/-- The algorithm `A` accepts `e` under the arrival order `σ` and the weights `w`: its
decision at the arrival time `σ.symm e` of `e`, on the arrivals up to that time, is "accept". -/
def Accepts (A : OnlineAlg E) (σ : ArrivalOrder E) (w : E → ℝ) (e : E) : Prop :=
  A (σ.symm e) (arrivals σ w (σ.symm e))

/-- The set of accepted elements. -/
def selected (A : OnlineAlg E) (σ : ArrivalOrder E) (w : E → ℝ) : Finset E :=
  univ.filter (Accepts A σ w)

@[simp] lemma mem_selected {A : OnlineAlg E} {σ : ArrivalOrder E} {w : E → ℝ} {e : E} :
    e ∈ selected A σ w ↔ Accepts A σ w e := by
  simp [selected]

/-- The expected weight of the accepted set under a uniformly random arrival order: the
average over all `n!` arrival orders. -/
def expWeight (A : OnlineAlg E) (w : E → ℝ) : ℝ :=
  (∑ σ : ArrivalOrder E, ∑ e ∈ selected A σ w, w e) / (Fintype.card E)!

/-- The algorithm always (for every arrival order and all non-negative weights) accepts an
independent set of the matroid `M`. -/
def IsFeasible (M : Matroid E) (A : OnlineAlg E) : Prop :=
  ∀ (σ : ArrivalOrder E) (w : E → ℝ), (∀ e, 0 ≤ w e) → M.Indep (selected A σ w : Set E)

/-- The algorithm is `c`-competitive: for all non-negative weights its expected weight is at
least `c` times the weight of every independent set. -/
def IsCompetitive (M : Matroid E) (A : OnlineAlg E) (c : ℝ) : Prop :=
  ∀ w : E → ℝ, (∀ e, 0 ≤ w e) → ∀ I : Finset E, M.Indep (I : Set E) →
    c * ∑ e ∈ I, w e ≤ expWeight A w

/-- There is a randomized feasible online algorithm that is `c`-competitive: a probability
space `(Ω, P)` and feasible online algorithms `A ω` whose expected weight, averaged over `ω`,
is at least `c` times the weight of every independent set, for all non-negative weights.
(The integral is the Bochner integral, which is `0` if `ω ↦ expWeight (A ω) w` is not
integrable; this can only hurt the algorithm.) -/
def HasCompetitiveRandomized (M : Matroid E) (c : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω)
    (_ : MeasureTheory.IsProbabilityMeasure P) (A : Ω → OnlineAlg E),
    (∀ ω, IsFeasible M (A ω)) ∧
      ∀ w : E → ℝ, (∀ e, 0 ≤ w e) → ∀ I : Finset E, M.Indep (I : Set E) →
        c * ∑ e ∈ I, w e ≤ ∫ ω, expWeight (A ω) w ∂P

lemma expWeight_nonneg (A : OnlineAlg E) {w : E → ℝ} (hw : ∀ e, 0 ≤ w e) :
    0 ≤ expWeight A w :=
  div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => hw _) (Nat.cast_nonneg _)

/-- A deterministic competitive algorithm is in particular a randomized one. -/
theorem IsCompetitive.hasCompetitiveRandomized {M : Matroid E} {A : OnlineAlg E} {c : ℝ}
    (hA : IsFeasible M A) (hc : IsCompetitive M A c) : HasCompetitiveRandomized M c := by
  refine ⟨Unit, inferInstance, MeasureTheory.Measure.dirac (), inferInstance, fun _ => A,
    fun _ => hA, fun w hw I hI => ?_⟩
  simpa using hc w hw I hI

/-! ### Accepting nothing -/

/-- The algorithm that never accepts. -/
def never : OnlineAlg E := fun _ _ => False

@[simp] lemma selected_never (σ : ArrivalOrder E) (w : E → ℝ) : selected never σ w = ∅ := by
  ext e; simp [Accepts, never]

/-- Accepting nothing is feasible for every matroid. -/
theorem never_isFeasible (M : Matroid E) : IsFeasible M never := by
  intro σ w _
  simp

/-- Accepting nothing has expected weight `0`. -/
@[simp] theorem expWeight_never (w : E → ℝ) : expWeight (never : OnlineAlg E) w = 0 := by
  simp [expWeight]

/-! ### Averaging over arrival orders -/

/-- Under a uniformly random arrival order, the element at a fixed time is uniform:
`n * ∑_σ g (σ i) = n! * ∑_e g e`. -/
lemma card_mul_sum_orders_apply (g : E → ℝ) (i : Fin (Fintype.card E)) :
    (Fintype.card E : ℝ) * ∑ σ : ArrivalOrder E, g (σ i) = (Fintype.card E)! * ∑ e, g e := by
  have h : ∀ j, ∑ σ : ArrivalOrder E, g (σ j) = ∑ σ : ArrivalOrder E, g (σ i) := by
    intro j
    refine Fintype.sum_equiv ((Equiv.swap i j).equivCongr (Equiv.refl E)) _ _ fun σ => ?_
    simp
  calc (Fintype.card E : ℝ) * ∑ σ : ArrivalOrder E, g (σ i)
      = ∑ j : Fin (Fintype.card E), ∑ σ : ArrivalOrder E, g (σ j) := by simp [h]
    _ = ∑ σ : ArrivalOrder E, ∑ j, g (σ j) := Finset.sum_comm
    _ = ∑ σ : ArrivalOrder E, ∑ e, g e :=
        Finset.sum_congr rfl fun σ _ => Equiv.sum_comp σ g
    _ = (Fintype.card E)! * ∑ e, g e := by
        simp [Fintype.card_equiv (Fintype.equivFin E).symm]

/-! ### Accepting the first arrival: a `1/n`-competitive algorithm -/

/-- Accept the first arrival if it is a non-loop of `M`; accept nothing else. -/
def firstNonloop (M : Matroid E) : OnlineAlg E := fun k h => k = 0 ∧ M.Indep {(h 0).1}

lemma accepts_firstNonloop (M : Matroid E) (σ : ArrivalOrder E) (w : E → ℝ) (e : E) :
    Accepts (firstNonloop M) σ w e ↔ ((σ.symm e : ℕ) = 0 ∧ M.Indep {e}) := by
  unfold Accepts firstNonloop
  refine and_congr_right fun h => ?_
  have h0 : Fin.castLE (σ.symm e).isLt (0 : Fin ((σ.symm e : ℕ) + 1)) = σ.symm e :=
    Fin.ext (by simp [h])
  simp [arrivals, h0]

/-- "Accept the first arrival if it is not a loop" is feasible for every matroid: it accepts at
most one element, and only a non-loop. -/
theorem firstNonloop_isFeasible (M : Matroid E) : IsFeasible M (firstNonloop M) := by
  intro σ w _
  rcases (selected (firstNonloop M) σ w).eq_empty_or_nonempty with h | ⟨e, he⟩
  · rw [h]; simp
  · have hs : selected (firstNonloop M) σ w = {e} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨he, fun e' he' => ?_⟩
      rw [mem_selected, accepts_firstNonloop] at he he'
      have : σ.symm e' = σ.symm e := Fin.ext (by rw [he.1, he'.1])
      exact σ.symm.injective this
    rw [hs, Finset.coe_singleton]
    exact ((accepts_firstNonloop M σ w e).1 (mem_selected.1 he)).2

/-- For every matroid on a set of `n` elements, accepting the first arrival (if it is not a
loop) is `1/n`-competitive. -/
theorem firstNonloop_isCompetitive (M : Matroid E) :
    IsCompetitive M (firstNonloop M) (1 / Fintype.card E) := by
  intro w hw I hI
  rcases Nat.eq_zero_or_pos (Fintype.card E) with hn | hn
  · simpa [hn] using expWeight_nonneg (firstNonloop M) hw
  set g : E → ℝ := fun e => if M.Indep {e} then w e else 0 with hg
  have hg0 : ∀ e, 0 ≤ g e := fun e => by rw [hg]; dsimp only; split_ifs <;> simp [hw e]
  have hsel : ∀ σ : ArrivalOrder E, ∑ e ∈ selected (firstNonloop M) σ w, w e = g (σ ⟨0, hn⟩) := by
    intro σ
    rw [selected, Finset.sum_filter, Finset.sum_eq_single (σ ⟨0, hn⟩)]
    · simp [accepts_firstNonloop, hg]
    · intro e _ he
      rw [ite_eq_right_iff, accepts_firstNonloop]
      rintro ⟨h0, -⟩
      exfalso
      apply he
      rw [← σ.symm_apply_eq]
      exact Fin.ext h0
    · simp
  have hn' : (0 : ℝ) < Fintype.card E := by exact_mod_cast hn
  have hfac : (0 : ℝ) < (Fintype.card E)! := by exact_mod_cast Nat.factorial_pos _
  have key := card_mul_sum_orders_apply g (⟨0, hn⟩ : Fin (Fintype.card E))
  have hexp : expWeight (firstNonloop M) w = (∑ e, g e) / Fintype.card E := by
    rw [expWeight, Finset.sum_congr rfl fun σ _ => hsel σ, div_eq_div_iff hfac.ne' hn'.ne']
    linarith
  have hI' : ∑ e ∈ I, w e ≤ ∑ e, g e := by
    calc ∑ e ∈ I, w e = ∑ e ∈ I, g e := by
          refine Finset.sum_congr rfl fun e he => ?_
          have : M.Indep {e} := hI.subset (by simpa using he)
          simp only [hg]
          split_ifs
          rfl
      _ ≤ ∑ e, g e := Finset.sum_le_univ_sum_of_nonneg hg0
  rw [hexp, one_div, inv_mul_eq_div]
  gcongr

end Applied.Economics.MatroidSecretary
