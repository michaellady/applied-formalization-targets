import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Fisher–Neyman factorization theorem, finite sample space

A statistical model on a finite sample space `X` is a family `p θ : X → ℝ` of non-negative
weights (probability mass functions; that they sum to one is never used). For a statistic
`T : X → Y`:

* `marginal p T θ t` is `P_θ(T = t) = ∑ x with T x = t, p θ x`;
* `condProb p T θ x` is `P_θ(sample = x | T = T x) = p θ x / P_θ(T = T x)`;
* `IsSufficient p T` says that the conditional law of the sample given `T` does not depend on
  the parameter: for all `θ, θ'` and all `x` such that `T = T x` has positive probability under
  both, the two conditional probabilities of `x` agree.

`isSufficient_iff_factorization` is the **Fisher–Neyman factorization theorem**: `T` is
sufficient if and only if `p θ x = g θ (T x) * h x` for some `g` and some `h ≥ 0`.
`isSufficient_iff_exists_kernel` restates sufficiency as the existence of a single
parameter-free conditional pmf.
-/

open Finset

namespace Applied.Statistics

variable {Θ X Y : Type*} [Fintype X] [DecidableEq Y]

/-- `P_θ(T = t)`: the total mass of the fibre of `T` over `t`. -/
def marginal (p : Θ → X → ℝ) (T : X → Y) (θ : Θ) (t : Y) : ℝ :=
  ∑ x with T x = t, p θ x

/-- `P_θ(sample = x | T = T x)`. (Equal to `0` by convention when `P_θ(T = T x) = 0`.) -/
noncomputable def condProb (p : Θ → X → ℝ) (T : X → Y) (θ : Θ) (x : X) : ℝ :=
  p θ x / marginal p T θ (T x)

/-- `T` is **sufficient** for the family `p`: the conditional probability of each sample point
given the value of `T` is the same under any two parameters for which that value of `T` has
positive probability. -/
def IsSufficient (p : Θ → X → ℝ) (T : X → Y) : Prop :=
  ∀ θ θ' x, 0 < marginal p T θ (T x) → 0 < marginal p T θ' (T x) →
    condProb p T θ x = condProb p T θ' x

/-- `p` **factorizes** through `T`: `p θ x = g θ (T x) * h x` with `h ≥ 0`. -/
def HasFactorization (p : Θ → X → ℝ) (T : X → Y) : Prop :=
  ∃ (g : Θ → Y → ℝ) (h : X → ℝ), (∀ x, 0 ≤ h x) ∧ ∀ θ x, p θ x = g θ (T x) * h x

variable {p : Θ → X → ℝ} {T : X → Y}

theorem marginal_nonneg (hp : ∀ θ x, 0 ≤ p θ x) (θ : Θ) (t : Y) : 0 ≤ marginal p T θ t :=
  sum_nonneg fun x _ => hp θ x

/-- A sample point in a fibre of probability zero has probability zero. -/
theorem eq_zero_of_marginal_eq_zero (hp : ∀ θ x, 0 ≤ p θ x) {θ : Θ} {x : X}
    (h : marginal p T θ (T x) = 0) : p θ x = 0 :=
  (sum_eq_zero_iff_of_nonneg fun y _ => hp θ y).mp h x (by simp)

/-- The marginals of `T` sum to the total mass. -/
theorem sum_marginal [Fintype Y] (p : Θ → X → ℝ) (T : X → Y) (θ : Θ) :
    ∑ t, marginal p T θ t = ∑ x, p θ x := by
  simp only [marginal]
  exact sum_fiberwise univ T (p θ)

/-- Under a factorization, the conditional probability is `h x / ∑_{T y = T x} h y`. -/
theorem condProb_eq_of_factorization {g : Θ → Y → ℝ} {h : X → ℝ}
    (hfac : ∀ θ x, p θ x = g θ (T x) * h x) {θ : Θ} {x : X}
    (hpos : 0 < marginal p T θ (T x)) :
    condProb p T θ x = h x / ∑ y with T y = T x, h y := by
  have hm : marginal p T θ (T x) = g θ (T x) * ∑ y with T y = T x, h y := by
    rw [marginal, mul_sum]
    refine sum_congr rfl fun y hy => ?_
    rw [hfac θ y, (mem_filter.mp hy).2]
  have hg : g θ (T x) ≠ 0 := by
    rintro h0
    rw [hm, h0, zero_mul] at hpos
    exact lt_irrefl _ hpos
  rw [condProb, hm, hfac θ x, mul_div_mul_left _ _ hg]

/-- The easy direction of the factorization theorem. (Non-negativity is not needed.) -/
theorem IsSufficient.of_factorization {g : Θ → Y → ℝ} {h : X → ℝ}
    (hfac : ∀ θ x, p θ x = g θ (T x) * h x) : IsSufficient p T := fun θ θ' x hθ hθ' => by
  rw [condProb_eq_of_factorization hfac hθ, condProb_eq_of_factorization hfac hθ']

open Classical in
/-- The hard direction: a sufficient statistic gives the factorization
`p θ x = P_θ(T = T x) * h x`, where `h x` is the common conditional probability of `x` given
`T = T x`. -/
theorem IsSufficient.exists_factorization (hp : ∀ θ x, 0 ≤ p θ x) (hT : IsSufficient p T) :
    ∃ h : X → ℝ, (∀ x, 0 ≤ h x) ∧ ∀ θ x, p θ x = marginal p T θ (T x) * h x := by
  refine ⟨fun x => if hx : ∃ θ, 0 < marginal p T θ (T x) then condProb p T hx.choose x else 0,
    fun x => ?_, fun θ x => ?_⟩
  · dsimp only
    split_ifs with hx
    · exact div_nonneg (hp _ _) (marginal_nonneg hp _ _)
    · exact le_rfl
  · rcases (marginal_nonneg (T := T) hp θ (T x)).eq_or_lt with h0 | hpos
    · rw [eq_zero_of_marginal_eq_zero hp h0.symm, ← h0, zero_mul]
    · have hx : ∃ θ, 0 < marginal p T θ (T x) := ⟨θ, hpos⟩
      dsimp only
      split_ifs
      rw [← hT θ hx.choose x hpos hx.choose_spec, condProb, mul_div_cancel₀ _ hpos.ne']

/-- **Fisher–Neyman factorization theorem** (finite sample space): a statistic is sufficient
if and only if the pmf factorizes as `p θ x = g θ (T x) * h x` with `h ≥ 0`. -/
theorem isSufficient_iff_factorization (hp : ∀ θ x, 0 ≤ p θ x) :
    IsSufficient p T ↔ HasFactorization p T := by
  constructor
  · intro hT
    obtain ⟨h, hh, hfac⟩ := hT.exists_factorization hp
    exact ⟨fun θ t => marginal p T θ t, h, hh, hfac⟩
  · rintro ⟨g, h, -, hfac⟩
    exact IsSufficient.of_factorization hfac

/-- In the factorization, `g` can be taken non-negative: it can be taken to be the pmf of `T`. -/
theorem IsSufficient.exists_nonneg_factorization (hp : ∀ θ x, 0 ≤ p θ x)
    (hT : IsSufficient p T) :
    ∃ (g : Θ → Y → ℝ) (h : X → ℝ), (∀ θ t, 0 ≤ g θ t) ∧ (∀ x, 0 ≤ h x) ∧
      ∀ θ x, p θ x = g θ (T x) * h x := by
  obtain ⟨h, hh, hfac⟩ := hT.exists_factorization hp
  exact ⟨fun θ t => marginal p T θ t, h, fun θ t => marginal_nonneg hp θ t, hh, hfac⟩

/-- Sufficiency means that there is one conditional pmf, not depending on the parameter, that
serves for every parameter: `P_θ(sample = x | T = T x) = c x` whenever `P_θ(T = T x) > 0`. -/
theorem isSufficient_iff_exists_kernel (hp : ∀ θ x, 0 ≤ p θ x) :
    IsSufficient p T ↔
      ∃ c : X → ℝ, ∀ θ x, 0 < marginal p T θ (T x) → condProb p T θ x = c x := by
  constructor
  · intro hT
    obtain ⟨h, -, hfac⟩ := hT.exists_factorization hp
    refine ⟨h, fun θ x hpos => ?_⟩
    rw [condProb]
    nth_rewrite 1 [hfac θ x]
    rw [mul_div_cancel_left₀ _ hpos.ne']
  · rintro ⟨c, hc⟩ θ θ' x hθ hθ'
    rw [hc θ x hθ, hc θ' x hθ']

end Applied.Statistics
