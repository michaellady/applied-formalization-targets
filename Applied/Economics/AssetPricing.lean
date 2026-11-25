import Applied.Economics.Minimax
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# The fundamental theorem of asset pricing: one period, finitely many states

A one-period market has finitely many assets `i : ι` with prices `π i` today and payoffs
`D i s` tomorrow in each of finitely many states `s : S`. A portfolio is `θ : ι → ℝ` (short
sales allowed, no frictions); it costs `cost π θ = ∑ i, θ i * π i` and pays
`payoff D θ s = ∑ i, θ i * D i s` in state `s`.

* `IsArbitrage π D θ`: `θ` costs at most zero, pays at least zero in every state, and one of
  these inequalities is strict.
* `IsStatePrice π D q`: `q s > 0` for all `s` and `π i = ∑ s, q s * D i s` for all `i`.
* `cost_eq_sum_statePrice`: with state prices `q`, every portfolio costs the `q`-weighted sum
  of its payoffs.
* `noArbitrage_of_isStatePrice`: state prices exclude arbitrage (the easy direction).
* `exists_isStatePrice_of_noArbitrage`: no arbitrage gives state prices (the hard direction),
  by strictly separating the unit simplex of `Option S → ℝ` from the subspace of attainable
  (minus cost, payoff) vectors.
* `noArbitrage_iff_exists_isStatePrice`: the equivalence.
-/

open Finset

namespace Applied.Economics.AssetPricing

variable {ι S : Type*} [Fintype ι] [Fintype S]

/-- Cost today of the portfolio `θ` at prices `π`. -/
def cost (π : ι → ℝ) (θ : ι → ℝ) : ℝ := ∑ i, θ i * π i

/-- Payoff of the portfolio `θ` in state `s`. -/
def payoff (D : ι → S → ℝ) (θ : ι → ℝ) (s : S) : ℝ := ∑ i, θ i * D i s

/-- An arbitrage: a portfolio that costs at most zero, never loses, and either has strictly
negative cost or pays strictly positively in some state. -/
def IsArbitrage (π : ι → ℝ) (D : ι → S → ℝ) (θ : ι → ℝ) : Prop :=
  cost π θ ≤ 0 ∧ (∀ s, 0 ≤ payoff D θ s) ∧ (cost π θ < 0 ∨ ∃ s, 0 < payoff D θ s)

/-- The market admits no arbitrage. -/
def NoArbitrage (π : ι → ℝ) (D : ι → S → ℝ) : Prop := ∀ θ, ¬ IsArbitrage π D θ

/-- Strictly positive state prices: every asset's price is the state-price-weighted sum of its
payoffs. -/
def IsStatePrice (π : ι → ℝ) (D : ι → S → ℝ) (q : S → ℝ) : Prop :=
  (∀ s, 0 < q s) ∧ ∀ i, π i = ∑ s, q s * D i s

/-- With state prices, the cost of any portfolio is the weighted sum of its payoffs. -/
theorem cost_eq_sum_statePrice {π : ι → ℝ} {D : ι → S → ℝ} {q : S → ℝ}
    (hq : ∀ i, π i = ∑ s, q s * D i s) (θ : ι → ℝ) :
    cost π θ = ∑ s, q s * payoff D θ s := by
  simp only [cost, payoff, hq, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring

/-- **Fundamental theorem of asset pricing, easy direction.** Strictly positive state prices
exclude arbitrage. -/
theorem noArbitrage_of_isStatePrice {π : ι → ℝ} {D : ι → S → ℝ} {q : S → ℝ}
    (hq : IsStatePrice π D q) : NoArbitrage π D := by
  rintro θ ⟨hc, hp, hstrict⟩
  have hcost := cost_eq_sum_statePrice hq.2 θ
  have hnn : ∀ s ∈ (Finset.univ : Finset S), 0 ≤ q s * payoff D θ s :=
    fun s _ => mul_nonneg (hq.1 s).le (hp s)
  rcases hstrict with h | ⟨s, hs⟩
  · have := Finset.sum_nonneg hnn
    linarith
  · have : 0 < ∑ s, q s * payoff D θ s :=
      Finset.sum_pos' hnn ⟨s, Finset.mem_univ s, mul_pos (hq.1 s) hs⟩
    linarith

/-- The linear map sending a portfolio to (minus its cost, its payoff in each state). -/
private def outcome (π : ι → ℝ) (D : ι → S → ℝ) : (ι → ℝ) →ₗ[ℝ] (Option S → ℝ) where
  toFun θ o := Option.elim o (-cost π θ) (payoff D θ)
  map_add' θ θ' := by
    funext o
    cases o <;> simp [cost, payoff, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c θ := by
    funext o
    cases o <;> simp [cost, payoff, mul_assoc, Finset.mul_sum]

/-- **Fundamental theorem of asset pricing, hard direction.** A market without arbitrage has
strictly positive state prices. -/
theorem exists_isStatePrice_of_noArbitrage {π : ι → ℝ} {D : ι → S → ℝ}
    (h : NoArbitrage π D) : ∃ q, IsStatePrice π D q := by
  classical
  set L := outcome π D with hL
  set M : Submodule ℝ (Option S → ℝ) := LinearMap.range L with hM
  have hdisj : Disjoint (mixedStrategies (Option S)) (M : Set (Option S → ℝ)) := by
    rw [Set.disjoint_left]
    rintro x ⟨hx0, hx1⟩ ⟨θ, rfl⟩
    refine h θ ⟨?_, fun s => ?_, ?_⟩
    · have := hx0 none
      simp only [hL, outcome, LinearMap.coe_mk, AddHom.coe_mk, Option.elim] at this
      linarith
    · simpa [hL, outcome] using hx0 (some s)
    · by_contra hcon
      rw [not_or, not_lt, not_exists] at hcon
      have h0 : ∀ o, L θ o = 0 := by
        intro o
        refine le_antisymm ?_ (hx0 o)
        cases o with
        | none =>
          simp only [hL, outcome, LinearMap.coe_mk, AddHom.coe_mk, Option.elim]
          linarith [hcon.1]
        | some s => simpa [hL, outcome] using hcon.2 s
      simp [h0] at hx1
  obtain ⟨f, u, v, hfK, huv, hfM⟩ := geometric_hahn_banach_compact_closed
    convex_mixedStrategies isCompact_mixedStrategies M.convex
    (Submodule.isClosed_of_finiteDimensional M) hdisj
  have hv : v < 0 := by simpa using hfM 0 M.zero_mem
  have hfL : ∀ θ, f (L θ) = 0 := by
    intro θ
    by_contra hne
    have hmem : L (((v - 1) / f (L θ)) • θ) ∈ (M : Set (Option S → ℝ)) := ⟨_, rfl⟩
    have := hfM _ hmem
    rw [map_smul, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
    linarith
  set e : Option S → ℝ := fun o => f (fun j => if o = j then 1 else 0) with he
  have hfe : ∀ x : Option S → ℝ, f x = ∑ o, x o * e o := fun x => by
    simpa [he] using LinearMap.pi_apply_eq_sum_univ (f : (Option S → ℝ) →ₗ[ℝ] ℝ) x
  have heneg : ∀ o, e o < 0 := by
    intro o
    have hmem : (fun j => if o = j then (1 : ℝ) else 0) ∈ mixedStrategies (Option S) :=
      ⟨fun j => by dsimp only; split_ifs <;> norm_num, by simp⟩
    have := hfK _ hmem
    simp only [he]
    linarith
  refine ⟨fun s => e (some s) / e none, fun s => div_pos_of_neg_of_neg (heneg _) (heneg _),
    fun i => ?_⟩
  have key := hfL (Pi.single i 1)
  rw [hfe, Fintype.sum_option] at key
  simp only [hL, outcome, LinearMap.coe_mk, AddHom.coe_mk, Option.elim, cost, payoff,
    Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at key
  have hne : e none ≠ 0 := (heneg none).ne
  have : π i * e none = ∑ s, D i s * e (some s) := by linarith
  rw [eq_comm, ← div_eq_iff hne, Finset.sum_div] at this
  rw [← this]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **Fundamental theorem of asset pricing** (one period, finitely many states): there is no
arbitrage if and only if there are strictly positive state prices. -/
theorem noArbitrage_iff_exists_isStatePrice (π : ι → ℝ) (D : ι → S → ℝ) :
    NoArbitrage π D ↔ ∃ q, IsStatePrice π D q :=
  ⟨exists_isStatePrice_of_noArbitrage, fun ⟨_, hq⟩ => noArbitrage_of_isStatePrice hq⟩

end Applied.Economics.AssetPricing
