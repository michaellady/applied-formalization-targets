import Applied.InformationTheory.Gibbs
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen

/-!
# Fano's inequality for finite alphabets

All logarithms are natural, so entropies are in nats.

* `entropy_le_binEntropy_add`: for a probability vector `p` on a finite type `X` and a guess
  `x₀`, with `e = 1 - p x₀` the probability that the guess is wrong,
  `H(p) ≤ h(e) + e log (|X| - 1)`.
* `condEntropy`: for a joint probability mass function `P : X → Y → ℝ`, the conditional entropy
  `H(X | Y) = ∑ P(x, y) log (P_Y(y) / P(x, y))`.
* `errorProb`: the probability `∑_{x ≠ g y} P(x, y)` that the estimator `g : Y → X` is wrong.
* `fano_inequality`: `H(X | Y) ≤ h(Pₑ) + Pₑ log (|X| - 1)`.
-/

open Finset Real

namespace Applied.InformationTheory

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]

/-- **Fano's inequality for a single distribution.** If `p` is a probability vector on a finite
type `X` and `x₀ : X`, then with `e = 1 - p x₀`,
`H(p) ≤ h(e) + e log (|X| - 1)`, where `h` is the binary entropy. -/
theorem entropy_le_binEntropy_add (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (x₀ : X) :
    ∑ x, negMulLog (p x)
      ≤ binEntropy (1 - p x₀) + (1 - p x₀) * log ((Fintype.card X : ℝ) - 1) := by
  have hsplit : ∀ f : X → ℝ, ∑ x, f x = f x₀ + ∑ x ∈ univ.erase x₀, f x := fun f =>
    (Finset.add_sum_erase univ f (mem_univ x₀)).symm
  have he : ∑ x ∈ univ.erase x₀, p x = 1 - p x₀ := by
    have := hsplit p; linarith
  have hcard : ((univ.erase x₀).card : ℝ) = (Fintype.card X : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ x₀), Finset.card_univ,
      Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨x₀⟩), Nat.cast_one]
  have h := sum_negMulLog_le (univ.erase x₀) p fun x _ => hp x
  rw [he, hcard] at h
  rw [hsplit fun x => negMulLog (p x), binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    sub_sub_cancel]
  linarith

/-- Conditional entropy `H(X | Y) = ∑_{x, y} P(x, y) log (P_Y(y) / P(x, y))` of a joint
probability mass function `P` on `X × Y`, in nats. Terms with `P(x, y) = 0` vanish. -/
noncomputable def condEntropy (P : X → Y → ℝ) : ℝ :=
  ∑ y, ∑ x, P x y * log ((∑ x', P x' y) / P x y)

/-- The probability that the estimator `g : Y → X` is wrong: `∑_{x ≠ g y} P(x, y)`. -/
noncomputable def errorProb (P : X → Y → ℝ) (g : Y → X) : ℝ :=
  ∑ y, ∑ x ∈ univ.erase (g y), P x y

/-- Fano's inequality for one value of `y`, before averaging. -/
private lemma fano_fiber (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x₀ : X) :
    ∑ x, w x * log ((∑ x', w x') / w x)
      ≤ (∑ x, w x) * binEntropy ((∑ x ∈ univ.erase x₀, w x) / ∑ x, w x)
        + (∑ x ∈ univ.erase x₀, w x) * log ((Fintype.card X : ℝ) - 1) := by
  set s := ∑ x, w x with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun x _ => hw x
  have herase : ∑ x ∈ univ.erase x₀, w x = s - w x₀ := by
    have := Finset.add_sum_erase univ w (mem_univ x₀); linarith
  rcases hs0.eq_or_lt with hz | hpos
  · have hzero : ∀ x, w x = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hw x).mp hz.symm x (mem_univ x)
    simp [hzero]
  have h := entropy_le_binEntropy_add (fun x => w x / s) (fun x => div_nonneg (hw x) hs0)
    (by rw [← Finset.sum_div, ← hs, div_self hpos.ne']) x₀
  have h1 : 1 - w x₀ / s = (s - w x₀) / s := by field_simp
  have h2 : ∑ x, w x * log (s / w x) = s * ∑ x, negMulLog (w x / s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : log (s / w x) = -log (w x / s) := by rw [← log_inv, inv_div]
    rw [this, negMulLog]; field_simp
  rw [h1] at h
  rw [h2, herase]
  have h3 := mul_le_mul_of_nonneg_left h hs0
  have h4 : s * ((s - w x₀) / s * log ((Fintype.card X : ℝ) - 1))
      = (s - w x₀) * log ((Fintype.card X : ℝ) - 1) := by field_simp
  rw [mul_add, h4] at h3
  exact h3

/-- **Fano's inequality.** Let `P` be a joint probability mass function on `X × Y` (`X`, `Y`
finite) and `g : Y → X` any estimator of `X` from `Y`, with error probability
`Pₑ = P(X ≠ g(Y))`. Then `H(X | Y) ≤ h(Pₑ) + Pₑ log (|X| - 1)`, where `h` is the binary
entropy; all entropies in nats. -/
theorem fano_inequality (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hsum : ∑ y, ∑ x, P x y = 1)
    (g : Y → X) :
    condEntropy P ≤ binEntropy (errorProb P g)
      + errorProb P g * log ((Fintype.card X : ℝ) - 1) := by
  set s : Y → ℝ := fun y => ∑ x, P x y with hs
  set e : Y → ℝ := fun y => ∑ x ∈ univ.erase (g y), P x y with he
  have hs0 : ∀ y, 0 ≤ s y := fun y => Finset.sum_nonneg fun x _ => hP x y
  have he0 : ∀ y, 0 ≤ e y := fun y => Finset.sum_nonneg fun x _ => hP x y
  have hes : ∀ y, e y ≤ s y := fun y =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun x _ _ => hP x y
  -- fibrewise bound
  have hfib : condEntropy P
      ≤ ∑ y, (s y * binEntropy (e y / s y) + e y * log ((Fintype.card X : ℝ) - 1)) :=
    Finset.sum_le_sum fun y _ => fano_fiber (fun x => P x y) (fun x => hP x y) (g y)
  -- Jensen for the concave binary entropy
  have hjen := strictConcave_binEntropy.concaveOn.le_map_sum (t := univ) (w := s)
    (p := fun y => e y / s y) (fun y _ => hs0 y) hsum
    (fun y _ => ⟨div_nonneg (he0 y) (hs0 y), div_le_one_of_le₀ (hes y) (hs0 y)⟩)
  have hmean : ∑ y, s y • (e y / s y) = errorProb P g := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_eq_mul]
    by_cases h : s y = 0
    · have : e y = 0 := le_antisymm (h ▸ hes y) (he0 y)
      rw [h, zero_mul]; exact this.symm
    · rw [mul_div_cancel₀ _ h]
  rw [hmean] at hjen
  simp only [smul_eq_mul] at hjen
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hfib
  exact hfib.trans (add_le_add hjen le_rfl)

end Applied.InformationTheory
