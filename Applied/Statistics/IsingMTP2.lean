import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Total positivity of sums over sign patterns (a Griffiths–Ginibre inequality)

For a real matrix `M` and `w : ι → ℝ` let

`signSum M w = ∑ over σ ∈ {±1}^ι of exp (∑ i, ∑ j, M i j * (σ i * w i) * (σ j * w j))`.

Up to a constant this is the density at `w` of the vector of absolute values `(|Z i|)` of a
centred normal vector `Z` with precision matrix `-2 M`, and it is the partition function of an
Ising model with couplings `M i j * w i * w j`.

* `signSum_mul_le`: if all entries of `M` are non-negative then on the non-negative orthant
  `signSum M x * signSum M y ≤ signSum M (x ⊔ y) * signSum M (x ⊓ y)`, i.e. `signSum M` is
  multivariate totally positive of order two (MTP2).
* `signSum_mtp2`: the same when the off-diagonal entries become non-negative after a change of
  signs `M i j ↦ M i j * d i * d j`, `d i = ± 1` (the condition of Karlin and Rinott); the
  diagonal is arbitrary.

This is the "if" part of Karlin and Rinott (1981), *Total positivity properties of absolute value
multinormal variables with applications to confidence interval estimates and related
probabilistic inequalities*, Ann. Statist. 9, Theorem 3.1 (statement to be confirmed). The proof
here is by Ginibre's duplicate-variable method (Ginibre 1970, as for the Griffiths–Kelly–Sherman
inequalities): with two copies `σ, τ` of the signs and the rotated variables
`p i = σ i u i + τ i v i`, `q i = σ i u i - τ i v i` (`u = x ⊔ y ≥ v = x ⊓ y ≥ 0`), the difference
of the two sides is a limit of sums of products of the `p i`, `q i` with non-negative
coefficients, and the sum over signs of any such product is non-negative.
-/

open Finset Filter
open scoped Topology Nat

namespace Applied.Probability

/-- The sign `±1` coded by a Boolean: `true ↦ -1`, `false ↦ 1`. -/
def sg (b : Bool) : ℝ := if b then -1 else 1

/-- `true` codes the sign `-1`. -/
@[simp] lemma sg_true : sg true = -1 := by simp [sg]

/-- `false` codes the sign `+1`. -/
@[simp] lemma sg_false : sg false = 1 := by simp [sg]

/-- A sign squares to one. -/
lemma sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp

/-- Multiplying signs corresponds to `xor` of their codes. -/
lemma sg_xor (a b : Bool) : sg (xor a b) = sg a * sg b := by cases a <;> cases b <;> simp

/-- A sign has absolute value one. -/
lemma abs_sg (b : Bool) : |sg b| = 1 := by cases b <;> simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∑ over sign patterns σ of exp (∑ i j, M i j * (σ i * w i) * (σ j * w j))`. -/
noncomputable def signSum (M : ι → ι → ℝ) (w : ι → ℝ) : ℝ :=
  ∑ σ : ι → Bool, Real.exp (∑ i, ∑ j, M i j * (sg (σ i) * w i) * (sg (σ j) * w j))

/-- The sign sum is a sum of exponentials, hence positive. -/
lemma signSum_pos (M : ι → ι → ℝ) (w : ι → ℝ) : 0 < signSum M w :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

section Ginibre

/-- For `a, b ≥ 0`:
`(-a) ^ m * (-b) ^ n + (-b) ^ m * (-a) ^ n + b ^ m * a ^ n + a ^ m * b ^ n ≥ 0`
(the two negative-sign terms are cancelled by the two positive ones when `m + n` is odd). -/
lemma four_term_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (m n : ℕ) :
    0 ≤ (-a) ^ m * (-b) ^ n + (-b) ^ m * (-a) ^ n + (b ^ m * a ^ n + a ^ m * b ^ n) := by
  have hX : 0 ≤ a ^ m * b ^ n := mul_nonneg (pow_nonneg ha m) (pow_nonneg hb n)
  have hY : 0 ≤ b ^ m * a ^ n := mul_nonneg (pow_nonneg hb m) (pow_nonneg ha n)
  rw [neg_pow a, neg_pow b, neg_pow a, neg_pow b]
  rcases neg_one_pow_eq_or ℝ m with hm | hm <;> rcases neg_one_pow_eq_or ℝ n with hn | hn <;>
    rw [hm, hn] <;> nlinarith

/-- Sum over the two signs at one site of a product of powers of the rotated variables. -/
lemma sum_site_nonneg {u v : ℝ} (hv : 0 ≤ v) (huv : v ≤ u) (m n : ℕ) :
    0 ≤ ∑ ab : Bool × Bool,
      (sg ab.1 * u + sg ab.2 * v) ^ m * (sg ab.1 * u - sg ab.2 * v) ^ n := by
  have e : (∑ ab : Bool × Bool,
      (sg ab.1 * u + sg ab.2 * v) ^ m * (sg ab.1 * u - sg ab.2 * v) ^ n) =
      (-(u + v)) ^ m * (-(u - v)) ^ n + (-(u - v)) ^ m * (-(u + v)) ^ n +
        ((u - v) ^ m * (u + v) ^ n + (u + v) ^ m * (u - v) ^ n) := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, sg_true, sg_false]
    have h1 : (-1 * u + -1 * v) = -(u + v) := by ring
    have h2 : (-1 * u - -1 * v) = -(u - v) := by ring
    have h3 : (-1 * u + 1 * v) = -(u - v) := by ring
    have h4 : (-1 * u - 1 * v) = -(u + v) := by ring
    have h5 : (1 * u + -1 * v) = u - v := by ring
    have h6 : (1 * u - -1 * v) = u + v := by ring
    have h7 : (1 * u + 1 * v) = u + v := by ring
    have h8 : (1 * u - 1 * v) = u - v := by ring
    rw [h1, h2, h3, h4, h5, h6, h7, h8]
  rw [e]
  exact four_term_nonneg (by linarith) (by linarith) m n

/-- Rotated variable `p i = σ i u i + τ i v i` on configurations `ω = (σ, τ)`. -/
def pF (u v : ι → ℝ) (i : ι) : (ι → Bool × Bool) → ℝ :=
  fun ω => sg (ω i).1 * u i + sg (ω i).2 * v i

/-- Rotated variable `q i = σ i u i - τ i v i`. -/
def qF (u v : ι → ℝ) (i : ι) : (ι → Bool × Bool) → ℝ :=
  fun ω => sg (ω i).1 * u i - sg (ω i).2 * v i

/-- The cone generated by non-negative constants and the rotated variables. -/
def ginibreCone (u v : ι → ℝ) : Subsemiring ((ι → Bool × Bool) → ℝ) :=
  Subsemiring.closure
    ({F | ∃ c : ℝ, 0 ≤ c ∧ F = fun _ => c} ∪ Set.range (pF u v) ∪ Set.range (qF u v))

omit [Fintype ι] [DecidableEq ι] in
/-- Non-negative constants lie in the cone. -/
lemma const_mem_ginibreCone (u v : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (fun _ => c) ∈ ginibreCone u v :=
  Subsemiring.subset_closure (Or.inl (Or.inl ⟨c, hc, rfl⟩))

omit [Fintype ι] [DecidableEq ι] in
/-- The rotated variables `p i` lie in the cone. -/
lemma pF_mem_ginibreCone (u v : ι → ℝ) (i : ι) : pF u v i ∈ ginibreCone u v :=
  Subsemiring.subset_closure (Or.inl (Or.inr ⟨i, rfl⟩))

omit [Fintype ι] [DecidableEq ι] in
/-- The rotated variables `q i` lie in the cone. -/
lemma qF_mem_ginibreCone (u v : ι → ℝ) (i : ι) : qF u v i ∈ ginibreCone u v :=
  Subsemiring.subset_closure (Or.inr ⟨i, rfl⟩)

/-- **Ginibre positivity.** For `u ≥ v ≥ 0`, the sum over all pairs of sign patterns of an
element of the cone is non-negative. -/
lemma sum_nonneg_of_mem_ginibreCone {u v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) (huv : ∀ i, v i ≤ u i)
    {F : (ι → Bool × Bool) → ℝ} (hF : F ∈ ginibreCone u v) : 0 ≤ ∑ ω, F ω := by
  rw [ginibreCone, Subsemiring.mem_closure_iff] at hF
  induction hF using AddSubmonoid.closure_induction with
  | mem F hF =>
    have hmono : ∃ c : ℝ, 0 ≤ c ∧ ∃ m n : ι → ℕ,
        F = fun ω => c * ∏ i, pF u v i ω ^ m i * qF u v i ω ^ n i := by
      induction hF using Submonoid.closure_induction with
      | mem G hG =>
        rcases hG with (⟨c, hc, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
        · exact ⟨c, hc, 0, 0, by simp⟩
        · refine ⟨1, zero_le_one, fun j => if i = j then 1 else 0, 0, ?_⟩
          funext ω
          simp
        · refine ⟨1, zero_le_one, 0, fun j => if i = j then 1 else 0, ?_⟩
          funext ω
          simp
      | one => exact ⟨1, zero_le_one, 0, 0, by funext ω; simp⟩
      | mul F G _ _ hF hG =>
        obtain ⟨c, hc, m, n, rfl⟩ := hF
        obtain ⟨c', hc', m', n', rfl⟩ := hG
        refine ⟨c * c', mul_nonneg hc hc', m + m', n + n', ?_⟩
        funext ω
        simp only [Pi.mul_apply, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
        ring
    obtain ⟨c, hc, m, n, rfl⟩ := hmono
    rw [← Finset.mul_sum]
    refine mul_nonneg hc ?_
    have hps := Finset.prod_univ_sum (fun _ : ι => (univ : Finset (Bool × Bool)))
      (fun i ab => (sg ab.1 * u i + sg ab.2 * v i) ^ m i * (sg ab.1 * u i - sg ab.2 * v i) ^ n i)
    rw [Fintype.piFinset_univ] at hps
    have hrw : (∑ ω : ι → Bool × Bool, ∏ i, pF u v i ω ^ m i * qF u v i ω ^ n i)
        = ∏ i, ∑ ab : Bool × Bool,
          (sg ab.1 * u i + sg ab.2 * v i) ^ m i * (sg ab.1 * u i - sg ab.2 * v i) ^ n i :=
      hps.symm
    rw [hrw]
    exact Finset.prod_nonneg fun i _ => sum_site_nonneg (hv i) (huv i) (m i) (n i)
  | zero => simp
  | add F G _ _ hF hG =>
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    exact add_nonneg hF hG

end Ginibre

section Main

/-- Product of two sign sums as one sum over pairs of sign patterns. -/
lemma sum_mul_sum_config (f g : (ι → Bool) → ℝ) :
    (∑ σ, f σ) * (∑ τ, g τ) =
      ∑ ω : ι → Bool × Bool, f (fun i => (ω i).1) * g (fun i => (ω i).2) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  exact ((Equiv.arrowProdEquivProdArrow ι (fun _ => Bool) (fun _ => Bool)).sum_comp
    (fun p : (ι → Bool) × (ι → Bool) => f p.1 * g p.2)).symm

/-- The exponential series of a real number. -/
lemma hasSum_exp_real (a : ℝ) : HasSum (fun n : ℕ => a ^ n / (n ! : ℝ)) (Real.exp a) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp a

/-- `1 - (-1) ^ m` is `0` or `2`, hence non-negative. -/
lemma one_sub_neg_one_pow_nonneg (m : ℕ) : (0 : ℝ) ≤ 1 - (-1) ^ m := by
  rcases neg_one_pow_eq_or ℝ m with h | h <;> rw [h] <;> norm_num

set_option linter.unusedSimpArgs false in
/-- **Ginibre's inequality for the sign sum.** If all entries of `M` are non-negative, then on
the non-negative orthant `signSum M` is multivariate totally positive of order two. -/
theorem signSum_mul_le (M : ι → ι → ℝ) (hM : ∀ i j, 0 ≤ M i j) {x y : ι → ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    signSum M x * signSum M y ≤ signSum M (x ⊔ y) * signSum M (x ⊓ y) := by
  classical
  set u : ι → ℝ := x ⊔ y with hu
  set v : ι → ℝ := x ⊓ y with hv
  have hv0 : ∀ i, 0 ≤ v i := fun i => le_inf (hx i) (hy i)
  have hvu : ∀ i, v i ≤ u i := fun i => inf_le_left.trans le_sup_left
  let S : ι → Prop := fun i => y i ≤ x i
  have hS : ∀ i, S i → x i = u i ∧ y i = v i := fun i h =>
    ⟨(sup_of_le_left h).symm, (inf_of_le_right h).symm⟩
  have hS' : ∀ i, ¬ S i → x i = v i ∧ y i = u i := fun i h =>
    ⟨(inf_of_le_left (le_of_not_ge h)).symm, (sup_of_le_right (le_of_not_ge h)).symm⟩
  let Q : (ι → ℝ) → (ι → Bool) → ℝ := fun w σ =>
    ∑ i, ∑ j, M i j * (sg (σ i) * w i) * (sg (σ j) * w j)
  have hprod : ∀ a b : ι → ℝ, signSum M a * signSum M b =
      ∑ ω : ι → Bool × Bool,
        Real.exp (Q a (fun i => (ω i).1) + Q b (fun i => (ω i).2)) := by
    intro a b
    simp only [signSum]
    rw [sum_mul_sum_config]
    exact Finset.sum_congr rfl fun ω _ => (Real.exp_add _ _).symm
  -- swap the two copies on the sites where `x < y`
  let Φ : Equiv.Perm (ι → Bool × Bool) := Function.Involutive.toPerm
    (fun ω i => if S i then ω i else (ω i).swap) (fun ω => by
      funext i
      by_cases h : S i <;> simp [h])
  have hΦ : ∀ ω i, Φ ω i = if S i then ω i else (ω i).swap := fun ω i => rfl
  -- the two exponents
  set A : (ι → Bool × Bool) → ℝ := ∑ i, ∑ j, (fun _ => M i j / 2) *
    (pF u v i * pF u v j + if (S i ↔ S j) then qF u v i * qF u v j else 0) with hA
  set B : (ι → Bool × Bool) → ℝ := ∑ i, ∑ j, (fun _ => M i j / 2) *
    (if (S i ↔ S j) then 0 else qF u v i * qF u v j) with hB
  have hAmem : A ∈ ginibreCone u v := by
    refine Subsemiring.sum_mem _ fun i _ => Subsemiring.sum_mem _ fun j _ => ?_
    refine Subsemiring.mul_mem _ (const_mem_ginibreCone u v (div_nonneg (hM i j) (by norm_num)))
      (Subsemiring.add_mem _ (Subsemiring.mul_mem _ (pF_mem_ginibreCone u v i)
        (pF_mem_ginibreCone u v j)) ?_)
    split_ifs
    · exact Subsemiring.mul_mem _ (qF_mem_ginibreCone u v i) (qF_mem_ginibreCone u v j)
    · exact Subsemiring.zero_mem _
  have hBmem : B ∈ ginibreCone u v := by
    refine Subsemiring.sum_mem _ fun i _ => Subsemiring.sum_mem _ fun j _ => ?_
    refine Subsemiring.mul_mem _ (const_mem_ginibreCone u v (div_nonneg (hM i j) (by norm_num)))
      ?_
    split_ifs
    · exact Subsemiring.zero_mem _
    · exact Subsemiring.mul_mem _ (qF_mem_ginibreCone u v i) (qF_mem_ginibreCone u v j)
  have hAω : ∀ ω, A ω = ∑ i, ∑ j, M i j / 2 *
      (pF u v i ω * pF u v j ω + if (S i ↔ S j) then qF u v i ω * qF u v j ω else 0) := by
    intro ω
    simp only [hA, Finset.sum_apply, Pi.mul_apply, Pi.add_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hBω : ∀ ω, B ω = ∑ i, ∑ j, M i j / 2 *
      (if (S i ↔ S j) then 0 else qF u v i ω * qF u v j ω) := by
    intro ω
    simp only [hB, Finset.sum_apply, Pi.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hE1 : ∀ ω : ι → Bool × Bool,
      Q u (fun i => (ω i).1) + Q v (fun i => (ω i).2) = A ω + B ω := by
    intro ω
    rw [hAω, hBω]
    simp only [Q, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : (S i ↔ S j) <;> simp only [h, ite_true, ite_false, pF, qF] <;> ring
  have hE2 : ∀ ω : ι → Bool × Bool,
      Q x (fun i => (Φ ω i).1) + Q y (fun i => (Φ ω i).2) = A ω - B ω := by
    intro ω
    have hAi : ∀ i, sg (Φ ω i).1 * x i = if S i then sg (ω i).1 * u i else sg (ω i).2 * v i := by
      intro i
      by_cases h : S i
      · simp [hΦ, h, (hS i h).1]
      · simp [hΦ, h, (hS' i h).1]
    have hBi : ∀ i, sg (Φ ω i).2 * y i = if S i then sg (ω i).2 * v i else sg (ω i).1 * u i := by
      intro i
      by_cases h : S i
      · simp [hΦ, h, (hS i h).2]
      · simp [hΦ, h, (hS' i h).2]
    rw [hAω, hBω]
    simp only [Q, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, hAi, hBi]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hi : S i <;> by_cases hj : S j <;>
      simp only [hi, hj, ite_true, ite_false, pF, qF, iff_true, iff_false, not_true_eq_false,
        not_false_eq_true, true_iff, false_iff] <;> ring
  have hxy : signSum M x * signSum M y = ∑ ω, Real.exp (A ω - B ω) := by
    rw [hprod x y, ← Equiv.sum_comp Φ]
    exact Finset.sum_congr rfl fun ω _ => by rw [hE2 ω]
  have huv : signSum M u * signSum M v = ∑ ω, Real.exp (A ω + B ω) := by
    rw [hprod u v]
    exact Finset.sum_congr rfl fun ω _ => by rw [hE1 ω]
  rw [hxy, huv, ← sub_nonneg, ← Finset.sum_sub_distrib]
  have hlim : Tendsto (fun N : ℕ => ∑ ω : ι → Bool × Bool, ∑ n ∈ range N,
      ((A ω + B ω) ^ n / (n ! : ℝ) - (A ω - B ω) ^ n / (n ! : ℝ))) atTop
      (𝓝 (∑ ω, (Real.exp (A ω + B ω) - Real.exp (A ω - B ω)))) :=
    tendsto_finsetSum _ fun ω _ =>
      ((hasSum_exp_real (A ω + B ω)).sub (hasSum_exp_real (A ω - B ω))).tendsto_sum_nat
  refine ge_of_tendsto' hlim fun N => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun n _ => ?_
  have hpt : ∀ ω, (A ω + B ω) ^ n / (n ! : ℝ) - (A ω - B ω) ^ n / (n ! : ℝ) =
      ∑ k ∈ range (n + 1), ((1 - (-1) ^ (n - k)) * (n.choose k) / (n ! : ℝ)) *
        (A ^ k * B ^ (n - k)) ω := by
    intro ω
    rw [← sub_div, sub_eq_add_neg (A ω) (B ω), add_pow, add_pow, ← Finset.sum_sub_distrib,
      div_eq_inv_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_pow (B ω)]
    simp only [Pi.mul_apply, Pi.pow_apply]
    ring
  simp_rw [hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [← Finset.mul_sum]
  exact mul_nonneg (div_nonneg (mul_nonneg (one_sub_neg_one_pow_nonneg _) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _))
    (sum_nonneg_of_mem_ginibreCone hv0 hvu
      (Subsemiring.mul_mem _ (Subsemiring.pow_mem _ hAmem k) (Subsemiring.pow_mem _ hBmem _)))

/-- Changing the signs of the matrix, `M i j ↦ M i j * d i * d j`, does not change the sign
sum. -/
lemma signSum_signChange (M : ι → ι → ℝ) (d : ι → Bool) (w : ι → ℝ) :
    signSum (fun i j => M i j * sg (d i) * sg (d j)) w = signSum M w := by
  let e : Equiv.Perm (ι → Bool) := Function.Involutive.toPerm
    (fun σ i => xor (σ i) (d i)) (fun σ => by funext i; simp)
  let g : (ι → Bool) → ℝ := fun σ =>
    Real.exp (∑ i, ∑ j, M i j * (sg (σ i) * w i) * (sg (σ j) * w j))
  have h1 : signSum (fun i j => M i j * sg (d i) * sg (d j)) w = ∑ σ, g (e σ) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [g]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have he : ∀ k, e σ k = xor (σ k) (d k) := fun k => rfl
    rw [he, he, sg_xor, sg_xor]
    ring
  rw [h1]
  exact Equiv.sum_comp e g

/-- The diagonal of the matrix contributes a product factor. -/
lemma signSum_diag (M : ι → ι → ℝ) (w : ι → ℝ) :
    signSum M w = Real.exp (∑ i, M i i * w i ^ 2) *
      signSum (fun i j => if i = j then 0 else M i j) w := by
  simp only [signSum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Real.exp_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : M i i * w i ^ 2 =
      ∑ j, if i = j then M i j * (sg (σ i) * w i) * (sg (σ j) * w j) else 0 := by
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    have := sg_mul_self (σ i)
    calc M i i * w i ^ 2 = M i i * (sg (σ i) * sg (σ i)) * w i ^ 2 := by rw [this]; ring
      _ = _ := by ring
  rw [hd, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **Total positivity of the sign sum under the Karlin–Rinott sign condition.** If the
off-diagonal entries of `M` become non-negative after a change of signs
(`0 ≤ M i j * d i * d j` for `i ≠ j`, `d i = ± 1` coded by Booleans; the diagonal of `M` is
arbitrary), then for `x, y ≥ 0`:
`signSum M x * signSum M y ≤ signSum M (x ⊔ y) * signSum M (x ⊓ y)`. -/
theorem signSum_mtp2 (M : ι → ι → ℝ) (d : ι → Bool)
    (hM : ∀ i j, i ≠ j → 0 ≤ M i j * sg (d i) * sg (d j)) {x y : ι → ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    signSum M x * signSum M y ≤ signSum M (x ⊔ y) * signSum M (x ⊓ y) := by
  set M' : ι → ι → ℝ := fun i j => if i = j then 0 else M i j * sg (d i) * sg (d j) with hM'
  have key : ∀ w : ι → ℝ, signSum M w = Real.exp (∑ i, M i i * w i ^ 2) * signSum M' w := by
    intro w
    rw [← signSum_signChange M d w, signSum_diag]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc (M i i), sg_mul_self, mul_one]
  have hdiag : (∑ i, M i i * x i ^ 2) + ∑ i, M i i * y i ^ 2 =
      (∑ i, M i i * (x ⊔ y) i ^ 2) + ∑ i, M i i * (x ⊓ y) i ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total (x i) (y i) with h | h
    · rw [Pi.sup_apply, Pi.inf_apply, sup_of_le_right h, inf_of_le_left h]; ring
    · rw [Pi.sup_apply, Pi.inf_apply, sup_of_le_left h, inf_of_le_right h]
  have hG := signSum_mul_le M' (fun i j => by
    simp only [hM']
    split_ifs with h
    · exact le_rfl
    · exact hM i j h) hx hy
  rw [key x, key y, key (x ⊔ y), key (x ⊓ y)]
  calc Real.exp (∑ i, M i i * x i ^ 2) * signSum M' x *
        (Real.exp (∑ i, M i i * y i ^ 2) * signSum M' y)
      = Real.exp ((∑ i, M i i * x i ^ 2) + ∑ i, M i i * y i ^ 2) *
        (signSum M' x * signSum M' y) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp ((∑ i, M i i * x i ^ 2) + ∑ i, M i i * y i ^ 2) *
        (signSum M' (x ⊔ y) * signSum M' (x ⊓ y)) :=
        mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le
    _ = _ := by rw [hdiag, Real.exp_add]; ring

end Main

end Applied.Probability
