import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Compressed sensing: the null space property and exact recovery by ℓ¹ minimisation

Vectors are functions `ι → ℝ` on a finite index type; the measurement map is a linear map
`A : (ι → ℝ) →ₗ[ℝ] F` (for a matrix, `Matrix.mulVecLin`). The ℓ¹ norm is written out as
`∑ i, |x i|` and the squared ℓ² norm as `∑ i, x i ^ 2`.

* `IsSparse s x`: `x` has at most `s` nonzero entries.
* `NullSpaceProperty A s`: for every nonzero `v` with `A v = 0` and every index set `S` with at
  most `s` elements, `∑_{i ∈ S} |v i| < ∑_{i ∉ S} |v i|`.
* `ExactRecovery A s`: every `s`-sparse `x` is the unique minimiser of the ℓ¹ norm among all `z`
  with `A z = A x`.
* `nullSpaceProperty_iff_exactRecovery`: the two are equivalent.
* `RestrictedIsometry A k δ`: `(1 - δ) ‖x‖₂² ≤ ‖A x‖² ≤ (1 + δ) ‖x‖₂²` for all `k`-sparse `x`.
* `RestrictedIsometry.nullSpaceProperty`: the restricted isometry property of order `2 s` with
  constant `δ < 1/3` implies the null space property of order `s`.
* `RestrictedIsometry.exactRecovery`: hence exact recovery of `s`-sparse vectors.
* `Matrix` versions: `Matrix.nullSpaceProperty_iff_exactRecovery`,
  `Matrix.exactRecovery_of_restrictedIsometry`.

The constant `1/3` is the one given by the classical block argument (sort the entries of a
kernel vector, cut into blocks of size `s`); it is not the best known constant.
-/

open Finset
open scoped RealInnerProductSpace

namespace Applied.SignalProcessing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `x` has at most `s` nonzero entries. -/
def IsSparse (s : ℕ) (x : ι → ℝ) : Prop :=
  (univ.filter fun i => x i ≠ 0).card ≤ s

/-- The vector that agrees with `v` on `S` and vanishes elsewhere. -/
def restr (S : Finset ι) (v : ι → ℝ) : ι → ℝ := fun i => if i ∈ S then v i else 0

omit [Fintype ι] in
lemma restr_apply_of_mem {S : Finset ι} (v : ι → ℝ) {i : ι} (h : i ∈ S) : restr S v i = v i :=
  ite_eq_left h

omit [Fintype ι] in
lemma restr_apply_of_notMem {S : Finset ι} (v : ι → ℝ) {i : ι} (h : i ∉ S) : restr S v i = 0 :=
  ite_eq_right h

omit [Fintype ι] in
@[simp] lemma restr_empty (v : ι → ℝ) : restr ∅ v = 0 := by
  funext i; simp [restr]

/-- A vector vanishing off a set with at most `s` elements is `s`-sparse. -/
lemma isSparse_of_support_subset {s : ℕ} {x : ι → ℝ} (S : Finset ι) (hS : S.card ≤ s)
    (hx : ∀ i, i ∉ S → x i = 0) : IsSparse s x := by
  refine le_trans (card_le_card ?_) hS
  intro i hi
  rw [mem_filter] at hi
  by_contra h
  exact hi.2 (hx i h)

omit [DecidableEq ι] in
lemma sum_abs_pos_of_ne_zero {v : ι → ℝ} (hv : v ≠ 0) : 0 < ∑ i, |v i| := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  exact lt_of_lt_of_le (abs_pos.mpr hi)
    (single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg _) (mem_univ i))

section NSP

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- The **null space property** of order `s`: every nonzero vector of the kernel of `A` has
strictly less ℓ¹ mass on any set of at most `s` indices than on its complement. -/
def NullSpaceProperty (A : (ι → ℝ) →ₗ[ℝ] F) (s : ℕ) : Prop :=
  ∀ v : ι → ℝ, A v = 0 → v ≠ 0 → ∀ S : Finset ι, S.card ≤ s →
    ∑ i ∈ S, |v i| < ∑ i ∈ Sᶜ, |v i|

/-- **Exact recovery by ℓ¹ minimisation** for `s`-sparse vectors: every `s`-sparse `x` has
strictly smaller ℓ¹ norm than any other `z` with the same measurements `A z = A x`. -/
def ExactRecovery (A : (ι → ℝ) →ₗ[ℝ] F) (s : ℕ) : Prop :=
  ∀ x : ι → ℝ, IsSparse s x → ∀ z : ι → ℝ, A z = A x → z ≠ x → ∑ i, |x i| < ∑ i, |z i|

/-- **The null space property is equivalent to exact recovery by ℓ¹ minimisation.** -/
theorem nullSpaceProperty_iff_exactRecovery (A : (ι → ℝ) →ₗ[ℝ] F) (s : ℕ) :
    NullSpaceProperty A s ↔ ExactRecovery A s := by
  constructor
  · intro h x hx z hz hne
    set S : Finset ι := univ.filter fun i => x i ≠ 0 with hS
    have hx0 : ∀ i ∈ Sᶜ, x i = 0 := by
      intro i hi
      rw [mem_compl, hS, mem_filter] at hi
      by_contra h0
      exact hi ⟨mem_univ i, h0⟩
    have hv : A (z - x) = 0 := by rw [map_sub, hz, sub_self]
    have hv0 : z - x ≠ 0 := sub_ne_zero.mpr hne
    have key := h (z - x) hv hv0 S hx
    have e1 : ∑ i ∈ Sᶜ, |(z - x) i| = ∑ i ∈ Sᶜ, |z i| :=
      sum_congr rfl fun i hi => by rw [Pi.sub_apply, hx0 i hi, sub_zero]
    have e2 : ∑ i ∈ Sᶜ, |x i| = 0 :=
      sum_eq_zero fun i hi => by rw [hx0 i hi, abs_zero]
    have e3 : ∑ i ∈ S, |x i| ≤ ∑ i ∈ S, |(z - x) i| + ∑ i ∈ S, |z i| := by
      rw [← sum_add_distrib]
      refine sum_le_sum fun i _ => ?_
      have := abs_sub_le (x i) (z i) 0
      rw [Pi.sub_apply, abs_sub_comm (z i) (x i)]
      simpa using this
    have ex := sum_add_sum_compl S fun i => |x i|
    have ez := sum_add_sum_compl S fun i => |z i|
    linarith
  · intro h v hv hv0 S hS
    set x : ι → ℝ := restr S v with hx
    set z : ι → ℝ := fun i => if i ∈ S then 0 else -v i with hz
    have hxz : x - z = v := by
      funext i
      by_cases hi : i ∈ S <;> simp [hx, hz, restr, hi]
    have hA : A z = A x := by
      have : A x - A z = 0 := by rw [← map_sub, hxz, hv]
      exact (sub_eq_zero.mp this).symm
    have hne : z ≠ x := by
      intro e
      rw [e, sub_self] at hxz
      exact hv0 hxz.symm
    have hsp : IsSparse s x :=
      isSparse_of_support_subset S hS fun i hi => restr_apply_of_notMem v hi
    have key := h x hsp z hA hne
    have ex := sum_add_sum_compl S fun i => |x i|
    have ez := sum_add_sum_compl S fun i => |z i|
    have e1 : ∑ i ∈ S, |x i| = ∑ i ∈ S, |v i| :=
      sum_congr rfl fun i hi => by rw [hx, restr_apply_of_mem v hi]
    have e2 : ∑ i ∈ Sᶜ, |x i| = 0 :=
      sum_eq_zero fun i hi => by
        rw [hx, restr_apply_of_notMem v (mem_compl.mp hi), abs_zero]
    have e3 : ∑ i ∈ S, |z i| = 0 :=
      sum_eq_zero fun i hi => by simp [hz, hi]
    have e4 : ∑ i ∈ Sᶜ, |z i| = ∑ i ∈ Sᶜ, |v i| :=
      sum_congr rfl fun i hi => by simp [hz, mem_compl.mp hi]
    linarith

end NSP

/-! ### Choosing the largest entries -/

omit [Fintype ι] in
/-- A set of the `min s |T|` largest values of `a` on `T`. -/
lemma exists_top (a : ι → ℝ) (T : Finset ι) (s : ℕ) :
    ∃ T₁ ⊆ T, T₁.card = min s T.card ∧ ∀ i ∈ T₁, ∀ j ∈ T \ T₁, a j ≤ a i := by
  induction s with
  | zero => exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ s ih =>
    obtain ⟨T₁, hsub, hcard, htop⟩ := ih
    by_cases hne : (T \ T₁).Nonempty
    · obtain ⟨j, hj, hmax⟩ := exists_max_image (T \ T₁) a hne
      have hjT : j ∈ T := (mem_sdiff.mp hj).1
      have hjT₁ : j ∉ T₁ := (mem_sdiff.mp hj).2
      have hlt : T₁.card < T.card :=
        card_lt_card ⟨hsub, fun h => hjT₁ (h hjT)⟩
      refine ⟨insert j T₁, insert_subset hjT hsub, ?_, ?_⟩
      · rw [card_insert_of_notMem hjT₁, hcard]
        omega
      · intro i hi k hk
        rw [mem_sdiff, mem_insert, not_or] at hk
        have hk' : k ∈ T \ T₁ := mem_sdiff.mpr ⟨hk.1, hk.2.2⟩
        rcases mem_insert.mp hi with rfl | hi
        · exact hmax k hk'
        · exact htop i hi k hk'
    · rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at hne
      have hEq : T₁ = T := subset_antisymm hsub hne
      refine ⟨T₁, hsub, ?_, htop⟩
      rw [hEq] at hcard ⊢; omega

omit [Fintype ι] in
/-- If `T₁` consists of the `min s |T|` largest values of the nonnegative function `a` on `T`,
then the values off `T₁` are bounded by some `M ≥ 0` with `s · M ≤ ∑_{T₁} a`. -/
lemma exists_bound_of_top (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (T T₁ : Finset ι) (s : ℕ)
    (hs0 : 0 < s) (hsub : T₁ ⊆ T) (hcard : T₁.card = min s T.card)
    (htop : ∀ i ∈ T₁, ∀ j ∈ T \ T₁, a j ≤ a i) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ j ∈ T \ T₁, a j ≤ M) ∧ s * M ≤ ∑ i ∈ T₁, a i := by
  by_cases hne : (T \ T₁).Nonempty
  · obtain ⟨j, hj⟩ := hne
    have hlt : T₁.card < T.card :=
      card_lt_card ⟨hsub, fun h => (mem_sdiff.mp hj).2 (h (mem_sdiff.mp hj).1)⟩
    have hs : T₁.card = s := by omega
    have hT₁ : T₁.Nonempty := card_pos.mp (by omega)
    obtain ⟨m, hm, hmin⟩ := exists_min_image T₁ a hT₁
    refine ⟨a m, ha m, fun k hk => htop m hm k hk, ?_⟩
    have := card_nsmul_le_sum T₁ a (a m) hmin
    rw [hs, nsmul_eq_mul] at this
    exact this
  · rw [not_nonempty_iff_eq_empty] at hne
    exact ⟨0, le_rfl, fun j hj => by rw [hne] at hj; simp at hj,
      by simpa using sum_nonneg fun i _ => ha i⟩

omit [Fintype ι] in
/-- A set of at most `|T₁|` indices in `T` carries at most as much of the nonnegative function
`a` as the top set `T₁`. -/
lemma sum_le_sum_top (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (T T₁ S : Finset ι)
    (htop : ∀ i ∈ T₁, ∀ j ∈ T \ T₁, a j ≤ a i) (hS : S ⊆ T) (hcard : S.card ≤ T₁.card) :
    ∑ i ∈ S, a i ≤ ∑ i ∈ T₁, a i := by
  have h1 : ∑ i ∈ S \ T₁, a i + ∑ i ∈ S ∩ T₁, a i = ∑ i ∈ S, a i := by
    have := sum_sdiff (f := a) (inter_subset_left : S ∩ T₁ ⊆ S)
    rwa [sdiff_inter_self_left] at this
  have h2 : ∑ i ∈ T₁ \ S, a i + ∑ i ∈ S ∩ T₁, a i = ∑ i ∈ T₁, a i := by
    have := sum_sdiff (f := a) (inter_subset_right : S ∩ T₁ ⊆ T₁)
    rwa [inter_comm, sdiff_inter_self_left, inter_comm] at this
  have hc : (S \ T₁).card ≤ (T₁ \ S).card := by
    have e1 := card_sdiff_add_card_inter S T₁
    have e2 := card_sdiff_add_card_inter T₁ S
    rw [inter_comm T₁ S] at e2
    omega
  have key : ∑ i ∈ S \ T₁, a i ≤ ∑ i ∈ T₁ \ S, a i := by
    by_cases hne : (T₁ \ S).Nonempty
    · obtain ⟨m, hm, hmin⟩ := exists_min_image (T₁ \ S) a hne
      have hup : ∑ i ∈ S \ T₁, a i ≤ (S \ T₁).card • a m :=
        sum_le_card_nsmul _ _ _ fun j hj =>
          htop m (mem_sdiff.mp hm).1 j
            (mem_sdiff.mpr ⟨hS (mem_sdiff.mp hj).1, (mem_sdiff.mp hj).2⟩)
      have hlow : (T₁ \ S).card • a m ≤ ∑ i ∈ T₁ \ S, a i := card_nsmul_le_sum _ _ _ hmin
      have hmid : (S \ T₁).card • a m ≤ (T₁ \ S).card • a m := by
        rw [nsmul_eq_mul, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (ha m)
      linarith
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, card_empty, Nat.le_zero, card_eq_zero] at hc
      rw [hc, hne]
  linarith

/-! ### The restricted isometry property -/

section RIP

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The **restricted isometry property** of order `k` with constant `δ`: on `k`-sparse vectors
`A` distorts the squared Euclidean norm by a factor in `[1 - δ, 1 + δ]`. -/
def RestrictedIsometry (A : (ι → ℝ) →ₗ[ℝ] F) (k : ℕ) (δ : ℝ) : Prop :=
  ∀ x : ι → ℝ, IsSparse k x →
    (1 - δ) * ∑ i, x i ^ 2 ≤ ‖A x‖ ^ 2 ∧ ‖A x‖ ^ 2 ≤ (1 + δ) * ∑ i, x i ^ 2

/-- Under the restricted isometry property of order `2 s`, images of vectors supported on
disjoint sets of size at most `s` are almost orthogonal. -/
lemma RestrictedIsometry.abs_inner_le {A : (ι → ℝ) →ₗ[ℝ] F} {s : ℕ} {δ : ℝ}
    (hA : RestrictedIsometry A (2 * s) δ) (S T : Finset ι) (hS : S.card ≤ s) (hT : T.card ≤ s)
    (hST : Disjoint S T) (u v : ι → ℝ) (hu : ∀ i, i ∉ S → u i = 0) (hv : ∀ i, i ∉ T → v i = 0) :
    |⟪A u, A v⟫| ≤ δ * (√(∑ i, u i ^ 2) * √(∑ i, v i ^ 2)) := by
  set a := √(∑ i, u i ^ 2) with ha
  set b := √(∑ i, v i ^ 2) with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hsu : 0 ≤ ∑ i, u i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hsv : 0 ≤ ∑ i, v i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have ha2 : a ^ 2 = ∑ i, u i ^ 2 := Real.sq_sqrt hsu
  have hb2 : b ^ 2 = ∑ i, v i ^ 2 := Real.sq_sqrt hsv
  have huv : ∀ i, u i * v i = 0 := by
    intro i
    by_cases hi : i ∈ S
    · rw [hv i (disjoint_left.mp hST hi), mul_zero]
    · rw [hu i hi, zero_mul]
  -- sparsity and norm of combinations
  have hcomb : ∀ α β : ℝ, IsSparse (2 * s) (α • u + β • v) ∧
      ∑ i, (α • u + β • v) i ^ 2 = α ^ 2 * a ^ 2 + β ^ 2 * b ^ 2 := by
    intro α β
    constructor
    · refine isSparse_of_support_subset (S ∪ T) ((card_union_le S T).trans (by omega)) ?_
      intro i hi
      rw [mem_union, not_or] at hi
      simp [hu i hi.1, hv i hi.2]
    · rw [ha2, hb2, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := huv i
      linear_combination 2 * α * β * this
  obtain ⟨hs1, hn1⟩ := hcomb b a
  obtain ⟨hs2, hn2⟩ := hcomb b (-a)
  have r1 := hA _ hs1
  have r2 := hA _ hs2
  rw [hn1] at r1
  rw [hn2] at r2
  have e1 : ‖A (b • u + a • v)‖ ^ 2
      = b ^ 2 * ‖A u‖ ^ 2 + 2 * (a * b) * ⟪A u, A v⟫ + a ^ 2 * ‖A v‖ ^ 2 := by
    rw [map_add, map_smul, map_smul, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  have e2 : ‖A (b • u + (-a) • v)‖ ^ 2
      = b ^ 2 * ‖A u‖ ^ 2 - 2 * (a * b) * ⟪A u, A v⟫ + a ^ 2 * ‖A v‖ ^ 2 := by
    rw [map_add, map_smul, map_smul, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  rw [e1] at r1
  rw [e2] at r2
  rcases eq_or_lt_of_le ha0 with ha' | ha'
  · -- `u = 0`
    have hu0 : u = 0 := by
      funext i
      have : ∑ i, u i ^ 2 = 0 := by rw [← ha2, ← ha']; ring
      have := (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (u i)).mp this i (mem_univ i)
      simpa using this
    rw [hu0, map_zero, inner_zero_left, abs_zero, ← ha']
    simp
  rcases eq_or_lt_of_le hb0 with hb' | hb'
  · have hv0 : v = 0 := by
      funext i
      have : ∑ i, v i ^ 2 = 0 := by rw [← hb2, ← hb']; ring
      have := (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v i)).mp this i (mem_univ i)
      simpa using this
    rw [hv0, map_zero, inner_zero_right, abs_zero, ← hb']
    simp
  have hab : 0 < a * b := mul_pos ha' hb'
  rw [abs_le]
  constructor
  · have : a * b * (-(δ * (a * b))) ≤ a * b * ⟪A u, A v⟫ := by nlinarith [r1.1, r2.2]
    exact le_of_mul_le_mul_left this hab
  · have : a * b * ⟪A u, A v⟫ ≤ a * b * (δ * (a * b)) := by nlinarith [r1.2, r2.1]
    exact le_of_mul_le_mul_left this hab

omit [DecidableEq ι] in
/-- A restricted isometry constant of positive order on a nonempty index set is nonnegative. -/
lemma RestrictedIsometry.nonneg [Nonempty ι] {A : (ι → ℝ) →ₗ[ℝ] F} {k : ℕ} {δ : ℝ}
    (hA : RestrictedIsometry A k δ) (hk : 0 < k) : 0 ≤ δ := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hsp : IsSparse k (Pi.single i (1 : ℝ)) := by
    refine isSparse_of_support_subset {i} (by rw [card_singleton]; omega) fun j hj => ?_
    rw [mem_singleton] at hj
    simp [hj]
  have hsum : ∑ j, (Pi.single i (1 : ℝ) : ι → ℝ) j ^ 2 = 1 := by
    simp [Pi.single_apply]
  have := hA _ hsp
  rw [hsum] at this
  linarith [this.1, this.2]

lemma sum_restr_sq (S : Finset ι) (v : ι → ℝ) : ∑ i, restr S v i ^ 2 = ∑ i ∈ S, v i ^ 2 := by
  have h := sum_add_sum_compl S fun i => restr S v i ^ 2
  have e1 : ∑ i ∈ S, restr S v i ^ 2 = ∑ i ∈ S, v i ^ 2 :=
    sum_congr rfl fun i hi => by rw [restr_apply_of_mem v hi]
  have e2 : ∑ i ∈ Sᶜ, restr S v i ^ 2 = 0 :=
    sum_eq_zero fun i hi => by rw [restr_apply_of_notMem v (mem_compl.mp hi)]; ring
  linarith

omit [Fintype ι] in
lemma restr_union (S T : Finset ι) (hST : Disjoint S T) (v : ι → ℝ) :
    restr (S ∪ T) v = restr S v + restr T v := by
  funext i
  by_cases hS : i ∈ S
  · have hT : i ∉ T := disjoint_left.mp hST hS
    simp [restr, hS, hT]
  · by_cases hT : i ∈ T <;> simp [restr, hS, hT]

/-- The block estimate: the image of the part of `v` on `S₀` is almost orthogonal to the image
of the part of `v` on a disjoint set `T` all of whose entries are at most `M` in absolute
value. Proved by peeling off the `s` largest entries of `T` repeatedly. -/
lemma RestrictedIsometry.block_bound {A : (ι → ℝ) →ₗ[ℝ] F} {s : ℕ} {δ : ℝ}
    (hA : RestrictedIsometry A (2 * s) δ) (hδ : 0 ≤ δ) (hs : 0 < s) (v : ι → ℝ)
    (S₀ : Finset ι) (hS₀ : S₀.card ≤ s) :
    ∀ (n : ℕ) (T : Finset ι), T.card = n → Disjoint S₀ T → ∀ M : ℝ, 0 ≤ M →
      (∀ i ∈ T, |v i| ≤ M) →
      √s * |⟪A (restr S₀ v), A (restr T v)⟫|
        ≤ δ * √(∑ i ∈ S₀, v i ^ 2) * (s * M + ∑ i ∈ T, |v i|) := by
  set N := √(∑ i ∈ S₀, v i ^ 2) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hsqs : 0 ≤ √(s : ℝ) := Real.sqrt_nonneg _
  have hss : √(s : ℝ) * √(s : ℝ) = s := Real.mul_self_sqrt (Nat.cast_nonneg s)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hTn hdisj M hM hTM
    obtain ⟨T₁, hsub, hcard, htop⟩ := exists_top (fun i => |v i|) T s
    obtain ⟨M', hM', hM'bd, hM'sum⟩ := exists_bound_of_top (fun i => |v i|)
      (fun i => abs_nonneg _) T T₁ s hs hsub hcard htop
    have hT₁s : T₁.card ≤ s := by omega
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · subst hTe
      rw [restr_empty, map_zero, inner_zero_right, abs_zero, mul_zero]
      have : 0 ≤ (s : ℝ) * M := mul_nonneg (Nat.cast_nonneg s) hM
      have h0 : 0 ≤ δ * N := mul_nonneg hδ hN0
      simpa using mul_nonneg h0 this
    have hT₁pos : 0 < T₁.card := by
      have := card_pos.mpr hTne
      omega
    have hsplit : restr T v = restr T₁ v + restr (T \ T₁) v := by
      rw [← restr_union T₁ (T \ T₁) disjoint_sdiff, union_sdiff_of_subset hsub]
    -- first block
    have hfirst : √s * |⟪A (restr S₀ v), A (restr T₁ v)⟫| ≤ δ * N * (s * M) := by
      have h := hA.abs_inner_le S₀ T₁ hS₀ hT₁s (disjoint_of_subset_right hsub hdisj)
        (restr S₀ v) (restr T₁ v) (fun i hi => restr_apply_of_notMem v hi)
        (fun i hi => restr_apply_of_notMem v hi)
      rw [sum_restr_sq, sum_restr_sq, ← hN] at h
      have hb : √(∑ i ∈ T₁, v i ^ 2) ≤ √s * M := by
        rw [← Real.sqrt_sq (mul_nonneg hsqs hM)]
        refine Real.sqrt_le_sqrt ?_
        have h1 : ∑ i ∈ T₁, v i ^ 2 ≤ T₁.card • M ^ 2 :=
          sum_le_card_nsmul _ _ _ fun i hi => by
            have := hTM i (hsub hi)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) this 2
        rw [nsmul_eq_mul] at h1
        have h2 : (T₁.card : ℝ) * M ^ 2 ≤ s * M ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hT₁s) (sq_nonneg M)
        calc ∑ i ∈ T₁, v i ^ 2 ≤ s * M ^ 2 := h1.trans h2
          _ = (√s * M) ^ 2 := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg s)]
      calc √s * |⟪A (restr S₀ v), A (restr T₁ v)⟫|
          ≤ √s * (δ * (N * √(∑ i ∈ T₁, v i ^ 2))) := mul_le_mul_of_nonneg_left h hsqs
        _ ≤ √s * (δ * (N * (√s * M))) := by
            refine mul_le_mul_of_nonneg_left ?_ hsqs
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hN0) hδ
        _ = δ * N * (√s * √s * M) := by ring
        _ = δ * N * (s * M) := by rw [hss]
    -- remaining blocks, by induction
    have hlt : (T \ T₁).card < n := by
      rw [← hTn, card_sdiff_of_subset hsub]
      have := card_le_card hsub
      omega
    have hrest := ih _ hlt (T \ T₁) rfl (disjoint_of_subset_right sdiff_subset hdisj) M' hM'
      hM'bd
    have hsum : ∑ i ∈ T \ T₁, |v i| + ∑ i ∈ T₁, |v i| = ∑ i ∈ T, |v i| := sum_sdiff hsub
    have htri : |⟪A (restr S₀ v), A (restr T v)⟫|
        ≤ |⟪A (restr S₀ v), A (restr T₁ v)⟫| + |⟪A (restr S₀ v), A (restr (T \ T₁) v)⟫| := by
      rw [hsplit, map_add, inner_add_right]
      exact abs_add_le _ _
    have h0 : 0 ≤ δ * N := mul_nonneg hδ hN0
    calc √s * |⟪A (restr S₀ v), A (restr T v)⟫|
        ≤ √s * |⟪A (restr S₀ v), A (restr T₁ v)⟫|
          + √s * |⟪A (restr S₀ v), A (restr (T \ T₁) v)⟫| := by
          rw [← mul_add]; exact mul_le_mul_of_nonneg_left htri hsqs
      _ ≤ δ * N * (s * M) + δ * N * (s * M' + ∑ i ∈ T \ T₁, |v i|) := add_le_add hfirst hrest
      _ ≤ δ * N * (s * M) + δ * N * (∑ i ∈ T₁, |v i| + ∑ i ∈ T \ T₁, |v i|) := by
          gcongr
      _ = δ * N * (s * M + ∑ i ∈ T, |v i|) := by rw [← hsum]; ring

/-- **The restricted isometry property implies the null space property.** If `A` has the
restricted isometry property of order `2 s` with constant `δ < 1/3`, then it has the null space
property of order `s`. -/
theorem RestrictedIsometry.nullSpaceProperty {A : (ι → ℝ) →ₗ[ℝ] F} {s : ℕ} {δ : ℝ}
    (hA : RestrictedIsometry A (2 * s) δ) (hδ : δ < 1 / 3) : NullSpaceProperty A s := by
  intro v hAv hv S hS
  have hW : 0 < ∑ i, |v i| := sum_abs_pos_of_ne_zero hv
  have hsplitS := sum_add_sum_compl S fun i => |v i|
  rcases Nat.eq_zero_or_pos s with hs0 | hs
  · subst hs0
    rw [Nat.le_zero, card_eq_zero] at hS
    subst hS
    simpa using hW
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hv (Subsingleton.elim _ _)
  have hδ0 : 0 ≤ δ := hA.nonneg (by omega)
  -- the `s` largest entries
  obtain ⟨S₀, -, hcard, htop⟩ := exists_top (fun i => |v i|) univ s
  obtain ⟨M, hM, hMbd, hMsum⟩ := exists_bound_of_top (fun i => |v i|)
    (fun i => abs_nonneg _) univ S₀ s hs (subset_univ _) hcard htop
  have hS₀s : S₀.card ≤ s := by omega
  have hSS₀ : ∑ i ∈ S, |v i| ≤ ∑ i ∈ S₀, |v i| := by
    refine sum_le_sum_top (fun i => |v i|) (fun i => abs_nonneg _) univ S₀ S htop (subset_univ _) ?_
    have := card_le_univ S
    rw [card_univ] at hcard
    omega
  set N := √(∑ i ∈ S₀, v i ^ 2) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hN2 : N ^ 2 = ∑ i ∈ S₀, v i ^ 2 := Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _)
  have hsqs : 0 < √(s : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hs)
  have hss : √(s : ℝ) * √(s : ℝ) = s := Real.mul_self_sqrt (Nat.cast_nonneg s)
  -- Cauchy–Schwarz on the top block
  have hCS : ∑ i ∈ S₀, |v i| ≤ √s * N := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := S₀) (f := fun i => |v i|)
    simp only [sq_abs] at h1
    have h2 : (S₀.card : ℝ) * ∑ i ∈ S₀, v i ^ 2 ≤ s * ∑ i ∈ S₀, v i ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hS₀s) (sum_nonneg fun i _ => sq_nonneg _)
    have h3 : (∑ i ∈ S₀, |v i|) ^ 2 ≤ (√s * N) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg s), hN2]
      exact h1.trans h2
    exact (abs_le_of_sq_le_sq' h3 (mul_nonneg hsqs.le hN0)).2
  -- the kernel relation
  have hsplit : v = restr S₀ v + restr S₀ᶜ v := by
    rw [← restr_union S₀ S₀ᶜ disjoint_compl_right, union_compl]
    funext i; simp [restr]
  have hker : A (restr S₀ v) = -A (restr S₀ᶜ v) := by
    have : A (restr S₀ v) + A (restr S₀ᶜ v) = 0 := by rw [← map_add, ← hsplit, hAv]
    exact eq_neg_of_add_eq_zero_left this
  have hlow : (1 - δ) * N ^ 2 ≤ |⟪A (restr S₀ v), A (restr S₀ᶜ v)⟫| := by
    have h1 := (hA (restr S₀ v) (isSparse_of_support_subset S₀ (by omega)
      fun i hi => restr_apply_of_notMem v hi)).1
    rw [sum_restr_sq, ← hN2] at h1
    have h2 : ‖A (restr S₀ v)‖ ^ 2 = -⟪A (restr S₀ v), A (restr S₀ᶜ v)⟫ := by
      rw [← real_inner_self_eq_norm_sq]
      nth_rewrite 2 [hker]
      rw [inner_neg_right]
    rw [h2] at h1
    exact h1.trans (neg_le_abs _)
  have hblock := hA.block_bound hδ0 hs v S₀ hS₀s _ S₀ᶜ rfl disjoint_compl_right M hM
    (fun i hi => hMbd i (by simpa using hi))
  rw [← hN] at hblock
  have hsplit₀ := sum_add_sum_compl S₀ fun i => |v i|
  set P := ∑ i ∈ S₀, |v i| with hP
  set W := ∑ i, |v i| with hWdef
  -- `√s (1 - δ) N² ≤ δ N W`
  have hmain : √s * ((1 - δ) * N ^ 2) ≤ δ * N * W := by
    calc √s * ((1 - δ) * N ^ 2) ≤ √s * |⟪A (restr S₀ v), A (restr S₀ᶜ v)⟫| :=
          mul_le_mul_of_nonneg_left hlow hsqs.le
      _ ≤ δ * N * (s * M + ∑ i ∈ S₀ᶜ, |v i|) := hblock
      _ ≤ δ * N * W := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hδ0 hN0)
          linarith
  have hgoal : 2 * P < W := by
    rcases eq_or_lt_of_le hN0 with hN' | hN'
    · rw [← hN', mul_zero] at hCS
      linarith
    · have h1 : √s * N * (1 - δ) ≤ δ * W := by
        have : N * (√s * N * (1 - δ)) ≤ N * (δ * W) := by nlinarith [hmain]
        exact le_of_mul_le_mul_left this hN'
      have h2 : P * (1 - δ) ≤ δ * W := by
        have : P * (1 - δ) ≤ √s * N * (1 - δ) :=
          mul_le_mul_of_nonneg_right hCS (by linarith)
        linarith
      have hP0 : 0 ≤ P := sum_nonneg fun i _ => abs_nonneg _
      nlinarith
  linarith

/-- **Exact recovery from the restricted isometry property.** If `A` has the restricted
isometry property of order `2 s` with constant `δ < 1/3`, then every `s`-sparse vector is the
unique ℓ¹ minimiser among the vectors with the same measurements. -/
theorem RestrictedIsometry.exactRecovery {A : (ι → ℝ) →ₗ[ℝ] F} {s : ℕ} {δ : ℝ}
    (hA : RestrictedIsometry A (2 * s) δ) (hδ : δ < 1 / 3) : ExactRecovery A s :=
  (nullSpaceProperty_iff_exactRecovery A s).mp (hA.nullSpaceProperty hδ)

end RIP

/-! ### Matrix versions -/

section Matrix

variable {κ : Type*} [Fintype κ]

omit [Fintype κ] in
/-- **Null space property ⟺ exact ℓ¹ recovery, for a matrix**, with both sides written out. -/
theorem matrix_nullSpaceProperty_iff_exactRecovery (A : Matrix κ ι ℝ) (s : ℕ) :
    (∀ v : ι → ℝ, A.mulVec v = 0 → v ≠ 0 → ∀ S : Finset ι, S.card ≤ s →
        ∑ i ∈ S, |v i| < ∑ i ∈ Sᶜ, |v i|) ↔
      (∀ x : ι → ℝ, IsSparse s x → ∀ z : ι → ℝ, A.mulVec z = A.mulVec x → z ≠ x →
        ∑ i, |x i| < ∑ i, |z i|) :=
  nullSpaceProperty_iff_exactRecovery A.mulVecLin s

/-- The linear map `x ↦ A x` into Euclidean space. -/
noncomputable def matrixEuclideanMap (A : Matrix κ ι ℝ) : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ κ :=
  (WithLp.linearEquiv 2 ℝ (κ → ℝ)).symm.toLinearMap ∘ₗ A.mulVecLin

omit [DecidableEq ι] in
lemma norm_matrixEuclideanMap_sq (A : Matrix κ ι ℝ) (x : ι → ℝ) :
    ‖matrixEuclideanMap A x‖ ^ 2 = ∑ j, A.mulVec x j ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- **Exact ℓ¹ recovery from the restricted isometry property, for a matrix**, with all
hypotheses written out: if `(1 - δ) ‖x‖₂² ≤ ‖A x‖₂² ≤ (1 + δ) ‖x‖₂²` for all `2 s`-sparse `x`
and `δ < 1/3`, then every `s`-sparse `x` is the unique ℓ¹ minimiser subject to `A z = A x`. -/
theorem matrix_exactRecovery_of_restrictedIsometry (A : Matrix κ ι ℝ) (s : ℕ) (δ : ℝ)
    (hδ : δ < 1 / 3)
    (hA : ∀ x : ι → ℝ, IsSparse (2 * s) x →
      (1 - δ) * ∑ i, x i ^ 2 ≤ ∑ j, A.mulVec x j ^ 2 ∧
        ∑ j, A.mulVec x j ^ 2 ≤ (1 + δ) * ∑ i, x i ^ 2)
    (x : ι → ℝ) (hx : IsSparse s x) (z : ι → ℝ) (hz : A.mulVec z = A.mulVec x) (hne : z ≠ x) :
    ∑ i, |x i| < ∑ i, |z i| := by
  have hR : RestrictedIsometry (matrixEuclideanMap A) (2 * s) δ := by
    intro y hy
    rw [norm_matrixEuclideanMap_sq]
    exact hA y hy
  refine hR.exactRecovery hδ x hx z ?_ hne
  simp only [matrixEuclideanMap, LinearMap.comp_apply, Matrix.mulVecLin_apply, hz]

/-- Non-vacuity: the identity matrix has the restricted isometry property of every order with
constant `0`. -/
theorem restrictedIsometry_one (k : ℕ) :
    RestrictedIsometry (matrixEuclideanMap (1 : Matrix ι ι ℝ)) k 0 := by
  intro x _
  rw [norm_matrixEuclideanMap_sq, Matrix.one_mulVec]
  simp

end Matrix

end Applied.SignalProcessing
