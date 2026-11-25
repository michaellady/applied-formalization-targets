import Applied.InformationTheory.ShannonCapacity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Lovász's orthonormal-representation bound on the Shannon capacity

L. Lovász, "On the Shannon capacity of a graph", IEEE Trans. Inform. Theory 25 (1979).

An *orthonormal representation* of a graph `G` (Lovász's convention, matching the library's
convention that adjacent letters are confusable and codes are independent sets) assigns a unit
vector `u v` to every vertex so that distinct **non-adjacent** vertices get orthogonal vectors.

* `IsOrthonormalRep G u`: the predicate above, for `u : V → E`, `E` a real inner product space.
* `IsOrthonormalRep.sum_inner_sq_le`: for an independent set `S` and any vector `c`,
  `∑_{v ∈ S} ⟪c, u v⟫² ≤ ‖c‖²` (Bessel's inequality).
* `indepNum_le_of_isOrthonormalRep`: if `‖c‖ = 1` and `1 ≤ M ⟪c, u v⟫²` for all `v`, then
  `α(G) ≤ M`; `indepNum_le_sup_inv_inner_sq`: `α(G) ≤ max_v 1 / ⟪c, u v⟫²` when no
  `⟪c, u v⟫` vanishes.
* `tensorProd`, `inner_tensorProd`: the tensor product of `k` vectors of `EuclideanSpace ℝ ι`,
  realized in `EuclideanSpace ℝ (Fin k → ι)`; inner products multiply.
* `IsOrthonormalRep.strongPow`: tensor powers of an orthonormal representation of `G` form an
  orthonormal representation of the strong power `G^{⊠k}`.
* `indepNum_strongPow_le_of_isOrthonormalRep`: `α(G^{⊠k}) ≤ M^k`, hence
  `shannonCapacity_le_of_isOrthonormalRep`: `Θ(G) ≤ M` (Lovász's Theorem 1 direction
  `Θ(G) ≤ ϑ(G)`, stated for one representation rather than for the infimum `ϑ`).
* `shannonCapacity_cycleGraph_five`: `Θ(C₅) = √5` (Lovász's umbrella in `ℝ³`).
* `shannonCapacity_cycleGraph_seven_le`: `Θ(C₇) ≤ 70000 / 21099 ≈ 3.317693`, from an explicit
  orthonormal representation of `C₇` in `ℝ⁷` with circulant Gram matrix.
-/

open Finset
open scoped RealInnerProductSpace

namespace Applied.InformationTheory

variable {V : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An orthonormal representation of `G` in Lovász's convention: unit vectors such that
distinct non-adjacent vertices are sent to orthogonal vectors. -/
def IsOrthonormalRep (G : SimpleGraph V) (u : V → E) : Prop :=
  (∀ v, ‖u v‖ = 1) ∧ ∀ v w, v ≠ w → ¬ G.Adj v w → ⟪u v, u w⟫ = 0

lemma norm_eq_one_of_inner_self {x : E} (h : ⟪x, x⟫ = 1) : ‖x‖ = 1 := by
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg x]

/-- **Bessel step of Lovász's bound.** On an independent set the vectors of an orthonormal
representation are orthonormal, so `∑_{v ∈ S} ⟪c, u v⟫² ≤ ‖c‖²`. -/
theorem IsOrthonormalRep.sum_inner_sq_le {G : SimpleGraph V} {u : V → E}
    (hu : IsOrthonormalRep G u) {s : Finset V} (hs : G.IsIndepSet (s : Set V)) (c : E) :
    ∑ v ∈ s, ⟪c, u v⟫ ^ 2 ≤ ‖c‖ ^ 2 := by
  classical
  have hon : Orthonormal ℝ (fun v : s => u v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨v, hv⟩ ⟨w, hw⟩
    by_cases h : v = w
    · subst h
      simp [hu.1]
    · have hne : (⟨v, hv⟩ : s) ≠ ⟨w, hw⟩ := fun h' => h (congrArg Subtype.val h')
      rw [ite_eq_right_iff.2 fun h' => absurd h' hne]
      exact hu.2 v w h (hs (Finset.mem_coe.2 hv) (Finset.mem_coe.2 hw) h)
  have h := hon.sum_inner_products_le (s := Finset.univ) c
  rw [← Finset.sum_coe_sort s]
  simpa [Real.norm_eq_abs, sq_abs, real_inner_comm] using h

/-- **Lovász's bound** `α(G) ≤ M` from one orthonormal representation `u` and one unit
"handle" vector `c` with `⟪c, u v⟫² ≥ 1 / M` for every vertex (written without division). -/
theorem indepNum_le_of_isOrthonormalRep [Fintype V] [Nonempty V] {G : SimpleGraph V}
    {u : V → E} (hu : IsOrthonormalRep G u) {c : E} (hc : ‖c‖ = 1) {M : ℝ}
    (hM : ∀ v, 1 ≤ M * ⟪c, u v⟫ ^ 2) : (G.indepNum : ℝ) ≤ M := by
  classical
  have hM0 : 0 ≤ M := by
    have := hM (Classical.arbitrary V)
    nlinarith [sq_nonneg ⟪c, u (Classical.arbitrary V)⟫]
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  have hsum := hu.sum_inner_sq_le hs.isIndepSet c
  rw [hc, one_pow] at hsum
  calc (s.card : ℝ) = ∑ _v ∈ s, (1 : ℝ) := by simp
    _ ≤ ∑ v ∈ s, M * ⟪c, u v⟫ ^ 2 := Finset.sum_le_sum fun v _ => hM v
    _ = M * ∑ v ∈ s, ⟪c, u v⟫ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hsum hM0
    _ = M := mul_one M

/-- Lovász's bound in the form `α(G) ≤ max_v 1 / ⟪c, u v⟫²` (all `⟪c, u v⟫ ≠ 0`). -/
theorem indepNum_le_sup_inv_inner_sq [Fintype V] [Nonempty V] {G : SimpleGraph V}
    {u : V → E} (hu : IsOrthonormalRep G u) {c : E} (hc : ‖c‖ = 1)
    (hne : ∀ v, ⟪c, u v⟫ ≠ 0) :
    (G.indepNum : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty (fun v => 1 / ⟪c, u v⟫ ^ 2) := by
  refine indepNum_le_of_isOrthonormalRep hu hc fun v => ?_
  have hle : 1 / ⟪c, u v⟫ ^ 2 ≤
      Finset.univ.sup' Finset.univ_nonempty (fun v => 1 / ⟪c, u v⟫ ^ 2) :=
    Finset.le_sup' (fun v => 1 / ⟪c, u v⟫ ^ 2) (Finset.mem_univ v)
  have hpos : 0 < ⟪c, u v⟫ ^ 2 := sq_pos_of_ne_zero (hne v)
  calc (1 : ℝ) = 1 / ⟪c, u v⟫ ^ 2 * ⟪c, u v⟫ ^ 2 := (one_div_mul_cancel hpos.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hle hpos.le

/-! ### Tensor powers -/

variable {ι : Type*} [Fintype ι]

/-- The tensor product `w 0 ⊗ ⋯ ⊗ w (k-1)` of vectors of `EuclideanSpace ℝ ι`, as the vector
`x ↦ ∏ i, w i (x i)` of `EuclideanSpace ℝ (Fin k → ι)`. -/
noncomputable def tensorProd {k : ℕ} (w : Fin k → EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (Fin k → ι) :=
  WithLp.toLp 2 fun x => ∏ i, w i (x i)

lemma inner_euclidean (x y : EuclideanSpace ℝ ι) : ⟪x, y⟫ = ∑ j, x j * y j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

/-- Inner products of tensor products multiply. -/
theorem inner_tensorProd {k : ℕ} (w w' : Fin k → EuclideanSpace ℝ ι) :
    ⟪tensorProd w, tensorProd w'⟫ = ∏ i, ⟪w i, w' i⟫ := by
  classical
  simp only [inner_euclidean]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [tensorProd, ← Finset.prod_mul_distrib]

/-- Tensor powers of an orthonormal representation of `G` form an orthonormal representation
of the strong power `G^{⊠k}`. -/
theorem IsOrthonormalRep.strongPow {G : SimpleGraph V} {u : V → EuclideanSpace ℝ ι}
    (hu : IsOrthonormalRep G u) (k : ℕ) :
    IsOrthonormalRep (strongPow G k) (fun f => tensorProd fun i => u (f i)) := by
  refine ⟨fun f => norm_eq_one_of_inner_self ?_, fun f g hfg hadj => ?_⟩
  · rw [inner_tensorProd]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [real_inner_self_eq_norm_sq, hu.1, one_pow]
  · rw [strongPow_adj] at hadj
    push Not at hadj
    obtain ⟨i, hi, hni⟩ := hadj hfg
    rw [inner_tensorProd]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hu.2 _ _ hi hni)

/-- Lovász's bound for strong powers: `α(G^{⊠k}) ≤ M^k`. -/
theorem indepNum_strongPow_le_of_isOrthonormalRep [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {u : V → EuclideanSpace ℝ ι} (hu : IsOrthonormalRep G u)
    {c : EuclideanSpace ℝ ι} (hc : ‖c‖ = 1) {M : ℝ} (hM : ∀ v, 1 ≤ M * ⟪c, u v⟫ ^ 2)
    (k : ℕ) : ((strongPow G k).indepNum : ℝ) ≤ M ^ k := by
  classical
  refine indepNum_le_of_isOrthonormalRep (hu.strongPow k) (c := tensorProd fun _ => c)
    (norm_eq_one_of_inner_self ?_) fun f => ?_
  · rw [inner_tensorProd]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [real_inner_self_eq_norm_sq, hc, one_pow]
  · rw [inner_tensorProd, ← Finset.prod_pow]
    have h1 : M ^ k = ∏ _i : Fin k, M := by simp
    rw [h1, ← Finset.prod_mul_distrib]
    exact Finset.one_le_prod₀ fun i _ => hM (f i)

/-- **Lovász (1979).** An orthonormal representation `u` of `G` in `EuclideanSpace ℝ ι` and a
unit vector `c` with `1 ≤ M ⟪c, u v⟫²` for every vertex give `Θ(G) ≤ M`. -/
theorem shannonCapacity_le_of_isOrthonormalRep [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {u : V → EuclideanSpace ℝ ι} (hu : IsOrthonormalRep G u)
    {c : EuclideanSpace ℝ ι} (hc : ‖c‖ = 1) {M : ℝ} (hM : ∀ v, 1 ≤ M * ⟪c, u v⟫ ^ 2) :
    shannonCapacity G ≤ M := by
  have hM0 : 0 ≤ M := by
    have := hM (Classical.arbitrary V)
    nlinarith [sq_nonneg ⟪c, u (Classical.arbitrary V)⟫]
  refine ciSup_le fun k => ?_
  have h := indepNum_strongPow_le_of_isOrthonormalRep hu hc hM (k + 1)
  calc ((strongPow G (k + 1)).indepNum : ℝ) ^ (((k + 1 : ℕ) : ℝ)⁻¹)
      ≤ (M ^ (k + 1)) ^ (((k + 1 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h (by positivity)
    _ = M := Real.pow_rpow_inv_natCast hM0 (Nat.succ_ne_zero k)

end Applied.InformationTheory
