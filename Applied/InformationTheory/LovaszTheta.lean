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
open Real

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

/-! ### The pentagon: Lovász's umbrella -/

/-- Azimuth `2πi/5` of the `i`-th rib of the umbrella. -/
noncomputable def umbrellaAngle (i : Fin 5) : ℝ := 2 * π * (i : ℕ) / 5

/-- Lovász's umbrella for `C₅`: unit vectors at azimuth `2πi/5` whose height
`√(cos(π/5)/(1+cos(π/5)))` makes ribs `i` and `i ± 2` orthogonal. -/
noncomputable def umbrella5 (i : Fin 5) : EuclideanSpace ℝ (Fin 3) :=
  !₂[√(1 / (1 + cos (π / 5))) * cos (umbrellaAngle i),
     √(1 / (1 + cos (π / 5))) * sin (umbrellaAngle i), √(cos (π / 5) / (1 + cos (π / 5)))]

lemma cos_pi_div_five_pos : 0 < cos (π / 5) := by
  rw [cos_pi_div_five]; positivity

lemma inner_umbrella5 (i j : Fin 5) : ⟪umbrella5 i, umbrella5 j⟫ =
    (cos (umbrellaAngle i - umbrellaAngle j) + cos (π / 5)) / (1 + cos (π / 5)) := by
  have hk := cos_pi_div_five_pos
  rw [inner_euclidean, Fin.sum_univ_three]
  simp only [umbrella5]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hA := Real.mul_self_sqrt (show 0 ≤ 1 / (1 + cos (π / 5)) by positivity)
  have hB := Real.mul_self_sqrt (show 0 ≤ cos (π / 5) / (1 + cos (π / 5)) by positivity)
  rw [cos_sub]
  set A := √(1 / (1 + cos (π / 5)))
  set B := √(cos (π / 5) / (1 + cos (π / 5)))
  calc _ = A * A * (cos (umbrellaAngle i) * cos (umbrellaAngle j) +
        sin (umbrellaAngle i) * sin (umbrellaAngle j)) + B * B := by simp; ring
    _ = _ := by rw [hA, hB]; field_simp

lemma umbrellaAngle_sub (i j : Fin 5) (hij : i ≠ j)
    (hadj : ¬ (SimpleGraph.cycleGraph 5).Adj i j) :
    cos (umbrellaAngle i - umbrellaAngle j) = - cos (π / 5) := by
  have key : ((i : ℕ) : ℤ) - (j : ℕ) = 2 ∨ ((i : ℕ) : ℤ) - (j : ℕ) = -2 ∨
      ((i : ℕ) : ℤ) - (j : ℕ) = 3 ∨ ((i : ℕ) : ℤ) - (j : ℕ) = -3 := by
    rw [SimpleGraph.cycleGraph_adj] at hadj
    revert i j; decide
  have hsub : umbrellaAngle i - umbrellaAngle j = 2 * π * ((((i : ℕ) : ℤ) - (j : ℕ) : ℤ) : ℝ) / 5 := by
    simp [umbrellaAngle]; ring
  rw [hsub]
  rcases key with h | h | h | h <;> rw [h] <;> push_cast
  · rw [show 2 * π * 2 / 5 = π - π / 5 by ring, cos_pi_sub]
  · rw [show 2 * π * (-2) / 5 = -(π - π / 5) by ring, cos_neg, cos_pi_sub]
  · rw [show 2 * π * 3 / 5 = π / 5 + π by ring, cos_add_pi]
  · rw [show 2 * π * (-3) / 5 = -(π / 5 + π) by ring, cos_neg, cos_add_pi]

theorem isOrthonormalRep_umbrella5 :
    IsOrthonormalRep (SimpleGraph.cycleGraph 5) umbrella5 := by
  have hk := cos_pi_div_five_pos
  refine ⟨fun i => norm_eq_one_of_inner_self ?_, fun i j hij hadj => ?_⟩
  · rw [inner_umbrella5, sub_self, cos_zero]; field_simp
  · rw [inner_umbrella5, umbrellaAngle_sub i j hij hadj]; simp

/-- The handle of the umbrella. -/
noncomputable def umbrellaHandle : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 1]

theorem inner_umbrellaHandle (i : Fin 5) :
    ⟪umbrellaHandle, umbrella5 i⟫ ^ 2 = cos (π / 5) / (1 + cos (π / 5)) := by
  have hk := cos_pi_div_five_pos
  rw [inner_euclidean, Fin.sum_univ_three]
  simp [umbrellaHandle, umbrella5]
  rw [Real.sq_sqrt (by positivity)]

theorem norm_umbrellaHandle : ‖umbrellaHandle‖ = 1 := by
  refine norm_eq_one_of_inner_self ?_
  rw [inner_euclidean, Fin.sum_univ_three]
  simp [umbrellaHandle]

/-- `Θ(C₅) ≤ √5`, from the umbrella. -/
theorem shannonCapacity_cycleGraph_five_le :
    shannonCapacity (SimpleGraph.cycleGraph 5) ≤ √5 := by
  refine shannonCapacity_le_of_isOrthonormalRep isOrthonormalRep_umbrella5 norm_umbrellaHandle
    fun i => ?_
  rw [inner_umbrellaHandle, cos_pi_div_five]
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have h0 : 0 < √5 := by positivity
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith

/-- **Lovász (1979).** `Θ(C₅) = √5` (with Shannon's lower bound). -/
theorem shannonCapacity_cycleGraph_five :
    shannonCapacity (SimpleGraph.cycleGraph 5) = √5 :=
  le_antisymm shannonCapacity_cycleGraph_five_le sqrt_five_le_shannonCapacity_cycleGraph_five

end Applied.InformationTheory
