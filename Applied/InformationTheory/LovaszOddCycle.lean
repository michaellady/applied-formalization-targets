import Applied.InformationTheory.LovaszTheta

/-!
# Lovász's bound for odd cycles: `Θ(Cₙ) ≤ n cos(π/n) / (1 + cos(π/n))`

L. Lovász, "On the Shannon capacity of a graph", IEEE Trans. Inform. Theory 25 (1979): for odd
`n`, `ϑ(Cₙ) = n cos(π/n) / (1 + cos(π/n))`. Here only the upper bound on the Shannon capacity is
proved, by an explicit orthonormal representation.

For odd `n ≥ 3` put `t = 1 / (2 cos(π/n))` and `λ_k = 1 + 2t cos(2πk/n)` (`oddLam`), which is
`≥ 0` because `n` is odd (`oddLam_nonneg`). The vectors (`oddRep`)
`uᵢ = (√(λ_k/n) (cos(2πki/n) + sin(2πki/n)))_{k < n} ∈ ℝⁿ` have Gram matrix `1` on the
diagonal, `t` between neighbours and `0` between non-neighbours (proved from the sums of
`n`-th roots of unity, `sum_cos_root`, `sum_sin_root`), so they form an orthonormal
representation of `Cₙ` (`isOrthonormalRep_oddRep`). With the handle `e₀` (`oddHandle`),
`⟪e₀, uᵢ⟫² = λ₀/n = (1 + 1/cos(π/n))/n` (`inner_oddHandle_sq`), which gives
`shannonCapacity_cycleGraph_odd_le` and, for `n = 7`,
`shannonCapacity_cycleGraph_seven_le_lovaszTheta`:
`Θ(C₇) ≤ 7 cos(π/7) / (1 + cos(π/7))`.
-/

open scoped RealInnerProductSpace
open Real Finset

namespace Applied.InformationTheory

/-- Sums of `n`-th roots of unity: `∑_{k<n} exp(2πikm/n)` is `n` if `n ∣ m` and `0` otherwise. -/
lemma sum_exp_root (n : ℕ) (hn : 0 < n) (m : ℤ) :
    ∑ k ∈ range n, Complex.exp (((2 * π / n * k * m : ℝ) : ℂ) * Complex.I) =
      if (n : ℤ) ∣ m then (n : ℂ) else 0 := by
  set z : ℂ := Complex.exp (((2 * π / n * m : ℝ) : ℂ) * Complex.I) with hz
  have hk : ∀ k : ℕ, Complex.exp (((2 * π / n * k * m : ℝ) : ℂ) * Complex.I) = z ^ k := by
    intro k
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [hk]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    have : z = 1 := by
      rw [hz]
      convert Complex.exp_int_mul_two_pi_mul_I q using 2
      push_cast
      field_simp
    simp [this]
  · have hz1 : z ≠ 1 := by
      intro h1
      rw [hz, Complex.exp_eq_one_iff] at h1
      obtain ⟨l, hl⟩ := h1
      apply h
      refine ⟨l, ?_⟩
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have : ((m : ℝ) : ℂ) = (n : ℂ) * (l : ℂ) := by
        push_cast at hl ⊢
        field_simp at hl
        linear_combination hl
      exact_mod_cast this
    have hzn : z ^ n = 1 := by
      rw [hz, ← Complex.exp_nat_mul]
      convert Complex.exp_int_mul_two_pi_mul_I m using 2
      push_cast
      field_simp
    rw [geom_sum_eq hz1, hzn, sub_self, zero_div]

lemma sum_cos_root (n : ℕ) (hn : 0 < n) (m : ℤ) :
    ∑ k ∈ range n, cos (2 * π / n * k * m) = if (n : ℤ) ∣ m then (n : ℝ) else 0 := by
  have h := congrArg Complex.re (sum_exp_root n hn m)
  rw [Complex.re_sum] at h
  simp only [Complex.exp_ofReal_mul_I_re] at h
  rw [h]; split_ifs <;> simp

lemma sum_sin_root (n : ℕ) (hn : 0 < n) (m : ℤ) :
    ∑ k ∈ range n, sin (2 * π / n * k * m) = 0 := by
  have h := congrArg Complex.im (sum_exp_root n hn m)
  rw [Complex.im_sum] at h
  simp only [Complex.exp_ofReal_mul_I_im] at h
  rw [h]; split_ifs <;> simp

/-- The circulant weights `λ_k = 1 + cos(2πk/n)/cos(π/n)` (eigenvalues of the Gram matrix of
the representation below). -/
noncomputable def oddLam (n : ℕ) (k : ℕ) : ℝ := 1 + cos (2 * π / n * k) / cos (π / n)

lemma cos_pi_div_pos (n : ℕ) (hn : 3 ≤ n) : 0 < cos (π / n) := by
  apply cos_pos_of_mem_Ioo
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · have : 0 < π / n := by positivity
    linarith [pi_pos]
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [pi_pos]

lemma oddLam_nonneg (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) (k : ℕ) (hk : k < n) :
    0 ≤ oddLam n k := by
  have hc := cos_pi_div_pos n hn
  have hn0 : (0 : ℝ) < n := by positivity
  suffices h : -cos (π / n) ≤ cos (2 * π / n * k) by
    unfold oddLam
    have : -1 ≤ cos (2 * π / n * k) / cos (π / n) := by
      rw [le_div_iff₀ hc]; linarith
    linarith
  rw [← cos_pi_sub]
  obtain ⟨r, hr⟩ := hodd
  rcases Nat.lt_or_ge (2 * k) n with h | h
  · -- `2k ≤ n - 1`
    have h2 : (2 * k : ℝ) + 1 ≤ n := by exact_mod_cast (show 2 * k + 1 ≤ n by omega)
    apply cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (by linarith [pi_pos, (by positivity : 0 ≤ π / n)])
    rw [show π - π / n = π * (n - 1) / n by field_simp,
      show 2 * π / n * k = π * (2 * k) / n by ring]
    gcongr
    linarith
  · -- `2k ≥ n + 1`: use `cos x = cos (2π - x)`
    have h2 : (n : ℝ) + 1 ≤ 2 * k := by exact_mod_cast (show n + 1 ≤ 2 * k by omega)
    have hk' : (k : ℝ) < n := by exact_mod_cast hk
    rw [show 2 * π / n * k = 2 * π - 2 * π / n * (n - k) by field_simp; ring, cos_two_pi_sub]
    apply cos_le_cos_of_nonneg_of_le_pi
    · have : (0 : ℝ) ≤ n - k := by linarith
      positivity
    · linarith [pi_pos, (by positivity : 0 ≤ π / n)]
    rw [show π - π / n = π * (n - 1) / n by field_simp,
      show 2 * π / n * (n - k) = π * (2 * (n - k)) / n by ring]
    gcongr
    linarith

lemma sum_oddLam_cos (n : ℕ) (hn : 0 < n) (m : ℤ) :
    ∑ k ∈ range n, oddLam n k * cos (2 * π / n * k * m) =
      (if (n : ℤ) ∣ m then (n : ℝ) else 0) +
        ((if (n : ℤ) ∣ (m + 1) then (n : ℝ) else 0) +
          (if (n : ℤ) ∣ (m - 1) then (n : ℝ) else 0)) / (2 * cos (π / n)) := by
  rw [← sum_cos_root n hn, ← sum_cos_root n hn, ← sum_cos_root n hn, ← sum_add_distrib,
    sum_div, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  have h1 : 2 * π / n * k * ((m + 1 : ℤ) : ℝ) = 2 * π / n * k * m + 2 * π / n * k := by
    push_cast; ring
  have h2 : 2 * π / n * k * ((m - 1 : ℤ) : ℝ) = 2 * π / n * k * m - 2 * π / n * k := by
    push_cast; ring
  rw [h1, h2, cos_add, cos_sub, oddLam]
  ring

lemma sum_oddLam_sin (n : ℕ) (hn : 0 < n) (m : ℤ) :
    ∑ k ∈ range n, oddLam n k * sin (2 * π / n * k * m) = 0 := by
  have key : ∑ k ∈ range n, oddLam n k * sin (2 * π / n * k * m) =
      ∑ k ∈ range n, sin (2 * π / n * k * m) +
        (∑ k ∈ range n, sin (2 * π / n * k * ((m + 1 : ℤ) : ℝ)) +
          ∑ k ∈ range n, sin (2 * π / n * k * ((m - 1 : ℤ) : ℝ))) / (2 * cos (π / n)) := by
    rw [← sum_add_distrib, sum_div, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    have h1 : 2 * π / n * k * ((m + 1 : ℤ) : ℝ) = 2 * π / n * k * m + 2 * π / n * k := by
      push_cast; ring
    have h2 : 2 * π / n * k * ((m - 1 : ℤ) : ℝ) = 2 * π / n * k * m - 2 * π / n * k := by
      push_cast; ring
    rw [h1, h2, sin_add, sin_sub, oddLam]
    ring
  rw [key, sum_sin_root n hn, sum_sin_root n hn, sum_sin_root n hn]
  simp

/-- Lovász's orthonormal representation of the odd cycle `Cₙ` in `ℝⁿ`: coordinate `k` of the
vector of vertex `i` is `√(λ_k / n) (cos(2πki/n) + sin(2πki/n))`. -/
noncomputable def oddRep (n : ℕ) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun k : Fin n => √(oddLam n k / n) *
    (cos (2 * π / n * (k : ℕ) * (i : ℕ)) + sin (2 * π / n * (k : ℕ) * (i : ℕ)))

lemma inner_oddRep (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) (i j : Fin n) :
    ⟪oddRep n i, oddRep n j⟫ = (1 / n) *
      (∑ k ∈ range n, oddLam n k * cos (2 * π / n * k * (((i : ℕ) : ℤ) - (j : ℕ) : ℤ)) +
        ∑ k ∈ range n, oddLam n k * sin (2 * π / n * k * (((i : ℕ) : ℤ) + (j : ℕ) : ℤ))) := by
  rw [inner_euclidean]
  simp only [oddRep]
  rw [Fin.sum_univ_eq_sum_range (fun k => √(oddLam n k / n) *
      (cos (2 * π / n * k * (i : ℕ)) + sin (2 * π / n * k * (i : ℕ))) *
      (√(oddLam n k / n) * (cos (2 * π / n * k * (j : ℕ)) + sin (2 * π / n * k * (j : ℕ))))) n,
    ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hl := oddLam_nonneg n hn hodd k (mem_range.1 hk)
  have hs := Real.mul_self_sqrt (show 0 ≤ oddLam n k / n by positivity)
  have e1 : 2 * π / n * k * ((((i : ℕ) : ℤ) - (j : ℕ) : ℤ) : ℝ) =
      2 * π / n * k * (i : ℕ) - 2 * π / n * k * (j : ℕ) := by push_cast; ring
  have e2 : 2 * π / n * k * ((((i : ℕ) : ℤ) + (j : ℕ) : ℤ) : ℝ) =
      2 * π / n * k * (i : ℕ) + 2 * π / n * k * (j : ℕ) := by push_cast; ring
  rw [e1, e2, cos_sub, sin_add]
  set a := 2 * π / n * k * (i : ℕ)
  set b := 2 * π / n * k * (j : ℕ)
  calc √(oddLam n k / n) * (cos a + sin a) * (√(oddLam n k / n) * (cos b + sin b))
      = (√(oddLam n k / n) * √(oddLam n k / n)) *
          (cos a * cos b + sin a * sin b + (sin a * cos b + cos a * sin b)) := by ring
    _ = _ := by rw [hs]; ring

lemma int_dvd_cases (n : ℕ) (hn : 0 < n) (x : ℤ) (hd : (n : ℤ) ∣ x) (h1 : -(n : ℤ) ≤ x)
    (h2 : x ≤ n) : x = 0 ∨ x = n ∨ x = -n := by
  obtain ⟨q, rfl⟩ := hd
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hq1 : -1 ≤ q := by nlinarith
  have hq2 : q ≤ 1 := by nlinarith
  interval_cases q <;> simp

lemma cycleGraph_adj_of_val (n : ℕ) (hn : 3 ≤ n) (i j : Fin n)
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i ∨ ((i : ℕ) + 1 = n ∧ (j : ℕ) = 0) ∨
      ((j : ℕ) + 1 = n ∧ (i : ℕ) = 0)) :
    (SimpleGraph.cycleGraph n).Adj i j := by
  rw [SimpleGraph.cycleGraph_adj']
  have hi := i.isLt
  have hj := j.isLt
  rcases h with h | h | h | h
  · right; rw [Fin.coe_sub_iff_le.2 (Fin.le_def.2 (by omega))]; omega
  · left; rw [Fin.coe_sub_iff_le.2 (Fin.le_def.2 (by omega))]; omega
  · obtain ⟨h1, h2⟩ := h
    have hji : j < i := by rw [Fin.lt_def]; omega
    right; rw [Fin.coe_sub_iff_lt.2 hji]; omega
  · obtain ⟨h1, h2⟩ := h
    have hij : i < j := by rw [Fin.lt_def]; omega
    left; rw [Fin.coe_sub_iff_lt.2 hij]; omega

/-- For odd `n ≥ 3`, `oddRep n` is an orthonormal representation of the cycle `Cₙ`: unit
vectors, orthogonal for distinct non-adjacent vertices (Lovász's generalised umbrella). -/
theorem isOrthonormalRep_oddRep (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    IsOrthonormalRep (SimpleGraph.cycleGraph n) (oddRep n) := by
  have hn0 : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by positivity
  refine ⟨fun i => norm_eq_one_of_inner_self ?_, fun i j hij hadj => ?_⟩
  · rw [inner_oddRep n hn hodd, sum_oddLam_cos n hn0, sum_oddLam_sin n hn0, sub_self, zero_add]
    have h1 : ¬ (n : ℤ) ∣ 1 := fun h => by
      have := Int.le_of_dvd one_pos h; omega
    have h2 : ¬ (n : ℤ) ∣ (0 - 1) := fun h => h1 (by simpa using h)
    simp only [dvd_zero, ite_true, h1, h2, ite_false]
    field_simp
    ring
  · have hi := i.isLt
    have hj := j.isLt
    have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    set m : ℤ := ((i : ℕ) : ℤ) - (j : ℕ) with hm
    have d0 : ¬ (n : ℤ) ∣ m := fun h => by
      rcases int_dvd_cases n hn0 m h (by omega) (by omega) with h | h | h <;> omega
    have d1 : ¬ (n : ℤ) ∣ (m + 1) := fun h => by
      rcases int_dvd_cases n hn0 _ h (by omega) (by omega) with h | h | h
      · exact hadj (cycleGraph_adj_of_val n hn i j (by omega))
      · exact hadj (cycleGraph_adj_of_val n hn i j (by omega))
      · omega
    have d2 : ¬ (n : ℤ) ∣ (m - 1) := fun h => by
      rcases int_dvd_cases n hn0 _ h (by omega) (by omega) with h | h | h
      · exact hadj (cycleGraph_adj_of_val n hn i j (by omega))
      · omega
      · exact hadj (cycleGraph_adj_of_val n hn i j (by omega))
    rw [inner_oddRep n hn hodd, sum_oddLam_cos n hn0, sum_oddLam_sin n hn0, ← hm]
    simp [d0, d1, d2]

/-- The handle: the first standard basis vector of `ℝⁿ`. -/
noncomputable def oddHandle (n : ℕ) (hn : 0 < n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single ⟨0, hn⟩ 1

lemma inner_oddHandle_sq (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) (i : Fin n) :
    ⟪oddHandle n (by omega), oddRep n i⟫ ^ 2 = (1 + 1 / cos (π / n)) / n := by
  rw [oddHandle, EuclideanSpace.inner_single_left]
  simp only [oddRep, PiLp.toLp_apply]
  have hl := oddLam_nonneg n hn hodd 0 (by omega)
  simp only [Nat.cast_zero, mul_zero, zero_mul, cos_zero, sin_zero, add_zero, mul_one,
    map_one, one_mul]
  rw [Real.sq_sqrt (by positivity), oddLam]
  simp

/-- **Lovász (1979).** For odd `n ≥ 3`, `Θ(Cₙ) ≤ n cos(π/n) / (1 + cos(π/n))` (`= ϑ(Cₙ)`). -/
theorem shannonCapacity_cycleGraph_odd_le (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    shannonCapacity (SimpleGraph.cycleGraph n) ≤ n * cos (π / n) / (1 + cos (π / n)) := by
  have hn0 : 0 < n := by omega
  have : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  refine shannonCapacity_le_of_isOrthonormalRep (isOrthonormalRep_oddRep n hn hodd)
    (c := oddHandle n hn0) (by simp [oddHandle]) fun i => ?_
  rw [inner_oddHandle_sq n hn hodd]
  have hc := cos_pi_div_pos n hn
  have hnR : (0 : ℝ) < n := by positivity
  apply le_of_eq
  field_simp
  ring


/-- **Lovász's bound for `C₇`.** `Θ(C₇) ≤ 7 cos(π/7) / (1 + cos(π/7)) ≈ 3.3177`. -/
theorem shannonCapacity_cycleGraph_seven_le_lovaszTheta :
    shannonCapacity (SimpleGraph.cycleGraph 7) ≤ 7 * cos (π / 7) / (1 + cos (π / 7)) := by
  simpa using shannonCapacity_cycleGraph_odd_le 7 (by norm_num) ⟨3, rfl⟩

end Applied.InformationTheory
