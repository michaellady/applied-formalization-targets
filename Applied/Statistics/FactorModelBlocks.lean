import Applied.Statistics.FactorModelLaw

/-!
# One-factor block models: from a finite certificate about `Φ` to a violation of the level

A *block model* has finitely many blocks `g : β`; block `g` consists of `mult g * N` statistics
`θ g + b g * z + s g * ε` with a common factor `z` and independent noises `ε` (all standard
normal). `blockIndex mult N` is the index type, of cardinality `(∑ g, mult g) * N`. The true
nulls are the statistics of the blocks in `β₀`.

* `fdr_block_ge`: the bound of `fdr_factor_ge` with conditional means written through `Φ`
  (hypotheses quantified over the factor value in each bin).
* `fdr_block_ge_endpoints`: the same with the hypotheses evaluated at the bin end points only
  (monotonicity of `Φ`), so that every hypothesis is a finite statement about values of `Φ`.
* `fdr_block_gt`: if the finite sum `∑ k, f k / u(a k) * (Φ(zh k) - Φ(zl k))` exceeds one, the
  false discovery rate exceeds `α` for every sufficiently large replication number `N`.
* `exists_gaussian_fdr_gt_of_block`: the resulting instance in the form used by the open
  proposition `Targets.Statistics.BHTwoSidedGaussian` (indices `Fin n`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

open Applied.Statistics

local notation "γ" => gaussianReal 0 1
local notation "Φ" => cdf (gaussianReal 0 1)

section Reindex

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {α : ℝ}

lemma bhK_reindex (e : κ ≃ ι) (q : ι → ℝ) : bhK α (q ∘ e) = bhK α q := by
  unfold bhK bhCount
  rw [Fintype.card_congr e]
  congr 1
  funext k
  congr 2
  exact Finset.card_equiv e (by simp)

lemma bhReject_reindex (e : κ ≃ ι) (q : ι → ℝ) :
    bhReject α (q ∘ e) = (bhReject α q).map e.symm.toEmbedding := by
  ext j
  simp only [bhReject, mem_filter, mem_univ, true_and, Finset.mem_map_equiv, Equiv.symm_symm,
    bhK_reindex, Fintype.card_congr e, Function.comp_apply]

omit [Fintype ι] [Fintype κ] in
lemma fdp_map [DecidableEq ι] [DecidableEq κ] (e : ι ↪ κ) (H R : Finset ι) :
    fdp (H.map e) (R.map e) = fdp H R := by
  simp only [fdp, ← Finset.map_inter, Finset.card_map]

end Reindex

/-- A discrete intermediate value step: a threshold `t` with `u n < t ≤ u 0` lies in some cell
`(u (j + 1), u j]` with `j < n`. -/
lemma exists_cell (u : ℕ → ℝ) (n : ℕ) (t : ℝ) (h0 : t ≤ u 0) (hn : u n < t) :
    ∃ j < n, u (j + 1) < t ∧ t ≤ u j := by
  induction n with
  | zero => exact absurd (hn.trans_le h0) (lt_irrefl _)
  | succ n ih =>
    by_cases h : u n < t
    · obtain ⟨j, hj, hj'⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hj'⟩
    · exact ⟨n, Nat.lt_succ_self n, hn, not_lt.mp h⟩

section Blocks

variable {β : Type*} [Fintype β] [DecidableEq β] (mult : β → ℕ) (θ b s : β → ℝ)

/-- Index type of a block model with replication number `N`. -/
abbrev blockIndex (mult : β → ℕ) (N : ℕ) : Type _ := (Σ g : β, Fin (mult g)) × Fin N

omit [DecidableEq β] in
lemma card_blockIndex (N : ℕ) : Fintype.card (blockIndex mult N) = (∑ g, mult g) * N := by
  simp [blockIndex, Fintype.card_sigma]

omit [DecidableEq β] in
lemma sum_blockIndex (N : ℕ) (F : β → ℝ) :
    ∑ i : blockIndex mult N, F i.1.1 = N * ∑ g, mult g * F g := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The true nulls of a block model: the statistics of the blocks in `β₀`. -/
def blockNulls (β₀ : Finset β) (N : ℕ) : Finset (blockIndex mult N) :=
  univ.filter fun i => i.1.1 ∈ β₀

lemma sum_blockNulls (β₀ : Finset β) (N : ℕ) (F : β → ℝ) :
    ∑ i ∈ blockNulls mult β₀ N, F i.1.1 = N * ∑ g ∈ β₀, mult g * F g := by
  rw [blockNulls, Finset.sum_filter]
  have := sum_blockIndex mult N fun g => if g ∈ β₀ then F g else 0
  rw [this]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ β₀)]
  have h1 : ∑ g ∈ univ.filter (· ∈ β₀), (mult g : ℝ) * (if g ∈ β₀ then F g else 0)
      = ∑ g ∈ β₀, mult g * F g := by
    have : univ.filter (· ∈ β₀) = β₀ := by ext g; simp
    rw [this]
    exact Finset.sum_congr rfl fun g hg => by simp [hg]
  have h2 : ∑ g ∈ univ.filter (fun g => ¬ g ∈ β₀), (mult g : ℝ) * (if g ∈ β₀ then F g else 0)
      = 0 := Finset.sum_eq_zero fun g hg => by
    have : g ∉ β₀ := (mem_filter.mp hg).2
    simp [this]
  rw [h1, h2, add_zero]

/-- The two-sided p-value threshold with cut-off `c`: `u(c) = 2 (1 - Φ(c))`. -/
noncomputable def uTail (c : ℝ) : ℝ := 2 * (1 - Φ c)

lemma uTail_pos (c : ℝ) : 0 < uTail c := by
  have := cdf_gaussian_lt_one c
  unfold uTail; linarith

/-- Conditional probability, given the factor `z`, that a statistic of block `g` exceeds `c`
in absolute value. -/
noncomputable def blockTail (g : β) (z c : ℝ) : ℝ :=
  Φ ((θ g + b g * z - c) / s g) + Φ ((-(θ g + b g * z) - c) / s g)

/-- The normalised conditional mean of the number of statistics of the blocks in `S` exceeding
`c` in absolute value, given the factor `z`. -/
noncomputable def blockG (S : Finset β) (z c : ℝ) : ℝ :=
  (∑ g ∈ S, mult g * blockTail θ b s g z c) / (∑ g, mult g : ℕ)

omit [Fintype β] [DecidableEq β] in
lemma condProb_block (N : ℕ) (hs : ∀ g, 0 < s g) (i : blockIndex mult N) (z : ℝ) {c : ℝ}
    (hc : 0 < c) :
    condProb (fun i : blockIndex mult N => θ i.1.1) (fun i => b i.1.1) (fun i => s i.1.1) i z
      (uTail c) = blockTail θ b s i.1.1 z c :=
  condProb_eq _ _ _ i z hc (hs _)

/-- **Lower bound for the false discovery rate in a block model**, hypotheses quantified over
the factor value in each bin `(zl k, zh k]`. For bin `k`: cut-offs `0 < c k 0, …, c k (n k)`
with `u(c k 0) ≥ α`, a cut-off `bc k > 0` with `u(bc k) ≤ α`, and `f k ≥ 0`. -/
theorem fdr_block_ge {α : ℝ} (hα : 0 < α) (hs : ∀ g, 0 < s g) (β₀ : Finset β) (N : ℕ)
    {𝒦 : Type*} [Fintype 𝒦] (zl zh : 𝒦 → ℝ)
    (hdisj : Pairwise (Function.onFun Disjoint fun k => Set.Ioc (zl k) (zh k)))
    (n : 𝒦 → ℕ) (c : 𝒦 → ℕ → ℝ) (bc f : 𝒦 → ℝ) {η : ℝ} (hη : 0 < η)
    (hN : 1 ≤ η * ((∑ g, mult g : ℕ) * N))
    (hc : ∀ k j, j ≤ n k → 0 < c k j) (hc0 : ∀ k, α ≤ uTail (c k 0))
    (hbc : ∀ k, 0 < bc k) (hbα : ∀ k, uTail (bc k) ≤ α) (hf : ∀ k, 0 ≤ f k)
    (hU : ∀ k, ∀ z ∈ Set.Ioc (zl k) (zh k), ∀ j < n k,
      blockG mult θ b s univ z (c k j) + η ≤ uTail (c k (j + 1)) / α)
    (hL : ∀ k, ∀ z ∈ Set.Ioc (zl k) (zh k),
      uTail (bc k) / α + 2 * η ≤ blockG mult θ b s univ z (bc k))
    (hNull : ∀ k, ∀ z ∈ Set.Ioc (zl k) (zh k), f k + η ≤ blockG mult θ b s β₀ z (bc k)) :
    ∑ k, ENNReal.ofReal (α * f k / uTail (c k (n k))) * ((γ) (Set.Ioc (zl k) (zh k))
        * (1 - (n k + 2 : ℕ) * ENNReal.ofReal (1 / (η ^ 2 * ((∑ g, mult g : ℕ) * N : ℕ)))))
      ≤ fdr (factorMeasure (blockIndex mult N)) (blockNulls mult β₀ N)
          (fun ω => bhReject α (factorP (fun i : blockIndex mult N => θ i.1.1)
            (fun i => b i.1.1) (fun i => s i.1.1) ω)) := by
  set θ' : blockIndex mult N → ℝ := fun i => θ i.1.1 with hθ'
  set b' : blockIndex mult N → ℝ := fun i => b i.1.1 with hb'
  set s' : blockIndex mult N → ℝ := fun i => s i.1.1 with hs'
  set Mtot : ℕ := ∑ g, mult g with hMtot
  have hcard : Fintype.card (blockIndex mult N) = Mtot * N := card_blockIndex mult N
  have hmpos : (0 : ℝ) < (Mtot : ℝ) * N := by
    by_contra h
    have h0 : (Mtot : ℝ) * N ≤ 0 := not_lt.mp h
    nlinarith
  have hMpos : (0 : ℝ) < Mtot := by
    rcases Nat.eq_zero_or_pos Mtot with h0 | h0
    · rw [h0] at hmpos; simp at hmpos
    · exact_mod_cast h0
  have hNpos : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0] at hmpos; simp at hmpos
    · exact_mod_cast h0
  have hsumAll : ∀ z cc, 0 < cc → ∑ i, condProb θ' b' s' i z (uTail cc)
      = (Mtot : ℝ) * N * blockG mult θ b s univ z cc := by
    intro z cc hcc
    have h1 : ∑ i, condProb θ' b' s' i z (uTail cc)
        = ∑ i : blockIndex mult N, blockTail θ b s i.1.1 z cc :=
      Finset.sum_congr rfl fun i _ => condProb_block mult θ b s N hs i z hcc
    rw [h1, sum_blockIndex mult N fun g => blockTail θ b s g z cc, blockG, ← hMtot]
    field_simp
  have hsumNull : ∀ z cc, 0 < cc → ∑ i ∈ blockNulls mult β₀ N, condProb θ' b' s' i z (uTail cc)
      = (Mtot : ℝ) * N * blockG mult θ b s β₀ z cc := by
    intro z cc hcc
    have h1 : ∑ i ∈ blockNulls mult β₀ N, condProb θ' b' s' i z (uTail cc)
        = ∑ i ∈ blockNulls mult β₀ N, blockTail θ b s i.1.1 z cc :=
      Finset.sum_congr rfl fun i _ => condProb_block mult θ b s N hs i z hcc
    rw [h1, sum_blockNulls mult β₀ N fun g => blockTail θ b s g z cc, blockG, ← hMtot]
    field_simp
  have key := fdr_factor_ge θ' b' s' hα (blockNulls mult β₀ N)
    (fun k => Set.Ioc (zl k) (zh k)) (fun k => measurableSet_Ioc) hdisj
    (J := fun k => Fin (n k))
    (fun k j => uTail (c k (j + 1))) (fun k j => uTail (c k j))
    (fun k => uTail (bc k)) (fun k => uTail (c k (n k))) f hη
    (fun k => uTail_pos _) hbα (fun k => uTail_pos _) hf
    (fun k t ht1 ht2 => by
      obtain ⟨j, hj, hj1, hj2⟩ := exists_cell (fun j => uTail (c k j)) (n k) t
        (ht2.trans (hc0 k)) ht1
      exact ⟨⟨j, hj⟩, hj1, hj2⟩)
    (fun k z hz j => by
      rw [hsumAll z _ (hc k j j.2.le), hcard]
      push_cast
      have h := hU k z hz j j.2
      have h2 : (Mtot : ℝ) * N * (blockG mult θ b s univ z (c k j) + η)
          ≤ (Mtot : ℝ) * N * (uTail (c k (j + 1)) / α) :=
        mul_le_mul_of_nonneg_left h hmpos.le
      calc (Mtot : ℝ) * N * blockG mult θ b s univ z (c k j) + η * (Mtot * N)
          = (Mtot : ℝ) * N * (blockG mult θ b s univ z (c k j) + η) := by ring
        _ ≤ (Mtot : ℝ) * N * (uTail (c k (j + 1)) / α) := h2
        _ = (Mtot : ℝ) * N * uTail (c k (j + 1)) / α := by ring)
    (fun k z hz => by
      rw [hsumAll z _ (hbc k), hcard]
      push_cast
      have h := hL k z hz
      have h2 := mul_le_mul_of_nonneg_left h hmpos.le
      have hN' : 1 ≤ η * ((Mtot : ℝ) * N) := hN
      calc (Mtot : ℝ) * N * uTail (bc k) / α + 1
          ≤ (Mtot : ℝ) * N * uTail (bc k) / α + η * (Mtot * N) := by linarith
        _ = (Mtot : ℝ) * N * (uTail (bc k) / α + 2 * η) - η * (Mtot * N) := by ring
        _ ≤ (Mtot : ℝ) * N * blockG mult θ b s univ z (bc k) - η * (Mtot * N) := by linarith)
    (fun k z hz => by
      rw [hsumNull z _ (hbc k), hcard]
      push_cast
      have h := hNull k z hz
      have h2 := mul_le_mul_of_nonneg_left h hmpos.le
      calc (Mtot : ℝ) * N * f k = (Mtot : ℝ) * N * (f k + η) - η * (Mtot * N) := by ring
        _ ≤ (Mtot : ℝ) * N * blockG mult θ b s β₀ z (bc k) - η * (Mtot * N) := by linarith)
  simp only [Fintype.card_fin, hcard] at key
  exact key

/-- Upper bound for `blockTail` over a bin, from monotonicity of `Φ` only. -/
noncomputable def blockTailUpper (g : β) (zl zh c : ℝ) : ℝ :=
  Φ ((max (θ g + b g * zl) (θ g + b g * zh) - c) / s g)
    + Φ ((-min (θ g + b g * zl) (θ g + b g * zh) - c) / s g)

/-- Lower bound for `blockTail` over a bin, from monotonicity of `Φ` only. -/
noncomputable def blockTailLower (g : β) (zl zh c : ℝ) : ℝ :=
  Φ ((min (θ g + b g * zl) (θ g + b g * zh) - c) / s g)
    + Φ ((-max (θ g + b g * zl) (θ g + b g * zh) - c) / s g)

omit [Fintype β] [DecidableEq β] in
lemma affine_mem_of_mem_Ioc (g : β) {zl zh z : ℝ} (hz : z ∈ Set.Ioc zl zh) :
    min (θ g + b g * zl) (θ g + b g * zh) ≤ θ g + b g * z ∧
      θ g + b g * z ≤ max (θ g + b g * zl) (θ g + b g * zh) := by
  rcases le_total 0 (b g) with hb | hb
  · have h1 : b g * zl ≤ b g * z := mul_le_mul_of_nonneg_left hz.1.le hb
    have h2 : b g * z ≤ b g * zh := mul_le_mul_of_nonneg_left hz.2 hb
    exact ⟨(min_le_left _ _).trans (by linarith), le_trans (by linarith) (le_max_right _ _)⟩
  · have h1 : b g * z ≤ b g * zl := mul_le_mul_of_nonpos_left hz.1.le hb
    have h2 : b g * zh ≤ b g * z := mul_le_mul_of_nonpos_left hz.2 hb
    exact ⟨(min_le_right _ _).trans (by linarith), le_trans (by linarith) (le_max_left _ _)⟩

omit [Fintype β] [DecidableEq β] in
lemma blockTail_le_upper (hs : ∀ g, 0 < s g) (g : β) {zl zh z : ℝ} (hz : z ∈ Set.Ioc zl zh)
    (c : ℝ) : blockTail θ b s g z c ≤ blockTailUpper θ b s g zl zh c := by
  obtain ⟨h1, h2⟩ := affine_mem_of_mem_Ioc θ b g hz
  unfold blockTail blockTailUpper
  have hmono : Monotone Φ := monotone_cdf _
  refine add_le_add (hmono ?_) (hmono ?_)
  · exact div_le_div_of_nonneg_right (by linarith) (hs g).le
  · exact div_le_div_of_nonneg_right (by linarith) (hs g).le

omit [Fintype β] [DecidableEq β] in
lemma blockTail_ge_lower (hs : ∀ g, 0 < s g) (g : β) {zl zh z : ℝ} (hz : z ∈ Set.Ioc zl zh)
    (c : ℝ) : blockTailLower θ b s g zl zh c ≤ blockTail θ b s g z c := by
  obtain ⟨h1, h2⟩ := affine_mem_of_mem_Ioc θ b g hz
  unfold blockTail blockTailLower
  have hmono : Monotone Φ := monotone_cdf _
  refine add_le_add (hmono ?_) (hmono ?_)
  · exact div_le_div_of_nonneg_right (by linarith) (hs g).le
  · exact div_le_div_of_nonneg_right (by linarith) (hs g).le

/-- Bin-wise upper bound for `blockG`: a finite expression in values of `Φ`. -/
noncomputable def blockGUpper (S : Finset β) (zl zh c : ℝ) : ℝ :=
  (∑ g ∈ S, mult g * blockTailUpper θ b s g zl zh c) / (∑ g, mult g : ℕ)

/-- Bin-wise lower bound for `blockG`: a finite expression in values of `Φ`. -/
noncomputable def blockGLower (S : Finset β) (zl zh c : ℝ) : ℝ :=
  (∑ g ∈ S, mult g * blockTailLower θ b s g zl zh c) / (∑ g, mult g : ℕ)

omit [DecidableEq β] in
lemma blockG_le_upper (hs : ∀ g, 0 < s g) (S : Finset β) {zl zh z : ℝ}
    (hz : z ∈ Set.Ioc zl zh) (c : ℝ) :
    blockG mult θ b s S z c ≤ blockGUpper mult θ b s S zl zh c := by
  unfold blockG blockGUpper
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun g _ => ?_) (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (blockTail_le_upper θ b s hs g hz c) (Nat.cast_nonneg _)

omit [DecidableEq β] in
lemma blockG_ge_lower (hs : ∀ g, 0 < s g) (S : Finset β) {zl zh z : ℝ}
    (hz : z ∈ Set.Ioc zl zh) (c : ℝ) :
    blockGLower mult θ b s S zl zh c ≤ blockG mult θ b s S z c := by
  unfold blockG blockGLower
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun g _ => ?_) (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (blockTail_ge_lower θ b s hs g hz c) (Nat.cast_nonneg _)

/-- **Lower bound for the false discovery rate in a block model, end-point form.** Every
hypothesis is a finite statement about values of `Φ`. -/
theorem fdr_block_ge_endpoints {α : ℝ} (hα : 0 < α) (hs : ∀ g, 0 < s g) (β₀ : Finset β) (N : ℕ)
    {𝒦 : Type*} [Fintype 𝒦] (zl zh : 𝒦 → ℝ)
    (hdisj : Pairwise (Function.onFun Disjoint fun k => Set.Ioc (zl k) (zh k)))
    (n : 𝒦 → ℕ) (c : 𝒦 → ℕ → ℝ) (bc f : 𝒦 → ℝ) {η : ℝ} (hη : 0 < η)
    (hN : 1 ≤ η * ((∑ g, mult g : ℕ) * N))
    (hc : ∀ k j, j ≤ n k → 0 < c k j) (hc0 : ∀ k, α ≤ uTail (c k 0))
    (hbc : ∀ k, 0 < bc k) (hbα : ∀ k, uTail (bc k) ≤ α) (hf : ∀ k, 0 ≤ f k)
    (hU : ∀ k, ∀ j < n k,
      blockGUpper mult θ b s univ (zl k) (zh k) (c k j) + η ≤ uTail (c k (j + 1)) / α)
    (hL : ∀ k, uTail (bc k) / α + 2 * η ≤ blockGLower mult θ b s univ (zl k) (zh k) (bc k))
    (hNull : ∀ k, f k + η ≤ blockGLower mult θ b s β₀ (zl k) (zh k) (bc k)) :
    ∑ k, ENNReal.ofReal (α * f k / uTail (c k (n k))) * ((γ) (Set.Ioc (zl k) (zh k))
        * (1 - (n k + 2 : ℕ) * ENNReal.ofReal (1 / (η ^ 2 * ((∑ g, mult g : ℕ) * N : ℕ)))))
      ≤ fdr (factorMeasure (blockIndex mult N)) (blockNulls mult β₀ N)
          (fun ω => bhReject α (factorP (fun i : blockIndex mult N => θ i.1.1)
            (fun i => b i.1.1) (fun i => s i.1.1) ω)) :=
  fdr_block_ge mult θ b s hα hs β₀ N zl zh hdisj n c bc f hη hN hc hc0 hbc hbα hf
    (fun k z hz j hj => by
      have h1 := blockG_le_upper mult θ b s hs univ hz (c k j)
      have h2 := hU k j hj
      linarith)
    (fun k z hz => (hL k).trans (blockG_ge_lower mult θ b s hs univ hz _))
    (fun k z hz => (hNull k).trans (blockG_ge_lower mult θ b s hs β₀ hz _))

/-- **The certificate sum exceeding one forces a violation of the level.** In the setting of
`fdr_block_ge_endpoints`, with at most `nmax - 2` cells per bin, if
`S = ∑ k, f k / u(c k (n k)) * (Φ(zh k) - Φ(zl k)) > 1`, then for every replication number `N`
with `1 ≤ η M N` and `nmax S < (S - 1) η² M N` (`M` the total multiplicity) the false discovery
rate of Benjamini–Hochberg at level `α` is strictly larger than `α`. -/
theorem fdr_block_gt {α : ℝ} (hα : 0 < α) (hs : ∀ g, 0 < s g) (β₀ : Finset β) (N : ℕ)
    {𝒦 : Type*} [Fintype 𝒦] (zl zh : 𝒦 → ℝ) (hzz : ∀ k, zl k ≤ zh k)
    (hdisj : Pairwise (Function.onFun Disjoint fun k => Set.Ioc (zl k) (zh k)))
    (n : 𝒦 → ℕ) (c : 𝒦 → ℕ → ℝ) (bc f : 𝒦 → ℝ) {η : ℝ} (hη : 0 < η)
    (hN : 1 ≤ η * ((∑ g, mult g : ℕ) * N))
    (hc : ∀ k j, j ≤ n k → 0 < c k j) (hc0 : ∀ k, α ≤ uTail (c k 0))
    (hbc : ∀ k, 0 < bc k) (hbα : ∀ k, uTail (bc k) ≤ α) (hf : ∀ k, 0 ≤ f k)
    (hU : ∀ k, ∀ j < n k,
      blockGUpper mult θ b s univ (zl k) (zh k) (c k j) + η ≤ uTail (c k (j + 1)) / α)
    (hL : ∀ k, uTail (bc k) / α + 2 * η ≤ blockGLower mult θ b s univ (zl k) (zh k) (bc k))
    (hNull : ∀ k, f k + η ≤ blockGLower mult θ b s β₀ (zl k) (zh k) (bc k))
    (nmax : ℕ) (hnmax : ∀ k, n k + 2 ≤ nmax)
    (hS : 1 < ∑ k, f k / uTail (c k (n k)) * (Φ (zh k) - Φ (zl k)))
    (hN2 : nmax * (∑ k, f k / uTail (c k (n k)) * (Φ (zh k) - Φ (zl k)))
      < ((∑ k, f k / uTail (c k (n k)) * (Φ (zh k) - Φ (zl k))) - 1)
        * (η ^ 2 * ((∑ g, mult g : ℕ) * N))) :
    ENNReal.ofReal α < fdr (factorMeasure (blockIndex mult N)) (blockNulls mult β₀ N)
      (fun ω => bhReject α (factorP (fun i : blockIndex mult N => θ i.1.1)
        (fun i => b i.1.1) (fun i => s i.1.1) ω)) := by
  set S := ∑ k, f k / uTail (c k (n k)) * (Φ (zh k) - Φ (zl k)) with hSdef
  set Mtot : ℕ := ∑ g, mult g with hMtot
  have hmpos : (0 : ℝ) < (Mtot : ℝ) * N := by
    by_contra h
    have h0 : (Mtot : ℝ) * N ≤ 0 := not_lt.mp h
    nlinarith
  set x : ℝ := 1 / (η ^ 2 * ((Mtot : ℝ) * N)) with hx
  have hden : 0 < η ^ 2 * ((Mtot : ℝ) * N) := mul_pos (pow_pos hη 2) hmpos
  have hx0 : 0 < x := by rw [hx]; positivity
  have hkey : 1 < S * (1 - nmax * x) := by
    have h1 : (nmax : ℝ) * S * x < S - 1 := by
      rw [hx, mul_one_div, div_lt_iff₀ hden]
      exact hN2
    nlinarith
  have hpos1 : 0 < 1 - (nmax : ℝ) * x := by
    by_contra h
    have h0 : 1 - (nmax : ℝ) * x ≤ 0 := not_lt.mp h
    have hS0 : 0 < S := by linarith
    nlinarith
  have hbound := fdr_block_ge_endpoints mult θ b s hα hs β₀ N zl zh hdisj n c bc f hη hN hc hc0
    hbc hbα hf hU hL hNull
  refine lt_of_lt_of_le ?_ hbound
  have hterm : ∀ k, ENNReal.ofReal (α * (f k / uTail (c k (n k)) * (Φ (zh k) - Φ (zl k)))
        * (1 - nmax * x))
      ≤ ENNReal.ofReal (α * f k / uTail (c k (n k))) * ((γ) (Set.Ioc (zl k) (zh k))
        * (1 - (n k + 2 : ℕ) * ENNReal.ofReal (1 / (η ^ 2 * ((Mtot * N : ℕ) : ℝ))))) := by
    intro k
    have ha : 0 ≤ α * f k / uTail (c k (n k)) :=
      div_nonneg (mul_nonneg hα.le (hf k)) (uTail_pos _).le
    have hd : 0 ≤ Φ (zh k) - Φ (zl k) := sub_nonneg.mpr (monotone_cdf _ (hzz k))
    have h1 : ENNReal.ofReal (1 - nmax * x)
        ≤ 1 - (n k + 2 : ℕ) * ENNReal.ofReal (1 / (η ^ 2 * ((Mtot * N : ℕ) : ℝ))) := by
      have hcast : (1 : ℝ) / (η ^ 2 * ((Mtot * N : ℕ) : ℝ)) = x := by
        rw [hx]; push_cast; rfl
      rw [hcast, ← ENNReal.ofReal_natCast (n k + 2), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      have hle : ((n k + 2 : ℕ) : ℝ) * x ≤ nmax * x := by
        have : ((n k + 2 : ℕ) : ℝ) ≤ nmax := by exact_mod_cast hnmax k
        exact mul_le_mul_of_nonneg_right this hx0.le
      calc ENNReal.ofReal (1 - nmax * x)
          ≤ ENNReal.ofReal (1 - ((n k + 2 : ℕ) : ℝ) * x) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ = ENNReal.ofReal 1 - ENNReal.ofReal (((n k + 2 : ℕ) : ℝ) * x) :=
            ENNReal.ofReal_sub _ (by positivity)
        _ = 1 - ENNReal.ofReal (((n k + 2 : ℕ) : ℝ) * x) := by rw [ENNReal.ofReal_one]
    calc ENNReal.ofReal (α * (f k / uTail (c k (n k)) * (Φ (zh k) - Φ (zl k)))
          * (1 - nmax * x))
        = ENNReal.ofReal (α * f k / uTail (c k (n k))) * (ENNReal.ofReal (Φ (zh k) - Φ (zl k))
            * ENNReal.ofReal (1 - nmax * x)) := by
          rw [← ENNReal.ofReal_mul hd, ← ENNReal.ofReal_mul ha]
          congr 1; ring
      _ ≤ _ := by
          rw [gaussianReal_Ioc]
          gcongr
  calc ENNReal.ofReal α < ENNReal.ofReal (α * (S * (1 - nmax * x))) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        nlinarith
    _ = ENNReal.ofReal (∑ k, α * (f k / uTail (c k (n k)) * (Φ (zh k) - Φ (zl k)))
          * (1 - nmax * x)) := by
        congr 1
        rw [hSdef, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ k, ENNReal.ofReal (α * (f k / uTail (c k (n k)) * (Φ (zh k) - Φ (zl k)))
          * (1 - nmax * x)) := by
        refine ENNReal.ofReal_sum_of_nonneg fun k _ => ?_
        have hd : 0 ≤ Φ (zh k) - Φ (zl k) := sub_nonneg.mpr (monotone_cdf _ (hzz k))
        have hq : 0 ≤ f k / uTail (c k (n k)) := div_nonneg (hf k) (uTail_pos _).le
        exact mul_nonneg (mul_nonneg hα.le (mul_nonneg hq hd)) hpos1.le
    _ ≤ _ := Finset.sum_le_sum fun k _ => hterm k

end Blocks

/-- **A block model as an instance of the two-sided Gaussian setting.** If the unit-variance
block model (`b g ^ 2 + s g ^ 2 = 1`, mean zero on the null blocks) has false discovery rate
above `α` for the Benjamini–Hochberg procedure, then there are `n`, a probability space, a
jointly Gaussian vector `Z : Fin n → Ω → ℝ` with unit variances and a set `H₀` of mean-zero
coordinates for which Benjamini–Hochberg applied to the two-sided p-values `2 (1 - Φ(|Z i|))`
has false discovery rate above `α`. -/
theorem exists_gaussian_fdr_gt_of_block {β : Type} [Fintype β] [DecidableEq β] (mult : β → ℕ)
    (θ b s : β → ℝ) (hbs : ∀ g, b g ^ 2 + s g ^ 2 = 1) (β₀ : Finset β)
    (hθ : ∀ g ∈ β₀, θ g = 0) (N : ℕ) {α : ℝ}
    (h : ENNReal.ofReal α < fdr (factorMeasure (blockIndex mult N)) (blockNulls mult β₀ N)
      (fun ω => bhReject α (factorP (fun i : blockIndex mult N => θ i.1.1)
        (fun i => b i.1.1) (fun i => s i.1.1) ω))) :
    ∃ (n : ℕ) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : Fin n → Ω → ℝ) (H₀ : Finset (Fin n)), (∀ i, Measurable (Z i)) ∧
      IsGaussian (P.map fun ω i => Z i ω) ∧ (∀ i, Var[Z i; P] = 1) ∧
      (∀ i ∈ H₀, ∫ ω, Z i ω ∂P = 0) ∧
      ENNReal.ofReal α < fdr P H₀ (fun ω => bhReject α fun i => 2 * (1 - Φ |Z i ω|)) := by
  set ι := blockIndex mult N with hι
  set θ' : ι → ℝ := fun i => θ i.1.1 with hθ'
  set b' : ι → ℝ := fun i => b i.1.1 with hb'
  set s' : ι → ℝ := fun i => s i.1.1 with hs'
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  refine ⟨Fintype.card ι, ℝ × (ι → ℝ), inferInstance, factorMeasure ι, inferInstance,
    fun j => factorStat θ' b' s' (e j), (blockNulls mult β₀ N).map e.symm.toEmbedding,
    fun j => measurable_factorStat θ' b' s' (e j), ?_, ?_, ?_, ?_⟩
  · exact isGaussian_map_factor (fun j => θ' (e j)) (fun j => b' (e j)) (fun j => s' (e j)) e
  · intro j
    exact variance_factorStat θ' b' s' (e j) (hbs _)
  · intro j hj
    rw [integral_factorStat θ' b' s' (e j) (hbs _)]
    rw [Finset.mem_map_equiv, Equiv.symm_symm] at hj
    exact hθ _ (mem_filter.mp hj).2
  · have hfdr : fdr (factorMeasure ι) ((blockNulls mult β₀ N).map e.symm.toEmbedding)
          (fun ω => bhReject α fun j => 2 * (1 - Φ |factorStat θ' b' s' (e j) ω|))
        = fdr (factorMeasure ι) (blockNulls mult β₀ N)
          (fun ω => bhReject α (factorP θ' b' s' ω)) := by
      unfold fdr
      refine lintegral_congr fun ω => ?_
      have : (bhReject α fun j => 2 * (1 - Φ |factorStat θ' b' s' (e j) ω|))
          = bhReject α (factorP θ' b' s' ω ∘ e) := rfl
      simp only [this, bhReject_reindex, fdp_map]
    rw [hfdr]
    exact h

end Applied.MultipleTesting
