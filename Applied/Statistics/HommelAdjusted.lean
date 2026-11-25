import Applied.Statistics.Simes

/-!
# Hommel-adjusted p-values

Hommel's procedure `hommel α p` is the closed test built from Simes local tests. Its adjusted
p-value is the closed-testing adjusted value: the largest Simes p-value among the intersection
hypotheses containing `i`.

* `simesCount p ω S j`: the number of `l ∈ S` with `p l ω ≤ p j ω`.
* `simesPValue p ω S`: the Simes p-value `min_{j ∈ S} |S| p_j / #{l ∈ S | p_l ≤ p_j}` of the
  intersection hypothesis `S` (zero for `S = ∅`, a value never used below). Without ties this is
  the textbook `min_k |S| p_(k) / k`.
* `simesLocal_iff_simesPValue_le`: for `α ≥ 0` and non-empty `S`, the Simes local test rejects
  `S` at level `α` exactly when the Simes p-value is at most `α`.
* `hommelAdjusted p ω i = max_{S ∋ i} simesPValue p ω S` (not capped at one).
* `mem_hommel_iff_hommelAdjusted_le`: for `α ≥ 0`, Hommel's procedure rejects `i` iff its
  adjusted p-value is at most `α`. `mem_hommel_mono`, `le_hommelAdjusted`.
-/

open Finset

namespace Applied.MultipleTesting

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The number of members `l` of `S` with `p l ω ≤ p j ω`. -/
noncomputable def simesCount (p : ι → Ω → ℝ) (ω : Ω) (S : Finset ι) (j : ι) : ℕ :=
  (univ.filter fun l : S => p l ω ≤ p j ω).card

/-- The Simes p-value of the intersection hypothesis `S`:
`min_{j ∈ S} |S| p_j / #{l ∈ S | p_l ≤ p_j}`; zero when `S` is empty. -/
noncomputable def simesPValue (p : ι → Ω → ℝ) (ω : Ω) (S : Finset ι) : ℝ :=
  if h : S.Nonempty then
    S.inf' h fun j => (S.card : ℝ) * p j ω / simesCount p ω S j
  else 0

omit [Fintype ι] [DecidableEq ι] in
lemma simesCount_pos (p : ι → Ω → ℝ) (ω : Ω) {S : Finset ι} {j : ι} (hj : j ∈ S) :
    0 < simesCount p ω S j := by
  classical
  unfold simesCount
  exact Finset.card_pos.mpr ⟨⟨j, hj⟩, by simp⟩

omit [Fintype ι] [DecidableEq ι] in
/-- For `α ≥ 0` the Simes local test rejects `S` exactly when some `j ∈ S` has
`p_j ≤ α #{l ∈ S | p_l ≤ p_j} / |S|`. -/
lemma simesLocal_iff_exists {α : ℝ} (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω) (S : Finset ι) :
    simesLocal α p S ω ↔
      ∃ j ∈ S, p j ω ≤ α * simesCount p ω S j / S.card := by
  classical
  unfold simesLocal
  constructor
  · intro h
    set k := bhK α fun j : S => p j ω with hk
    have hkc : k ≤ bhCount α (fun j : S => p j ω) k := bhK_le_bhCount _
    set F := univ.filter fun l : S => p l ω ≤ α * k / Fintype.card S with hF
    have hFk : k ≤ F.card := hkc
    have hFne : F.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le h hFk)
    obtain ⟨j, hjF, hjmax⟩ := Finset.exists_max_image F (fun l : S => p l ω) hFne
    refine ⟨j, j.2, ?_⟩
    have hjle : p j ω ≤ α * k / Fintype.card S := (mem_filter.mp hjF).2
    have hsub : F ⊆ univ.filter fun l : S => p l ω ≤ p j ω := by
      intro l hl
      exact mem_filter.mpr ⟨mem_univ _, hjmax l hl⟩
    have hkc' : k ≤ simesCount p ω S j := hFk.trans (Finset.card_le_card hsub)
    rw [Fintype.card_coe] at hjle
    refine hjle.trans ?_
    have : (k : ℝ) ≤ simesCount p ω S j := by exact_mod_cast hkc'
    gcongr
  · rintro ⟨j, hj, hle⟩
    have hc := simesCount_pos p ω hj
    refine Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
      (lt_of_lt_of_le hc (le_bhK _ ?_ ?_)))
    · rw [Fintype.card_coe]
      unfold simesCount
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_coe S)
    · unfold bhCount simesCount
      refine Finset.card_le_card fun l hl => ?_
      simp only [mem_filter, mem_univ, true_and] at hl ⊢
      rw [Fintype.card_coe]
      exact hl.trans hle

omit [Fintype ι] [DecidableEq ι] in
/-- **Simes p-value characterises the Simes test.** For `α ≥ 0` and non-empty `S`, the Simes
local test rejects `S` at level `α` iff the Simes p-value of `S` is at most `α`. -/
theorem simesLocal_iff_simesPValue_le {α : ℝ} (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω)
    {S : Finset ι} (hS : S.Nonempty) :
    simesLocal α p S ω ↔ simesPValue p ω S ≤ α := by
  rw [simesLocal_iff_exists hα, simesPValue, dif_pos hS, Finset.inf'_le_iff]
  refine exists_congr fun j => and_congr_right fun hj => ?_
  have hc : (0 : ℝ) < simesCount p ω S j := by exact_mod_cast simesCount_pos p ω hj
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [div_le_iff₀ hc, le_div_iff₀ hn, mul_comm (p j ω)]

/-- The Hommel-adjusted p-value of hypothesis `i` (not capped at one): the largest Simes
p-value among the intersection hypotheses `S` with `i ∈ S`. -/
noncomputable def hommelAdjusted (p : ι → Ω → ℝ) (ω : Ω) (i : ι) : ℝ :=
  (univ.filter fun S : Finset ι => i ∈ S).sup'
    (show (univ.filter fun S : Finset ι => i ∈ S).Nonempty from
      ⟨{i}, mem_filter.mpr ⟨mem_univ _, mem_singleton_self i⟩⟩) (simesPValue p ω)

lemma hommelAdjusted_le_iff (p : ι → Ω → ℝ) (ω : Ω) (i : ι) (a : ℝ) :
    hommelAdjusted p ω i ≤ a ↔ ∀ S : Finset ι, i ∈ S → simesPValue p ω S ≤ a := by
  unfold hommelAdjusted
  rw [Finset.sup'_le_iff]
  simp

/-- **Hommel-adjusted p-values characterise Hommel's procedure.** For every level `α ≥ 0`,
Hommel's procedure rejects `i` exactly when its adjusted p-value is at most `α`. -/
theorem mem_hommel_iff_hommelAdjusted_le {α : ℝ} (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω)
    (i : ι) : i ∈ hommel α p ω ↔ hommelAdjusted p ω i ≤ α := by
  classical
  rw [hommelAdjusted_le_iff]
  simp only [hommel, closedTest, mem_filter, mem_univ, true_and]
  exact forall_congr' fun S => forall_congr' fun hi =>
    simesLocal_iff_simesPValue_le hα p ω ⟨i, hi⟩

/-- The set rejected by Hommel's procedure, in terms of adjusted p-values (`α ≥ 0`). -/
theorem hommel_eq_filter_hommelAdjusted {α : ℝ} (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω) :
    hommel α p ω = univ.filter fun i => hommelAdjusted p ω i ≤ α := by
  ext i
  rw [mem_hommel_iff_hommelAdjusted_le hα]
  simp

/-- Hommel's procedure rejects more at larger levels (for `0 ≤ α ≤ β`). -/
theorem mem_hommel_mono {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (p : ι → Ω → ℝ) (ω : Ω)
    {i : ι} (h : i ∈ hommel α p ω) : i ∈ hommel β p ω := by
  rw [mem_hommel_iff_hommelAdjusted_le hα] at h
  rw [mem_hommel_iff_hommelAdjusted_le (hα.trans hαβ)]
  exact h.trans hαβ

omit [Fintype ι] [DecidableEq ι] in
/-- The Simes p-value of a singleton is the p-value itself. -/
lemma simesPValue_singleton (p : ι → Ω → ℝ) (ω : Ω) (i : ι) :
    simesPValue p ω {i} = p i ω := by
  classical
  rw [simesPValue, dif_pos (singleton_nonempty i), Finset.inf'_singleton, card_singleton]
  have h1 : simesCount p ω {i} i = 1 := by
    have hle : simesCount p ω {i} i ≤ 1 := by
      unfold simesCount
      exact (Finset.card_le_univ _).trans_eq (by simp)
    have := simesCount_pos p ω (mem_singleton_self i)
    omega
  rw [h1]
  simp

/-- Every p-value is at most its Hommel adjustment (no sign condition needed). -/
theorem le_hommelAdjusted (p : ι → Ω → ℝ) (ω : Ω) (i : ι) :
    p i ω ≤ hommelAdjusted p ω i := by
  rw [← simesPValue_singleton p ω i]
  unfold hommelAdjusted
  exact Finset.le_sup' (simesPValue p ω) (mem_filter.mpr ⟨mem_univ _, mem_singleton_self i⟩)

/-- The capped version, for levels `0 ≤ α < 1`. -/
theorem mem_hommel_iff_min_one_hommelAdjusted_le {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (p : ι → Ω → ℝ) (ω : Ω) (i : ι) :
    i ∈ hommel α p ω ↔ min 1 (hommelAdjusted p ω i) ≤ α := by
  rw [mem_hommel_iff_hommelAdjusted_le hα, min_le_iff]
  exact ⟨Or.inr, fun h => h.resolve_left (not_le.mpr hα1)⟩

end Applied.MultipleTesting
