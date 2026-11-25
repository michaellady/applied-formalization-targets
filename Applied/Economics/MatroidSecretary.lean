import Applied.Economics.MatroidSecretaryModel

/-!
# The matroid secretary problem: the threshold rule and rank one

The model (`ArrivalOrder`, `OnlineAlg`, `Accepts`, `selected`, `expWeight`, `IsFeasible`,
`IsCompetitive`, `HasCompetitiveRandomized`) and the trivial algorithms `never` and
`firstNonloop` are in `Applied/Economics/MatroidSecretaryModel.lean`, which this file imports
and re-exports; importing this file gives everything it gave before the model was split off.

## Results

* `thresholdRule m κ`: skip the first `m` arrivals, then accept the first arrival whose key
  (`κ` of the element and its weight, in a linear order) is strictly larger than the keys of
  all earlier arrivals. `thresholdRule_success`: with `m = ⌊n/2⌋` and injective keys, the
  element of largest key is accepted in at least `n!/4` of the `n!` arrival orders.
* `secretary_half_rule`: the classical secretary problem. For distinct weights, the rule
  "skip `⌊n/2⌋` arrivals, then accept the first arrival heavier than everything before it"
  accepts the heaviest element in at least a quarter of the arrival orders.
* `rankOne E`: the rank-one uniform matroid on `E` (independent = at most one element).
  `exists_isCompetitive_rankOne`: it has a feasible deterministic `1/4`-competitive online
  algorithm, for arbitrary non-negative weights (ties are broken by a fixed order on `E`).

## Not in this file

The optimal constant `1/e` for the classical problem is in `SecretaryOneOverE.lean`; matroids
of higher rank are in the other `MatroidSecretary*.lean` files.
-/

open Finset Function

open scoped Nat

open Classical

noncomputable section

namespace Applied.Economics.MatroidSecretary

variable {E : Type*} [Fintype E]

/-! ### The threshold rule and the classical secretary problem -/

section Threshold

variable {α : Type*} [LinearOrder α]

/-- Skip the first `m` arrivals; then accept the first arrival whose key `κ` is strictly
larger than the keys of all earlier arrivals. In terms of the prefix `h` of the first `k + 1`
arrivals: the current arrival `h (Fin.last k)` is accepted iff `m ≤ k`, its key is strictly
larger than the keys of all earlier arrivals, and no arrival at a time in `[m, k)` was a
strict record, i.e. each of them has key at most the key of one of the first `m` arrivals. -/
def thresholdRule (m : ℕ) (κ : E × ℝ → α) : OnlineAlg E := fun k h =>
  m ≤ k ∧ (∀ j : Fin (k + 1), (j : ℕ) < k → κ (h j) < κ (h (Fin.last k))) ∧
    ∀ i : Fin (k + 1), m ≤ (i : ℕ) → (i : ℕ) < k →
      ∃ j : Fin (k + 1), (j : ℕ) < m ∧ κ (h i) ≤ κ (h j)

lemma accepts_thresholdRule (m : ℕ) (κ : E × ℝ → α) (σ : ArrivalOrder E) (w : E → ℝ) (e : E) :
    Accepts (thresholdRule m κ) σ w e ↔
      m ≤ (σ.symm e : ℕ) ∧
        (∀ i : Fin (Fintype.card E), i < σ.symm e → κ (σ i, w (σ i)) < κ (e, w e)) ∧
        ∀ i : Fin (Fintype.card E), m ≤ (i : ℕ) → i < σ.symm e →
          ∃ j : Fin (Fintype.card E), (j : ℕ) < m ∧ κ (σ i, w (σ i)) ≤ κ (σ j, w (σ j)) := by
  have hlast : arrivals σ w (σ.symm e) (Fin.last _) = (e, w e) := by
    have : Fin.castLE (σ.symm e).isLt (Fin.last (σ.symm e : ℕ)) = σ.symm e := Fin.ext rfl
    simp [arrivals, this]
  have harr : ∀ j : Fin ((σ.symm e : ℕ) + 1), arrivals σ w (σ.symm e) j =
      (σ (Fin.castLE (σ.symm e).isLt j), w (σ (Fin.castLE (σ.symm e).isLt j))) := fun _ => rfl
  have hlift : ∀ i : Fin (Fintype.card E), i < σ.symm e →
      ∃ j : Fin ((σ.symm e : ℕ) + 1), (j : ℕ) = i ∧ Fin.castLE (σ.symm e).isLt j = i :=
    fun i hi => ⟨⟨i, Nat.lt_succ_of_lt hi⟩, rfl, Fin.ext rfl⟩
  unfold Accepts thresholdRule
  rw [hlast]
  refine and_congr_right fun _ => and_congr ⟨fun h i hi => ?_, fun h j hj => ?_⟩
    ⟨fun h i hmi hi => ?_, fun h i hmi hi => ?_⟩
  · obtain ⟨j, hj, hji⟩ := hlift i hi
    have := h j (by rw [hj]; exact hi)
    rwa [harr, hji] at this
  · rw [harr]
    exact h _ (by simpa [Fin.lt_def] using hj)
  · obtain ⟨j, hj, hji⟩ := hlift i hi
    obtain ⟨j', hj', hle⟩ := h j (by rw [hj]; exact hmi) (by rw [hj]; exact hi)
    refine ⟨Fin.castLE (σ.symm e).isLt j', by simpa using hj', ?_⟩
    rwa [harr, harr, hji] at hle
  · obtain ⟨j', hj', hle⟩ := h (Fin.castLE (σ.symm e).isLt i) (by simpa using hmi)
      (by simpa [Fin.lt_def] using hi)
    have hj'' : j' < σ.symm e := by
      rw [Fin.lt_def]
      have : (i : ℕ) < (σ.symm e : ℕ) := hi
      omega
    obtain ⟨j, hj, hji⟩ := hlift j' hj''
    refine ⟨j, by rw [hj]; exact hj', ?_⟩
    rw [harr, harr, hji]
    exact hle

/-- The threshold rule accepts at most one element, whatever the arrival order, the weights
and the key. -/
theorem selected_thresholdRule_subsingleton (m : ℕ) (κ : E × ℝ → α) (σ : ArrivalOrder E)
    (w : E → ℝ) : (selected (thresholdRule m κ) σ w : Set E).Subsingleton := by
  have key : ∀ e e' : E, Accepts (thresholdRule m κ) σ w e → Accepts (thresholdRule m κ) σ w e' →
      ¬ σ.symm e < σ.symm e' := by
    intro e e' he he' hlt
    rw [accepts_thresholdRule] at he he'
    obtain ⟨j, hj, hle⟩ := he'.2.2 (σ.symm e) he.1 hlt
    have hlt' := he.2.1 j (by rw [Fin.lt_def]; omega)
    rw [Equiv.apply_symm_apply] at hle
    exact absurd hlt' (not_lt.2 hle)
  intro e he e' he'
  rw [Finset.mem_coe, mem_selected] at he he'
  rcases lt_trichotomy (σ.symm e) (σ.symm e') with h | h | h
  · exact absurd h (key e e' he he')
  · exact σ.symm.injective h
  · exact absurd h (key e' e he' he)

/-- Two distinct points can be moved to two distinct points by a permutation. -/
private lemma exists_perm_two {β : Type*} {i j i' j' : β} (h : i ≠ j) (h' : i' ≠ j') :
    ∃ π : Equiv.Perm β, π i' = i ∧ π j' = j := by
  have h1 : Equiv.swap i' i j' ≠ i := by
    intro hc
    have : Equiv.swap i' i j' = Equiv.swap i' i i' := by rw [hc, Equiv.swap_apply_left]
    exact h' ((Equiv.swap i' i).injective this).symm
  refine ⟨(Equiv.swap i' i).trans (Equiv.swap j (Equiv.swap i' i j')), ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h h1.symm]
  · rw [Equiv.trans_apply, Equiv.swap_apply_right]

/-- Under a uniformly random arrival order, the pair of arrival times of two distinct
elements is uniform over pairs of distinct times: for a set `T` of such pairs,
`#{σ | (σ⁻¹ a, σ⁻¹ b) ∈ T} * (n * (n - 1)) = #T * n!`. -/
lemma card_orders_pair_mem (a b : E) (hab : a ≠ b)
    (T : Finset (Fin (Fintype.card E) × Fin (Fintype.card E))) (hT : ∀ p ∈ T, p.1 ≠ p.2) :
    #{σ : ArrivalOrder E | (σ.symm a, σ.symm b) ∈ T} *
        (Fintype.card E * (Fintype.card E - 1)) = #T * (Fintype.card E)! := by
  let pos : ArrivalOrder E → Fin (Fintype.card E) × Fin (Fintype.card E) := fun σ => (σ.symm a, σ.symm b)
  let N : Fin (Fintype.card E) × Fin (Fintype.card E) → ℕ := fun p => #{σ : ArrivalOrder E | pos σ = p}
  have hN : ∀ p p' : Fin (Fintype.card E) × Fin (Fintype.card E), p.1 ≠ p.2 → p'.1 ≠ p'.2 → N p = N p' := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h h'
    obtain ⟨π, hπ1, hπ2⟩ : ∃ π : Equiv.Perm (Fin (Fintype.card E)), π i' = i ∧ π j' = j :=
      exists_perm_two h h'
    refine Finset.card_equiv (π.symm.equivCongr (Equiv.refl E)) fun σ => ?_
    simp only [mem_filter, mem_univ, true_and, pos, Prod.mk.injEq]
    have e1 : ∀ x : E, ((π.symm.equivCongr (Equiv.refl E)) σ).symm x = π.symm (σ.symm x) := by
      intro x
      rw [Equiv.symm_apply_eq]
      simp
    rw [e1, e1, Equiv.symm_apply_eq (e := π), Equiv.symm_apply_eq (e := π), hπ1, hπ2]
  have hoff : ∀ σ : ArrivalOrder E, pos σ ∈ (univ : Finset (Fin (Fintype.card E))).offDiag := by
    intro σ
    simp only [mem_offDiag, mem_univ, true_and, pos]
    exact fun h => hab (σ.symm.injective h)
  have hfib : ∀ S : Finset (Fin (Fintype.card E) × Fin (Fintype.card E)),
      #{σ : ArrivalOrder E | pos σ ∈ S} = ∑ p ∈ S, N p := by
    intro S
    rw [Finset.card_eq_sum_card_fiberwise (s := univ.filter fun σ : ArrivalOrder E => pos σ ∈ S)
      (f := pos) (t := S) (fun σ hσ => (mem_filter.1 (mem_coe.1 hσ)).2)]
    refine Finset.sum_congr rfl fun p hp => ?_
    congr 1
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hp, h⟩⟩
  rcases T.eq_empty_or_nonempty with hT0 | ⟨p₀, hp₀⟩
  · simp [hT0]
  have htot : (Fintype.card E * (Fintype.card E - 1)) * N p₀ = (Fintype.card E)! := by
    have h1 : #{σ : ArrivalOrder E | pos σ ∈ (univ : Finset (Fin (Fintype.card E))).offDiag} = (Fintype.card E)! := by
      rw [Finset.filter_true_of_mem fun σ _ => hoff σ, Finset.card_univ,
        Fintype.card_equiv (Fintype.equivFin E).symm, Fintype.card_fin]
    rw [hfib, Finset.sum_congr rfl fun p hp => hN p p₀ (mem_offDiag.1 hp).2.2 (hT p₀ hp₀),
      Finset.sum_const, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      at h1
    rw [← h1, Nat.mul_sub_one]
  change #{σ : ArrivalOrder E | pos σ ∈ T} * (Fintype.card E * (Fintype.card E - 1)) = #T * (Fintype.card E)!
  rw [hfib, Finset.sum_congr rfl fun p hp => hN p p₀ (hT p hp) (hT p₀ hp₀), Finset.sum_const,
    smul_eq_mul, ← htot]
  ring

private lemma quarter_arith (n : ℕ) : n * (n - 1) ≤ 4 * (n / 2 * (n - n / 2)) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases k with _ | k
    · simp
    · have h1 : 2 * (k + 1) / 2 = k + 1 := by omega
      have h2 : 2 * (k + 1) - (k + 1) = k + 1 := by omega
      have h3 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [h1, h2, h3]
      nlinarith
  · have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : 2 * k + 1 - k = k + 1 := by omega
    have h3 : 2 * k + 1 - 1 = 2 * k := by omega
    rw [h1, h2, h3]
    nlinarith

/-- **Secretary problem, key form.** Let `n = |E|` and let the keys `κ (e, w e)` be pairwise
distinct, with `b` the element of largest key. The rule "skip the first `⌊n/2⌋` arrivals, then
accept the first arrival whose key exceeds all earlier keys" accepts `b` in at least `n!/4` of
the `n!` arrival orders. -/
theorem thresholdRule_success (κ : E × ℝ → α) (w : E → ℝ)
    (hinj : Injective fun e => κ (e, w e)) (b : E) (hb : ∀ e, κ (e, w e) ≤ κ (b, w b)) :
    (Fintype.card E)! ≤
      4 * #{σ : ArrivalOrder E | b ∈ selected (thresholdRule (Fintype.card E / 2) κ) σ w} := by
  set n := Fintype.card E with hn
  have hblt : ∀ e, e ≠ b → κ (e, w e) < κ (b, w b) := fun e he =>
    lt_of_le_of_ne (hb e) fun h => he (hinj h)
  have hnpos : 0 < n := Fintype.card_pos_iff.2 ⟨b⟩
  rcases Nat.lt_or_ge 1 n with hn2 | hn1
  · -- at least two elements: let `a` have the second largest key
    have hne : (univ.erase b : Finset E).Nonempty := by
      obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card hn2 b
      exact ⟨a, by simp [ha]⟩
    obtain ⟨a, ha, hamax⟩ := Finset.exists_max_image (univ.erase b) (fun e => κ (e, w e)) hne
    have hab : a ≠ b := (Finset.mem_erase.1 ha).1
    set T : Finset (Fin n × Fin n) :=
      univ.filter fun p => (p.1 : ℕ) < n / 2 ∧ n / 2 ≤ (p.2 : ℕ) with hTdef
    have hT : ∀ p ∈ T, p.1 ≠ p.2 := by
      intro p hp h
      rw [hTdef, mem_filter] at hp
      rw [h] at hp
      omega
    have hTcard : #T = n / 2 * (n - n / 2) := by
      have hprod : T = (univ.filter fun i : Fin n => (i : ℕ) < n / 2) ×ˢ
          (univ.filter fun i : Fin n => n / 2 ≤ (i : ℕ)) := by
        ext p; simp [hTdef]
      have hc1 : #(univ.filter fun i : Fin n => (i : ℕ) < n / 2) = n / 2 := by
        rw [Fin.card_filter_val_lt]; omega
      have hc2 : #(univ.filter fun i : Fin n => n / 2 ≤ (i : ℕ)) = n - n / 2 := by
        have : (univ.filter fun i : Fin n => n / 2 ≤ (i : ℕ)) =
            (univ.filter fun i : Fin n => (i : ℕ) < n / 2)ᶜ := by
          ext i; simp
        rw [this, Finset.card_compl, hc1, Fintype.card_fin]
      rw [hprod, Finset.card_product, hc1, hc2]
    have hcount := card_orders_pair_mem a b hab T hT
    have hsub : (univ.filter fun σ : ArrivalOrder E => (σ.symm a, σ.symm b) ∈ T) ⊆
        univ.filter fun σ : ArrivalOrder E =>
          b ∈ selected (thresholdRule (n / 2) κ) σ w := by
      intro σ hσ
      rw [mem_filter, hTdef, mem_filter] at hσ
      obtain ⟨-, -, h1, h2⟩ := hσ
      rw [mem_filter, mem_selected, accepts_thresholdRule]
      refine ⟨mem_univ _, h2, fun i hi => hblt _ fun h => ?_, fun i _ hi => ⟨σ.symm a, h1, ?_⟩⟩
      · rw [← h, Equiv.symm_apply_apply] at hi
        exact lt_irrefl _ hi
      · rw [Equiv.apply_symm_apply]
        refine hamax _ (Finset.mem_erase.2 ⟨fun h => ?_, mem_univ _⟩)
        rw [← h, Equiv.symm_apply_apply] at hi
        exact lt_irrefl _ hi
    have hle := Finset.card_le_card hsub
    have hpos : 0 < n * (n - 1) := Nat.mul_pos hnpos (by omega)
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc n ! * (n * (n - 1)) ≤ n ! * (4 * (n / 2 * (n - n / 2))) :=
          Nat.mul_le_mul_left _ (quarter_arith n)
      _ = 4 * (#T * n !) := by rw [hTcard]; ring
      _ = 4 * (#{σ : ArrivalOrder E | (σ.symm a, σ.symm b) ∈ T} * (n * (n - 1))) := by
          rw [hcount]
      _ ≤ 4 * (#{σ : ArrivalOrder E | b ∈ selected (thresholdRule (n / 2) κ) σ w} *
            (n * (n - 1))) := by gcongr
      _ = _ := by ring
  · -- a single element: it is always accepted
    have hn1' : n = 1 := by omega
    have hall : (univ.filter fun σ : ArrivalOrder E =>
        b ∈ selected (thresholdRule (n / 2) κ) σ w) = univ := by
      refine Finset.filter_true_of_mem fun σ _ => ?_
      rw [mem_selected, accepts_thresholdRule]
      have h0 : ∀ i : Fin n, ¬ i < σ.symm b := by
        intro i hi
        rw [Fin.lt_def] at hi
        have := (σ.symm b).isLt
        omega
      exact ⟨by omega, fun i hi => absurd hi (h0 i), fun i _ hi => absurd hi (h0 i)⟩
    rw [hall, Finset.card_univ, Fintype.card_equiv (Fintype.equivFin E).symm, Fintype.card_fin]
    omega

/-- The rule of the classical secretary problem: skip the first `⌊n/2⌋` arrivals, then accept
the first arrival that is strictly heavier than all earlier arrivals. -/
def halfRule (E : Type*) [Fintype E] : OnlineAlg E :=
  thresholdRule (Fintype.card E / 2) Prod.snd

/-- **The classical secretary problem (half rule).** For pairwise distinct weights, the rule
"skip the first `⌊n/2⌋` arrivals, then accept the first arrival heavier than all earlier ones"
accepts the heaviest element `b` in at least `n!/4` of the `n!` arrival orders, i.e. with
probability at least `1/4` under a uniformly random arrival order. -/
theorem secretary_half_rule (w : E → ℝ) (hw : Injective w) (b : E) (hb : ∀ e, w e ≤ w b) :
    (Fintype.card E)! ≤ 4 * #{σ : ArrivalOrder E | b ∈ selected (halfRule E) σ w} :=
  thresholdRule_success Prod.snd w hw b hb

end Threshold

/-! ### The rank-one uniform matroid -/

/-- The rank-one uniform matroid on `E`: a set is independent iff it has at most one
element. -/
def rankOne (E : Type*) [Fintype E] : Matroid E :=
  (IndepMatroid.ofFinite (E := (Set.univ : Set E)) Set.finite_univ (fun I => I.Subsingleton)
    Set.subsingleton_empty (fun _ _ hJ hIJ => hJ.anti hIJ)
    (by
      intro I J hI hJ hlt
      have hJne : J.Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        rintro rfl
        simp at hlt
      obtain ⟨e, he⟩ := hJne
      have hI0 : I = ∅ := by
        by_contra hne
        obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
        have h1 : I = {x} := hI.eq_singleton_of_mem hx
        have h2 : J = {e} := hJ.eq_singleton_of_mem he
        rw [h1, h2] at hlt
        simp at hlt
      subst hI0
      exact ⟨e, he, by simp, by simp⟩)
    (fun _ _ => Set.subset_univ _)).matroid

/-- A set is independent in the rank-one uniform matroid iff it has at most one element. -/
@[simp] lemma rankOne_indep_iff {I : Set E} : (rankOne E).Indep I ↔ I.Subsingleton := by
  simp [rankOne]

/-- The ground set of `rankOne E` is all of `E`. -/
@[simp] lemma rankOne_ground : (rankOne E).E = Set.univ := rfl

/-- The half rule with ties broken by a fixed enumeration of `E`: skip the first `⌊n/2⌋`
arrivals, then accept the first arrival that beats all earlier ones in the lexicographic order
on (weight, index of the element). -/
def halfRuleLex (E : Type*) [Fintype E] : OnlineAlg E :=
  thresholdRule (α := ℝ ×ₗ Fin (Fintype.card E)) (Fintype.card E / 2)
    fun p => toLex (p.2, Fintype.equivFin E p.1)

/-- The half rule accepts at most one element, so it is feasible for the rank-one matroid. -/
theorem halfRuleLex_isFeasible : IsFeasible (rankOne E) (halfRuleLex E) := fun σ w _ =>
  rankOne_indep_iff.2 (selected_thresholdRule_subsingleton _ _ σ w)

/-- The half rule (with ties broken by a fixed order) is `1/4`-competitive for the rank-one
uniform matroid: for arbitrary non-negative weights, its expected weight is at least a quarter
of the largest weight. -/
theorem halfRuleLex_isCompetitive : IsCompetitive (rankOne E) (halfRuleLex E) (1 / 4) := by
  intro w hw I hI
  rw [rankOne_indep_iff] at hI
  rcases I.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · simpa using expWeight_nonneg (halfRuleLex E) hw
  have hIe : I = {e₀} := Finset.eq_singleton_iff_unique_mem.2 ⟨he₀, fun x hx => hI hx he₀⟩
  set κ : E × ℝ → ℝ ×ₗ Fin (Fintype.card E) := fun p => toLex (p.2, Fintype.equivFin E p.1)
    with hκ
  have hinj : Injective fun e => κ (e, w e) := by
    intro e e' h
    simp only [hκ, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at h
    exact h.2
  obtain ⟨b, -, hbmax⟩ := Finset.exists_max_image (univ : Finset E) (fun e => κ (e, w e))
    ⟨e₀, mem_univ _⟩
  have hb : ∀ e, κ (e, w e) ≤ κ (b, w b) := fun e => hbmax e (mem_univ _)
  have hwb : ∀ e, w e ≤ w b := by
    intro e
    have := hb e
    simp only [hκ, Prod.Lex.toLex_le_toLex] at this
    rcases this with h | h
    · exact h.le
    · exact h.1.le
  have hcount := thresholdRule_success κ w hinj b hb
  set S : Finset (ArrivalOrder E) :=
    univ.filter fun σ : ArrivalOrder E => b ∈ selected (halfRuleLex E) σ w with hS
  have hsum : (#S : ℝ) * w b ≤ ∑ σ : ArrivalOrder E, ∑ e ∈ selected (halfRuleLex E) σ w, w e := by
    calc (#S : ℝ) * w b = ∑ σ : ArrivalOrder E, if b ∈ selected (halfRuleLex E) σ w then w b
          else 0 := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          split_ifs with h
          · exact Finset.single_le_sum (fun e _ => hw e) h
          · exact Finset.sum_nonneg fun e _ => hw e
  have hfac : (0 : ℝ) < (Fintype.card E)! := by exact_mod_cast Nat.factorial_pos _
  have hcount' : ((Fintype.card E)! : ℝ) ≤ 4 * #S := by exact_mod_cast hcount
  rw [hIe, Finset.sum_singleton, expWeight, le_div_iff₀ hfac]
  have h1 : 1 / 4 * w e₀ * (Fintype.card E)! ≤ 1 / 4 * w b * (4 * #S) := by
    have := hwb e₀
    have := hw e₀
    have := hw b
    gcongr
  linarith

/-- The matroid secretary problem for rank-one uniform matroids (the classical secretary
problem with arbitrary non-negative weights) has a feasible deterministic `1/4`-competitive
online algorithm. -/
theorem exists_isCompetitive_rankOne (E : Type*) [Fintype E] :
    ∃ A : OnlineAlg E, IsFeasible (rankOne E) A ∧ IsCompetitive (rankOne E) A (1 / 4) :=
  ⟨halfRuleLex E, halfRuleLex_isFeasible, halfRuleLex_isCompetitive⟩

end Applied.Economics.MatroidSecretary
