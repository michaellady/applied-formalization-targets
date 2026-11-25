import Applied.Economics.SecretaryRankOptimal

/-!
# Optimality of threshold rules in the arrival-order model (classical secretary problem)

This file connects the relative-rank model of `Applied/Economics/SecretaryRankOptimal.lean`
with the arrival-order model of `Applied/Economics/MatroidSecretary.lean`.

## Results

Let `E` be a finite set with `n = |E|` elements and `f : E → α` injective (distinct keys).

* `rankSeqOf f σ`: the relative-rank sequence of the arrival order `σ`; its `t`-th entry is
  `relRank f σ t`, the number of earlier arrivals (times `s < t`) whose key is larger than that
  of the arrival at time `t` (`0` = best so far).
* `rankSeqOf_bijective`: `σ ↦ rankSeqOf f σ` is a bijection from the `n!` arrival orders onto
  the `n!` relative-rank sequences. Hence the relative ranks of a uniformly random arrival
  order are uniformly distributed on `RankSeq n`.
* `pattern_of_relRank`: the relative ranks at times `≤ T` determine all comparisons between
  the arrivals at times `≤ T` (and conversely, `relRank_eq_of_pattern`).
* `IsOrdinal κ A`: an online algorithm whose decision at each time depends only on the
  relative order of the keys of the arrivals so far. `FirstAccepts A σ w e`: `e` is the first
  element the algorithm accepts (the algorithm stops at its first acceptance).
* `ordinal_success_prob_le`: every ordinal online algorithm stops on the best element with
  probability at most `M n 0 = max_{r ≤ n} thrVal n r` (uniformly random arrival order).
* `thresholdRule_isOrdinal`, `firstAccepts_thresholdRule_iff`: threshold rules are ordinal and
  stop on what they select.
* `secretary_optimal`: the best threshold rule and the best ordinal rule have the same success
  probability, `M n 0`; both maxima are attained.
* `M_le_inv_exp_add`, `inv_exp_le_M`, `tendsto_M_inv_exp`: `1/e ≤ M n 0 ≤ 1/e + 1/n` for
  `n ≥ 1`, so the optimal success probability tends to `1/e`.
-/

open Finset Function

open Classical

open scoped Nat

noncomputable section

namespace Applied.Economics.SecretaryRank

open Applied.Economics.MatroidSecretary

variable {E α : Type*} [Fintype E] [LinearOrder α]

/-! ### Relative ranks of an arrival order -/

/-- The relative rank of the arrival at time `t`: the number of earlier arrivals with a larger
key. -/
def relRank (f : E → α) (σ : ArrivalOrder E) (t : Fin (Fintype.card E)) : ℕ :=
  #{s : Fin (Fintype.card E) | s < t ∧ f (σ t) < f (σ s)}

lemma relRank_le (f : E → α) (σ : ArrivalOrder E) (t : Fin (Fintype.card E)) :
    relRank f σ t ≤ t := by
  calc relRank f σ t ≤ #{s : Fin (Fintype.card E) | (s : ℕ) < t} :=
        card_le_card fun s => by
          simp only [mem_filter, mem_univ, true_and]
          exact fun h => Fin.lt_def.mp h.1
    _ = t := by rw [Fin.card_filter_val_lt]; exact min_eq_right t.2.le

/-- The relative-rank sequence of an arrival order. -/
def rankSeqOf (f : E → α) (σ : ArrivalOrder E) : RankSeq (Fintype.card E) :=
  fun t => ⟨relRank f σ t, Nat.lt_succ_of_le (relRank_le f σ t)⟩

@[simp] lemma rankSeqOf_val (f : E → α) (σ : ArrivalOrder E) (t : Fin (Fintype.card E)) :
    ((rankSeqOf f σ t : Fin ((t : ℕ) + 1)) : ℕ) = relRank f σ t := rfl

lemma lt_iff_not_lt_of_ne {a b : α} (h : a ≠ b) : a < b ↔ ¬ b < a := by
  rw [not_lt, h.le_iff_lt]

lemma relRank_eq_zero_iff {f : E → α} (hf : Injective f) (σ : ArrivalOrder E)
    (t : Fin (Fintype.card E)) : relRank f σ t = 0 ↔ ∀ s, s < t → f (σ s) < f (σ t) := by
  unfold relRank
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  refine forall_congr' fun s => ?_
  simp only [mem_univ, true_imp_iff, not_and]
  refine imp_congr_right fun hs => ?_
  have hne : f (σ s) ≠ f (σ t) := fun h => (ne_of_lt hs) (σ.injective (hf h))
  rw [lt_iff_not_lt_of_ne hne]

/-- One step of the reconstruction: if two key sequences have the same order pattern before
time `t` and the same number of earlier larger keys at time `t`, then the earlier arrivals that
beat the arrival at time `t` are the same. -/
lemma upper_aux {N : ℕ} {g g' : Fin N → α} {t : Fin N}
    (hpat : ∀ i j, i < t → j < t → (g i < g j ↔ g' i < g' j))
    (hcard : #{s | s < t ∧ g t < g s} = #{s | s < t ∧ g' t < g' s})
    {i : Fin N} (hi : i < t) (h1 : g t < g i) : g' t < g' i := by
  by_contra h2
  rw [not_lt] at h2
  have hsub : (univ.filter fun s => s < t ∧ g' t < g' s) ⊂
      (univ.filter fun s => s < t ∧ g t < g s) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨i, by simp [hi, h1], by simp [hi, not_lt.2 h2]⟩
    · intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      refine ⟨hj.1, h1.trans ((hpat i j hi hj.1).2 (lt_of_le_of_lt h2 hj.2))⟩
  have := Finset.card_lt_card hsub
  omega

/-- **Relative ranks determine the order pattern.** If two arrival orders have the same
relative ranks at all times `≤ T`, then the arrivals at times `≤ T` compare in the same way. -/
theorem pattern_of_relRank {f : E → α} (hf : Injective f) {σ τ : ArrivalOrder E} {T : ℕ}
    (h : ∀ t : Fin (Fintype.card E), (t : ℕ) ≤ T → relRank f σ t = relRank f τ t) :
    ∀ i j : Fin (Fintype.card E), (i : ℕ) ≤ T → (j : ℕ) ≤ T →
      (f (σ i) < f (σ j) ↔ f (τ i) < f (τ j)) := by
  have flip : ∀ (π : ArrivalOrder E) (i j : Fin (Fintype.card E)), i ≠ j →
      (f (π i) < f (π j) ↔ ¬ f (π j) < f (π i)) := fun π i j hij =>
    lt_iff_not_lt_of_ne fun h => hij (π.injective (hf h))
  have key : ∀ m : ℕ, ∀ t : Fin (Fintype.card E), (t : ℕ) = m → (t : ℕ) ≤ T →
      ∀ i, i < t → (f (σ i) < f (σ t) ↔ f (τ i) < f (τ t)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro t htm htT
      have hpat : ∀ i j, i < t → j < t → (f (σ i) < f (σ j) ↔ f (τ i) < f (τ j)) := by
        intro i j hi hj
        rcases lt_trichotomy i j with hij | rfl | hij
        · exact ih j (by rw [← htm]; exact hj) j rfl
            (le_trans (Fin.lt_def.mp hj).le htT) i hij
        · simp
        · rw [flip σ i j hij.ne', flip τ i j hij.ne',
            ih i (by rw [← htm]; exact hi) i rfl (le_trans (Fin.lt_def.mp hi).le htT) j hij]
      have hcard := h t htT
      intro i hi
      have hne : i ≠ t := ne_of_lt hi
      rw [flip σ i t hne, flip τ i t hne]
      refine not_congr ⟨fun h1 => ?_, fun h1 => ?_⟩
      · exact upper_aux (g := fun s => f (σ s)) (g' := fun s => f (τ s)) hpat hcard hi h1
      · exact upper_aux (g := fun s => f (τ s)) (g' := fun s => f (σ s))
          (fun i j hi hj => (hpat i j hi hj).symm) hcard.symm hi h1
  intro i j hi hj
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact key j j rfl hj i hij
  · simp
  · rw [flip σ i j hij.ne', flip τ i j hij.ne', key i i rfl hi j hij]

/-- Conversely, the order pattern of the arrivals at times `≤ t` determines the relative rank
at time `t`. -/
lemma relRank_eq_of_pattern {f : E → α} {σ τ : ArrivalOrder E} {t : Fin (Fintype.card E)}
    (h : ∀ i j : Fin (Fintype.card E), i ≤ t → j ≤ t →
      (f (σ i) < f (σ j) ↔ f (τ i) < f (τ j))) :
    relRank f σ t = relRank f τ t := by
  unfold relRank
  congr 1
  refine Finset.filter_congr fun s _ => and_congr_right fun hs => h t s le_rfl hs.le

/-- An arrival order is determined by the order pattern of its keys. -/
lemma eq_of_pattern {f : E → α} (hf : Injective f) {σ τ : ArrivalOrder E}
    (h : ∀ i j, f (σ i) < f (σ j) ↔ f (τ i) < f (τ j)) : σ = τ := by
  have hr : ∀ x y : E, #{z | f z < f x} = #{z | f z < f y} → x = y := by
    intro x y hxy
    by_contra hne
    have hfne : f x ≠ f y := fun h => hne (hf h)
    have aux : ∀ x y : E, f x < f y → #{z | f z < f x} < #{z | f z < f y} := by
      intro x y hlt
      refine Finset.card_lt_card ?_
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨x, by simp [hlt], by simp⟩
      · intro z hz
        simp only [mem_filter, mem_univ, true_and] at hz ⊢
        exact hz.trans hlt
    rcases lt_or_gt_of_ne hfne with hlt | hlt
    · have := aux x y hlt; omega
    · have := aux y x hlt; omega
  have hcount : ∀ (π : ArrivalOrder E) (i : Fin (Fintype.card E)),
      #{z | f z < f (π i)} = #{j : Fin (Fintype.card E) | f (π j) < f (π i)} := by
    intro π i
    refine Finset.card_equiv π.symm fun z => ?_
    simp
  ext i
  apply hr
  rw [hcount σ i, hcount τ i]
  congr 1
  exact Finset.filter_congr fun j _ => h j i

theorem rankSeqOf_injective {f : E → α} (hf : Injective f) :
    Injective (rankSeqOf (E := E) f) := by
  intro σ τ hστ
  have h : ∀ t : Fin (Fintype.card E), (t : ℕ) ≤ Fintype.card E →
      relRank f σ t = relRank f τ t := fun t _ => by
    have := congrArg (fun c : RankSeq (Fintype.card E) => ((c t : Fin _) : ℕ)) hστ
    simpa using this
  exact eq_of_pattern hf fun i j => pattern_of_relRank hf h i j i.2.le j.2.le

/-- **Relative ranks of a uniformly random arrival order are uniform.** For distinct keys, the
map from the `n!` arrival orders to the `n!` relative-rank sequences is a bijection. -/
theorem rankSeqOf_bijective {f : E → α} (hf : Injective f) :
    Bijective (rankSeqOf (E := E) f) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨rankSeqOf_injective hf, ?_⟩
  rw [card_rankSeq, Fintype.card_equiv (Fintype.equivFin E).symm, Fintype.card_fin]

/-- The arrival at time `t` is the best element iff it is best so far and no later arrival is
best so far. -/
lemma eq_best_iff {f : E → α} (hf : Injective f) {b : E} (hb : ∀ e, f e ≤ f b)
    (σ : ArrivalOrder E) (t : Fin (Fintype.card E)) :
    σ t = b ↔ relRank f σ t = 0 ∧ ∀ s, t < s → relRank f σ s ≠ 0 := by
  have hlt : ∀ e, e ≠ b → f e < f b := fun e he => lt_of_le_of_ne (hb e) fun h => he (hf h)
  rw [relRank_eq_zero_iff hf]
  constructor
  · rintro rfl
    refine ⟨fun s hs => hlt _ fun h => (ne_of_lt hs) (σ.injective h), fun s hs h0 => ?_⟩
    rw [relRank_eq_zero_iff hf] at h0
    exact absurd (h0 t hs) (not_lt.2 (hb _))
  · rintro ⟨h1, h2⟩
    by_contra hne
    have hs0 : σ.symm b ≠ t := fun h => hne (by rw [← h, Equiv.apply_symm_apply])
    rcases lt_or_gt_of_ne hs0 with h | h
    · have := h1 _ h
      rw [Equiv.apply_symm_apply] at this
      exact absurd this (not_lt.2 (hb _))
    · refine h2 _ h ((relRank_eq_zero_iff hf σ _).2 fun s hs => ?_)
      rw [Equiv.apply_symm_apply]
      exact hlt _ fun h' => (ne_of_lt hs) (by rw [← h', Equiv.symm_apply_apply])

/-! ### Ordinal online algorithms in the arrival-order model -/

/-- An online algorithm is *ordinal* (rank-based) for the key function `κ` if its decision at
each time depends only on the relative order of the keys of the arrivals so far. -/
def IsOrdinal (κ : E × ℝ → α) (A : OnlineAlg E) : Prop :=
  ∀ (k : ℕ) (h h' : Fin (k + 1) → E × ℝ),
    (∀ i j, κ (h i) < κ (h j) ↔ κ (h' i) < κ (h' j)) → (A k h ↔ A k h')

/-- `e` is the first element accepted by `A`: the algorithm, used as a stopping rule, stops at
the arrival of `e`. -/
def FirstAccepts (A : OnlineAlg E) (σ : ArrivalOrder E) (w : E → ℝ) (e : E) : Prop :=
  Accepts A σ w e ∧ ∀ i : Fin (Fintype.card E), i < σ.symm e → ¬ A i (arrivals σ w i)

section Ordinal

variable (κ : E × ℝ → α) (w : E → ℝ)

lemma arrivals_pattern {σ τ : ArrivalOrder E} {t : Fin (Fintype.card E)}
    (h : ∀ i j : Fin (Fintype.card E), (i : ℕ) ≤ t → (j : ℕ) ≤ t →
      (κ (σ i, w (σ i)) < κ (σ j, w (σ j)) ↔ κ (τ i, w (τ i)) < κ (τ j, w (τ j)))) :
    ∀ i j, κ (arrivals σ w t i) < κ (arrivals σ w t j) ↔
      κ (arrivals τ w t i) < κ (arrivals τ w t j) := fun i j =>
  h _ _ (Nat.lt_succ_iff.mp i.2) (Nat.lt_succ_iff.mp j.2)

variable {κ w}

/-- The relative-rank stopping rule induced by an ordinal online algorithm. -/
def toRankRule (hinj : Injective fun e => κ (e, w e)) (A : OnlineAlg E) (hA : IsOrdinal κ A) :
    RankRule (Fintype.card E) where
  D t c := A t (arrivals (surjInv (rankSeqOf_bijective hinj).2 c) w t)
  adapted t c d hcd := by
    set g := surjInv (rankSeqOf_bijective hinj).2
    have hc : rankSeqOf (fun e => κ (e, w e)) (g c) = c := surjInv_eq _ c
    have hd : rankSeqOf (fun e => κ (e, w e)) (g d) = d := surjInv_eq _ d
    refine hA _ _ _ (arrivals_pattern κ w (pattern_of_relRank hinj fun s hs => ?_))
    have h1 := congrArg (fun c : RankSeq (Fintype.card E) => ((c s : Fin _) : ℕ)) hc
    have h2 := congrArg (fun c : RankSeq (Fintype.card E) => ((c s : Fin _) : ℕ)) hd
    simp only [rankSeqOf_val] at h1 h2
    rw [h1, h2, hcd s (Fin.le_def.mpr hs)]

lemma toRankRule_D (hinj : Injective fun e => κ (e, w e)) (A : OnlineAlg E) (hA : IsOrdinal κ A)
    (t : Fin (Fintype.card E)) (σ : ArrivalOrder E) :
    (toRankRule hinj A hA).D t (rankSeqOf (fun e => κ (e, w e)) σ) ↔ A t (arrivals σ w t) := by
  show A t (arrivals (surjInv (rankSeqOf_bijective hinj).2 (rankSeqOf (fun e => κ (e, w e)) σ)) w t) ↔ _
  set σ' := surjInv (rankSeqOf_bijective hinj).2 (rankSeqOf (fun e => κ (e, w e)) σ)
  have h : rankSeqOf (fun e => κ (e, w e)) σ' = rankSeqOf (fun e => κ (e, w e)) σ := surjInv_eq _ _
  refine hA _ _ _ (arrivals_pattern κ w (pattern_of_relRank hinj (T := t) fun s _ => ?_))
  have := congrArg (fun c : RankSeq (Fintype.card E) => ((c s : Fin _) : ℕ)) h
  simpa using this

lemma toRankRule_success_iff (hinj : Injective fun e => κ (e, w e)) {b : E}
    (hb : ∀ e, κ (e, w e) ≤ κ (b, w b)) (A : OnlineAlg E) (hA : IsOrdinal κ A)
    (σ : ArrivalOrder E) :
    (toRankRule hinj A hA).Success (rankSeqOf (fun e => κ (e, w e)) σ) ↔ FirstAccepts A σ w b := by
  have hstop : ∀ t, (toRankRule hinj A hA).StopAt t (rankSeqOf (fun e => κ (e, w e)) σ) ↔
      A t (arrivals σ w t) ∧ ∀ s, s < t → ¬ A s (arrivals σ w s) := by
    intro t
    unfold RankRule.StopAt
    simp only [toRankRule_D]
  have hzero : ∀ t, (rankSeqOf (fun e => κ (e, w e)) σ t = 0) ↔
      relRank (fun e => κ (e, w e)) σ t = 0 := fun t => by
    rw [Fin.ext_iff, rankSeqOf_val, Fin.val_zero]
  unfold RankRule.Success FirstAccepts Accepts
  simp only [hstop, hzero, ne_eq]
  constructor
  · rintro ⟨t, ⟨hA1, hA2⟩, h0, hlater⟩
    have hbt : σ t = b := (eq_best_iff hinj hb σ t).2 ⟨h0, hlater⟩
    have ht : σ.symm b = t := by rw [← hbt, Equiv.symm_apply_apply]
    rw [ht]
    exact ⟨hA1, hA2⟩
  · rintro ⟨hA1, hA2⟩
    obtain ⟨h0, hlater⟩ := (eq_best_iff hinj hb σ (σ.symm b)).1 (Equiv.apply_symm_apply σ b)
    exact ⟨σ.symm b, ⟨hA1, hA2⟩, h0, hlater⟩

/-- **No ordinal online algorithm beats the best threshold rule (arrival-order model).** Let
the keys `κ (e, w e)` be pairwise distinct and `b` the element of largest key. Every online
algorithm whose decisions depend only on the relative order of the keys seen so far, used as a
stopping rule (stop at the first acceptance), stops on `b` in at most a fraction
`M n 0 = max_{r ≤ n} thrVal n r` of the `n!` arrival orders. -/
theorem ordinal_success_prob_le (hinj : Injective fun e => κ (e, w e)) (b : E)
    (hb : ∀ e, κ (e, w e) ≤ κ (b, w b)) (A : OnlineAlg E) (hA : IsOrdinal κ A) :
    (#{σ : ArrivalOrder E | FirstAccepts A σ w b} : ℝ) / (Fintype.card E)! ≤
      M (Fintype.card E) 0 := by
  have hcard : #{σ : ArrivalOrder E | FirstAccepts A σ w b} =
      #(univ.filter fun c => (toRankRule hinj A hA).Success c) := by
    refine Finset.card_equiv (Equiv.ofBijective _ (rankSeqOf_bijective hinj)) fun σ => ?_
    simp only [mem_filter, mem_univ, true_and, Equiv.ofBijective_apply]
    exact (toRankRule_success_iff hinj hb A hA σ).symm
  rw [hcard]
  exact (toRankRule hinj A hA).success_prob_le

omit [Fintype E] in
/-- Threshold rules are ordinal. -/
theorem thresholdRule_isOrdinal (r : ℕ) (κ : E × ℝ → α) : IsOrdinal κ (thresholdRule r κ) := by
  intro k h h' hpat
  unfold thresholdRule
  simp only [← not_lt, hpat]

/-- A threshold rule accepts at most one element, so it stops exactly on what it selects. -/
theorem firstAccepts_thresholdRule_iff (r : ℕ) (σ : ArrivalOrder E) (e : E) :
    FirstAccepts (thresholdRule r κ) σ w e ↔ e ∈ selected (thresholdRule r κ) σ w := by
  rw [mem_selected]
  refine ⟨fun h => h.1, fun h => ⟨h, fun i hi hAi => ?_⟩⟩
  have hacc : Accepts (thresholdRule r κ) σ w (σ i) := by
    unfold Accepts
    rw [Equiv.symm_apply_apply]
    exact hAi
  have := selected_thresholdRule_subsingleton r κ σ w (mem_selected.2 hacc) (mem_selected.2 h)
  rw [← this, Equiv.symm_apply_apply] at hi
  exact lt_irrefl _ hi

/-- **The classical secretary theorem in the arrival-order model.** For pairwise distinct keys
and `b` the element of largest key, the largest success probability of a threshold rule and the
largest success probability of an ordinal online algorithm (used as a stopping rule) are both
equal to `M n 0 = max_{r ≤ n} thrVal n r`, and both maxima are attained. -/
theorem secretary_optimal (hinj : Injective fun e => κ (e, w e)) (b : E)
    (hb : ∀ e, κ (e, w e) ≤ κ (b, w b)) :
    IsGreatest {p : ℝ | ∃ r : ℕ,
        p = #{σ : ArrivalOrder E | b ∈ selected (thresholdRule r κ) σ w} / (Fintype.card E)!}
      (M (Fintype.card E) 0) ∧
    IsGreatest {p : ℝ | ∃ A : OnlineAlg E, IsOrdinal κ A ∧
        p = #{σ : ArrivalOrder E | FirstAccepts A σ w b} / (Fintype.card E)!}
      (M (Fintype.card E) 0) := by
  obtain ⟨r, -, hr⟩ := exists_M_eq (Fintype.card E)
  have hthr : ∀ r : ℕ, (#{σ : ArrivalOrder E | b ∈ selected (thresholdRule r κ) σ w} : ℝ) =
      #{σ : ArrivalOrder E | FirstAccepts (thresholdRule r κ) σ w b} := fun r => by
    congr 2
    exact Finset.filter_congr fun σ _ => (firstAccepts_thresholdRule_iff r σ b).symm
  refine ⟨⟨⟨r, by rw [hr, thrVal_eq_threshold_prob κ w hinj b hb r]⟩, ?_⟩,
    ⟨⟨thresholdRule r κ, thresholdRule_isOrdinal r κ, ?_⟩, ?_⟩⟩
  · rintro p ⟨r', rfl⟩
    rw [hthr]
    exact ordinal_success_prob_le hinj b hb _ (thresholdRule_isOrdinal r' κ)
  · rw [← hthr, hr, thrVal_eq_threshold_prob κ w hinj b hb r]
  · rintro p ⟨A, hA, rfl⟩
    exact ordinal_success_prob_le hinj b hb A hA

end Ordinal

/-! ### Asymptotics: the optimal success probability tends to `1/e` -/

lemma thrVal_le_M (n r : ℕ) : thrVal n r ≤ M n 0 := by
  rcases le_or_gt r n with hrn | hnr
  · exact le_M (Nat.zero_le r) hrn
  · have : thrVal n r = 0 := by
      unfold thrVal
      split_ifs with h
      · omega
      · rw [Finset.Ico_eq_empty_of_le hnr.le, sum_empty, mul_zero]
    rw [this]
    exact M_nonneg (Nat.zero_le n)

/-- `∑_{t=r}^{r+k} 1/t ≤ 1/r + log ((r + k)/r)`. -/
lemma sum_inv_le_log (r : ℕ) (hr : 0 < r) (k : ℕ) :
    ∑ t ∈ Ico r (r + 1 + k), (1 : ℝ) / t ≤ 1 / r + Real.log (((r + k : ℕ) : ℝ) / r) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  induction k with
  | zero =>
    rw [add_zero, add_zero, Nat.Ico_succ_singleton, sum_singleton, div_self hr0.ne',
      Real.log_one, add_zero]
  | succ k ih =>
    rw [show r + 1 + (k + 1) = (r + 1 + k) + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
    have hrk : (0 : ℝ) < (r : ℝ) + k := by positivity
    set x : ℝ := ((r : ℝ) + k + 1) / ((r : ℝ) + k) with hxdef
    have hx : 0 < x := by positivity
    have h1 := Real.one_sub_inv_le_log_of_pos hx
    have hsplit : Real.log (((r + (k + 1) : ℕ) : ℝ) / r) =
        Real.log x + Real.log (((r + k : ℕ) : ℝ) / r) := by
      rw [← Real.log_mul hx.ne' (by positivity)]
      congr 1
      rw [hxdef]
      push_cast
      field_simp
      ring
    have hinv : 1 - x⁻¹ = 1 / (((r + 1 + k : ℕ) : ℝ)) := by
      rw [hxdef]
      push_cast
      field_simp
      ring
    rw [hsplit]
    linarith

lemma log_le_div_exp {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 1))
  rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

/-- Every threshold value is at most `1/e + 1/n`. -/
lemma thrVal_le_inv_exp_add (n r : ℕ) (hn : 0 < n) :
    thrVal n r ≤ 1 / Real.exp 1 + 1 / n := by
  have he : 0 < 1 / Real.exp 1 := by positivity
  unfold thrVal
  split_ifs with hr0
  · linarith
  · rcases le_or_gt n r with hnr | hrn
    · rw [Finset.Ico_eq_empty_of_le hnr, sum_empty, mul_zero]
      positivity
    · have hr : 0 < r := Nat.pos_of_ne_zero hr0
      have hs := sum_inv_le_log r hr (n - 1 - r)
      rw [show r + 1 + (n - 1 - r) = n by omega, show r + (n - 1 - r) = n - 1 by omega] at hs
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr
      have hn1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
      have hlog : Real.log (((n - 1 : ℕ) : ℝ) / r) ≤ Real.log (n / r) := by
        apply Real.log_le_log (div_pos hn1 hrR)
        gcongr
        exact_mod_cast Nat.sub_le n 1
      have hl2 := log_le_div_exp (div_pos hnR hrR)
      calc (r : ℝ) / n * ∑ t ∈ Ico r n, (1 : ℝ) / t ≤ r / n * (1 / r + Real.log (n / r)) := by
            gcongr
            linarith
        _ ≤ r / n * (1 / r + (n / r) / Real.exp 1) := by gcongr
        _ = 1 / Real.exp 1 + 1 / n := by field_simp; ring

/-- **Upper bound:** the optimal success probability is at most `1/e + 1/n`. -/
theorem M_le_inv_exp_add {n : ℕ} (hn : 0 < n) : M n 0 ≤ 1 / Real.exp 1 + 1 / n :=
  (M_le_iff (Nat.zero_le n) _).2 fun r _ _ => thrVal_le_inv_exp_add n r hn

/-- **Lower bound:** the optimal success probability is at least `1/e` (from the library's
`1/e` bound for the threshold `⌊n/e⌋`). -/
theorem inv_exp_le_M {n : ℕ} (hn : 0 < n) : 1 / Real.exp 1 ≤ M n 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hw : Injective fun e : Fin (m + 1) => (Prod.snd (e, ((e : ℕ) : ℝ)) : ℝ) := by
    intro a b h
    simp only at h
    exact Fin.ext (by exact_mod_cast h)
  have hb : ∀ e : Fin (m + 1), (Prod.snd (e, ((e : ℕ) : ℝ)) : ℝ) ≤
      Prod.snd (Fin.last m, (((Fin.last m : Fin (m + 1)) : ℕ) : ℝ)) := by
    intro e
    show ((e : ℕ) : ℝ) ≤ (((Fin.last m : Fin (m + 1)) : ℕ) : ℝ)
    exact_mod_cast Fin.le_last e
  have h1 := thresholdRule_success_prob_ge (E := Fin (m + 1)) Prod.snd
    (fun e => ((e : ℕ) : ℝ)) hw (Fin.last m) hb
  rw [← thrVal_eq_threshold_prob (E := Fin (m + 1)) Prod.snd (fun e => ((e : ℕ) : ℝ)) hw
    (Fin.last m) hb] at h1
  simp only [Fintype.card_fin] at h1
  exact h1.trans (thrVal_le_M _ _)

/-- **The optimal success probability tends to `1/e`.** -/
theorem tendsto_M_inv_exp :
    Filter.Tendsto (fun n => M n 0) Filter.atTop (nhds (1 / Real.exp 1)) := by
  have hup : Filter.Tendsto (fun n : ℕ => 1 / Real.exp 1 + 1 / (n : ℝ)) Filter.atTop
      (nhds (1 / Real.exp 1)) := by
    simpa using (tendsto_const_nhds (x := 1 / Real.exp 1)).add
      tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn using inv_exp_le_M hn
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn using M_le_inv_exp_add hn

end Applied.Economics.SecretaryRank
