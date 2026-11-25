import Applied.Economics.SecretaryOneOverE
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Optimality of threshold rules among relative-rank stopping rules (secretary problem)

Dynkin's backward-induction argument, in the relative-rank model.

**Model.** A relative-rank sequence of length `n` is `c : (t : Fin n) → Fin (t + 1)`; `c t` is
the rank of arrival `t` among arrivals `0, …, t` (`0` = best so far). There are `n!` such
sequences (`card_rankSeq`), and the uniform distribution on them is the law of the relative
ranks of a uniformly random arrival order (classical; the bijection with arrival orders is
**not** formalized here). A `RankRule n` decides at each time `t` whether to stop, using only
`c 0, …, c t`. It succeeds on `c` if it stops at a time `t` with `c t = 0` and no later
`c s = 0` (i.e. it stops on the overall best arrival).

**Results.**
* `RankRule.success_prob_le`: every rank rule succeeds with probability at most
  `M n 0 = max_{r ≤ n} thrVal n r`, where `thrVal n r` is `1/n` for `r = 0` and
  `(r / n) ∑_{t=r}^{n-1} 1/t` for `r ≥ 1`.
* `thrVal_eq_threshold_prob`: `thrVal n r` is the exact success probability of the library's
  `thresholdRule r κ` (arrival-order model, `Applied/Economics/SecretaryOneOverE.lean`).
* `exists_thresholdRule_ge`: hence some threshold rule (in the arrival-order model) does at
  least as well as any rank rule (in the relative-rank model).

**Proof.** Let `a_t` be the probability of stopping at `t` on a best-so-far arrival. Adaptedness
and the independence of the coordinates give `(t + 1) a_t ≤ 1 - ∑_{s<t} a_s`
(`RankRule.constraint`) and success probability `∑_t (t + 1) a_t / n`
(`RankRule.card_success_at`). The linear-programming bound `lp_bound` is proved by backward
induction using `M_key`.
-/

open Finset

open Classical

open scoped Nat

noncomputable section

namespace Applied.Economics.SecretaryRank

/-! ### The threshold values and their running maximum -/

/-- The success probability of the threshold rule that skips the first `r` of `n` arrivals:
`1/n` for `r = 0` and `(r / n) ∑_{t=r}^{n-1} 1/t` for `r ≥ 1`. -/
def thrVal (n r : ℕ) : ℝ := if r = 0 then 1 / n else r / n * ∑ t ∈ Ico r n, (1 : ℝ) / t

lemma thrVal_nonneg (n r : ℕ) : 0 ≤ thrVal n r := by
  unfold thrVal
  split_ifs
  · positivity
  · exact mul_nonneg (by positivity) (sum_nonneg fun _ _ => by positivity)

lemma thrVal_self (n : ℕ) : thrVal n n = 0 := by
  unfold thrVal
  split_ifs with h
  · subst h; simp
  · simp

/-- The backward recursion `thrVal n t = 1/n + (1 - 1/(t+1)) thrVal n (t+1)` for `t < n`. -/
lemma thrVal_succ {n t : ℕ} (ht : t < n) :
    thrVal n t = 1 / n + (1 - 1 / ((t : ℝ) + 1)) * thrVal n (t + 1) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
  unfold thrVal
  simp only [Nat.succ_ne_zero, ↓reduceIte]
  split_ifs with h0
  · subst h0; simp
  · rw [Finset.sum_eq_sum_Ico_succ_bot ht]
    have : (t : ℝ) ≠ 0 := by exact_mod_cast h0
    push_cast
    field_simp
    ring

/-- `M n t = max_{t ≤ r ≤ n} thrVal n r` (for `t ≤ n`). -/
def M (n t : ℕ) : ℝ :=
  (Icc t (max t n)).sup' (nonempty_Icc.2 (le_max_left _ _)) (thrVal n)

lemma le_M {n t r : ℕ} (htr : t ≤ r) (hrn : r ≤ n) : thrVal n r ≤ M n t :=
  Finset.le_sup' (thrVal n) (mem_Icc.2 ⟨htr, hrn.trans (le_max_right _ _)⟩)

lemma M_le_iff {n t : ℕ} (ht : t ≤ n) (a : ℝ) :
    M n t ≤ a ↔ ∀ r, t ≤ r → r ≤ n → thrVal n r ≤ a := by
  unfold M
  rw [Finset.sup'_le_iff, max_eq_right ht]
  simp only [mem_Icc, and_imp]

lemma M_self (n : ℕ) : M n n = 0 := by
  refine le_antisymm ((M_le_iff le_rfl 0).2 fun r h1 h2 => ?_) ?_
  · rw [show r = n by omega, thrVal_self]
  · rw [← thrVal_self n]; exact le_M le_rfl le_rfl

lemma M_nonneg {n t : ℕ} (ht : t ≤ n) : 0 ≤ M n t :=
  (thrVal_nonneg n n).trans (le_M ht le_rfl)

lemma M_succ_le {n t : ℕ} (ht : t < n) : M n (t + 1) ≤ M n t :=
  (M_le_iff (by omega) _).2 fun r h1 h2 => le_M (by omega) h2

/-- The key inequality of the backward induction:
`1/n + (1 - 1/(t+1)) M n (t+1) ≤ M n t`. -/
lemma M_key {n t : ℕ} (ht : t < n) :
    1 / n + (1 - 1 / ((t : ℝ) + 1)) * M n (t + 1) ≤ M n t := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  set m := M n (t + 1) with hm
  have hc : 1 / ((t : ℝ) + 1) * ((t : ℝ) + 1) = 1 := by field_simp
  by_cases h : ((t : ℝ) + 1) / n ≤ m
  · -- then the bracket is at most `m`
    refine le_trans ?_ (M_succ_le ht)
    have h1 : 1 / (n : ℝ) ≤ 1 / ((t : ℝ) + 1) * m := by
      rw [div_le_iff₀ hnpos] at h
      rw [div_le_iff₀ hnpos]
      calc (1 : ℝ) = 1 / ((t : ℝ) + 1) * ((t : ℝ) + 1) := hc.symm
        _ ≤ 1 / ((t : ℝ) + 1) * (m * n) := by gcongr
        _ = _ := by ring
    linarith
  · rw [not_le] at h
    -- the threshold values are non-increasing on `[t+1, n]`, so `m = thrVal n (t+1)`
    have hdec : ∀ r, t + 1 ≤ r → r ≤ n → thrVal n r ≤ thrVal n (t + 1) := by
      intro r hr
      induction r, hr using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ r hr ih =>
        intro hrn
        refine le_trans ?_ (ih (by omega))
        have hrec := thrVal_succ (n := n) (t := r) (by omega)
        have hle : thrVal n (r + 1) ≤ m := le_M (by omega) hrn
        have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
        have htr : ((t : ℝ) + 1) ≤ (r : ℝ) + 1 := by
          have : (t : ℝ) + 1 ≤ r := by exact_mod_cast hr
          linarith
        have h2 : thrVal n (r + 1) < ((r : ℝ) + 1) / n :=
          lt_of_le_of_lt hle (lt_of_lt_of_le h (by gcongr))
        have h3 : 1 / ((r : ℝ) + 1) * thrVal n (r + 1) ≤ 1 / n := by
          rw [lt_div_iff₀ hnpos] at h2
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hr1 hnpos, one_mul]
          linarith
        rw [hrec]
        nlinarith
    have hmeq : m ≤ thrVal n (t + 1) := (M_le_iff (by omega) _).2 hdec
    have hcoef : 0 ≤ 1 - 1 / ((t : ℝ) + 1) := by
      rw [sub_nonneg, div_le_one ht1]
      have : (0 : ℝ) ≤ t := t.cast_nonneg
      linarith
    calc 1 / (n : ℝ) + (1 - 1 / ((t : ℝ) + 1)) * m
        ≤ 1 / n + (1 - 1 / ((t : ℝ) + 1)) * thrVal n (t + 1) := by gcongr
      _ = thrVal n t := (thrVal_succ ht).symm
      _ ≤ M n t := le_M le_rfl ht.le

/-- **The linear-programming bound.** If `x₀, …, x_{n-1} ≥ 0` satisfy
`(t + 1) x_t ≤ 1 - ∑_{s<t} x_s` for every `t < n`, then
`∑_{t<n} (t + 1) x_t / n ≤ max_{r ≤ n} thrVal n r`. -/
theorem lp_bound (n : ℕ) (x : ℕ → ℝ) (hx0 : ∀ t < n, 0 ≤ x t)
    (hcon : ∀ t < n, ((t : ℝ) + 1) * x t ≤ 1 - ∑ s ∈ range t, x s) :
    ∑ t ∈ range n, ((t : ℝ) + 1) * x t / n ≤ M n 0 := by
  have hnn : (0 : ℝ) ≤ n := n.cast_nonneg
  -- claim for `t = n - k`
  have key : ∀ k ≤ n, ∑ s ∈ Ico (n - k) n, ((s : ℝ) + 1) * x s / n
      ≤ (1 - ∑ s ∈ range (n - k), x s) * M n (n - k) := by
    intro k
    induction k with
    | zero => intro _; simp [M_self]
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      set t := n - (k + 1) with ht
      have htn : t < n := by omega
      have ht1 : n - k = t + 1 := by omega
      rw [ht1] at ih
      rw [Finset.sum_eq_sum_Ico_succ_bot htn]
      rw [Finset.sum_range_succ] at ih
      set R := 1 - ∑ s ∈ range t, x s
      have hcon' := hcon t htn
      have hx := hx0 t htn
      have hK := M_key htn
      have hmono := M_succ_le htn
      set m := M n (t + 1)
      have hm0 : 0 ≤ m := M_nonneg (by omega)
      have hR : 0 ≤ R := le_trans (by positivity) hcon'
      have ih' : ∑ s ∈ Ico (t + 1) n, ((s : ℝ) + 1) * x s / n ≤ (R - x t) * m := by
        have : 1 - (∑ s ∈ range t, x s + x t) = R - x t := by ring
        rw [← this]; exact ih
      have ht1p : (0 : ℝ) < (t : ℝ) + 1 := by positivity
      -- write `x t = y / (t + 1)` with `0 ≤ y ≤ R`
      set y := ((t : ℝ) + 1) * x t with hy
      have hxy : x t = y / ((t : ℝ) + 1) := by rw [hy]; field_simp
      have hy0 : 0 ≤ y := by positivity
      have hfirst : ((t : ℝ) + 1) * x t / n + (R - x t) * m
          = R * m + y * (1 / n - 1 / ((t : ℝ) + 1) * m) := by
        rw [hxy]; field_simp; ring
      have hgoal : R * m + y * (1 / n - 1 / ((t : ℝ) + 1) * m) ≤ R * M n t := by
        by_cases hs : 1 / (n : ℝ) - 1 / ((t : ℝ) + 1) * m ≤ 0
        · have : y * (1 / n - 1 / ((t : ℝ) + 1) * m) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hy0 hs
          nlinarith
        · rw [not_le] at hs
          have h1 : y * (1 / n - 1 / ((t : ℝ) + 1) * m)
              ≤ R * (1 / n - 1 / ((t : ℝ) + 1) * m) :=
            mul_le_mul_of_nonneg_right hcon' hs.le
          have h2 : R * (m + (1 / n - 1 / ((t : ℝ) + 1) * m)) ≤ R * M n t := by
            refine mul_le_mul_of_nonneg_left ?_ hR
            linarith
          nlinarith
      linarith
  have := key n le_rfl
  rw [Nat.sub_self, Finset.range_zero, sum_empty, sub_zero, one_mul, ← Finset.range_eq_Ico] at this
  exact this

/-! ### The relative-rank model -/

/-- Relative-rank sequences of length `n`: `c t ∈ {0, …, t}` is the rank of arrival `t` among
the arrivals `0, …, t` (`0` = best so far). There are `n!` of them. -/
abbrev RankSeq (n : ℕ) := (t : Fin n) → Fin ((t : ℕ) + 1)

lemma card_rankSeq (n : ℕ) : Fintype.card (RankSeq n) = n ! := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Fin.prod_univ_eq_prod_range (fun i => i + 1) n, Finset.prod_range_add_one_eq_factorial]

/-- If a set of rank sequences is invariant under changing coordinate `t`, exactly a
`1 / (t + 1)` fraction of it has `c t = 0`. -/
lemma card_filter_zero_mul {n : ℕ} (t : Fin n) (A : Finset (RankSeq n))
    (hA : ∀ c (j : Fin ((t : ℕ) + 1)), c ∈ A → Function.update c t j ∈ A) :
    ((t : ℕ) + 1) * (A.filter fun c => c t = 0).card = A.card := by
  rw [Finset.card_eq_sum_card_fiberwise (s := A) (t := (univ : Finset (Fin ((t : ℕ) + 1))))
    (f := fun c => c t) (fun _ _ => mem_univ _)]
  have h : ∀ j ∈ (univ : Finset (Fin ((t : ℕ) + 1))),
      (A.filter fun c => c t = j).card = (A.filter fun c => c t = 0).card := by
    intro j _
    refine Finset.card_nbij' (fun c => Function.update c t 0) (fun c => Function.update c t j)
      ?_ ?_ ?_ ?_
    · intro c hc
      simp only [coe_filter, Set.mem_ofPred_eq] at hc ⊢
      exact ⟨hA _ _ hc.1, by simp⟩
    · intro c hc
      simp only [coe_filter, Set.mem_ofPred_eq] at hc ⊢
      exact ⟨hA _ _ hc.1, by simp⟩
    · intro c hc
      simp only [coe_filter, Set.mem_ofPred_eq] at hc
      simp only
      rw [Function.update_idem, ← hc.2, Function.update_eq_self]
    · intro c hc
      simp only [coe_filter, Set.mem_ofPred_eq] at hc
      simp only
      rw [Function.update_idem, ← hc.2, Function.update_eq_self]
  rw [Finset.sum_congr rfl h, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- A stopping rule that sees only relative ranks: `D t c` says "stop at time `t`", and it may
depend only on the relative ranks `c s` with `s ≤ t`. -/
structure RankRule (n : ℕ) where
  /-- stop at time `t` (if not stopped earlier) -/
  D : Fin n → RankSeq n → Prop
  /-- the decision at time `t` depends only on the relative ranks up to time `t` -/
  adapted : ∀ t c d, (∀ s, s ≤ t → c s = d s) → (D t c ↔ D t d)

variable {n : ℕ}

/-- The rule stops at time `t`: `D t` holds and no earlier `D s` holds. -/
def RankRule.StopAt (R : RankRule n) (t : Fin n) (c : RankSeq n) : Prop :=
  R.D t c ∧ ∀ s, s < t → ¬ R.D s c

/-- The rule selects the overall best arrival: it stops at a time `t` whose arrival is best so
far (`c t = 0`) and no later arrival is best so far. -/
def RankRule.Success (R : RankRule n) (c : RankSeq n) : Prop :=
  ∃ t, R.StopAt t c ∧ c t = 0 ∧ ∀ s, t < s → c s ≠ 0

lemma RankRule.stopAt_unique (R : RankRule n) {t t' : Fin n} {c : RankSeq n}
    (h : R.StopAt t c) (h' : R.StopAt t' c) : t = t' := by
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd h.1 (h'.2 t hlt)
  · exact heq
  · exact absurd h'.1 (h.2 t' hgt)

lemma update_agree {c : RankSeq n} {u : Fin n} (j : Fin ((u : ℕ) + 1)) {t : Fin n}
    (htu : t < u) : ∀ s, s ≤ t → Function.update c u j s = c s :=
  fun _ hs => Function.update_of_ne (ne_of_lt (lt_of_le_of_lt hs htu)) _ _

lemma RankRule.stopAt_update (R : RankRule n) {c : RankSeq n} {t u : Fin n}
    (j : Fin ((u : ℕ) + 1)) (htu : t < u) :
    R.StopAt t (Function.update c u j) ↔ R.StopAt t c := by
  unfold RankRule.StopAt
  rw [R.adapted t _ _ (update_agree j htu)]
  refine and_congr_right fun _ => forall_congr' fun s => imp_congr_right fun hs => ?_
  rw [R.adapted s _ _ (update_agree j (hs.trans htu))]

lemma RankRule.notBefore_update (R : RankRule n) {c : RankSeq n} {t : Fin n}
    (j : Fin ((t : ℕ) + 1)) :
    (∀ s, s < t → ¬ R.D s (Function.update c t j)) ↔ (∀ s, s < t → ¬ R.D s c) := by
  refine forall_congr' fun s => imp_congr_right fun hs => ?_
  rw [R.adapted s _ _ (update_agree j hs)]

/-- Number of rank sequences on which the rule stops at `t` on a best-so-far arrival. -/
def RankRule.a (R : RankRule n) (t : Fin n) : ℕ :=
  (univ.filter fun c => R.StopAt t c ∧ c t = 0).card

/-- Given that the rule stops at `t` on a best-so-far arrival, that arrival is the overall best
with conditional probability `(t + 1) / n`. -/
lemma RankRule.card_success_at (R : RankRule n) (t : Fin n) :
    n * (univ.filter fun c => R.StopAt t c ∧ c t = 0 ∧ ∀ s, t < s → c s ≠ 0).card
      = ((t : ℕ) + 1) * R.a t := by
  let G : ℕ → Finset (RankSeq n) := fun u => univ.filter fun c =>
    R.StopAt t c ∧ c t = 0 ∧ ∀ s : Fin n, t < s → (s : ℕ) < u → c s ≠ 0
  have hG : ∀ k, (t : ℕ) + 1 + k ≤ n → ((t : ℕ) + 1 + k) * (G ((t : ℕ) + 1 + k)).card
      = ((t : ℕ) + 1) * R.a t := by
    intro k
    induction k with
    | zero =>
      intro _
      congr 2
      ext c
      simp only [G, mem_filter, mem_univ, true_and, add_zero]
      refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun s hs hs' => ?_⟩⟩
      have : (t : ℕ) < s := hs
      omega
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      set u := (t : ℕ) + 1 + k with hu
      have hun : u < n := by omega
      set U : Fin n := ⟨u, hun⟩
      have htU : t < U := Fin.lt_def.mpr (by simp only [U]; omega)
      have hL := card_filter_zero_mul U (G u) (by
        intro c j hc
        simp only [G, mem_filter, mem_univ, true_and] at hc ⊢
        refine ⟨(R.stopAt_update j htU).2 hc.1, ?_, fun s hs hsu => ?_⟩
        · rw [Function.update_of_ne (ne_of_lt htU)]; exact hc.2.1
        · have hsU : s ≠ U := by
            intro h; rw [h] at hsu; simp [U] at hsu
          rw [Function.update_of_ne hsU]; exact hc.2.2 s hs hsu)
      have hsplit := Finset.card_filter_add_card_filter_not (s := G u) (fun c => c U = 0)
      have hnext : (G u).filter (fun c => ¬ c U = 0) = G (u + 1) := by
        ext c
        simp only [G, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨⟨h1, h2, h3⟩, h4⟩
          refine ⟨h1, h2, fun s hs hsu => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hsu with h | h
          · exact h3 s hs h
          · have : s = U := Fin.ext h
            rw [this]; exact h4
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨h1, h2, fun s hs hsu => h3 s hs (by omega)⟩, h3 U htU (by simp [U])⟩
      rw [hnext] at hsplit
      rw [show (t : ℕ) + 1 + (k + 1) = u + 1 by omega]
      have e1 : (u + 1) * (G (u + 1)).card + (u + 1) * ((G u).filter fun c => c U = 0).card
          = (u + 1) * (G u).card := by rw [← hsplit]; ring
      rw [hL] at e1
      have e2 : (u + 1) * (G u).card = u * (G u).card + (G u).card := by ring
      omega
  have h := hG (n - ((t : ℕ) + 1)) (by omega)
  rw [show (t : ℕ) + 1 + (n - ((t : ℕ) + 1)) = n by omega] at h
  rw [← h]
  congr 2
  ext c
  simp only [G, mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨h.1, h.2.1, fun s hs _ => h.2.2 s hs⟩,
    fun h => ⟨h.1, h.2.1, fun s hs => h.2.2 s hs s.2⟩⟩

/-- The constraint of the linear program:
`(t + 1) a_t ≤ n! - ∑_{s<t} a_s`. -/
lemma RankRule.constraint (R : RankRule n) (t : Fin n) :
    ((t : ℕ) + 1) * R.a t + ∑ s ∈ univ.filter (· < t), R.a s ≤ n ! := by
  set NB := univ.filter fun c : RankSeq n => ∀ s, s < t → ¬ R.D s c
  have h1 : R.a t ≤ (NB.filter fun c => c t = 0).card := by
    refine Finset.card_le_card fun c hc => ?_
    simp only [NB, mem_filter, mem_univ, true_and] at hc ⊢
    exact ⟨hc.1.2, hc.2⟩
  have h2 := card_filter_zero_mul t NB (by
    intro c j hc
    simp only [NB, mem_filter, mem_univ, true_and] at hc ⊢
    exact (R.notBefore_update j).2 hc)
  set SA := fun s : Fin n => univ.filter fun c : RankSeq n => R.StopAt s c
  have h3 : ∀ s, R.a s ≤ (SA s).card := fun s => Finset.card_le_card fun c hc => by
    simp only [SA, mem_filter, mem_univ, true_and] at hc ⊢; exact hc.1
  have hdisj : Disjoint NB ((univ.filter (· < t)).biUnion SA) := by
    rw [Finset.disjoint_biUnion_right]
    intro s hs
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [NB, SA, mem_filter, mem_univ, true_and] at hc hc' hs
    exact hc s hs hc'.1
  have hcardU : NB.card + ((univ.filter (· < t)).biUnion SA).card ≤ n ! := by
    rw [← Finset.card_union_of_disjoint hdisj, ← card_rankSeq]
    exact Finset.card_le_univ _
  rw [Finset.card_biUnion (fun s _ s' _ hss' => by
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [SA, mem_filter, mem_univ, true_and] at hc hc'
    exact hss' (R.stopAt_unique hc hc'))] at hcardU
  have h4 : ∑ s ∈ univ.filter (· < t), R.a s ≤ ∑ s ∈ univ.filter (· < t), (SA s).card :=
    Finset.sum_le_sum fun s _ => h3 s
  have h5 : ((t : ℕ) + 1) * R.a t ≤ NB.card := by
    rw [← h2]; exact Nat.mul_le_mul_left _ h1
  omega

/-- The success count is the sum of the per-time success counts. -/
lemma RankRule.card_success (R : RankRule n) :
    (univ.filter fun c => R.Success c).card
      = ∑ t, (univ.filter fun c => R.StopAt t c ∧ c t = 0 ∧ ∀ s, t < s → c s ≠ 0).card := by
  rw [← Finset.card_biUnion (fun t _ t' _ htt' => by
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [mem_filter, mem_univ, true_and] at hc hc'
    exact htt' (R.stopAt_unique hc.1 hc'.1))]
  congr 1
  ext c
  rw [Finset.mem_filter, Finset.mem_biUnion]
  simp only [mem_univ, true_and, mem_filter, RankRule.Success]

/-- **No relative-rank rule beats the best threshold rule.** Under the uniform distribution on
the `n!` relative-rank sequences, every stopping rule that sees only relative ranks selects the
overall best arrival with probability at most `max_{0 ≤ r ≤ n} thrVal n r`. -/
theorem RankRule.success_prob_le (R : RankRule n) :
    ((univ.filter fun c => R.Success c).card : ℝ) / n ! ≤ M n 0 := by
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  let x : ℕ → ℝ := fun s => if h : s < n then (R.a ⟨s, h⟩ : ℝ) / n ! else 0
  have hx0 : ∀ t < n, 0 ≤ x t := fun t ht => by
    simp only [x, ht, ↓reduceDIte]; positivity
  have hsum : ∀ t : Fin n, ∑ s ∈ range t, x s
      = (∑ s ∈ univ.filter (· < t), (R.a s : ℝ)) / n ! := by
    intro t
    rw [Finset.sum_div, Finset.sum_filter]
    have h1 : ∀ s : Fin n, (if s < t then (R.a s : ℝ) / n ! else 0)
        = (fun i : ℕ => if i < (t : ℕ) then x i else 0) s := by
      intro s
      simp only
      by_cases hst : s < t
      · simp only [hst, Fin.lt_def.mp hst, ↓reduceIte]
        simp [x, s.2]
      · have hst' : ¬ (s : ℕ) < t := fun h => hst (Fin.lt_def.mpr h)
        simp only [hst, hst', ↓reduceIte]
    rw [Finset.sum_congr rfl (fun s _ => h1 s),
      Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < (t : ℕ) then x i else 0) n,
      ← Finset.sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    have := t.2
    omega
  have hcon : ∀ t < n, ((t : ℝ) + 1) * x t ≤ 1 - ∑ s ∈ range t, x s := by
    intro t ht
    have hc := R.constraint ⟨t, ht⟩
    have hc' : ((t : ℝ) + 1) * R.a ⟨t, ht⟩
        + ∑ s ∈ univ.filter (· < (⟨t, ht⟩ : Fin n)), (R.a s : ℝ) ≤ n ! := by
      exact_mod_cast hc
    have h2 := hsum ⟨t, ht⟩
    simp only at h2
    rw [h2]
    simp only [x, ht, ↓reduceDIte]
    rw [le_sub_iff_add_le, ← mul_div_assoc, ← add_div, div_le_one hfac]
    exact hc'
  have hsucc : ((univ.filter fun c => R.Success c).card : ℝ) / n !
      = ∑ t ∈ range n, ((t : ℝ) + 1) * x t / n := by
    rw [R.card_success, Nat.cast_sum, Finset.sum_div,
      ← Fin.sum_univ_eq_sum_range (fun t : ℕ => ((t : ℝ) + 1) * x t / n) n]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h := R.card_success_at t
    have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt t.2)
    have h' : (n : ℝ) * ((univ.filter fun c => R.StopAt t c ∧ c t = 0 ∧
        ∀ s, t < s → c s ≠ 0).card : ℝ) = ((t : ℝ) + 1) * R.a t := by exact_mod_cast h
    simp only [x, t.2, ↓reduceDIte, Fin.eta]
    field_simp
    linear_combination h'
  rw [hsucc]
  exact lp_bound n x hx0 hcon

/-- `max_{r ≤ n} thrVal n r` is attained. -/
lemma exists_M_eq (n : ℕ) : ∃ r ≤ n, M n 0 = thrVal n r := by
  obtain ⟨r, hr, h⟩ := Finset.exists_mem_eq_sup' (nonempty_Icc.2 (le_max_left 0 n)) (thrVal n)
  exact ⟨r, by simpa using (mem_Icc.1 hr).2, h⟩

open Applied.Economics.MatroidSecretary in
/-- `thrVal n r` is the exact success probability of the library's threshold rule
`thresholdRule r κ` under a uniformly random arrival order (`n = |E|`, distinct keys). -/
theorem thrVal_eq_threshold_prob {E α : Type*} [Fintype E] [LinearOrder α]
    (κ : E × ℝ → α) (w : E → ℝ) (hinj : Function.Injective fun e => κ (e, w e)) (b : E)
    (hb : ∀ e, κ (e, w e) ≤ κ (b, w b)) (r : ℕ) :
    thrVal (Fintype.card E) r =
      (#{σ : ArrivalOrder E | b ∈ selected (thresholdRule r κ) σ w} : ℝ) /
        (Fintype.card E)! := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h := card_thresholdRule_success_zero κ w b
    have hn : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos_iff.2 ⟨b⟩
    have hfac : (0 : ℝ) < (Fintype.card E)! := by exact_mod_cast Nat.factorial_pos _
    rw [thrVal, if_pos rfl, eq_div_iff hfac.ne', ← h]
    field_simp
  · rw [thresholdRule_success_prob κ w hinj b hb hr, thrVal, if_neg hr.ne']

open Applied.Economics.MatroidSecretary in
/-- **No relative-rank rule beats the best threshold rule (comparison with the arrival-order
model).** For any finite `E` with distinct keys and best element `b`, and any stopping rule `R`
in the relative-rank model of length `n = |E|`, some threshold `r ≤ n` makes the library's
`thresholdRule r κ` accept `b` with probability (over uniformly random arrival orders) at least
the success probability of `R` (over uniformly random relative-rank sequences). -/
theorem exists_thresholdRule_ge {E α : Type*} [Fintype E] [LinearOrder α]
    (κ : E × ℝ → α) (w : E → ℝ) (hinj : Function.Injective fun e => κ (e, w e)) (b : E)
    (hb : ∀ e, κ (e, w e) ≤ κ (b, w b)) (R : RankRule (Fintype.card E)) :
    ∃ r ≤ Fintype.card E,
      ((univ.filter fun c => R.Success c).card : ℝ) / (Fintype.card E)! ≤
        (#{σ : ArrivalOrder E | b ∈ selected (thresholdRule r κ) σ w} : ℝ) /
          (Fintype.card E)! := by
  obtain ⟨r, hr, h⟩ := exists_M_eq (Fintype.card E)
  refine ⟨r, hr, ?_⟩
  rw [← thrVal_eq_threshold_prob κ w hinj b hb r, ← h]
  exact R.success_prob_le

end Applied.Economics.SecretaryRank
