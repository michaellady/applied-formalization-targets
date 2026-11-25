import Applied.InformationTheory.DeletionChannel
import Applied.InformationTheory.SupersequenceCount
import Applied.InformationTheory.CodebookSelection
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Coding over the deletion channel with a subsequence decoder

Tools for lower bounds on the capacity of the binary deletion channel.

* `outList y`: a channel output as a list of bits; `outList_deleteBits`: the output for the
  kept set `s` is the list of the letters of `x` at the positions in `s`, in order;
  `outList_sublist`: every output is a subsequence (`List.Sublist`) of the input word.
* `delExp d x F`: the expectation of `F` over the output of the deletion channel on the word
  `x` (a list), defined by recursion on `x`; `sum_delWeight_eq_delExp` identifies it with the
  sum over the sets of kept positions. `delExp_append`: outputs of consecutive blocks are
  independent.
* The codebook is chosen with `exists_codebook_rows_le'` from `CodebookSelection` (greedy
  choice plus expurgation for a nonnegative, not necessarily symmetric, weight).
* `subseqCode`: the decoder that outputs some message whose codeword can produce the received
  word.
* `exists_deletion_code`: if every candidate word produces a "good" output except with
  probability `τ`, and every good output of a candidate can be produced by at most `B`
  candidates, then there is a code with `M + 1` candidates as codewords and maximal error
  probability at most `τ + 12 (M + 1) B / N`, `N` the number of candidates.
-/

open Finset Real

namespace Applied.InformationTheory

/-! ### Outputs as lists -/

/-- A deletion-channel output as a list of bits. -/
def outList {n : ℕ} (y : DelOut n) : List Bool := List.ofFn y.2

lemma sort_eq_filter_finRange {n : ℕ} (s : Finset (Fin n)) :
    s.sort (· ≤ ·) = (List.finRange n).filter (· ∈ s) := by
  have hnd : ((List.finRange n).filter (· ∈ s)).Nodup := (List.nodup_finRange n).filter _
  have hfs : ((List.finRange n).filter (· ∈ s)).toFinset = s := by
    ext i; simp
  have hpw : ((List.finRange n).filter (· ∈ s)).Pairwise (· ≤ ·) :=
    ((List.sortedLT_finRange n).pairwise.imp le_of_lt).filter _
  have := (List.toFinset_sort (r := (· ≤ ·)) hnd).mpr hpw
  rwa [hfs] at this

/-- The output for the kept set `s` lists the letters of `x` at the positions in `s`. -/
lemma outList_deleteBits {n : ℕ} (x : Fin n → Bool) (s : Finset (Fin n)) :
    outList (deleteBits x s) = ((List.finRange n).filter (· ∈ s)).map x := by
  rw [← sort_eq_filter_finRange]
  unfold outList deleteBits
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [Finset.orderEmbOfFin_apply]

/-- Every output of the deletion channel is a subsequence of the input. -/
lemma outList_sublist {n : ℕ} (x : Fin n → Bool) (s : Finset (Fin n)) :
    (outList (deleteBits x s)).Sublist (List.ofFn x) := by
  rw [outList_deleteBits, List.ofFn_eq_map]
  exact (List.filter_sublist).map x

lemma length_outList_deleteBits {n : ℕ} (x : Fin n → Bool) (s : Finset (Fin n)) :
    (outList (deleteBits x s)).length = s.card := by
  simp [outList, deleteBits]

/-! ### The output distribution by recursion on the input word -/

/-- The expectation of `F` over the output of the deletion channel with deletion probability
`d` on the input word `x`: the first letter is deleted with probability `d` and kept with
probability `1 - d`, independently of the rest. -/
noncomputable def delExp (d : ℝ) : List Bool → (List Bool → ℝ) → ℝ
  | [], F => F []
  | a :: x, F => d * delExp d x F + (1 - d) * delExp d x (fun z => F (a :: z))

@[simp] lemma delExp_nil (d : ℝ) (F : List Bool → ℝ) : delExp d [] F = F [] := rfl

lemma delExp_cons (d : ℝ) (a : Bool) (x : List Bool) (F : List Bool → ℝ) :
    delExp d (a :: x) F = d * delExp d x F + (1 - d) * delExp d x (fun z => F (a :: z)) := rfl

lemma delExp_const (d : ℝ) (c : ℝ) : ∀ x : List Bool, delExp d x (fun _ => c) = c
  | [] => rfl
  | a :: x => by rw [delExp_cons, delExp_const d c x]; ring

lemma delExp_add (d : ℝ) : ∀ (x : List Bool) (F G : List Bool → ℝ),
    delExp d x (fun z => F z + G z) = delExp d x F + delExp d x G
  | [], _, _ => rfl
  | a :: x, F, G => by
      rw [delExp_cons, delExp_cons, delExp_cons, delExp_add d x F G,
        delExp_add d x (fun z => F (a :: z)) (fun z => G (a :: z))]
      ring

lemma delExp_const_mul (d : ℝ) (c : ℝ) : ∀ (x : List Bool) (F : List Bool → ℝ),
    delExp d x (fun z => c * F z) = c * delExp d x F
  | [], _ => rfl
  | a :: x, F => by
      rw [delExp_cons, delExp_cons, delExp_const_mul d c x F,
        delExp_const_mul d c x (fun z => F (a :: z))]
      ring

/-- Monotonicity; only the values on subsequences of the input matter. -/
lemma delExp_mono {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) : ∀ (x : List Bool) {F G : List Bool → ℝ},
    (∀ z : List Bool, z.Sublist x → F z ≤ G z) → delExp d x F ≤ delExp d x G
  | [], _, _, h => h [] (List.Sublist.refl _)
  | a :: x, F, G, h => by
      rw [delExp_cons, delExp_cons]
      have e1 := delExp_mono h0 h1 x (F := F) (G := G) fun z hz => h z (hz.cons a)
      have e2 := delExp_mono h0 h1 x (F := fun z => F (a :: z)) (G := fun z => G (a :: z))
        fun z hz => h (a :: z) (hz.cons_cons a)
      have : 0 ≤ 1 - d := by linarith
      nlinarith

lemma delExp_congr {d : ℝ} : ∀ (x : List Bool) {F G : List Bool → ℝ},
    (∀ z : List Bool, z.Sublist x → F z = G z) → delExp d x F = delExp d x G
  | [], _, _, h => h [] (List.Sublist.refl _)
  | a :: x, F, G, h => by
      rw [delExp_cons, delExp_cons,
        delExp_congr x (F := F) (G := G) fun z hz => h z (hz.cons a),
        delExp_congr x (F := fun z => F (a :: z)) (G := fun z => G (a :: z))
          fun z hz => h (a :: z) (hz.cons_cons a)]

lemma delExp_nonneg {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (x : List Bool) {F : List Bool → ℝ}
    (h : ∀ z : List Bool, z.Sublist x → 0 ≤ F z) : 0 ≤ delExp d x F := by
  have := delExp_mono h0 h1 x (F := fun _ => 0) (G := F) h
  rwa [delExp_const] at this

lemma delExp_le_const {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (x : List Bool) {F : List Bool → ℝ}
    {c : ℝ} (h : ∀ z : List Bool, z.Sublist x → F z ≤ c) : delExp d x F ≤ c := by
  have := delExp_mono h0 h1 x (F := F) (G := fun _ => c) h
  rwa [delExp_const] at this

/-- **Independence of blocks**: the output of `x₁ ++ x₂` is the output of `x₁` followed by an
independent output of `x₂`. -/
lemma delExp_append (d : ℝ) : ∀ (x₁ x₂ : List Bool) (F : List Bool → ℝ),
    delExp d (x₁ ++ x₂) F = delExp d x₁ fun z₁ => delExp d x₂ fun z₂ => F (z₁ ++ z₂)
  | [], _, _ => rfl
  | a :: x₁, x₂, F => by
      rw [List.cons_append, delExp_cons, delExp_cons, delExp_append d x₁ x₂ F,
        delExp_append d x₁ x₂ (fun z => F (a :: z))]
      rfl

/-- The generating function of the output length. -/
lemma delExp_pow_length (d t : ℝ) : ∀ x : List Bool,
    delExp d x (fun z => t ^ z.length) = (d + (1 - d) * t) ^ x.length
  | [] => by simp
  | a :: x => by
      rw [delExp_cons, delExp_pow_length d t x]
      have : (fun z : List Bool => t ^ (a :: z).length) = fun z => t * t ^ z.length := by
        funext z; rw [List.length_cons, pow_succ]; ring
      rw [this, delExp_const_mul, delExp_pow_length d t x, List.length_cons, pow_succ]
      ring

/-- The pattern sum over the subsets of a duplicate-free list of positions. -/
lemma sum_powerset_eq_delExp {ι : Type*} [DecidableEq ι] (d : ℝ) (x : ι → Bool) :
    ∀ (l : List ι), l.Nodup → ∀ G : List Bool → ℝ,
      ∑ s ∈ l.toFinset.powerset, d ^ (l.length - s.card) * (1 - d) ^ s.card *
        G ((l.filter (· ∈ s)).map x) = delExp d (l.map x) G
  | [], _, G => by simp
  | a :: l, hl, G => by
      have ha : a ∉ l := (List.nodup_cons.mp hl).1
      have hl' : l.Nodup := (List.nodup_cons.mp hl).2
      have ha' : a ∉ l.toFinset := by simpa using ha
      rw [List.toFinset_cons, Finset.sum_powerset_insert ha', List.map_cons, delExp_cons,
        ← sum_powerset_eq_delExp d x l hl' G,
        ← sum_powerset_eq_delExp d x l hl' (fun z => G (x a :: z)), Finset.mul_sum,
        Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun t ht => ?_
        have hsub : t ⊆ l.toFinset := Finset.mem_powerset.mp ht
        have hat : a ∉ t := fun h => ha' (hsub h)
        have hcard : t.card ≤ l.length := by
          have := Finset.card_le_card hsub
          rwa [List.toFinset_card_of_nodup hl'] at this
        rw [List.filter_cons_of_neg (by simpa using hat), List.length_cons,
          Nat.succ_sub hcard, pow_succ]
        ring
      · refine Finset.sum_congr rfl fun t ht => ?_
        have hsub : t ⊆ l.toFinset := Finset.mem_powerset.mp ht
        have hat : a ∉ t := fun h => ha' (hsub h)
        have hfil : l.filter (· ∈ insert a t) = l.filter (· ∈ t) := by
          refine List.filter_congr fun b hb => ?_
          have : b ≠ a := fun h => ha (h ▸ hb)
          simp [this]
        rw [List.filter_cons_of_pos (by simp), hfil, List.map_cons,
          Finset.card_insert_of_notMem hat, List.length_cons, Nat.succ_sub_succ, pow_succ]
        ring

/-- **The deletion channel by recursion.** The sum over the sets of kept positions, weighted
by the pattern probabilities, of a function of the output list is `delExp`. -/
theorem sum_delWeight_eq_delExp (d : ℝ) {n : ℕ} (x : Fin n → Bool) (G : List Bool → ℝ) :
    ∑ s : Finset (Fin n), d ^ (n - s.card) * (1 - d) ^ s.card * G (outList (deleteBits x s))
      = delExp d (List.ofFn x) G := by
  have := sum_powerset_eq_delExp d x (List.finRange n) (List.nodup_finRange n) G
  rw [List.toFinset_finRange, Finset.powerset_univ, List.length_finRange] at this
  rw [List.ofFn_eq_map, ← this]
  exact Finset.sum_congr rfl fun s _ => by rw [outList_deleteBits]

/-- Sums against the deletion kernel are sums over the sets of kept positions. -/
lemma sum_delKernel_mul (d : ℝ) {n : ℕ} (x : Fin n → Bool) (h : DelOut n → ℝ) :
    ∑ y, delKernel d n x y * h y =
      ∑ s : Finset (Fin n), d ^ (n - s.card) * (1 - d) ^ s.card * h (deleteBits x s) := by
  unfold delKernel
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [ite_mul]

/-! ### The subsequence decoder -/

section Coding

variable {n : ℕ}

/-- Decode to some message whose codeword can produce the received word (message `0` if there
is none). -/
noncomputable def subseqCode (d : ℝ) {M : ℕ} (c : Fin (M + 1) → (Fin n → Bool)) :
    BlockCode (deletionChannel d) n (M + 1) where
  enc := c
  dec y := by
    classical
    exact if h : ∃ m, ∃ s, deleteBits (c m) s = y then Classical.choose h else 0

open Classical in
/-- **A coding theorem for the deletion channel with a subsequence decoder.** Let `w u`,
`u : ι`, be candidate codewords of length `n` and `Good` a set of outputs. If every candidate
produces a good output except with probability `τ`, and every good output of a candidate can be
produced by at most `B` candidates, then for every `M` there is a code with `M + 1` messages,
all codewords candidates, with maximal error probability at most `τ + 12 (M + 1) B / |ι|`. -/
theorem exists_deletion_code {ι : Type} [Fintype ι] [Nonempty ι] {d : ℝ} (h0 : 0 ≤ d)
    (h1 : d ≤ 1) (w : ι → Fin n → Bool) (Good : DelOut n → Prop) {τ B : ℝ} (hB0 : 0 ≤ B)
    (hτ : ∀ u, ∑ s : Finset (Fin n), d ^ (n - s.card) * (1 - d) ^ s.card *
      (if Good (deleteBits (w u) s) then 0 else 1) ≤ τ)
    (hB : ∀ u s, Good (deleteBits (w u) s) →
      ((univ.filter fun u' => ∃ s', deleteBits (w u') s' = deleteBits (w u) s).card : ℝ) ≤ B)
    (M : ℕ) :
    ∃ c : BlockCode (deletionChannel d) n (M + 1), (∀ m, ∃ u, c.enc m = w u) ∧
      c.maxError ≤ τ + 12 * ((M : ℝ) + 1) * (B / Fintype.card ι) := by
  set wt : Finset (Fin n) → ℝ := fun s => d ^ (n - s.card) * (1 - d) ^ s.card with hwt
  have hwt0 : ∀ s, 0 ≤ wt s := fun s =>
    mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)
  have hwt1 : ∑ s, wt s = 1 := sum_delWeight d n
  set f : ι → ι → ℝ := fun u u' => ∑ s, wt s *
    (if Good (deleteBits (w u) s) ∧ ∃ s', deleteBits (w u') s' = deleteBits (w u) s
      then 1 else 0) with hf
  have hf0 : ∀ u u', 0 ≤ f u u' := fun u u' =>
    Finset.sum_nonneg fun s _ => mul_nonneg (hwt0 s) (by split_ifs <;> norm_num)
  have hrow : ∀ u, ∑ u', f u u' ≤ B := by
    intro u
    rw [hf]
    simp only
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    calc ∑ s, wt s * ∑ u', (if Good (deleteBits (w u) s) ∧
          ∃ s', deleteBits (w u') s' = deleteBits (w u) s then (1 : ℝ) else 0)
        ≤ ∑ s, wt s * B := by
          refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hwt0 s)
          by_cases hg : Good (deleteBits (w u) s)
          · simp only [hg, true_and]
            rw [Finset.sum_boole]
            exact hB u s hg
          · simp [hg, hB0]
      _ = B := by rw [← Finset.sum_mul, hwt1, one_mul]
  obtain ⟨c, hc⟩ := exists_codebook_rows_le' hf0 hrow (M + 1)
  refine ⟨subseqCode d (fun m => w (c m)), fun m => ⟨c m, rfl⟩, ?_⟩
  have hτ0 : 0 ≤ τ := le_trans (Finset.sum_nonneg fun s _ =>
    mul_nonneg (hwt0 s) (by split_ifs <;> norm_num)) (hτ (Classical.arbitrary ι))
  refine Real.iSup_le (fun m => ?_) (by positivity)
  set C := subseqCode d (fun m => w (c m)) with hC
  have hrw : C.errorProb m = ∑ y : DelOut n, delKernel d n (w (c m)) y *
      (if C.dec y = m then 0 else 1) := by
    unfold BlockCode.errorProb
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp [hC, subseqCode]
  rw [hrw, sum_delKernel_mul]
  have hind : ∀ s : Finset (Fin n),
      (if C.dec (deleteBits (w (c m)) s) = m then (0 : ℝ) else 1) ≤
        (if Good (deleteBits (w (c m)) s) then 0 else 1) + ∑ m', if m = m' then 0 else
          (if Good (deleteBits (w (c m)) s) ∧
            ∃ s', deleteBits (w (c m')) s' = deleteBits (w (c m)) s then 1 else 0) := by
    intro s
    have hnn : ∀ m' ∈ (univ : Finset (Fin (M + 1))), (0 : ℝ) ≤ (if m = m' then 0 else
        (if Good (deleteBits (w (c m)) s) ∧
            ∃ s', deleteBits (w (c m')) s' = deleteBits (w (c m)) s then 1 else 0)) :=
      fun m' _ => by split_ifs <;> norm_num
    have hs := Finset.sum_nonneg hnn
    by_cases hd : C.dec (deleteBits (w (c m)) s) = m
    · rw [ite_eq_left hd]; split_ifs <;> linarith
    · rw [ite_eq_right hd]
      by_cases hg : Good (deleteBits (w (c m)) s)
      · rw [ite_eq_left hg, zero_add]
        have hex : ∃ m', ∃ s', deleteBits (w (c m')) s' = deleteBits (w (c m)) s :=
          ⟨m, s, rfl⟩
        have hdec : C.dec (deleteBits (w (c m)) s) = Classical.choose hex := by
          simp only [hC, subseqCode]
          rw [dite_eq_left hex]
        have hspec : ∃ s', deleteBits (w (c (C.dec (deleteBits (w (c m)) s)))) s'
            = deleteBits (w (c m)) s := by
          rw [hdec]; exact Classical.choose_spec hex
        refine le_trans ?_ (Finset.single_le_sum hnn
          (mem_univ (C.dec (deleteBits (w (c m)) s))))
        rw [ite_eq_right (Ne.symm hd), ite_eq_left ⟨hg, hspec⟩]
      · rw [ite_eq_right hg]; linarith
  calc ∑ s : Finset (Fin n), wt s *
        (if C.dec (deleteBits (w (c m)) s) = m then (0 : ℝ) else 1)
      ≤ ∑ s : Finset (Fin n), wt s * ((if Good (deleteBits (w (c m)) s) then 0 else 1) +
          ∑ m', if m = m' then 0 else
          (if Good (deleteBits (w (c m)) s) ∧
            ∃ s', deleteBits (w (c m')) s' = deleteBits (w (c m)) s then 1 else 0)) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hind s) (hwt0 s)
    _ = (∑ s : Finset (Fin n), wt s * (if Good (deleteBits (w (c m)) s) then 0 else 1)) +
          ∑ m', if m = m' then 0 else f (c m) (c m') := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m' _ => ?_
        rw [hf]
        split_ifs <;> simp
    _ ≤ τ + 12 * ((M : ℝ) + 1) * (B / Fintype.card ι) := by
        have := hc m
        push_cast at this
        exact add_le_add (hτ (c m)) this

end Coding

end Applied.InformationTheory
