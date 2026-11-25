import Applied.InformationTheory.DeletionChannel
import Applied.Coding.VarshamovTenengolts
import Mathlib.Data.Nat.Choose.Sum

/-!
# Single-deletion codes on the deletion channel

This file connects the combinatorial single-deletion codes of
`Applied/Coding/VarshamovTenengolts.lean` with the binary deletion channel of
`Applied/InformationTheory/DeletionChannel.lean`.

* `deleteBits_erase`: keeping all positions but `i` is `Fin.removeNth i`.
* `IsSingleDeletionCode.eq_of_deleteBits_eq`: in a single-deletion-correcting code of length
  `m + 1`, the channel output with at most one deletion determines the codeword.
* `IsSingleDeletionCode.exists_decoder`: hence a decoder that is always right when at most one
  bit is deleted (zero-error decoding of one deletion).
* `errorProb_le_of_decoder`: for a block code for the deletion channel with deletion
  probability `d ∈ [0, 1]` whose decoder is right whenever at most one bit is deleted, every
  message is decoded wrongly with probability at most
  `1 - (1 - d)^(m+1) - (m + 1) d (1 - d)^m`, the probability of two or more deletions.
* `IsSingleDeletionCode.exists_blockCode`: a nonempty single-deletion-correcting code gives
  such a block code, with `|C|` messages.
* `exists_blockCode_vt`: a VT code gives a block code with `M` messages,
  `(m + 2) M ≥ 2^(m+1)`, and this error bound.

Not in this file: any capacity statement.  For fixed `d > 0` the error bound tends to `1` as the
length grows (although the rate of the VT codes tends to `log 2`), so nothing follows for
`Achievable` or `deletionCapacity`; the capacity lower bounds are in `DeletionLowerBound` and
`DeletionPositive`.
-/

open Finset Applied.Coding

namespace Applied.InformationTheory

/-- Keeping every position except `i` is deleting the bit in position `i`. -/
lemma deleteBits_erase {m : ℕ} (x : Fin (m + 1) → Bool) (i : Fin (m + 1)) :
    deleteBits x (univ.erase i) = ⟨⟨m, by omega⟩, Fin.removeNth i x⟩ := by
  have hc : (univ.erase i).card = m := by simp [Finset.card_erase_of_mem]
  have hmono : StrictMono (fun k : Fin (univ.erase i).card => i.succAbove (Fin.cast hc k)) :=
    (Fin.strictMono_succAbove i).comp (Fin.castOrderIso hc).strictMono
  have hmem : ∀ k : Fin (univ.erase i).card, i.succAbove (Fin.cast hc k) ∈ univ.erase i :=
    fun k => by simp [Fin.succAbove_ne]
  have huniq := Finset.orderEmbOfFin_unique rfl hmem hmono
  unfold deleteBits
  refine Sigma.ext (Fin.ext hc) ?_
  refine (Fin.heq_fun_iff hc).mpr fun k => ?_
  simp only [Fin.removeNth_apply]
  rw [← huniq]
  rfl

/-- A set of kept positions of size at least `m` (out of `m + 1`) is everything, or everything
but one position. -/
lemma eq_univ_or_eq_erase {m : ℕ} {s : Finset (Fin (m + 1))} (hs : m ≤ s.card) :
    s = univ ∨ ∃ i, s = univ.erase i := by
  have hle : s.card ≤ m + 1 := by simpa using s.card_le_univ
  rcases (show s.card = m + 1 ∨ s.card = m by omega) with h | h
  · left; exact s.eq_univ_of_card (by simpa using h)
  · right
    have hc : sᶜ.card = 1 := by rw [Finset.card_compl]; simp [h]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    refine ⟨i, ?_⟩
    ext j
    have := congrArg (j ∈ ·) hi
    simp only [mem_compl, mem_singleton, eq_iff_iff] at this
    simp only [mem_erase, mem_univ, and_true]
    tauto

/-- **One deletion is corrected in the channel model.** In a single-deletion-correcting code
of length `m + 1`, if two codewords give the same channel output when at most one bit of each
is deleted, they are equal. -/
theorem IsSingleDeletionCode.eq_of_deleteBits_eq {m : ℕ} {C : Finset (Fin (m + 1) → Bool)}
    (hC : IsSingleDeletionCode C) {x x' : Fin (m + 1) → Bool} (hx : x ∈ C) (hx' : x' ∈ C)
    {s t : Finset (Fin (m + 1))} (hs : m ≤ s.card) (ht : m ≤ t.card)
    (h : deleteBits x s = deleteBits x' t) : x = x' := by
  have hcard : s.card = t.card := by
    have := congrArg (fun y : DelOut (m + 1) => (y.1 : ℕ)) h
    simpa [deleteBits] using this
  rcases eq_univ_or_eq_erase hs with rfl | ⟨i, rfl⟩ <;>
    rcases eq_univ_or_eq_erase ht with rfl | ⟨j, rfl⟩
  · exact deleteBits_univ_injective _ h
  · simp [Finset.card_erase_of_mem] at hcard
  · simp [Finset.card_erase_of_mem] at hcard
  · rw [deleteBits_erase, deleteBits_erase] at h
    have hrem : Fin.removeNth i x = Fin.removeNth j x' := eq_of_heq (Sigma.mk.inj h).2
    by_contra hne
    exact Finset.disjoint_left.mp (hC x hx x' hx' hne) (mem_delBall.mpr ⟨i, rfl⟩)
      (mem_delBall.mpr ⟨j, hrem.symm⟩)

/-- **Zero-error decoding of one deletion.** A single-deletion-correcting code has a decoder
that recovers the codeword from every channel output in which at most one bit was deleted. -/
theorem IsSingleDeletionCode.exists_decoder {m : ℕ} {C : Finset (Fin (m + 1) → Bool)}
    (hC : IsSingleDeletionCode C) :
    ∃ dec : DelOut (m + 1) → (Fin (m + 1) → Bool),
      ∀ x ∈ C, ∀ s : Finset (Fin (m + 1)), m ≤ s.card → dec (deleteBits x s) = x := by
  classical
  refine ⟨fun y => if h : ∃ x ∈ C, ∃ s : Finset (Fin (m + 1)), m ≤ s.card ∧ deleteBits x s = y
    then h.choose else fun _ => false, fun x hx s hs => ?_⟩
  dsimp only
  split_ifs with h'
  swap; · exact absurd ⟨x, hx, s, hs, rfl⟩ h'
  obtain ⟨hmem, t, ht, hteq⟩ := h'.choose_spec
  exact IsSingleDeletionCode.eq_of_deleteBits_eq hC hmem hx ht hs hteq

/-- The probability of at most one deletion among `m + 1` bits. -/
lemma sum_delWeight_filter (d : ℝ) (m : ℕ) :
    ∑ s ∈ (univ : Finset (Finset (Fin (m + 1)))).filter (fun s => m ≤ s.card),
      d ^ (m + 1 - s.card) * (1 - d) ^ s.card
      = (1 - d) ^ (m + 1) + (m + 1) * d * (1 - d) ^ m := by
  rw [Finset.sum_filter, ← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun k => if m ≤ k then d ^ (m + 1 - k) * (1 - d) ^ k else 0)]
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero fun k hk => by simp [Nat.not_le.mpr (mem_range.mp hk)]]
  simp [Nat.choose_succ_self_right]
  ring

/-- **Error probability of a single-deletion code on the deletion channel.** Let `C` be a
single-deletion-correcting code of length `m + 1` and `d ∈ [0, 1]`. Any block code that sends
codewords of `C` and decodes with a decoder that is right whenever at most one bit is deleted
has error probability at most `1 - (1 - d)^(m+1) - (m + 1) d (1 - d)^m` for every message. -/
theorem errorProb_le_of_decoder {m M : ℕ} {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1)
    (c : BlockCode (deletionChannel d) (m + 1) M)
    (hdec : ∀ k, ∀ s : Finset (Fin (m + 1)), m ≤ s.card → c.dec (deleteBits (c.enc k) s) = k)
    (k : Fin M) :
    c.errorProb k ≤ 1 - ((1 - d) ^ (m + 1) + (m + 1) * d * (1 - d) ^ m) := by
  classical
  set w : Finset (Fin (m + 1)) → ℝ := fun s => d ^ (m + 1 - s.card) * (1 - d) ^ s.card with hw
  have hw0 : ∀ s, 0 ≤ w s := fun s => mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)
  have hexp : c.errorProb k = ∑ s, if c.dec (deleteBits (c.enc k) s) = k then 0 else w s := by
    unfold BlockCode.errorProb
    change (∑ y : DelOut (m + 1), if c.dec y = k then 0 else delKernel d (m + 1) (c.enc k) y) = _
    unfold delKernel
    have : ∀ y : DelOut (m + 1), (if c.dec y = k then 0 else
        ∑ s : Finset (Fin (m + 1)), if deleteBits (c.enc k) s = y then w s else 0)
        = ∑ s : Finset (Fin (m + 1)), if deleteBits (c.enc k) s = y then
            (if c.dec (deleteBits (c.enc k) s) = k then 0 else w s) else 0 := by
      intro y
      split_ifs with hy
      · refine (Finset.sum_eq_zero fun s _ => ?_).symm
        split_ifs with h1 h2 <;> simp_all
      · refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs with h1 h2 <;> simp_all
    rw [Finset.sum_congr rfl fun y _ => this y, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp
  have hsum : (∑ s, if c.dec (deleteBits (c.enc k) s) = k then 0 else w s)
      + ∑ s, (if m ≤ s.card then w s else 0) ≤ ∑ s, w s := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    by_cases hs : m ≤ s.card
    · simp [hs, hdec k s hs]
    · simp only [hs, ite_false, add_zero]
      split_ifs
      · exact hw0 s
      · exact le_rfl
  have htot : ∑ s, w s = 1 := sum_delWeight d (m + 1)
  have hf : ∑ s, (if m ≤ s.card then w s else 0)
      = (1 - d) ^ (m + 1) + (m + 1) * d * (1 - d) ^ m := by
    rw [← sum_delWeight_filter d m, Finset.sum_filter]
  rw [hexp]
  linarith

/-- **Single-deletion codes on the deletion channel.** A nonempty single-deletion-correcting
code `C` of length `m + 1` gives a block code with `|C|` messages, whose codewords are the
elements of `C`, and whose error probability for every message is at most the probability
`1 - (1 - d)^(m+1) - (m + 1) d (1 - d)^m` of two or more deletions (`d ∈ [0, 1]`). -/
theorem IsSingleDeletionCode.exists_blockCode {m : ℕ} {C : Finset (Fin (m + 1) → Bool)}
    (hC : IsSingleDeletionCode C) (hne : C.Nonempty) {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) :
    ∃ c : BlockCode (deletionChannel d) (m + 1) C.card,
      (∀ k, c.enc k ∈ C) ∧ Function.Injective c.enc ∧
      ∀ k, c.errorProb k ≤ 1 - ((1 - d) ^ (m + 1) + (m + 1) * d * (1 - d) ^ m) := by
  classical
  obtain ⟨dec, hdec⟩ := IsSingleDeletionCode.exists_decoder hC
  let e : Fin C.card ≃ C := C.equivFin.symm
  have hpos : 0 < C.card := hne.card_pos
  let c : BlockCode (deletionChannel d) (m + 1) C.card :=
    { enc := fun k => (e k).1
      dec := fun y => if h : dec y ∈ C then e.symm ⟨dec y, h⟩ else ⟨0, hpos⟩ }
  have hcdec : ∀ k, ∀ s : Finset (Fin (m + 1)), m ≤ s.card →
      c.dec (deleteBits (c.enc k) s) = k := by
    intro k s hs
    have h := hdec (e k).1 (e k).2 s hs
    change (if h : dec (deleteBits (e k).1 s) ∈ C then e.symm ⟨_, h⟩ else ⟨0, hpos⟩) = k
    split_ifs with h'
    · rw [Equiv.symm_apply_eq]; exact Subtype.ext h
    · exact absurd (by rw [h]; exact (e k).2) h'
  refine ⟨c, fun k => (e k).2, fun k k' hkk' => e.injective (Subtype.ext hkk'), fun k => ?_⟩
  exact errorProb_le_of_decoder h0 h1 c hcdec k

/-- **VT codes on the deletion channel.** For every `m` and `d ∈ [0, 1]` there is a block code
for the deletion channel of length `m + 1` with `M` messages, `(m + 2) M ≥ 2^(m+1)`, whose
codewords form a Varshamov–Tenengolts code and whose error probability for every message is at
most `1 - (1 - d)^(m+1) - (m + 1) d (1 - d)^m`. -/
theorem exists_blockCode_vt (m : ℕ) {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) :
    ∃ a ≤ m + 1, ∃ M, 2 ^ (m + 1) ≤ (m + 2) * M ∧
      ∃ c : BlockCode (deletionChannel d) (m + 1) M,
        (∀ k, c.enc k ∈ vtCode (m + 1) a) ∧ Function.Injective c.enc ∧
        ∀ k, c.errorProb k ≤ 1 - ((1 - d) ^ (m + 1) + (m + 1) * d * (1 - d) ^ m) := by
  obtain ⟨a, ha, hcard⟩ := exists_vtCode_card_mul_ge (m + 1)
  have hne : (vtCode (m + 1) a).Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0'
    simp only [not_lt, nonpos_iff_eq_zero] at h0'
    rw [h0', mul_zero] at hcard
    exact absurd hcard (Nat.not_le.mpr (by positivity))
  obtain ⟨c, hmem, hinj, herr⟩ := IsSingleDeletionCode.exists_blockCode (isSingleDeletionCode_vtCode m a) hne h0 h1
  exact ⟨a, ha, _, hcard, c, hmem, hinj, herr⟩

end Applied.InformationTheory
