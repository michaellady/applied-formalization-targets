import Applied.InformationTheory.DeletionLowerBound
import Applied.InformationTheory.DataProcessing

/-!
# Degraded channel families and monotonicity of the deletion capacity

* `Achievable.of_degraded`: if every kernel of `F'` is the kernel of `F` followed by a
  row-stochastic kernel, then every rate achievable over `F'` is achievable over `F` (the
  randomised decoder "degrade, then decode" is replaced by a deterministic most-likely-message
  decoder, at the cost of a factor `2` in the maximal error probability).
* `opCapacity_le_of_degraded`: hence `opCapacity F' ≤ opCapacity F`.
* `delExp_delExp`: deleting with probability `d` and then with probability `e` is deleting with
  probability `d + (1 - d) e`.
* `delKernel_eq_comp_delDegrade`: the corresponding identity of kernels.
* `deletionCapacity_antitoneOn`: `deletionCapacity` is nonincreasing on `[0, 1]`.
-/

open Finset Real

namespace Applied.InformationTheory

/-! ### Degraded channel families -/

section Degraded

variable {X : Type*}

/-- **Degradation.** If `F'.kernel n = comp (F.kernel n) (K n)` with `K n` row-stochastic, then
every rate achievable over `F'` is achievable over `F`. -/
theorem Achievable.of_degraded {F F' : ChannelFamily X} (hF : ∀ n x y, 0 ≤ F.kernel n x y)
    (K : ∀ n, F.Out n → F'.Out n → ℝ) (hK : ∀ n, IsChannel (K n))
    (hcomp : ∀ n, F'.kernel n = comp (F.kernel n) (K n)) {R : ℝ} (h : Achievable F' R) :
    Achievable F R := by
  classical
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, c', hM, hc'⟩ := hN n hn
  have hMpos : 0 < M := by
    have : (0 : ℝ) < M := (exp_pos _).trans_le hM
    exact_mod_cast this
  set p : F.Out n → Fin M → ℝ := fun z m' => ∑ y, K n z y * (if c'.dec y = m' then 1 else 0)
    with hp
  have hp0 : ∀ z m', 0 ≤ p z m' := fun z m' =>
    Finset.sum_nonneg fun y _ => mul_nonneg ((hK n).nonneg z y) (by split_ifs <;> norm_num)
  have hpsum : ∀ z, ∑ m', p z m' = 1 := by
    intro z
    rw [hp]
    simp only
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_one]
    exact (hK n).sum_eq_one z
  have hex : ∀ z, ∃ m, ∀ m', p z m' ≤ p z m := fun z => by
    obtain ⟨m, -, hm⟩ := Finset.exists_max_image univ (p z) ⟨⟨0, hMpos⟩, mem_univ _⟩
    exact ⟨m, fun m' => hm m' (mem_univ _)⟩
  choose g hg using hex
  let c : BlockCode F n M := ⟨c'.enc, g⟩
  have herr' : ∀ m, c'.errorProb m = ∑ z, F.kernel n (c'.enc m) z * (1 - p z m) := by
    intro m
    unfold BlockCode.errorProb
    simp only [hcomp n, comp]
    have : ∀ y, (if c'.dec y = m then 0 else ∑ z, F.kernel n (c'.enc m) z * K n z y) =
        ∑ z, F.kernel n (c'.enc m) z * (K n z y * (if c'.dec y = m then 0 else 1)) := fun y => by
      split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    have h1 := (hK n).sum_eq_one z
    rw [hp]
    simp only
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine (Finset.sum_congr rfl fun y _ => ?_).trans h1
    split_ifs <;> ring
  have hple : ∀ z m, p z m ≤ 1 := fun z m => by
    rw [← hpsum z]
    exact Finset.single_le_sum (fun m' _ => hp0 z m') (mem_univ m)
  have herr : ∀ m, c.errorProb m ≤ 2 * c'.errorProb m := by
    intro m
    rw [herr', Finset.mul_sum]
    unfold BlockCode.errorProb
    refine Finset.sum_le_sum fun z _ => ?_
    have hple := hple z m
    have hk := hF n (c'.enc m) z
    change (if g z = m then 0 else F.kernel n (c'.enc m) z) ≤ _
    split_ifs with hgz
    · nlinarith
    · have hpair : p z m + p z (g z) ≤ 1 := by
        rw [← hpsum z, ← Finset.sum_pair (Ne.symm hgz)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun m' _ _ => hp0 z m'
      have := hg z m
      nlinarith
  refine ⟨M, c, hM, ?_⟩
  refine Real.iSup_le (fun m => ?_) hε.le
  have := c'.errorProb_le_maxError m
  linarith [herr m]

/-- A degraded channel family has smaller operational capacity. -/
theorem opCapacity_le_of_degraded [Fintype X] [Nonempty X] {F F' : ChannelFamily X}
    (hF : F.IsStochastic) (K : ∀ n, F.Out n → F'.Out n → ℝ) (hK : ∀ n, IsChannel (K n))
    (hcomp : ∀ n, F'.kernel n = comp (F.kernel n) (K n)) : opCapacity F' ≤ opCapacity F :=
  csSup_le ⟨0, achievable_zero F'⟩ fun _ h =>
    le_opCapacity hF (h.of_degraded (fun n x y => (hF n).nonneg x y) K hK hcomp)

end Degraded

/-! ### Two rounds of deletions -/

/-- Deleting with probability `d` and then with probability `e` is deleting with probability
`d + (1 - d) e`. -/
lemma delExp_delExp (d e : ℝ) : ∀ (x : List Bool) (G : List Bool → ℝ),
    delExp d x (fun z => delExp e z G) = delExp (d + (1 - d) * e) x G
  | [], _ => rfl
  | a :: x, G => by
      rw [delExp_cons, delExp_cons, delExp_delExp d e x G]
      have : (fun z => delExp e (a :: z) G) =
          fun z => e * delExp e z G + (1 - e) * delExp e z (fun w => G (a :: w)) := by
        funext z; rw [delExp_cons]
      rw [this, delExp_add, delExp_const_mul, delExp_const_mul, delExp_delExp d e x G,
        delExp_delExp d e x (fun w => G (a :: w))]
      ring

lemma delExp_sum {ι : Type*} (d : ℝ) (s : Finset ι) : ∀ (x : List Bool)
    (F : ι → List Bool → ℝ),
    delExp d x (fun z => ∑ i ∈ s, F i z) = ∑ i ∈ s, delExp d x (F i)
  | [], _ => rfl
  | a :: x, F => by
      simp only [delExp_cons]
      rw [delExp_sum d s x F, delExp_sum d s x (fun i z => F i (a :: z)), Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib]

variable {n : ℕ}

/-- The deletion kernel in terms of `delExp`. -/
lemma delKernel_eq_delExp (d : ℝ) (x : Fin n → Bool) (y : DelOut n) :
    delKernel d n x y = delExp d (List.ofFn x) (fun l => if l = outList y then 1 else 0) := by
  rw [← sum_delWeight_eq_delExp]
  unfold delKernel
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : deleteBits x s = y
  · simp [h]
  · have : outList (deleteBits x s) ≠ outList y := fun h' => h (outList_injective h')
    simp [h, this]

/-- A list of length at most `n` as a deletion-channel output. -/
def listOut (l : List Bool) (h : l.length ≤ n) : DelOut n :=
  ⟨⟨l.length, Nat.lt_succ_of_le h⟩, l.get⟩

lemma outList_listOut (l : List Bool) (h : l.length ≤ n) : outList (listOut l h) = l :=
  List.ofFn_get l

lemma length_outList_le (z : DelOut n) : (outList z).length ≤ n := by
  have := z.1.2
  simp only [outList, List.length_ofFn]
  omega

/-- For a list `l` of length at most `n`, summing over the outputs `z` with `outList z = l`
picks the single output `listOut l`. -/
lemma sum_ite_outList (l : List Bool) (h : l.length ≤ n) (f : DelOut n → ℝ) :
    ∑ z : DelOut n, f z * (if l = outList z then 1 else 0) = f (listOut l h) := by
  rw [Finset.sum_eq_single (listOut l h)]
  · simp [outList_listOut]
  · intro z _ hz
    have : l ≠ outList z := fun h' => hz (outList_injective (by rw [outList_listOut, h']))
    simp [this]
  · simp

/-- The kernel that deletes each letter of a received word with probability `e`. -/
noncomputable def delDegrade (e : ℝ) (n : ℕ) (z y : DelOut n) : ℝ :=
  delExp e (outList z) (fun l => if l = outList y then 1 else 0)

lemma isChannel_delDegrade {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) (n : ℕ) :
    IsChannel (delDegrade e n) where
  nonneg z y := delExp_nonneg h0 h1 _ fun l _ => by split_ifs <;> norm_num
  sum_eq_one z := by
    unfold delDegrade
    rw [← delExp_sum]
    rw [delExp_congr (G := fun _ => 1) _ fun l hl => ?_, delExp_const]
    have hlen : l.length ≤ n := hl.length_le.trans (length_outList_le z)
    have := sum_ite_outList l hlen (fun _ => 1)
    simpa using this

/-- **Deleting twice.** The deletion kernel with probability `d + (1 - d) e` is the deletion
kernel with probability `d` followed by deletions with probability `e`. -/
theorem delKernel_eq_comp_delDegrade (d e : ℝ) (n : ℕ) :
    delKernel (d + (1 - d) * e) n = comp (delKernel d n) (delDegrade e n) := by
  funext x y
  unfold comp
  simp only [delKernel_eq_delExp d]
  have : ∀ z : DelOut n,
      delExp d (List.ofFn x) (fun l => if l = outList z then 1 else 0) * delDegrade e n z y =
        delExp d (List.ofFn x)
          (fun l => delDegrade e n z y * (if l = outList z then 1 else 0)) := fun z => by
    rw [delExp_const_mul, mul_comm]
  simp only [this]
  rw [← delExp_sum, delKernel_eq_delExp, ← delExp_delExp]
  refine (delExp_congr _ fun l hl => ?_).symm
  have hlen : l.length ≤ n := by
    have := hl.length_le
    simpa using this
  rw [sum_ite_outList l hlen (fun z => delDegrade e n z y), delDegrade, outList_listOut]

/-- More deletions cannot help: for `0 ≤ d ≤ d' ≤ 1`, `C(d') ≤ C(d)`. -/
theorem deletionCapacity_le_of_le {d d' : ℝ} (h0 : 0 ≤ d) (hdd : d ≤ d') (h1 : d' ≤ 1) :
    deletionCapacity d' ≤ deletionCapacity d := by
  rcases (hdd.trans h1).lt_or_eq with hlt | rfl
  · have h1d : 0 < 1 - d := by linarith
    set e : ℝ := (d' - d) / (1 - d) with he
    have he0 : 0 ≤ e := div_nonneg (by linarith) h1d.le
    have he1 : e ≤ 1 := by rw [he, div_le_one h1d]; linarith
    have hd' : d' = d + (1 - d) * e := by rw [he]; field_simp; ring
    unfold deletionCapacity
    refine opCapacity_le_of_degraded (F := deletionChannel d) (F' := deletionChannel d')
      (isStochastic_deletionChannel h0 (hdd.trans h1)) (fun n => delDegrade e n)
      (fun n => isChannel_delDegrade he0 he1 n) fun n => ?_
    change delKernel d' n = comp (delKernel d n) (delDegrade e n)
    rw [hd', delKernel_eq_comp_delDegrade]
  · have : d' = 1 := le_antisymm h1 hdd
    rw [this]

/-- **Monotonicity**: the capacity of the deletion channel is nonincreasing in the deletion
probability on `[0, 1]`. -/
theorem deletionCapacity_antitoneOn : AntitoneOn deletionCapacity (Set.Icc 0 1) :=
  fun _ hd _ hd' hdd => deletionCapacity_le_of_le hd.1 hdd hd'.2

end Applied.InformationTheory
