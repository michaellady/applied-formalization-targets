import Applied.Economics.MatroidSecretary
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The matroid secretary problem: direct sums, partition matroids, elementary facts

Everything uses the model of `Applied/Economics/MatroidSecretary.lean` unchanged
(`ArrivalOrder`, `OnlineAlg`, `Accepts`, `selected`, `expWeight`, `IsFeasible`,
`IsCompetitive`, `HasCompetitiveRandomized`).

## Blocks and induced orders

* A map `f : E → ι` splits `E` into *blocks* `Block f i = {e // f e = i}`.
* `blockOrder f i σ : ArrivalOrder (Block f i)`: the elements of block `i` listed in the order
  in which they arrive under `σ` (defined from the list `List.ofFn σ` filtered to the block).
* `card_blockOrder_fiber` (**uniform restriction**, a counting statement): for every arrival
  order `τ` of block `i`, exactly `n! / nᵢ!` of the `n!` arrival orders `σ` of `E` induce `τ`
  (stated as `nᵢ! * #{σ | blockOrder f i σ = τ} = n!`). So a uniformly random arrival order
  of `E` induces a uniformly random arrival order of each block.
* `blockOrder_symm_lt_iff`: `blockOrder f i σ` is indeed the order of arrival: `x` comes before
  `y` in it iff `x` arrives before `y` under `σ`.
* `blockSum f A`: given online algorithms `A i` for the blocks, the online algorithm on `E`
  that, at the arrival of an element of block `i`, extracts from the arrivals so far the
  subsequence of block-`i` arrivals (with their weights) and asks `A i`. `accepts_blockSum`:
  it accepts `x` in block `i` iff `A i` accepts `x` under `blockOrder f i σ` and the
  restricted weights.
* `expWeight_blockSum`: the expected weight of `blockSum f A` is the sum over the blocks of the
  expected weights of the `A i`.

## Direct sums

* `IsBlockSum M Mb`: `M` is the direct sum of the matroids `Mb i` on the blocks (a set is
  independent iff each of its traces on the blocks is).
* `blockSum_isFeasible`, `blockSum_isCompetitive`: feasibility and `c`-competitiveness pass
  from the blocks to the direct sum (deterministic algorithms; `ι` finite).
* `HasCompetitiveRandomized.blockSum`: the same for randomized algorithms (`ι : Type`
  finite); the random seeds of the blocks are drawn independently (product measure).
  `HasCompetitiveRandomized.directSum`: the case of two summands.
* `integrable_of_competitive`: for `c > 0` the integrand in `HasCompetitiveRandomized` is
  automatically integrable.

## Partition matroids with capacities one

* `partitionOne f`: independent sets are the sets on which `f` is injective (at most one
  element per block). `partitionOne_isBlockSum`: it is the direct sum of the rank-one uniform
  matroids `rankOne (Block f i)`.
* `exists_isCompetitive_partitionOne`, `hasCompetitiveRandomized_partitionOne`: for every
  `f : E → ι` (any `ι`), running the half rule `halfRuleLex` independently inside each block is
  feasible and `1/4`-competitive.

## Elementary facts

* `IsCompetitive.mono`, `HasCompetitiveRandomized.mono`: monotone in the constant.
* `hasCompetitiveRandomized_of_nonpos`: every `c ≤ 0` is achieved (by accepting nothing).
* `HasCompetitiveRandomized.le_one`: if `M` has a non-loop then `c ≤ 1` (non-degeneracy).
* `HasCompetitiveRandomized.restrict`: a `c`-competitive randomized algorithm for `M` gives one
  for every restriction `M ↾ R` (deletion of the elements outside `R`).
-/

open Finset Function

open scoped Nat

open Classical

noncomputable section

namespace Applied.Economics.MatroidSecretary

variable {E : Type*} [Fintype E]

/-- Run an online algorithm on a list of arrivals: its decision on the last element of the
list (false for the empty list). -/
def runList {α : Type*} (A : OnlineAlg α) (L : List (α × ℝ)) : Prop :=
  ∃ (m : ℕ) (hm : L.length = m + 1), A m (fun j => L.get (Fin.cast hm.symm j))

lemma runList_ofFn {α : Type*} (A : OnlineAlg α) (k : ℕ) (h : Fin (k + 1) → α × ℝ) :
    runList A (List.ofFn h) ↔ A k h := by
  constructor
  · rintro ⟨m, hm, hA⟩
    have hmk : m = k := by simp at hm; omega
    subst hmk
    convert hA using 1
    funext j
    simp only [List.get_eq_getElem, List.getElem_ofFn, Fin.val_cast]
  · intro hA
    refine ⟨k, by simp, ?_⟩
    convert hA using 1
    funext j
    simp only [List.get_eq_getElem, List.getElem_ofFn, Fin.val_cast]

/-- The arrivals up to time `t`, as a list. -/
lemma ofFn_arrivals (σ : ArrivalOrder E) (w : E → ℝ) (t : Fin (Fintype.card E)) :
    List.ofFn (arrivals σ w t) = ((List.ofFn σ).take (t + 1)).map fun x => (x, w x) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, List.length_take]; omega
  · intro j h1 h2
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_take, arrivals]
    rfl

lemma accepts_iff_runList (A : OnlineAlg E) (σ : ArrivalOrder E) (w : E → ℝ) (e : E) :
    Accepts A σ w e ↔ runList A (((List.ofFn σ).take (σ.symm e + 1)).map fun x => (x, w x)) := by
  rw [← ofFn_arrivals, runList_ofFn]
  rfl

section Blocks

variable {ι : Type*} [DecidableEq ι] (f : E → ι)

/-- The block of `i`: the elements `e` with `f e = i`. -/
abbrev Block (f : E → ι) (i : ι) : Type _ := {e // f e = i}

/-- `e` as an element of the block of `i`, if it is one. -/
def toBlock (i : ι) (e : E) : Option (Block f i) := if h : f e = i then some ⟨e, h⟩ else none

/-- The elements of the block of `i` in a list, in the same relative order. -/
def blockList (i : ι) (l : List E) : List (Block f i) := l.filterMap (toBlock f i)

omit [Fintype E] in
lemma mem_blockList {i : ι} {l : List E} {x : Block f i} : x ∈ blockList f i l ↔ x.1 ∈ l := by
  simp only [blockList, List.mem_filterMap, toBlock]
  constructor
  · rintro ⟨a, ha, h⟩
    split_ifs at h with hfa
    cases h
    exact ha
  · intro hx
    exact ⟨x.1, hx, by simp [x.2]⟩

omit [Fintype E] in
lemma blockList_nodup (i : ι) {l : List E} (hl : l.Nodup) : (blockList f i l).Nodup := by
  refine hl.filterMap fun a a' b ha ha' => ?_
  simp only [toBlock, Option.mem_def] at ha ha'
  split_ifs at ha ha'
  cases ha; cases ha'
  rfl

omit [Fintype E] in
lemma blockList_append (i : ι) (l l' : List E) :
    blockList f i (l ++ l') = blockList f i l ++ blockList f i l' := List.filterMap_append

omit [Fintype E] in
lemma blockList_singleton_self (e : E) :
    blockList f (f e) [e] = [⟨e, rfl⟩] := by
  simp [blockList, toBlock]

omit [Fintype E] in
lemma blockList_map_perm (i : ι) (π : Equiv.Perm E) (ρ : Equiv.Perm (Block f i))
    (hπ : ∀ x : Block f i, π x = ρ x) (hπ' : ∀ e, f (π e) = i ↔ f e = i) (l : List E) :
    blockList f i (l.map π) = (blockList f i l).map ρ := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, blockList, List.filterMap_cons] at ih ⊢
    by_cases ha : f a = i
    · have ha' : f (π a) = i := (hπ' a).2 ha
      have h1 : toBlock f i (π a) = some (ρ ⟨a, ha⟩) := by
        simp only [toBlock, ha', dite_true]
        congr 1
        exact Subtype.ext (hπ ⟨a, ha⟩)
      have h2 : toBlock f i a = some ⟨a, ha⟩ := by simp [toBlock, ha]
      rw [h1, h2, ih]
      rfl
    · have ha' : ¬ f (π a) = i := fun h => ha ((hπ' a).1 h)
      have h1 : toBlock f i (π a) = none := by simp [toBlock, ha']
      have h2 : toBlock f i a = none := by simp [toBlock, ha]
      rw [h1, h2, ih]

lemma blockList_ofFn_nodup (i : ι) (σ : ArrivalOrder E) : (blockList f i (List.ofFn σ)).Nodup :=
  blockList_nodup f i (List.nodup_ofFn.2 σ.injective)

lemma mem_blockList_ofFn (i : ι) (σ : ArrivalOrder E) (x : Block f i) :
    x ∈ blockList f i (List.ofFn σ) :=
  (mem_blockList f).2 (List.mem_ofFn.2 ⟨σ.symm x, by simp⟩)

lemma length_blockList_ofFn (i : ι) (σ : ArrivalOrder E) :
    (blockList f i (List.ofFn σ)).length = Fintype.card (Block f i) := by
  have := Fintype.card_congr ((blockList_ofFn_nodup f i σ).getEquivOfForallMemList _
    (mem_blockList_ofFn f i σ))
  simpa using this

/-- The arrival order induced on the block of `i`: its elements in the order in which they
arrive under `σ`. -/
def blockOrder (i : ι) (σ : ArrivalOrder E) : ArrivalOrder (Block f i) :=
  (finCongr (length_blockList_ofFn f i σ).symm).trans
    ((blockList_ofFn_nodup f i σ).getEquivOfForallMemList _ (mem_blockList_ofFn f i σ))

lemma ofFn_blockOrder (i : ι) (σ : ArrivalOrder E) :
    List.ofFn (blockOrder f i σ) = blockList f i (List.ofFn σ) := by
  apply List.ext_getElem
  · simp [length_blockList_ofFn]
  · intro j h1 h2
    simp [blockOrder]

lemma blockOrder_trans (i : ι) (σ : ArrivalOrder E) (π : Equiv.Perm E) (ρ : Equiv.Perm (Block f i))
    (hπ : ∀ x : Block f i, π x = ρ x) (hπ' : ∀ e, f (π e) = i ↔ f e = i) :
    blockOrder f i (σ.trans π) = (blockOrder f i σ).trans ρ := by
  apply Equiv.coe_fn_injective
  apply List.ofFn_injective
  change List.ofFn (blockOrder f i (σ.trans π)) = List.ofFn (ρ ∘ blockOrder f i σ)
  rw [ofFn_blockOrder, Equiv.coe_trans, ← List.map_ofFn, blockList_map_perm f i π ρ hπ hπ',
    ← List.map_ofFn, ofFn_blockOrder]


/-- Run, inside each block `i`, the online algorithm `A i` on the arrivals of that block only:
an arrival in block `i` is accepted iff `A i` accepts it given the subsequence of earlier
arrivals (with their weights) that lie in block `i`. -/
def blockSum (A : ∀ i, OnlineAlg (Block f i)) : OnlineAlg E := fun k h =>
  runList (A (f (h (Fin.last k)).1))
    ((List.ofFn h).filterMap fun p => (toBlock f (f (h (Fin.last k)).1) p.1).map fun b => (b, p.2))

omit [Fintype E] in
lemma filterMap_toBlock_map (i : ι) (w : E → ℝ) (l : List E) :
    (l.map fun x => (x, w x)).filterMap (fun p => (toBlock f i p.1).map fun b => (b, p.2)) =
      (blockList f i l).map fun x : Block f i => (x, w x) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.filterMap_cons, blockList] at ih ⊢
    rw [ih]
    by_cases ha : f a = i <;> simp [toBlock, ha]

/-- The key fact: `blockSum` accepts an element `x` of block `i` iff `A i` accepts it under the
arrival order induced on block `i` and the restricted weights. -/
theorem accepts_blockSum (A : ∀ i, OnlineAlg (Block f i)) (σ : ArrivalOrder E) (w : E → ℝ)
    {i : ι} (x : Block f i) :
    Accepts (blockSum f A) σ w x.1 ↔ Accepts (A i) (blockOrder f i σ) (fun y => w y) x := by
  obtain ⟨e, rfl⟩ := x
  set t := σ.symm e with ht
  have hlast : arrivals σ w t (Fin.last _) = (e, w e) := by
    have : Fin.castLE t.isLt (Fin.last (t : ℕ)) = t := Fin.ext rfl
    simp [arrivals, this, ht]
  rw [accepts_iff_runList (A (f e)), ofFn_blockOrder]
  unfold Accepts blockSum
  rw [← ht, hlast, ofFn_arrivals]
  dsimp only
  rw [filterMap_toBlock_map]
  -- the block list of the prefix is a prefix of the block list
  set L := List.ofFn σ with hL
  have hLt : L[(t : ℕ)]? = some e := by simp [hL, ht]
  have htake : L.take (t + 1) = L.take t ++ [e] := by
    rw [List.take_add_one, hLt]; rfl
  set P := blockList f (f e) (L.take t) with hP
  have hsplit : blockList f (f e) L =
      (P ++ [⟨e, rfl⟩]) ++ blockList f (f e) (L.drop (t + 1)) := by
    conv_lhs => rw [← List.take_append_drop (t + 1) L]
    rw [blockList_append, htake, blockList_append, blockList_singleton_self]
  have hpre : blockList f (f e) (L.take (t + 1)) = P ++ [⟨e, rfl⟩] := by
    rw [htake, blockList_append, blockList_singleton_self]
  have hpos : (((blockOrder f (f e) σ).symm ⟨e, rfl⟩ : Fin _) : ℕ) = P.length := by
    have hlen : P.length < (blockList f (f e) L).length := by
      rw [hsplit]; simp
    have hget : (blockList f (f e) L)[P.length] = ⟨e, rfl⟩ := by
      simp only [hsplit, List.append_assoc]
      simp
    have hlen' : P.length < Fintype.card (Block f (f e)) := by
      rwa [← length_blockList_ofFn f (f e) σ]
    have : (blockOrder f (f e) σ) ⟨P.length, hlen'⟩ = ⟨e, rfl⟩ := by
      rw [← hget]
      simp [blockOrder, hL]
    rw [← this, Equiv.symm_apply_apply]
  rw [hpos, hpre, hsplit, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]


/-- The position of an element in the induced order of its block is the number of elements of
its block that arrive before it. -/
lemma blockOrder_symm_val (σ : ArrivalOrder E) (e : E) :
    (((blockOrder f (f e) σ).symm ⟨e, rfl⟩ : Fin _) : ℕ) =
      (blockList f (f e) ((List.ofFn σ).take (σ.symm e))).length := by
  set L := List.ofFn σ with hL
  set t := σ.symm e with ht
  have hLt : L[(t : ℕ)]? = some e := by simp [hL, ht]
  have htake : L.take (t + 1) = L.take t ++ [e] := by
    rw [List.take_add_one, hLt]; rfl
  set P := blockList f (f e) (L.take t) with hP
  have hsplit : blockList f (f e) L =
      (P ++ [⟨e, rfl⟩]) ++ blockList f (f e) (L.drop (t + 1)) := by
    conv_lhs => rw [← List.take_append_drop (t + 1) L]
    rw [blockList_append, htake, blockList_append, blockList_singleton_self]
  have hget : (blockList f (f e) L)[P.length]'(by rw [hsplit]; simp) = ⟨e, rfl⟩ := by
    simp only [hsplit, List.append_assoc]
    simp
  have hlen' : P.length < Fintype.card (Block f (f e)) := by
    rw [← length_blockList_ofFn f (f e) σ, hsplit]; simp
  have : (blockOrder f (f e) σ) ⟨P.length, hlen'⟩ = ⟨e, rfl⟩ := by
    rw [← hget]
    simp [blockOrder, hL]
  rw [← this, Equiv.symm_apply_apply]

omit [Fintype E] in
lemma blockList_singleton_val {i : ι} (x : Block f i) : blockList f i [x.1] = [x] := by
  obtain ⟨e, rfl⟩ := x
  exact blockList_singleton_self f e

lemma blockOrder_symm_val' {i : ι} (σ : ArrivalOrder E) (x : Block f i) :
    (((blockOrder f i σ).symm x : Fin _) : ℕ) =
      (blockList f i ((List.ofFn σ).take (σ.symm x))).length := by
  obtain ⟨e, rfl⟩ := x
  exact blockOrder_symm_val f σ e

/-- `blockOrder f i σ` lists the elements of block `i` in the order of their arrival under
`σ`. -/
theorem blockOrder_symm_lt_iff (i : ι) (σ : ArrivalOrder E) (x y : Block f i) :
    (blockOrder f i σ).symm x < (blockOrder f i σ).symm y ↔ σ.symm x < σ.symm y := by
  have key : ∀ x y : Block f i, σ.symm x < σ.symm y →
      (blockOrder f i σ).symm x < (blockOrder f i σ).symm y := by
    intro x y hxy
    rw [Fin.lt_def, blockOrder_symm_val', blockOrder_symm_val']
    set L := List.ofFn σ
    have hLt : L[((σ.symm x : Fin _) : ℕ)]? = some x.1 := by simp [L]
    have htake : L.take (σ.symm x + 1) = L.take (σ.symm x) ++ [x.1] := by
      rw [List.take_add_one, hLt]; rfl
    have hpre : L.take (σ.symm x + 1) <+: L.take (σ.symm y) :=
      List.take_prefix_take_left (by rw [Fin.lt_def] at hxy; omega)
    have := (hpre.filterMap (toBlock f i)).length_le
    rw [htake] at this
    change (blockList f i (L.take (σ.symm x) ++ [x.1])).length ≤
      (blockList f i (L.take (σ.symm y))).length at this
    rw [blockList_append, blockList_singleton_val, List.length_append,
      List.length_singleton] at this
    omega
  constructor
  · intro h
    rcases lt_trichotomy (σ.symm x) (σ.symm y) with h' | h' | h'
    · exact h'
    · have hxy : x = y := Subtype.ext (σ.symm.injective h')
      rw [hxy] at h; exact absurd h (lt_irrefl _)
    · exact absurd (key y x h') (not_lt.2 h.le)
  · exact key x y

lemma card_arrivalOrder (α : Type*) [Fintype α] [Fintype (ArrivalOrder α)] :
    Fintype.card (ArrivalOrder α) = (Fintype.card α)! := by
  have := Fintype.card_equiv (Fintype.equivFin α).symm
  rw [Fintype.card_fin] at this
  convert this

/-- All fibres of `σ ↦ blockOrder f i σ` have the same size. -/
lemma card_blockOrder_fiber_eq (i : ι) (τ τ' : ArrivalOrder (Block f i)) :
    #{σ : ArrivalOrder E | blockOrder f i σ = τ} = #{σ : ArrivalOrder E | blockOrder f i σ = τ'} := by
  set ρ : Equiv.Perm (Block f i) := τ.symm.trans τ' with hρ
  set π : Equiv.Perm E := Equiv.Perm.subtypeCongr ρ (Equiv.refl _) with hπ
  have hπ1 : ∀ x : Block f i, π x = ρ x := fun x => Equiv.Perm.subtypeCongr.left_apply_subtype _ _ x
  have hπ2 : ∀ e, f (π e) = i ↔ f e = i := by
    intro e
    by_cases he : f e = i
    · simp only [he, iff_true]
      rw [hπ1 ⟨e, he⟩]
      exact (ρ ⟨e, he⟩).2
    · simp only [he, iff_false]
      rw [hπ, Equiv.Perm.subtypeCongr.apply]
      simp [he]
  refine Finset.card_equiv ((Equiv.refl _).equivCongr π) fun σ => ?_
  have hσ : (Equiv.refl _).equivCongr π σ = σ.trans π := by ext; simp
  simp only [mem_filter, mem_univ, true_and]
  rw [hσ, blockOrder_trans f i σ π ρ hπ1 hπ2]
  constructor
  · intro h
    ext x
    simp [h, hρ]
  · intro h
    ext x
    have := congrArg Subtype.val (Equiv.congr_fun h x)
    simp only [Equiv.trans_apply, hρ] at this
    have h2 := τ'.injective (Subtype.ext this)
    rw [Equiv.symm_apply_eq] at h2
    rw [h2]

/-- **Uniform restriction.** Under a uniformly random arrival order of `E`, the induced arrival
order of each block is uniformly random: each of the `nᵢ!` orders of block `i` is induced by
exactly `n! / nᵢ!` of the `n!` orders of `E`. -/
theorem card_blockOrder_fiber (i : ι) (τ : ArrivalOrder (Block f i)) :
    (Fintype.card (Block f i))! * #{σ : ArrivalOrder E | blockOrder f i σ = τ} =
      (Fintype.card E)! := by
  have h := Fintype.sum_fiberwise (blockOrder f i) (fun _ : ArrivalOrder E => (1 : ℕ))
  simp only [sum_const, smul_eq_mul, mul_one, Finset.card_univ, card_arrivalOrder] at h
  rw [← h, Finset.sum_congr rfl fun τ' _ => ?_, sum_const, Finset.card_univ, card_arrivalOrder,
    smul_eq_mul]
  rw [Fintype.card_subtype, card_blockOrder_fiber_eq f i τ' τ]

lemma sum_blockOrder (i : ι) (F : ArrivalOrder (Block f i) → ℝ) :
    ((Fintype.card (Block f i))! : ℝ) * ∑ σ : ArrivalOrder E, F (blockOrder f i σ) =
      (Fintype.card E)! * ∑ τ, F τ := by
  rw [← Fintype.sum_fiberwise (blockOrder f i), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hc := card_blockOrder_fiber f i τ
  have hsum : ∑ σ : {σ : ArrivalOrder E // blockOrder f i σ = τ}, F (blockOrder f i σ) =
      #{σ : ArrivalOrder E | blockOrder f i σ = τ} * F τ := by
    rw [Finset.sum_congr rfl fun σ _ => by rw [σ.2], sum_const, Finset.card_univ,
      Fintype.card_subtype, nsmul_eq_mul]
  rw [hsum, ← mul_assoc, ← Nat.cast_mul, hc]


variable [Fintype ι]

omit [Fintype ι] in
lemma preimage_selected_blockSum (A : ∀ i, OnlineAlg (Block f i)) (σ : ArrivalOrder E)
    (w : E → ℝ) (i : ι) :
    Subtype.val ⁻¹' (selected (blockSum f A) σ w : Set E) =
      (selected (A i) (blockOrder f i σ) (fun y => w y) : Set (Block f i)) := by
  ext x
  simp [accepts_blockSum]

/-- The expected weight of `blockSum` is the sum over the blocks of the expected weights of the
block algorithms (each under a uniformly random order of its block). -/
theorem expWeight_blockSum (A : ∀ i, OnlineAlg (Block f i)) (w : E → ℝ) :
    expWeight (blockSum f A) w = ∑ i, expWeight (A i) (fun y : Block f i => w y) := by
  set G : ∀ i, ArrivalOrder (Block f i) → ℝ := fun i τ =>
    ∑ x ∈ selected (A i) τ (fun y => w y), w x with hG
  have hσ : ∀ σ : ArrivalOrder E, ∑ e ∈ selected (blockSum f A) σ w, w e =
      ∑ i, G i (blockOrder f i σ) := by
    intro σ
    rw [selected, Finset.sum_filter, ← Fintype.sum_fiberwise f]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hG, selected, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [accepts_blockSum]
  have hfac : ((Fintype.card E)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [expWeight, Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfi : ((Fintype.card (Block f i))! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have := sum_blockOrder f i (G i)
  rw [expWeight, div_eq_div_iff hfac hfi]
  simp only [hG] at this ⊢
  rw [mul_comm, mul_comm _ ((Fintype.card E)! : ℝ)]
  convert this using 4

variable {f}

/-- `M` is the direct sum of the matroids `Mb i` on the blocks: a set is independent in `M` iff
its trace on every block is independent in that block's matroid. -/
def IsBlockSum (M : Matroid E) (Mb : ∀ i, Matroid (Block f i)) : Prop :=
  ∀ I : Set E, M.Indep I ↔ ∀ i, (Mb i).Indep (Subtype.val ⁻¹' I)

omit [Fintype ι] in
theorem blockSum_isFeasible {M : Matroid E} {Mb : ∀ i, Matroid (Block f i)}
    (hM : IsBlockSum M Mb) {A : ∀ i, OnlineAlg (Block f i)} (hA : ∀ i, IsFeasible (Mb i) (A i)) :
    IsFeasible M (blockSum f A) := by
  intro σ w hw
  rw [hM]
  intro i
  rw [preimage_selected_blockSum]
  exact hA i _ _ fun y => hw y

/-- The weight of a set is the sum of the weights of its traces on the blocks. -/
lemma sum_eq_sum_blocks (I : Finset E) (w : E → ℝ) :
    ∑ e ∈ I, w e = ∑ i, ∑ x ∈ (univ.filter fun x : Block f i => x.1 ∈ I), w x := by
  have h1 : ∑ e ∈ I, w e = ∑ e, if e ∈ I then w e else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, ← Fintype.sum_fiberwise f]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter]

omit [Fintype ι] in
lemma coe_trace (I : Finset E) (i : ι) :
    ((univ.filter fun x : Block f i => x.1 ∈ I : Finset (Block f i)) : Set (Block f i)) =
      Subtype.val ⁻¹' (I : Set E) := by
  ext x; simp

/-- **Direct sums, deterministic.** Running `c`-competitive feasible algorithms independently in
the blocks of a direct sum gives a feasible `c`-competitive algorithm. -/
theorem blockSum_isCompetitive {M : Matroid E} {Mb : ∀ i, Matroid (Block f i)}
    (hM : IsBlockSum M Mb) {A : ∀ i, OnlineAlg (Block f i)} {c : ℝ}
    (hA : ∀ i, IsCompetitive (Mb i) (A i) c) : IsCompetitive M (blockSum f A) c := by
  intro w hw I hI
  rw [expWeight_blockSum, sum_eq_sum_blocks (f := f), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => hA i _ (fun y : Block f i => hw y) _ ?_
  rw [coe_trace]
  exact (hM _).1 hI i


end Blocks

/-! ### Elementary facts about competitiveness -/

theorem IsCompetitive.mono {M : Matroid E} {A : OnlineAlg E} {c c' : ℝ}
    (h : IsCompetitive M A c) (hc : c' ≤ c) : IsCompetitive M A c' := fun w hw I hI =>
  (mul_le_mul_of_nonneg_right hc (sum_nonneg fun e _ => hw e)).trans (h w hw I hI)

/-- Competitiveness is monotone in the constant. -/
theorem HasCompetitiveRandomized.mono {M : Matroid E} {c c' : ℝ}
    (h : HasCompetitiveRandomized M c) (hc : c' ≤ c) : HasCompetitiveRandomized M c' := by
  obtain ⟨Ω, _, P, hP, A, hA, hcomp⟩ := h
  exact ⟨Ω, _, P, hP, A, hA, fun w hw I hI =>
    (mul_le_mul_of_nonneg_right hc (sum_nonneg fun e _ => hw e)).trans (hcomp w hw I hI)⟩

/-- Every constant `c ≤ 0` is trivially achieved (by accepting nothing). -/
theorem hasCompetitiveRandomized_of_nonpos (M : Matroid E) {c : ℝ} (hc : c ≤ 0) :
    HasCompetitiveRandomized M c := by
  refine IsCompetitive.hasCompetitiveRandomized (never_isFeasible M) fun w hw I _ => ?_
  rw [expWeight_never]
  exact mul_nonpos_of_nonpos_of_nonneg hc (sum_nonneg fun e _ => hw e)

lemma expWeight_le_sum (A : OnlineAlg E) {w : E → ℝ} (hw : ∀ e, 0 ≤ w e) :
    expWeight A w ≤ ∑ e, w e := by
  have hfac : (0 : ℝ) < (Fintype.card E)! := by exact_mod_cast Nat.factorial_pos _
  rw [expWeight, div_le_iff₀ hfac]
  calc ∑ σ : ArrivalOrder E, ∑ e ∈ selected A σ w, w e ≤ ∑ _σ : ArrivalOrder E, ∑ e, w e :=
        sum_le_sum fun σ _ => sum_le_univ_sum_of_nonneg hw
    _ = (∑ e, w e) * (Fintype.card E)! := by
        rw [sum_const, Finset.card_univ, card_arrivalOrder, nsmul_eq_mul, mul_comm]

/-- **Non-degeneracy.** If `M` has a non-loop, no randomized online algorithm is more than
`1`-competitive. -/
theorem HasCompetitiveRandomized.le_one {M : Matroid E} {c : ℝ}
    (h : HasCompetitiveRandomized M c) {e : E} (he : M.Indep {e}) : c ≤ 1 := by
  obtain ⟨Ω, _, P, hP, A, -, hcomp⟩ := h
  set w : E → ℝ := fun x => if x = e then 1 else 0 with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => by rw [hw]; dsimp only; split_ifs <;> norm_num
  have hsum : ∑ x, w x = 1 := by simp [hw]
  have hle : ∀ ω, ‖expWeight (A ω) w‖ ≤ 1 := by
    intro ω
    rw [Real.norm_of_nonneg (expWeight_nonneg _ hw0), ← hsum]
    exact expWeight_le_sum _ hw0
  have hint := MeasureTheory.norm_integral_le_of_norm_le_const (μ := P)
    (Filter.Eventually.of_forall hle)
  have := hcomp w hw0 {e} (by simpa using he)
  simp only [sum_singleton, hw, ite_true, mul_one] at this
  have h1 : P.real Set.univ = 1 := by simp
  rw [h1, mul_one] at hint
  exact this.trans ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hint))

/-! ### Restriction (deletion) -/

/-- Run `A` with the weights of elements outside `R` replaced by `0`, and accept only
elements of `R`. -/
def restrictAlg (R : Set E) (A : OnlineAlg E) : OnlineAlg E := fun k h =>
  (h (Fin.last k)).1 ∈ R ∧ A k fun j => ((h j).1, if (h j).1 ∈ R then (h j).2 else 0)

lemma accepts_restrictAlg (R : Set E) (A : OnlineAlg E) (σ : ArrivalOrder E) (w : E → ℝ)
    (e : E) : Accepts (restrictAlg R A) σ w e ↔
      e ∈ R ∧ Accepts A σ (fun x => if x ∈ R then w x else 0) e := by
  have hlast : (arrivals σ w (σ.symm e) (Fin.last _)).1 = e := by
    have : Fin.castLE (σ.symm e).isLt (Fin.last (σ.symm e : ℕ)) = σ.symm e := Fin.ext rfl
    simp [arrivals, this]
  unfold Accepts restrictAlg
  rw [hlast]
  rfl

/-- **Restriction.** If `M` has a `c`-competitive randomized algorithm, so does its
restriction `M ↾ R` to any set `R` (the elements outside `R` are deleted). -/
theorem HasCompetitiveRandomized.restrict {M : Matroid E} {c : ℝ}
    (h : HasCompetitiveRandomized M c) (R : Set E) : HasCompetitiveRandomized (M.restrict R) c := by
  obtain ⟨Ω, mΩ, P, hP, A, hA, hcomp⟩ := h
  have hsel : ∀ ω σ w, (selected (restrictAlg R (A ω)) σ w : Set E) =
      (selected (A ω) σ (fun x => if x ∈ R then w x else 0) : Set E) ∩ R := by
    intro ω σ w
    ext x
    simp [accepts_restrictAlg, and_comm]
  have hexp : ∀ ω w, expWeight (restrictAlg R (A ω)) w =
      expWeight (A ω) (fun x => if x ∈ R then w x else 0) := by
    intro ω w
    unfold expWeight
    congr 1
    refine sum_congr rfl fun σ _ => ?_
    have : selected (restrictAlg R (A ω)) σ w =
        (selected (A ω) σ (fun x => if x ∈ R then w x else 0)).filter (· ∈ R) := by
      ext x; simp [accepts_restrictAlg, and_comm]
    rw [this, sum_filter]
  refine ⟨Ω, mΩ, P, hP, fun ω => restrictAlg R (A ω), fun ω σ w hw => ?_, fun w hw I hI => ?_⟩
  · rw [Matroid.restrict_indep_iff, hsel]
    refine ⟨(hA ω σ _ fun x => ?_).subset Set.inter_subset_left, Set.inter_subset_right⟩
    split_ifs
    · exact hw x
    · exact le_rfl
  · rw [Matroid.restrict_indep_iff] at hI
    have hw' : ∀ x, 0 ≤ (fun x => if x ∈ R then w x else 0) x := fun x => by
      dsimp only; split_ifs
      · exact hw x
      · exact le_rfl
    have hI' : ∑ e ∈ I, w e = ∑ e ∈ I, (fun x => if x ∈ R then w x else 0) e :=
      sum_congr rfl fun e he => by simp [hI.2 (by simpa using he)]
    rw [hI']
    simp only [hexp]
    exact hcomp _ hw' I hI.1

/-! ### Direct sums of randomized algorithms -/

section RandomizedSum

/-- For `c > 0`, the expected weight of the algorithms of a `c`-competitive randomized algorithm
is integrable (so the Bochner integral in `HasCompetitiveRandomized` is a genuine
expectation). -/
lemma integrable_of_competitive {M : Matroid E} {c : ℝ} (hc : 0 < c) {Ω : Type*}
    [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {A : Ω → OnlineAlg E}
    (hA : ∀ ω, IsFeasible M (A ω))
    (hcomp : ∀ w : E → ℝ, (∀ e, 0 ≤ w e) → ∀ I : Finset E, M.Indep (I : Set E) →
      c * ∑ e ∈ I, w e ≤ ∫ ω, expWeight (A ω) w ∂P)
    {w : E → ℝ} (hw : ∀ e, 0 ≤ w e) :
    MeasureTheory.Integrable (fun ω => expWeight (A ω) w) P := by
  by_contra hni
  have h0 : ∀ ω, expWeight (A ω) w = 0 := by
    intro ω
    have hzero : ∀ σ : ArrivalOrder E, ∑ e ∈ selected (A ω) σ w, w e = 0 := by
      intro σ
      have := hcomp w hw _ (hA ω σ w hw)
      rw [MeasureTheory.integral_undef hni] at this
      have hnn : 0 ≤ ∑ e ∈ selected (A ω) σ w, w e := sum_nonneg fun e _ => hw e
      nlinarith
    simp [expWeight, hzero]
  exact hni (by simp only [h0]; exact MeasureTheory.integrable_zero _ _ _)

/-- **Direct sums, randomized.** If `M` is the direct sum of matroids on the blocks and each
block matroid has a `c`-competitive randomized online algorithm, then so does `M`: draw the
random seeds of the blocks independently and run each block's algorithm on that block's
arrivals. -/
theorem HasCompetitiveRandomized.blockSum {ι : Type} [Fintype ι] [DecidableEq ι] {f : E → ι}
    {M : Matroid E} {Mb : ∀ i, Matroid (Block f i)} (hM : IsBlockSum M Mb) {c : ℝ}
    (h : ∀ i, HasCompetitiveRandomized (Mb i) c) : HasCompetitiveRandomized M c := by
  rcases le_or_gt c 0 with hc | hc
  · exact hasCompetitiveRandomized_of_nonpos M hc
  choose Ω mΩ P hP A hA hcomp using h
  refine ⟨∀ i, Ω i, MeasurableSpace.pi, MeasureTheory.Measure.pi P, inferInstance,
    fun ω => MatroidSecretary.blockSum f fun i => A i (ω i),
    fun ω => blockSum_isFeasible hM fun i => hA i (ω i), fun w hw I hI => ?_⟩
  have hw' : ∀ i, ∀ y : Block f i, 0 ≤ w y := fun i y => hw y
  have hint : ∀ i, MeasureTheory.Integrable (fun ω => expWeight (A i ω) fun y : Block f i => w y)
      (P i) := fun i => integrable_of_competitive hc (hA i) (hcomp i) (hw' i)
  have hmp : ∀ i, MeasureTheory.MeasurePreserving (Function.eval i)
      (MeasureTheory.Measure.pi P) (P i) := fun i => MeasureTheory.measurePreserving_eval P i
  have hint' : ∀ i, MeasureTheory.Integrable
      (fun ω : ∀ i, Ω i => expWeight (A i (ω i)) fun y : Block f i => w y)
      (MeasureTheory.Measure.pi P) := fun i => by
    have := (hmp i).integrable_comp_of_integrable (hint i)
    exact this
  have hmap : ∀ i, ∫ ω : ∀ i, Ω i, expWeight (A i (ω i)) (fun y : Block f i => w y)
      ∂MeasureTheory.Measure.pi P = ∫ ω, expWeight (A i ω) (fun y : Block f i => w y) ∂P i := by
    intro i
    have h1 := (hmp i).map_eq
    have hae : MeasureTheory.AEStronglyMeasurable
        (fun ω => expWeight (A i ω) fun y : Block f i => w y)
        (MeasureTheory.Measure.map (Function.eval i) (MeasureTheory.Measure.pi P)) := by
      rw [h1]; exact (hint i).aestronglyMeasurable
    have := MeasureTheory.integral_map (hmp i).measurable.aemeasurable hae
    rw [h1] at this
    exact this.symm
  simp only [expWeight_blockSum]
  rw [MeasureTheory.integral_finsetSum _ fun i _ => hint' i, sum_eq_sum_blocks (f := f),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hmap i]
  refine hcomp i _ (hw' i) _ ?_
  rw [coe_trace]
  exact (hM _).1 hI i

/-- **Direct sums of two matroids.** If `M` is the direct sum of `M₁` on `{e | f e = true}` and
`M₂` on `{e | f e = false}` and both have `c`-competitive randomized online algorithms, then so
does `M`. -/
theorem HasCompetitiveRandomized.directSum {f : E → Bool} {M : Matroid E}
    {M₁ : Matroid {e // f e = true}} {M₂ : Matroid {e // f e = false}}
    (hM : ∀ I : Set E, M.Indep I ↔
      M₁.Indep (Subtype.val ⁻¹' I) ∧ M₂.Indep (Subtype.val ⁻¹' I)) {c : ℝ}
    (h₁ : HasCompetitiveRandomized M₁ c) (h₂ : HasCompetitiveRandomized M₂ c) :
    HasCompetitiveRandomized M c := by
  let Mb : ∀ b : Bool, Matroid (Block f b) := fun b =>
    Bool.rec (motive := fun b => Matroid {e // f e = b}) M₂ M₁ b
  refine HasCompetitiveRandomized.blockSum (f := f) (Mb := Mb) (fun I => ?_) ?_
  · rw [hM, Bool.forall_bool, and_comm]
  · intro b
    cases b
    · exact h₂
    · exact h₁

end RandomizedSum

/-! ### Partition matroids with capacities one -/

section Partition

variable {ι : Type*}

/-- The partition matroid with capacities one: given `f : E → ι` (the block of each element), a
set is independent iff it contains at most one element of each block, i.e. `f` is injective on
it. -/
def partitionOne (f : E → ι) : Matroid E :=
  (IndepMatroid.ofFinite (E := (Set.univ : Set E)) Set.finite_univ (fun I => Set.InjOn f I)
    (Set.injOn_empty f) (fun _ _ hJ hIJ => hJ.mono hIJ)
    (by
      intro I J hI hJ hlt
      have hIJ : (f '' I).ncard < (f '' J).ncard := by
        rwa [hI.ncard_image, hJ.ncard_image]
      have hns : ¬ f '' J ⊆ f '' I := fun hsub =>
        absurd (Set.ncard_le_ncard hsub (Set.toFinite _)) (not_le.2 hIJ)
      obtain ⟨_, ⟨y, hyJ, rfl⟩, hy⟩ := Set.not_subset.1 hns
      have hyI : y ∉ I := fun h => hy ⟨y, h, rfl⟩
      exact ⟨y, hyJ, hyI, (Set.injOn_insert hyI).2 ⟨hI, hy⟩⟩)
    (fun _ _ => Set.subset_univ _)).matroid

@[simp] lemma partitionOne_ground (f : E → ι) : (partitionOne f).E = Set.univ := rfl

@[simp] lemma partitionOne_indep_iff {f : E → ι} {I : Set E} :
    (partitionOne f).Indep I ↔ Set.InjOn f I := by
  simp [partitionOne]

variable [DecidableEq ι]

/-- The partition matroid with capacities one is the direct sum of the rank-one uniform
matroids on its blocks. -/
lemma partitionOne_isBlockSum (f : E → ι) :
    IsBlockSum (partitionOne f) fun i => rankOne (Block f i) := by
  intro I
  simp only [partitionOne_indep_iff, rankOne_indep_iff]
  constructor
  · intro h i x hx y hy
    exact Subtype.ext (h hx hy (x.2.trans y.2.symm))
  · intro h a ha b hb hab
    have := h (f a) (x := ⟨a, rfl⟩) ha (y := ⟨b, hab.symm⟩) hb
    exact congrArg Subtype.val this

variable [Fintype ι]

/-- The rule for partition matroids: in each block, run the classical half rule (with ties
broken by a fixed order) on the arrivals of that block. -/
def partitionHalfRule (f : E → ι) : OnlineAlg E :=
  MatroidSecretary.blockSum f fun i => halfRuleLex (Block f i)

omit [Fintype ι] in
theorem partitionHalfRule_isFeasible (f : E → ι) :
    IsFeasible (partitionOne f) (partitionHalfRule f) :=
  blockSum_isFeasible (partitionOne_isBlockSum f) fun _ => halfRuleLex_isFeasible

/-- **Partition matroids with capacities one.** Running the half rule independently in each
block is `1/4`-competitive. -/
theorem partitionHalfRule_isCompetitive (f : E → ι) :
    IsCompetitive (partitionOne f) (partitionHalfRule f) (1 / 4) :=
  blockSum_isCompetitive (partitionOne_isBlockSum f) fun _ => halfRuleLex_isCompetitive

end Partition

/-- **Partition matroids with capacities one, any index type.** For every map `f : E → ι` (the
block of each element; `ι` arbitrary), the partition matroid `partitionOne f` has a feasible
deterministic `1/4`-competitive online algorithm. -/
theorem exists_isCompetitive_partitionOne {ι : Type*} (f : E → ι) :
    ∃ A : OnlineAlg E, IsFeasible (partitionOne f) A ∧ IsCompetitive (partitionOne f) A (1 / 4) := by
  -- reduce to the finite index type `Set.range f`
  let f' : E → Set.range f := fun e => ⟨f e, e, rfl⟩
  have heq : partitionOne f = partitionOne f' := by
    refine Matroid.ext_indep rfl fun I _ => ?_
    simp only [partitionOne_indep_iff]
    constructor
    · exact fun h a ha b hb hab => h ha hb (congrArg Subtype.val hab)
    · exact fun h a ha b hb hab => h ha hb (Subtype.ext hab)
  rw [heq]
  exact ⟨partitionHalfRule f', partitionHalfRule_isFeasible f', partitionHalfRule_isCompetitive f'⟩

theorem hasCompetitiveRandomized_partitionOne {ι : Type*} (f : E → ι) :
    HasCompetitiveRandomized (partitionOne f) (1 / 4) := by
  obtain ⟨A, hA, hc⟩ := exists_isCompetitive_partitionOne f
  exact hc.hasCompetitiveRandomized hA

end Applied.Economics.MatroidSecretary
