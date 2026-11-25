import Applied.Economics.StableMatchingOpposition

/-!
# Existence of the men-optimal stable matching

Setting of `Applied.Economics.IsStableMatching`: finitely many "men" `M` and "women" `W`,
equally many of each, strict preferences given by linear orders (larger = more preferred),
perfect matchings `μ : M ≃ W`, stability = no blocking pair.

* `exists_isMenOptimal`: there is a stable matching that every man weakly prefers to every
  stable matching (`IsMenOptimal`): each man gets the best partner he has in any stable
  matching.
* `existsUnique_isMenOptimal`: it is unique.
* `exists_stable_men_optimal_women_pessimal`: there is a stable matching that is weakly best
  for every man and weakly worst for every woman among all stable matchings.

Proof. A stable matching exists (`exists_stable_matching`), and there are finitely many, so
every man `m` has a best stable partner `f m`, attained in some stable matching `N m`. The map
`f` is injective: if `f a = f c = w` with `a ≠ c` and `w` prefers `a` to `c`, then `(a, w)`
blocks `N c`, because `a` strictly prefers his best stable partner `w` to his partner in `N c`
(which is not `w`, as `w` is matched to `c` there). Hence `f` is a perfect matching. It is
stable: if `(m, w)` blocked `f`, with `m'` the partner of `w` under `f`, then `(m, w)` would
block `N m'`, in which `w` is matched to `m'` and `m` to somebody no better than `f m`.
-/

open Finset Function

namespace Applied.Economics

variable {M W : Type*}

/-- **Existence of the men-optimal stable matching.** For equally many men and women with
strict preferences there is a stable matching in which every man has the best partner he has
in any stable matching. -/
theorem exists_isMenOptimal [Fintype M] [Fintype W] (hcard : Fintype.card M = Fintype.card W)
    (prefM : M → LinearOrder W) (prefW : W → LinearOrder M) :
    ∃ μ : M ≃ W, IsMenOptimal prefM prefW μ := by
  classical
  obtain ⟨μ₀, hμ₀⟩ := exists_stable_matching hcard prefM prefW
  -- for each man, a stable matching giving him his best stable partner
  have hbest : ∀ m : M, ∃ ν : M ≃ W, IsStableMatching prefM prefW ν ∧
      ∀ ν' : M ≃ W, IsStableMatching prefM prefW ν' → (prefM m).le (ν' m) (ν m) := by
    intro m
    let _ := prefM m
    obtain ⟨ν, hν, hmax⟩ := Finset.exists_max_image
      (univ.filter fun ν : M ≃ W => IsStableMatching prefM prefW ν) (fun ν => ν m)
      ⟨μ₀, mem_filter.2 ⟨mem_univ _, hμ₀⟩⟩
    exact ⟨ν, (mem_filter.1 hν).2, fun ν' h' => hmax ν' (mem_filter.2 ⟨mem_univ _, h'⟩)⟩
  choose N hN hNmax using hbest
  let f : M → W := fun m => N m m
  -- two men cannot share a best stable partner
  have key : ∀ a c : M, a ≠ c → f a = f c → (prefW (f a)).lt c a → False := by
    intro a c hne he hlt
    have h1 : (prefM a).le (N c a) (f a) := hNmax a (N c) (hN c)
    have h2 : N c a ≠ f a := fun h => hne ((N c).injective (h.trans he))
    refine hN c a (f a) ⟨?_, ?_⟩
    · let _ := prefM a
      exact lt_of_le_of_ne h1 h2
    · have h3 : (N c).symm (f a) = c := by
        rw [Equiv.symm_apply_eq]
        exact he
      rw [h3]
      exact hlt
  have hinj : Injective f := by
    intro m₁ m₂ he
    by_contra hne
    let _ := prefW (f m₁)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key m₂ m₁ (Ne.symm hne) he.symm (he ▸ hlt)
    · exact key m₁ m₂ hne he hlt
  have hbij : Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  refine ⟨Equiv.ofBijective f hbij, ?_, fun ν hν m => hNmax m ν hν⟩
  rintro m w ⟨h1, h2⟩
  -- the partner of `w`, and the stable matching in which he gets `w`
  obtain ⟨m', rfl⟩ := hbij.2 w
  have hsymm : (Equiv.ofBijective f hbij).symm (f m') = m' := by
    rw [Equiv.symm_apply_eq]
    rfl
  rw [hsymm] at h2
  refine hN m' m (f m') ⟨?_, ?_⟩
  · let _ := prefM m
    exact lt_of_le_of_lt (hNmax m (N m') (hN m')) h1
  · have h3 : (N m').symm (f m') = m' := by
      rw [Equiv.symm_apply_eq]
    rw [h3]
    exact h2

/-- There is exactly one men-optimal stable matching. -/
theorem existsUnique_isMenOptimal [Fintype M] [Fintype W]
    (hcard : Fintype.card M = Fintype.card W) (prefM : M → LinearOrder W)
    (prefW : W → LinearOrder M) : ∃! μ : M ≃ W, IsMenOptimal prefM prefW μ := by
  obtain ⟨μ, hμ⟩ := exists_isMenOptimal hcard prefM prefW
  exact ⟨μ, hμ, fun μ' hμ' => hμ'.unique hμ⟩

/-- There is a stable matching that is weakly best for every man and weakly worst for every
woman among all stable matchings. -/
theorem exists_stable_men_optimal_women_pessimal [Fintype M] [Fintype W]
    (hcard : Fintype.card M = Fintype.card W) (prefM : M → LinearOrder W)
    (prefW : W → LinearOrder M) :
    ∃ μ : M ≃ W, IsStableMatching prefM prefW μ ∧
      ∀ ν : M ≃ W, IsStableMatching prefM prefW ν →
        (∀ m, (prefM m).le (ν m) (μ m)) ∧ ∀ w, (prefW w).le (μ.symm w) (ν.symm w) := by
  obtain ⟨μ, hμ⟩ := exists_isMenOptimal hcard prefM prefW
  exact ⟨μ, hμ.1, fun ν hν => ⟨hμ.2 ν hν, hμ.women_pessimal ν hν⟩⟩

end Applied.Economics
