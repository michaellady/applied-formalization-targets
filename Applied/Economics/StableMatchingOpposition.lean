import Applied.Economics.StableMatching

/-!
# Opposition of interests in stable matchings

Setting of `Applied.Economics.IsStableMatching`: perfect matchings `μ : M ≃ W` between "men"
and "women" with strict preferences given by linear orders (larger = more preferred).

* `women_prefer_of_men_prefer`: if `ν` is stable and every man weakly prefers his partner in
  `μ` to his partner in `ν`, then every woman weakly prefers her partner in `ν` to her partner
  in `μ`. (Only stability of `ν` is used; `μ` may be any perfect matching.)
* `men_prefer_of_women_prefer`: the same with the roles of the two sides exchanged.
* `women_prefer_iff_men_prefer`: for two stable matchings, all men weakly prefer `μ` to `ν`
  if and only if all women weakly prefer `ν` to `μ`.
* `eq_of_men_prefer_of_women_prefer`: a stable matching `ν` cannot be weakly worse for
  everybody than another perfect matching `μ` unless `μ = ν` (stable matchings are weakly
  Pareto-undominated among perfect matchings).
* `IsMenOptimal.women_pessimal`, `IsMenOptimal.unique`: a stable matching that every man
  weakly prefers to every stable matching is the worst stable matching for every woman, and
  there is at most one such matching.

The existence of a men-optimal stable matching (which holds, by deferred acceptance) is *not*
proved here.
-/

open Function

namespace Applied.Economics

variable {M W : Type*}

/-- **Opposition of interests.** If `ν` is stable and every man weakly prefers `μ` to `ν`,
then every woman weakly prefers `ν` to `μ`. -/
theorem women_prefer_of_men_prefer (prefM : M → LinearOrder W) (prefW : W → LinearOrder M)
    (μ ν : M ≃ W) (hν : IsStableMatching prefM prefW ν)
    (hmen : ∀ m, (prefM m).le (ν m) (μ m)) (w : W) :
    (prefW w).le (μ.symm w) (ν.symm w) := by
  by_contra hcon
  have hlt : (prefW w).lt (ν.symm w) (μ.symm w) := by
    let _ := prefW w
    exact lt_of_not_ge hcon
  have hne : ν (μ.symm w) ≠ w := by
    intro h
    have h' : ν.symm w = μ.symm w := by rw [Equiv.symm_apply_eq]; exact h.symm
    rw [h'] at hlt
    let _ := prefW w
    exact lt_irrefl _ hlt
  have hm : (prefM (μ.symm w)).lt (ν (μ.symm w)) w := by
    have h := hmen (μ.symm w)
    rw [Equiv.apply_symm_apply] at h
    let _ := prefM (μ.symm w)
    exact lt_of_le_of_ne h hne
  exact hν (μ.symm w) w ⟨hm, hlt⟩

/-- **Opposition of interests, other side.** If `ν` is stable and every woman weakly prefers
`μ` to `ν`, then every man weakly prefers `ν` to `μ`. -/
theorem men_prefer_of_women_prefer (prefM : M → LinearOrder W) (prefW : W → LinearOrder M)
    (μ ν : M ≃ W) (hν : IsStableMatching prefM prefW ν)
    (hwomen : ∀ w, (prefW w).le (ν.symm w) (μ.symm w)) (m : M) :
    (prefM m).le (μ m) (ν m) := by
  by_contra hcon
  have hlt : (prefM m).lt (ν m) (μ m) := by
    let _ := prefM m
    exact lt_of_not_ge hcon
  have hne : ν.symm (μ m) ≠ m := by
    intro h
    have h' : ν m = μ m := ((Equiv.symm_apply_eq ν).1 h).symm
    rw [h'] at hlt
    let _ := prefM m
    exact lt_irrefl _ hlt
  have hw : (prefW (μ m)).lt (ν.symm (μ m)) m := by
    have h := hwomen (μ m)
    rw [Equiv.symm_apply_apply] at h
    let _ := prefW (μ m)
    exact lt_of_le_of_ne h hne
  exact hν m (μ m) ⟨hlt, hw⟩

/-- For two stable matchings, the men unanimously weakly prefer `μ` to `ν` if and only if the
women unanimously weakly prefer `ν` to `μ`. -/
theorem women_prefer_iff_men_prefer (prefM : M → LinearOrder W) (prefW : W → LinearOrder M)
    (μ ν : M ≃ W) (hμ : IsStableMatching prefM prefW μ) (hν : IsStableMatching prefM prefW ν) :
    (∀ m, (prefM m).le (ν m) (μ m)) ↔ ∀ w, (prefW w).le (μ.symm w) (ν.symm w) :=
  ⟨fun h w => women_prefer_of_men_prefer prefM prefW μ ν hν h w,
   fun h m => men_prefer_of_women_prefer prefM prefW ν μ hμ h m⟩

/-- A stable matching `ν` is not weakly Pareto-dominated by a different perfect matching: if
every man and every woman weakly prefers `μ` to `ν`, then `μ = ν`. -/
theorem eq_of_men_prefer_of_women_prefer (prefM : M → LinearOrder W)
    (prefW : W → LinearOrder M) (μ ν : M ≃ W) (hν : IsStableMatching prefM prefW ν)
    (hmen : ∀ m, (prefM m).le (ν m) (μ m))
    (hwomen : ∀ w, (prefW w).le (ν.symm w) (μ.symm w)) : μ = ν := by
  ext m
  let _ := prefM m
  exact le_antisymm (men_prefer_of_women_prefer prefM prefW μ ν hν hwomen m) (hmen m)

/-- `μ` is a men-optimal stable matching: it is stable and every man weakly prefers it to
every stable matching. -/
def IsMenOptimal (prefM : M → LinearOrder W) (prefW : W → LinearOrder M) (μ : M ≃ W) : Prop :=
  IsStableMatching prefM prefW μ ∧
    ∀ ν : M ≃ W, IsStableMatching prefM prefW ν → ∀ m, (prefM m).le (ν m) (μ m)

/-- A men-optimal stable matching is women-pessimal: every woman weakly prefers every stable
matching to it. -/
theorem IsMenOptimal.women_pessimal {prefM : M → LinearOrder W} {prefW : W → LinearOrder M}
    {μ : M ≃ W} (hμ : IsMenOptimal prefM prefW μ) (ν : M ≃ W)
    (hν : IsStableMatching prefM prefW ν) (w : W) : (prefW w).le (μ.symm w) (ν.symm w) :=
  women_prefer_of_men_prefer prefM prefW μ ν hν (hμ.2 ν hν) w

/-- There is at most one men-optimal stable matching. -/
theorem IsMenOptimal.unique {prefM : M → LinearOrder W} {prefW : W → LinearOrder M}
    {μ μ' : M ≃ W} (hμ : IsMenOptimal prefM prefW μ) (hμ' : IsMenOptimal prefM prefW μ') :
    μ = μ' := by
  ext m
  let _ := prefM m
  exact le_antisymm (hμ'.2 μ hμ.1 m) (hμ.2 μ' hμ'.1 m)

end Applied.Economics
