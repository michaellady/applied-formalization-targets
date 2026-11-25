import Applied.Topology.SpernerCube

/-!
# Brouwer's fixed point theorem

* `brouwer_cube`: a continuous map `g : (Fin m → ℝ) → (Fin m → ℝ)` with values in the cube
  `[0, 1]^m` has a fixed point. Proof: Sperner's lemma for the Kuhn triangulation of the cube
  (`Applied.Topology.Kuhn.exists_full`), uniform continuity and compactness.
-/

namespace Applied.Topology

open Set Finset

/-- **Brouwer's fixed point theorem for the cube.** A continuous map of `ℝ^m` whose values lie
in the cube `[0,1]^m` has a fixed point. -/
theorem brouwer_cube {m : ℕ} (g : (Fin m → ℝ) → (Fin m → ℝ)) (hg : Continuous g)
    (hmaps : ∀ y i, g y i ∈ Icc (0 : ℝ) 1) : ∃ y, g y = y := by
  classical
  by_contra hno
  simp only [not_exists] at hno
  set K : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ => Icc (0 : ℝ) 1) with hK
  have hKc : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hKne : K.Nonempty := ⟨fun _ => 0, by simp only [K, Set.mem_pi]; intro i _; simp⟩
  obtain ⟨y0, -, hy0min⟩ :=
    hKc.exists_isMinOn hKne ((hg.dist continuous_id).continuousOn)
  set δ := dist (g y0) y0 with hδdef
  have hδ : 0 < δ := dist_pos.2 (hno y0)
  have hUC := hKc.uniformContinuousOn_of_continuous hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨η, hη, hηg⟩ := hUC (δ / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / η) (2 / δ))
  have hη' : 0 < 1 / η := by positivity
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (le_max_of_le_left hη'.le) hN
  have hNη : 1 / (N : ℝ) < η := by
    rw [div_lt_iff₀ hNpos]
    have := lt_of_le_of_lt (le_max_left _ _) hN
    rw [div_lt_iff₀ hη] at this
    linarith
  have hNδ : 1 / (N : ℝ) < δ / 2 := by
    rw [div_lt_iff₀ hNpos]
    have := lt_of_le_of_lt (le_max_right _ _) hN
    rw [div_lt_iff₀ hδ] at this
    linarith
  -- grid points scaled into the cube
  set p : (Fin m → ℕ) → (Fin m → ℝ) := fun x i => (x i : ℝ) / N with hp
  -- the labelling
  set l : (Fin m → ℕ) → Fin (m + 1) := fun x =>
    if h : ∃ i, 0 < x i ∧ g (p x) i ≤ p x i then (Classical.choose h).castSucc
    else Fin.last m with hl_def
  have hlA : ∀ x i, x i = 0 → l x ≠ i.castSucc := by
    intro x i hx hli
    simp only [hl_def] at hli
    split_ifs at hli with h
    · have := (Classical.choose_spec h).1
      rw [Fin.castSucc_inj.1 hli, hx] at this
      exact lt_irrefl _ this
    · exact Fin.castSucc_ne_last i hli.symm
  have hlB : ∀ x i, x i = N → l x ≠ Fin.last m := by
    intro x i hx hli
    simp only [hl_def] at hli
    split_ifs at hli with h
    · exact Fin.castSucc_ne_last _ hli
    · apply h
      refine ⟨i, ?_, ?_⟩
      · rw [hx]; exact_mod_cast hNpos
      · have : p x i = 1 := by
          simp only [hp, hx]; field_simp
        rw [this]; exact (hmaps _ i).2
  obtain ⟨σ, hσ⟩ := Kuhn.exists_full (N := N) (by exact_mod_cast hNpos) l ⟨hlA, hlB⟩
  have hlab : ∀ c, ∃ k, l (Kuhn.vertex σ k) = c := by
    intro c
    have : c ∈ Finset.univ.image (fun k => l (Kuhn.vertex σ k)) := by
      rw [show Finset.univ.image (fun k => l (Kuhn.vertex σ k)) = Finset.univ from hσ]
      exact Finset.mem_univ c
    simpa using this
  -- the vertices, scaled, lie in the cube and are `1/N`-close
  have hmemK : ∀ k, p (Kuhn.vertex σ k) ∈ K := by
    intro k
    simp only [K, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, hp]
    intro i
    have := Kuhn.vertex_le σ k i
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNpos]; exact_mod_cast this
  have hclose : ∀ k k' i, |p (Kuhn.vertex σ k) i - p (Kuhn.vertex σ k') i| ≤ 1 / N := by
    intro k k' i
    simp only [hp]
    rw [← sub_div, abs_div, abs_of_pos hNpos]
    apply div_le_div_of_nonneg_right _ hNpos.le
    have h1 := Kuhn.vertex_ge σ k i
    have h2 := Kuhn.vertex_le_base σ k i
    have h3 := Kuhn.vertex_ge σ k' i
    have h4 := Kuhn.vertex_le_base σ k' i
    rw [abs_le]
    constructor
    · have : ((Kuhn.vertex σ k' i : ℕ) : ℝ) ≤ (Kuhn.vertex σ k i : ℝ) + 1 := by
        exact_mod_cast (by omega : Kuhn.vertex σ k' i ≤ Kuhn.vertex σ k i + 1)
      linarith
    · have : ((Kuhn.vertex σ k i : ℕ) : ℝ) ≤ (Kuhn.vertex σ k' i : ℝ) + 1 := by
        exact_mod_cast (by omega : Kuhn.vertex σ k i ≤ Kuhn.vertex σ k' i + 1)
      linarith
  have hdist : ∀ k k', dist (p (Kuhn.vertex σ k)) (p (Kuhn.vertex σ k')) < η := by
    intro k k'
    refine lt_of_le_of_lt ?_ hNη
    refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
    rw [Real.dist_eq]; exact hclose k k' i
  -- the vertex with label `last`
  obtain ⟨k0, hk0⟩ := hlab (Fin.last m)
  set a := p (Kuhn.vertex σ k0) with ha
  have hup : ∀ i, a i ≤ g a i := by
    intro i
    simp only [hl_def] at hk0
    split_ifs at hk0 with h
    · exact absurd hk0 (Fin.castSucc_ne_last _)
    · simp only [not_exists, not_and, not_le] at h
      by_cases hx : Kuhn.vertex σ k0 i = 0
      · have : a i = 0 := by simp only [ha, hp, hx]; simp
        rw [this]; exact (hmaps _ i).1
      · exact (h i (Nat.pos_of_ne_zero hx)).le
  have hdown : ∀ i, g a i - a i < δ := by
    intro i
    obtain ⟨ki, hki⟩ := hlab i.castSucc
    set b := p (Kuhn.vertex σ ki) with hb
    have hb_le : g b i ≤ b i := by
      simp only [hl_def] at hki
      split_ifs at hki with h
      · have hi : Classical.choose h = i := Fin.castSucc_inj.1 hki
        have := (Classical.choose_spec h).2
        rw [hi] at this
        exact this
      · exact absurd hki.symm (Fin.castSucc_ne_last _)
    have hgab : dist (g a) (g b) < δ / 2 := hηg a (hmemK k0) b (hmemK ki) (hdist k0 ki)
    have h1 : |g a i - g b i| < δ / 2 :=
      lt_of_le_of_lt (by rw [← Real.dist_eq]; exact dist_le_pi_dist _ _ i) hgab
    have h2 := hclose ki k0 i
    rw [abs_lt] at h1
    rw [abs_le] at h2
    linarith
  have : dist (g a) a < δ := by
    refine (dist_pi_lt_iff hδ).2 fun i => ?_
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [hup i]
    · exact hdown i
  exact absurd (hy0min (hmemK k0)) (not_le.2 this)

end Applied.Topology
