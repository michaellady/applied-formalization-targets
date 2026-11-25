import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

/-!
# Fractional multicommodity flow in undirected capacitated networks (routing rate region)

This is the *routing side* of the Li–Li multiple-unicast network coding conjecture: the set of
rate vectors that can be achieved by fractional routing. The network-coding side is not
defined here.

* `Network V`: an undirected network on a finite vertex set `V`, given by a symmetric
  non-negative capacity function (`cap u v = 0` means no edge).
* `Session V`: a unicast session, a source and a different sink.
* `IsRouting G σ r f`: `f i u v ≥ 0` is the flow of session `i` sent along the edge `{u, v}`
  in the direction `u → v`; every session's flow is conserved at all vertices other than its
  source and sink, the net outflow at the source of session `i` is `r i`, and on every edge the
  total flow of all sessions in both directions is at most the capacity.
* `Routable G σ r`: the rate vector `r` is achievable by fractional routing.

Proved: `routable_zero`; `Routable.smul` (scaling down); `Routable.combo` and
`convex_routable` (time sharing);
`Routable.rate_le_source_cap` (a session's rate is at most the total capacity at its source),
so the routable region is a convex set containing `0` whose rates are bounded above (negative
rates are not excluded by the definition, and no lower bound is stated as a theorem).
-/

open Finset

namespace Applied.Economics.MulticommodityFlow

variable {V K : Type*} [Fintype V] [Fintype K]

/-- An undirected capacitated network on the vertex set `V`. -/
structure Network (V : Type*) where
  /-- Capacity of the edge `{u, v}`; `0` if there is no edge. -/
  cap : V → V → ℝ
  cap_symm : ∀ u v, cap u v = cap v u
  cap_nonneg : ∀ u v, 0 ≤ cap u v

/-- A unicast session: a source and a sink, different from each other. -/
structure Session (V : Type*) where
  /-- The source of the session. -/
  src : V
  /-- The sink of the session. -/
  snk : V
  src_ne_snk : src ≠ snk

/-- Net outflow of the (directed) flow `g` at the vertex `v`. -/
def netOut (g : V → V → ℝ) (v : V) : ℝ := ∑ u, g v u - ∑ u, g u v

/-- `f` is a fractional routing of the sessions `σ` in the network `G` with rates `r`. -/
structure IsRouting (G : Network V) (σ : K → Session V) (r : K → ℝ) (f : K → V → V → ℝ) :
    Prop where
  nonneg : ∀ i u v, 0 ≤ f i u v
  conserve : ∀ i v, v ≠ (σ i).src → v ≠ (σ i).snk → netOut (f i) v = 0
  rate : ∀ i, netOut (f i) (σ i).src = r i
  capacity : ∀ u v, ∑ i, (f i u v + f i v u) ≤ G.cap u v

/-- The rate vector `r` is achievable by fractional routing. -/
def Routable (G : Network V) (σ : K → Session V) (r : K → ℝ) : Prop :=
  ∃ f, IsRouting G σ r f

lemma netOut_combo (g g' : V → V → ℝ) (a b : ℝ) (v : V) :
    netOut (fun u w => a * g u w + b * g' u w) v = a * netOut g v + b * netOut g' v := by
  simp only [netOut, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The zero rate vector is routable. -/
theorem routable_zero (G : Network V) (σ : K → Session V) : Routable G σ 0 :=
  ⟨fun _ _ _ => 0, ⟨fun _ _ _ => le_rfl, fun _ _ _ _ => by simp [netOut],
    fun _ => by simp [netOut], fun u v => by simpa using G.cap_nonneg u v⟩⟩

/-- **Time sharing.** Non-negative combinations with total weight at most one of routable rate
vectors are routable. -/
theorem Routable.combo {G : Network V} {σ : K → Session V} {r r' : K → ℝ}
    (h : Routable G σ r) (h' : Routable G σ r') {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) : Routable G σ (a • r + b • r') := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨f', hf'⟩ := h'
  refine ⟨fun i u v => a * f i u v + b * f' i u v, ⟨fun i u v => ?_, fun i v h1 h2 => ?_,
    fun i => ?_, fun u v => ?_⟩⟩
  · exact add_nonneg (mul_nonneg ha (hf.nonneg i u v)) (mul_nonneg hb (hf'.nonneg i u v))
  · rw [netOut_combo, hf.conserve i v h1 h2, hf'.conserve i v h1 h2]; simp
  · rw [netOut_combo, hf.rate, hf'.rate]; simp
  · have e : ∑ i, (a * f i u v + b * f' i u v + (a * f i v u + b * f' i v u)) =
        a * ∑ i, (f i u v + f i v u) + b * ∑ i, (f' i u v + f' i v u) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left (hf.capacity u v) ha
    have h2 := mul_le_mul_of_nonneg_left (hf'.capacity u v) hb
    have h3 := G.cap_nonneg u v
    nlinarith

/-- Scaling a routable rate vector down keeps it routable. -/
theorem Routable.smul {G : Network V} {σ : K → Session V} {r : K → ℝ} (h : Routable G σ r)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Routable G σ (t • r) := by
  have := h.combo (routable_zero G σ) ht0 le_rfl (by linarith)
  simpa using this

/-- The routable rate region is convex. -/
theorem convex_routable (G : Network V) (σ : K → Session V) :
    Convex ℝ {r : K → ℝ | Routable G σ r} :=
  fun _ hr _ hr' _ _ ha hb hab => hr.combo hr' ha hb hab.le

/-- A session's routable rate is at most the total capacity of the edges at its source. -/
theorem Routable.rate_le_source_cap {G : Network V} {σ : K → Session V} {r : K → ℝ}
    (h : Routable G σ r) (i : K) : r i ≤ ∑ u, G.cap (σ i).src u := by
  classical
  obtain ⟨f, hf⟩ := h
  rw [← hf.rate i, netOut]
  have h1 : 0 ≤ ∑ u, f i u (σ i).src := Finset.sum_nonneg fun u _ => hf.nonneg i u _
  have h2 : ∑ u, f i (σ i).src u ≤ ∑ u, G.cap (σ i).src u := by
    refine Finset.sum_le_sum fun u _ => ?_
    refine le_trans ?_ (hf.capacity (σ i).src u)
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun j => f j (σ i).src u + f j u (σ i).src)
      (fun j _ => add_nonneg (hf.nonneg j _ _) (hf.nonneg j _ _)) (Finset.mem_univ i))
    linarith [hf.nonneg i u (σ i).src]
  linarith

end Applied.Economics.MulticommodityFlow
