import Applied.Statistics.FactorModelBlocks
import Applied.Statistics.NormalTable
import Mathlib.Data.List.GetD

/-!
# A checker for certificates of three-block factor models

Integer data for a three-block one-factor model (block `0` is the null block), a list of bins of
the factor axis with cut-offs, and a Boolean function `certOK` that uses only integer arithmetic
and a table of the normal distribution function (`Applied.Statistics.NormalTable`).
`exists_fdr_gt_of_certOK`: if the table is valid and `certOK` returns `true`, the
Benjamini–Hochberg procedure at level `1 / αinv` has false discovery rate strictly above the
level in the block model, for every sufficiently large replication number.

All grid points are multiples of `1 / H` (`H = 1024`): bin end points `zl / H`, `zh / H` and
cut-offs `c / H`. The arguments `(M ± c) / s` of `Φ` are rounded outwards to the lattice
`1 / (H R)` using rational bounds `rl / RD ≤ 1 / s ≤ rh / RD`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting.BlockCert

open Applied.Statistics Applied.Statistics.NormalTable Applied.MultipleTesting

local notation "Φ" => cdf (gaussianReal 0 1)

/-- Denominator of the rational bounds for `1 / s`. -/
def RD : ℕ := 10 ^ 12

lemma RD_pos : (0 : ℝ) < RD := by norm_num [RD]

/-- Integer description of a block: multiplicity, mean `tn / td`, loading `bn / bd`, and bounds
`rl / RD ≤ 1 / s ≤ rh / RD` for the residual standard deviation `s = √(1 - (bn/bd)²)`. -/
structure BlockQ where
  mult : ℕ
  tn : ℤ
  td : ℕ
  bn : ℤ
  bd : ℕ
  rl : ℕ
  rh : ℕ

namespace BlockQ

variable (B : BlockQ)

/-- The mean of the block. -/
noncomputable def θ : ℝ := (B.tn : ℝ) / B.td
/-- The factor loading of the block. -/
noncomputable def b : ℝ := (B.bn : ℝ) / B.bd

/-- Check of the integer parameters of a block. -/
def paramOK : Bool :=
  decide (0 < B.td) && decide (0 < B.bd) &&
    decide ((B.rl : ℤ) ^ 2 * ((B.bd : ℤ) ^ 2 - B.bn ^ 2) ≤ (RD : ℤ) ^ 2 * (B.bd : ℤ) ^ 2) &&
    decide ((RD : ℤ) ^ 2 * (B.bd : ℤ) ^ 2 ≤ (B.rh : ℤ) ^ 2 * ((B.bd : ℤ) ^ 2 - B.bn ^ 2))

/-- Numerator of `θ + b z` at `z = zi / H`, over the denominator `td * bd * H`. -/
def Mnum (zi : ℤ) : ℤ := B.tn * B.bd * H + B.bn * zi * B.td

/-- A lattice point (in units `1 / (H R)`) above `num / (td bd H) / s`. -/
def yUp (num : ℤ) : ℤ :=
  (num * (if 0 ≤ num then (B.rh : ℤ) else B.rl) * R) / (B.td * B.bd * RD) + 1

/-- A lattice point (in units `1 / (H R)`) below `num / (td bd H) / s`. -/
def yDown (num : ℤ) : ℤ :=
  (num * (if 0 ≤ num then (B.rl : ℤ) else B.rh) * R) / (B.td * B.bd * RD)

variable {B}

lemma rinv_bounds (hok : B.paramOK = true) {s : ℝ} (hs : 0 < s) (hbs : B.b ^ 2 + s ^ 2 = 1) :
    (B.rl : ℝ) / RD ≤ 1 / s ∧ 1 / s ≤ (B.rh : ℝ) / RD := by
  simp only [paramOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨htd, hbd⟩, h1⟩, h2⟩ := hok
  have hbd' : (0 : ℝ) < B.bd := by exact_mod_cast hbd
  have hRD := RD_pos
  have h1' : ((B.rl : ℝ)) ^ 2 * ((B.bd : ℝ) ^ 2 - (B.bn : ℝ) ^ 2) ≤ (RD : ℝ) ^ 2 * (B.bd : ℝ) ^ 2 := by
    exact_mod_cast h1
  have h2' : (RD : ℝ) ^ 2 * (B.bd : ℝ) ^ 2 ≤ ((B.rh : ℝ)) ^ 2 * ((B.bd : ℝ) ^ 2 - (B.bn : ℝ) ^ 2) := by
    exact_mod_cast h2
  have hs2 : s ^ 2 * (B.bd : ℝ) ^ 2 = (B.bd : ℝ) ^ 2 - (B.bn : ℝ) ^ 2 := by
    have : s ^ 2 = 1 - ((B.bn : ℝ) / B.bd) ^ 2 := by
      unfold BlockQ.b at hbs; linarith
    rw [this]; field_simp
  rw [← hs2] at h1' h2'
  have hbd2 : (0 : ℝ) < (B.bd : ℝ) ^ 2 := by positivity
  have e1 : ((B.rl : ℝ) * s) ^ 2 ≤ (RD : ℝ) ^ 2 := by
    have : ((B.rl : ℝ) * s) ^ 2 * (B.bd : ℝ) ^ 2 ≤ (RD : ℝ) ^ 2 * (B.bd : ℝ) ^ 2 := by
      nlinarith
    exact le_of_mul_le_mul_right this hbd2
  have e2 : (RD : ℝ) ^ 2 ≤ ((B.rh : ℝ) * s) ^ 2 := by
    have : (RD : ℝ) ^ 2 * (B.bd : ℝ) ^ 2 ≤ ((B.rh : ℝ) * s) ^ 2 * (B.bd : ℝ) ^ 2 := by
      nlinarith
    exact le_of_mul_le_mul_right this hbd2
  have f1 : (B.rl : ℝ) * s ≤ RD :=
    (abs_le_of_sq_le_sq' e1 hRD.le).2
  have f2 : (RD : ℝ) ≤ (B.rh : ℝ) * s := by
    have h0 : (0 : ℝ) ≤ (B.rh : ℝ) * s := by positivity
    exact (abs_le_of_sq_le_sq' e2 h0).2
  constructor
  · rw [div_le_div_iff₀ hRD hs]; linarith
  · rw [div_le_div_iff₀ hs hRD]; linarith

lemma yUp_spec (hok : B.paramOK = true) {s : ℝ} (hs : 0 < s) (hbs : B.b ^ 2 + s ^ 2 = 1)
    (num : ℤ) :
    (num : ℝ) / (B.td * B.bd * H) / s ≤ (B.yUp num : ℝ) / (H * R) := by
  obtain ⟨hr1, hr2⟩ := rinv_bounds hok hs hbs
  simp only [paramOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨htd, hbd⟩, -⟩, -⟩ := hok
  have htd' : (0 : ℝ) < B.td := by exact_mod_cast htd
  have hbd' : (0 : ℝ) < B.bd := by exact_mod_cast hbd
  have hH := H_pos
  have hR := R_pos
  have hRD := RD_pos
  set r : ℤ := if 0 ≤ num then (B.rh : ℤ) else B.rl with hr
  have hden : (0 : ℤ) < B.td * B.bd * RD := by
    have : (0 : ℤ) < (RD : ℤ) := by norm_num [RD]
    have h1 : (0 : ℤ) < B.td := by exact_mod_cast htd
    have h2 : (0 : ℤ) < B.bd := by exact_mod_cast hbd
    positivity
  have hfl := Int.lt_ediv_add_one_mul_self (num * r * R) hden
  have hfl' : ((num * r * R : ℤ) : ℝ) < ((B.yUp num : ℤ) : ℝ) * ((B.td * B.bd * RD : ℤ) : ℝ) := by
    have : B.yUp num = num * r * R / (B.td * B.bd * RD) + 1 := rfl
    rw [this]
    exact_mod_cast hfl
  push_cast at hfl'
  have hkey : (num : ℝ) * (1 / s) ≤ num * (r : ℝ) / RD := by
    by_cases hn : 0 ≤ num
    · have hn' : (0 : ℝ) ≤ num := by exact_mod_cast hn
      have : (r : ℝ) = B.rh := by simp [hr, hn]
      rw [this, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hr2 hn'
    · have hn' : (num : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp hn).le
      have : (r : ℝ) = B.rl := by simp [hr, hn]
      rw [this, mul_div_assoc]
      exact mul_le_mul_of_nonpos_left hr1 hn'
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (num : ℝ) * (r : ℝ) * R < (B.yUp num : ℝ) * (B.td * B.bd * RD) := hfl'
  have h4 : (num : ℝ) ≤ num * (r : ℝ) / RD * s := by
    have := mul_le_mul_of_nonneg_right hkey hs.le
    have e : (num : ℝ) * (1 / s) * s = num := by field_simp
    rw [e] at this; exact this
  have h5 : (num : ℝ) * RD ≤ num * (r : ℝ) * s := by
    have := mul_le_mul_of_nonneg_right h4 hRD.le
    have e : (num : ℝ) * (r : ℝ) / RD * s * RD = num * r * s := by field_simp
    rw [e] at this; exact this
  have hpos : (0 : ℝ) < (B.td : ℝ) * B.bd * H * s := by positivity
  nlinarith [mul_pos (mul_pos htd' hbd') (mul_pos hH hR), mul_pos hs hR,
    mul_le_mul_of_nonneg_right h5 (mul_pos hH hR).le,
    mul_lt_mul_of_pos_right h3 (mul_pos hs hH)]

lemma yDown_spec (hok : B.paramOK = true) {s : ℝ} (hs : 0 < s) (hbs : B.b ^ 2 + s ^ 2 = 1)
    (num : ℤ) :
    (B.yDown num : ℝ) / (H * R) ≤ (num : ℝ) / (B.td * B.bd * H) / s := by
  obtain ⟨hr1, hr2⟩ := rinv_bounds hok hs hbs
  simp only [paramOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨htd, hbd⟩, -⟩, -⟩ := hok
  have htd' : (0 : ℝ) < B.td := by exact_mod_cast htd
  have hbd' : (0 : ℝ) < B.bd := by exact_mod_cast hbd
  have hH := H_pos
  have hR := R_pos
  have hRD := RD_pos
  set r : ℤ := if 0 ≤ num then (B.rl : ℤ) else B.rh with hr
  have hden : (B.td * B.bd * RD : ℤ) ≠ 0 := by
    have : (0 : ℤ) < (RD : ℤ) := by norm_num [RD]
    have h1 : (0 : ℤ) < B.td := by exact_mod_cast htd
    have h2 : (0 : ℤ) < B.bd := by exact_mod_cast hbd
    positivity
  have hfl := Int.ediv_mul_le (num * r * R) hden
  have hfl' : ((B.yDown num : ℤ) : ℝ) * ((B.td * B.bd * RD : ℤ) : ℝ) ≤ ((num * r * R : ℤ) : ℝ) := by
    have : B.yDown num = num * r * R / (B.td * B.bd * RD) := rfl
    rw [this]
    exact_mod_cast hfl
  push_cast at hfl'
  have hkey : (num : ℝ) * (r : ℝ) / RD ≤ num * (1 / s) := by
    by_cases hn : 0 ≤ num
    · have hn' : (0 : ℝ) ≤ num := by exact_mod_cast hn
      have : (r : ℝ) = B.rl := by simp [hr, hn]
      rw [this, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hr1 hn'
    · have hn' : (num : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp hn).le
      have : (r : ℝ) = B.rh := by simp [hr, hn]
      rw [this, mul_div_assoc]
      exact mul_le_mul_of_nonpos_left hr2 hn'
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (B.yDown num : ℝ) * (B.td * B.bd * RD) ≤ (num : ℝ) * (r : ℝ) * R := hfl'
  have h4 : num * (r : ℝ) / RD * s ≤ (num : ℝ) := by
    have := mul_le_mul_of_nonneg_right hkey hs.le
    have e : (num : ℝ) * (1 / s) * s = num := by field_simp
    rw [e] at this; exact this
  have h5 : num * (r : ℝ) * s ≤ (num : ℝ) * RD := by
    have := mul_le_mul_of_nonneg_right h4 hRD.le
    have e : (num : ℝ) * (r : ℝ) / RD * s * RD = num * r * s := by field_simp
    rw [e] at this; exact this
  nlinarith [mul_pos (mul_pos htd' hbd') (mul_pos hH hR), mul_pos hs hR,
    mul_le_mul_of_nonneg_right h5 (mul_pos hH hR).le,
    mul_le_mul_of_nonneg_right h3 (mul_pos hs hH).le]

/-- `θ + b z` at a grid point, as a quotient of integers. -/
lemma affine_eq (hok : B.paramOK = true) (zi : ℤ) :
    B.θ + B.b * ((zi : ℝ) / H) = (B.Mnum zi : ℝ) / (B.td * B.bd * H) := by
  simp only [paramOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨htd, hbd⟩, -⟩, -⟩ := hok
  have htd' : (0 : ℝ) < B.td := by exact_mod_cast htd
  have hbd' : (0 : ℝ) < B.bd := by exact_mod_cast hbd
  have hH := H_pos
  unfold BlockQ.θ BlockQ.b Mnum
  push_cast
  field_simp

variable (tab : ℕ → Entry) (imax : ℕ) (B)

/-- Integer upper bound for `D` times the conditional two-sided tail of the block over a bin. -/
def tU (zl zh : ℤ) (ci : ℕ) : ℕ :=
  PhiUp tab imax (B.yUp (max (B.Mnum zl) (B.Mnum zh) - ci * B.td * B.bd))
    + PhiUp tab imax (B.yUp (-min (B.Mnum zl) (B.Mnum zh) - ci * B.td * B.bd))

/-- Integer lower bound for `D` times the conditional two-sided tail of the block over a bin. -/
def tL (zl zh : ℤ) (ci : ℕ) : ℕ :=
  PhiDown tab imax (B.yDown (min (B.Mnum zl) (B.Mnum zh) - ci * B.td * B.bd))
    + PhiDown tab imax (B.yDown (-max (B.Mnum zl) (B.Mnum zh) - ci * B.td * B.bd))

variable {tab imax B}

lemma arg_eq (hok : B.paramOK = true) (m : ℤ) (ci : ℕ) :
    (m : ℝ) / (B.td * B.bd * H) - (ci : ℝ) / H
      = ((m - ci * B.td * B.bd : ℤ) : ℝ) / (B.td * B.bd * H) := by
  simp only [paramOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨htd, hbd⟩, -⟩, -⟩ := hok
  have htd' : (0 : ℝ) < B.td := by exact_mod_cast htd
  have hbd' : (0 : ℝ) < B.bd := by exact_mod_cast hbd
  have hH := H_pos
  push_cast
  field_simp

lemma den_nonneg (B : BlockQ) : (0 : ℝ) ≤ (B.td : ℝ) * B.bd * H := by
  have := H_pos; positivity

theorem tU_spec (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H)
    (hok : B.paramOK = true) {s : ℝ} (hs : 0 < s) (hbs : B.b ^ 2 + s ^ 2 = 1) (zl zh : ℤ)
    (ci : ℕ) :
    (D : ℝ) * (Φ ((max (B.θ + B.b * ((zl : ℝ) / H)) (B.θ + B.b * ((zh : ℝ) / H)) - (ci : ℝ) / H) / s)
        + Φ ((-min (B.θ + B.b * ((zl : ℝ) / H)) (B.θ + B.b * ((zh : ℝ) / H)) - (ci : ℝ) / H) / s))
      ≤ (B.tU tab imax zl zh ci : ℕ) := by
  rw [affine_eq hok, affine_eq hok, max_div_div_right (den_nonneg B),
    min_div_div_right (den_nonneg B), ← Int.cast_max, ← Int.cast_min]
  have e2 : -(((min (B.Mnum zl) (B.Mnum zh) : ℤ) : ℝ) / (B.td * B.bd * H))
      = ((-min (B.Mnum zl) (B.Mnum zh) : ℤ) : ℝ) / (B.td * B.bd * H) := by
    push_cast; ring
  rw [e2, arg_eq hok, arg_eq hok]
  unfold tU
  push_cast [mul_add]
  have h1 := PhiUp_le hv himax (yUp_spec hok hs hbs
    (max (B.Mnum zl) (B.Mnum zh) - ci * B.td * B.bd))
  have h2 := PhiUp_le hv himax (yUp_spec hok hs hbs
    (-min (B.Mnum zl) (B.Mnum zh) - ci * B.td * B.bd))
  push_cast at h1 h2 ⊢
  linarith

theorem tL_spec (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H)
    (hok : B.paramOK = true) {s : ℝ} (hs : 0 < s) (hbs : B.b ^ 2 + s ^ 2 = 1) (zl zh : ℤ)
    (ci : ℕ) :
    ((B.tL tab imax zl zh ci : ℕ) : ℝ)
      ≤ D * (Φ ((min (B.θ + B.b * ((zl : ℝ) / H)) (B.θ + B.b * ((zh : ℝ) / H)) - (ci : ℝ) / H) / s)
        + Φ ((-max (B.θ + B.b * ((zl : ℝ) / H)) (B.θ + B.b * ((zh : ℝ) / H)) - (ci : ℝ) / H) / s)) := by
  rw [affine_eq hok, affine_eq hok, max_div_div_right (den_nonneg B),
    min_div_div_right (den_nonneg B), ← Int.cast_max, ← Int.cast_min]
  have e2 : -(((max (B.Mnum zl) (B.Mnum zh) : ℤ) : ℝ) / (B.td * B.bd * H))
      = ((-max (B.Mnum zl) (B.Mnum zh) : ℤ) : ℝ) / (B.td * B.bd * H) := by
    push_cast; ring
  rw [e2, arg_eq hok, arg_eq hok]
  unfold tL
  have h1 := PhiDown_le hv himax (yDown_spec hok hs hbs
    (min (B.Mnum zl) (B.Mnum zh) - ci * B.td * B.bd))
  have h2 := PhiDown_le hv himax (yDown_spec hok hs hbs
    (-max (B.Mnum zl) (B.Mnum zh) - ci * B.td * B.bd))
  push_cast at h1 h2 ⊢
  linarith

end BlockQ

/-- A bin `(zl / H, zh / H]` of the factor axis with its cut-offs `cs` (in units `1 / H`,
increasing; the last one is the upper bracket) and the lower-bracket cut-off `bc`. -/
structure Bin where
  zl : ℤ
  zh : ℤ
  cs : List ℕ
  bc : ℕ
  deriving Inhabited

section Checker

variable (tab : ℕ → Entry) (imax : ℕ) (blk : Fin 3 → BlockQ) (αinv ETA : ℕ)

/-- Total multiplicity. -/
def Mtot : ℕ := (blk 0).mult + (blk 1).mult + (blk 2).mult

/-- Integer upper bound for `D * Mtot *` (conditional mean fraction above the cut-off). -/
def GupN (zl zh : ℤ) (ci : ℕ) : ℕ :=
  (blk 0).mult * (blk 0).tU tab imax zl zh ci + (blk 1).mult * (blk 1).tU tab imax zl zh ci
    + (blk 2).mult * (blk 2).tU tab imax zl zh ci

/-- Integer lower bound for `D * Mtot *` (conditional mean fraction above the cut-off). -/
def GlowN (zl zh : ℤ) (ci : ℕ) : ℕ :=
  (blk 0).mult * (blk 0).tL tab imax zl zh ci + (blk 1).mult * (blk 1).tL tab imax zl zh ci
    + (blk 2).mult * (blk 2).tL tab imax zl zh ci

/-- The same for the null block alone. -/
def GnullN (zl zh : ℤ) (ci : ℕ) : ℕ := (blk 0).mult * (blk 0).tL tab imax zl zh ci

/-- Check of the cells between consecutive cut-offs. -/
def cellsOK (zl zh : ℤ) : List ℕ → Bool
  | c :: c' :: rest =>
    decide (0 < c') && decide (c' ≤ imax) &&
      decide (GupN tab imax blk zl zh c + ETA ≤ 2 * αinv * Mtot blk * (tab c').tailLo) &&
      cellsOK zl zh (c' :: rest)
  | _ => true

/-- Integer lower bound for `D (Φ(zh / H) - Φ(zl / H))`. -/
def deltaN (zl zh : ℤ) : ℕ :=
  if 0 ≤ zl then (tab zl.toNat).tailLo - (tab zh.toNat).tailHi
  else (tab (-zh).toNat).tailLo - (tab (-zl).toNat).tailHi

/-- Check of one bin. -/
def binOK (B : Bin) : Bool :=
  decide (B.zl < B.zh) && decide (0 ≤ B.zl ∨ B.zh ≤ 0) && decide (B.zl.natAbs ≤ imax) &&
    decide (B.zh.natAbs ≤ imax) && decide (0 < B.cs.getD 0 0) && decide (B.cs.getD 0 0 ≤ imax) &&
    decide (D ≤ 2 * αinv * (tab (B.cs.getD 0 0)).tailLo) &&
    cellsOK tab imax blk αinv ETA B.zl B.zh B.cs &&
    decide (0 < B.bc) && decide (B.bc ≤ imax) && decide (2 * αinv * (tab B.bc).tailHi ≤ D) &&
    decide (2 * αinv * Mtot blk * (tab B.bc).tailHi + 2 * ETA ≤ GlowN tab imax blk B.zl B.zh B.bc) &&
    decide (ETA ≤ GnullN tab imax blk B.zl B.zh B.bc)

/-- The contribution of a bin to the certificate sum, scaled by `D`. -/
def binTerm (B : Bin) : ℕ :=
  (GnullN tab imax blk B.zl B.zh B.bc - ETA) * deltaN tab B.zl B.zh
    / (2 * Mtot blk * (tab (B.cs.getD (B.cs.length - 1) 0)).tailHi)

/-- Consecutive bins do not overlap. -/
def sortedOK : List Bin → Bool
  | B :: B' :: rest => decide (B.zh ≤ B'.zl) && sortedOK (B' :: rest)
  | _ => true

/-- Check of the model parameters. -/
def paramsOK : Bool :=
  (blk 0).paramOK && (blk 1).paramOK && (blk 2).paramOK && decide (0 < αinv) &&
    decide (0 < ETA) && decide (0 < Mtot blk)

/-- **The certificate check.** -/
def certOK (bins : List Bin) : Bool :=
  paramsOK blk αinv ETA && bins.all (binOK tab imax blk αinv ETA) && sortedOK bins &&
    decide (D < (bins.map (binTerm tab imax blk ETA)).sum)

/-- Check of a chunk of bins: every bin passes and the terms add up to at least `S`. -/
def chunkOK (l : List Bin) (S : ℕ) : Bool :=
  l.all (binOK tab imax blk αinv ETA) && decide (S ≤ (l.map (binTerm tab imax blk ETA)).sum)

variable {tab imax blk αinv ETA}

lemma chunks_key : ∀ (chunks : List (List Bin)) (Ss : List ℕ),
    List.Forall₂ (fun l S => chunkOK tab imax blk αinv ETA l S = true) chunks Ss →
    (chunks.flatten.all (binOK tab imax blk αinv ETA) = true) ∧
      Ss.sum ≤ (chunks.flatten.map (binTerm tab imax blk ETA)).sum := by
  intro chunks Ss hch
  induction hch with
  | nil => simp
  | @cons l S ls Ss' h _ ih =>
    simp only [chunkOK, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.flatten_cons, List.all_append, Bool.and_eq_true, List.map_append,
      List.sum_append, List.sum_cons]
    exact ⟨⟨h.1, ih.1⟩, Nat.add_le_add h.2 ih.2⟩

/-- The certificate check can be run chunk by chunk. -/
theorem certOK_of_chunks (hpar : paramsOK blk αinv ETA = true) (chunks : List (List Bin))
    (Ss : List ℕ)
    (hch : List.Forall₂ (fun l S => chunkOK tab imax blk αinv ETA l S = true) chunks Ss)
    (hsorted : sortedOK chunks.flatten = true) (hD : D < Ss.sum) :
    certOK tab imax blk αinv ETA chunks.flatten = true := by
  have key := chunks_key chunks Ss hch
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hpar, key.1⟩, hsorted⟩, lt_of_lt_of_le hD key.2⟩

lemma cellsOK_spec {zl zh : ℤ} : ∀ {cs : List ℕ}, cellsOK tab imax blk αinv ETA zl zh cs = true →
    ∀ j, j + 1 < cs.length → 0 < cs.getD (j + 1) 0 ∧ cs.getD (j + 1) 0 ≤ imax ∧
      GupN tab imax blk zl zh (cs.getD j 0) + ETA
        ≤ 2 * αinv * Mtot blk * (tab (cs.getD (j + 1) 0)).tailLo
  | [], _, j, hj => by simp at hj
  | [_], _, j, hj => by simp at hj
  | c :: c' :: rest, h, j, hj => by
    simp only [cellsOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases j with
    | zero => exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩
    | succ j =>
      have := cellsOK_spec h4 j (by simpa using hj)
      simpa [List.getD_cons_succ] using this

lemma deltaN_spec (hv : ∀ i ≤ imax, (tab i).Valid i) {zl zh : ℤ} (hlt : zl < zh)
    (hsign : 0 ≤ zl ∨ zh ≤ 0) (hzl : zl.natAbs ≤ imax) (hzh : zh.natAbs ≤ imax) :
    (deltaN tab zl zh : ℝ) ≤ D * (Φ ((zh : ℝ) / H) - Φ ((zl : ℝ) / H)) := by
  have hD := D_pos
  have hH := H_pos
  have hmono : Φ ((zl : ℝ) / H) ≤ Φ ((zh : ℝ) / H) := by
    refine monotone_cdf _ (div_le_div_of_nonneg_right ?_ hH.le)
    exact_mod_cast hlt.le
  have hnn : (0 : ℝ) ≤ D * (Φ ((zh : ℝ) / H) - Φ ((zl : ℝ) / H)) :=
    mul_nonneg hD.le (sub_nonneg.mpr hmono)
  have hsubcast : ∀ a b : ℕ, ∀ x : ℝ, 0 ≤ x → (a : ℝ) - b ≤ x → ((a - b : ℕ) : ℝ) ≤ x := by
    intro a b x hx h
    rcases le_total b a with hba | hab
    · rw [Nat.cast_sub hba]; exact h
    · rw [Nat.sub_eq_zero_of_le hab]; simpa using hx
  unfold deltaN
  by_cases h0 : 0 ≤ zl
  · simp only [h0, ite_true]
    have h0' : 0 ≤ zh := h0.trans hlt.le
    have i1 : zl.toNat ≤ imax := by omega
    have i2 : zh.toNat ≤ imax := by omega
    have c1 : ((zl.toNat : ℕ) : ℝ) = (zl : ℝ) := by
      have : ((zl.toNat : ℤ) : ℝ) = (zl : ℝ) := by rw [Int.toNat_of_nonneg h0]
      exact_mod_cast this
    have c2 : ((zh.toNat : ℕ) : ℝ) = (zh : ℝ) := by
      have : ((zh.toNat : ℤ) : ℝ) = (zh : ℝ) := by rw [Int.toNat_of_nonneg h0']
      exact_mod_cast this
    obtain ⟨-, -, hl, -⟩ := hv _ i1
    obtain ⟨-, -, -, hh⟩ := hv _ i2
    rw [c1] at hl
    rw [c2] at hh
    refine hsubcast _ _ _ hnn ?_
    linarith
  · simp only [h0, ite_false]
    have hzh0 : zh ≤ 0 := hsign.resolve_left h0
    have hzl0 : zl < 0 := not_le.mp h0
    have i1 : (-zh).toNat ≤ imax := by omega
    have i2 : (-zl).toNat ≤ imax := by omega
    have c1 : (((-zh).toNat : ℕ) : ℝ) = -(zh : ℝ) := by
      have : (((-zh).toNat : ℤ) : ℝ) = ((-zh : ℤ) : ℝ) := by
        rw [Int.toNat_of_nonneg (by omega)]
      rw [Int.cast_neg] at this
      exact_mod_cast this
    have c2 : (((-zl).toNat : ℕ) : ℝ) = -(zl : ℝ) := by
      have : (((-zl).toNat : ℤ) : ℝ) = ((-zl : ℤ) : ℝ) := by
        rw [Int.toNat_of_nonneg (by omega)]
      rw [Int.cast_neg] at this
      exact_mod_cast this
    obtain ⟨-, -, hl, -⟩ := hv _ i1
    obtain ⟨-, -, -, hh⟩ := hv _ i2
    rw [c1] at hl
    rw [c2] at hh
    have e1 : Φ ((zh : ℝ) / H) = 1 - Φ (-(zh : ℝ) / H) := by
      have : (zh : ℝ) / H = -(-(zh : ℝ) / H) := by ring
      rw [this, cdf_gaussian_neg]
    have e2 : Φ ((zl : ℝ) / H) = 1 - Φ (-(zl : ℝ) / H) := by
      have : (zl : ℝ) / H = -(-(zl : ℝ) / H) := by ring
      rw [this, cdf_gaussian_neg]
    refine hsubcast _ _ _ hnn ?_
    rw [e1, e2]
    linarith

end Checker

section Model

variable {tab : ℕ → Entry} {imax : ℕ} {blk : Fin 3 → BlockQ} {αinv ETA : ℕ} {s : Fin 3 → ℝ}

lemma sum_mult (blk : Fin 3 → BlockQ) : (∑ g : Fin 3, (blk g).mult) = Mtot blk := by
  rw [Fin.sum_univ_three]; rfl

theorem GupN_spec (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H)
    (hpar : paramsOK blk αinv ETA = true) (hs : ∀ g, 0 < s g)
    (hbs : ∀ g, (blk g).b ^ 2 + s g ^ 2 = 1) (zl zh : ℤ) (ci : ℕ) :
    (D : ℝ) * Mtot blk * blockGUpper (fun g => (blk g).mult) (fun g => (blk g).θ)
        (fun g => (blk g).b) s univ ((zl : ℝ) / H) ((zh : ℝ) / H) ((ci : ℝ) / H)
      ≤ GupN tab imax blk zl zh ci := by
  simp only [paramsOK, Bool.and_eq_true, decide_eq_true_eq] at hpar
  obtain ⟨⟨⟨⟨⟨hp0, hp1⟩, hp2⟩, -⟩, -⟩, hM⟩ := hpar
  have hM' : (0 : ℝ) < Mtot blk := by exact_mod_cast hM
  have h0 := BlockQ.tU_spec hv himax hp0 (hs 0) (hbs 0) zl zh ci
  have h1 := BlockQ.tU_spec hv himax hp1 (hs 1) (hbs 1) zl zh ci
  have h2 := BlockQ.tU_spec hv himax hp2 (hs 2) (hbs 2) zl zh ci
  have e : ∀ X : ℝ, (D : ℝ) * Mtot blk * (X / Mtot blk) = D * X := fun X => by field_simp
  unfold blockGUpper GupN
  rw [sum_mult, e, Fin.sum_univ_three]
  simp only [blockTailUpper]
  push_cast
  have m0 : (0 : ℝ) ≤ (blk 0).mult := Nat.cast_nonneg _
  have m1 : (0 : ℝ) ≤ (blk 1).mult := Nat.cast_nonneg _
  have m2 : (0 : ℝ) ≤ (blk 2).mult := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h0 m0, mul_le_mul_of_nonneg_left h1 m1,
    mul_le_mul_of_nonneg_left h2 m2]

theorem GlowN_spec (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H)
    (hpar : paramsOK blk αinv ETA = true) (hs : ∀ g, 0 < s g)
    (hbs : ∀ g, (blk g).b ^ 2 + s g ^ 2 = 1) (zl zh : ℤ) (ci : ℕ) :
    (GlowN tab imax blk zl zh ci : ℝ)
      ≤ (D : ℝ) * Mtot blk * blockGLower (fun g => (blk g).mult) (fun g => (blk g).θ)
        (fun g => (blk g).b) s univ ((zl : ℝ) / H) ((zh : ℝ) / H) ((ci : ℝ) / H) := by
  simp only [paramsOK, Bool.and_eq_true, decide_eq_true_eq] at hpar
  obtain ⟨⟨⟨⟨⟨hp0, hp1⟩, hp2⟩, -⟩, -⟩, hM⟩ := hpar
  have hM' : (0 : ℝ) < Mtot blk := by exact_mod_cast hM
  have h0 := BlockQ.tL_spec hv himax hp0 (hs 0) (hbs 0) zl zh ci
  have h1 := BlockQ.tL_spec hv himax hp1 (hs 1) (hbs 1) zl zh ci
  have h2 := BlockQ.tL_spec hv himax hp2 (hs 2) (hbs 2) zl zh ci
  have e : ∀ X : ℝ, (D : ℝ) * Mtot blk * (X / Mtot blk) = D * X := fun X => by field_simp
  unfold blockGLower GlowN
  rw [sum_mult, e, Fin.sum_univ_three]
  simp only [blockTailLower]
  push_cast
  have m0 : (0 : ℝ) ≤ (blk 0).mult := Nat.cast_nonneg _
  have m1 : (0 : ℝ) ≤ (blk 1).mult := Nat.cast_nonneg _
  have m2 : (0 : ℝ) ≤ (blk 2).mult := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h0 m0, mul_le_mul_of_nonneg_left h1 m1,
    mul_le_mul_of_nonneg_left h2 m2]

theorem GnullN_spec (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H)
    (hpar : paramsOK blk αinv ETA = true) (hs : ∀ g, 0 < s g)
    (hbs : ∀ g, (blk g).b ^ 2 + s g ^ 2 = 1) (zl zh : ℤ) (ci : ℕ) :
    (GnullN tab imax blk zl zh ci : ℝ)
      ≤ (D : ℝ) * Mtot blk * blockGLower (fun g => (blk g).mult) (fun g => (blk g).θ)
        (fun g => (blk g).b) s {0} ((zl : ℝ) / H) ((zh : ℝ) / H) ((ci : ℝ) / H) := by
  simp only [paramsOK, Bool.and_eq_true, decide_eq_true_eq] at hpar
  obtain ⟨⟨⟨⟨⟨hp0, -⟩, -⟩, -⟩, -⟩, hM⟩ := hpar
  have hM' : (0 : ℝ) < Mtot blk := by exact_mod_cast hM
  have h0 := BlockQ.tL_spec hv himax hp0 (hs 0) (hbs 0) zl zh ci
  have e : ∀ X : ℝ, (D : ℝ) * Mtot blk * (X / Mtot blk) = D * X := fun X => by field_simp
  unfold blockGLower GnullN
  rw [sum_mult, e, Finset.sum_singleton]
  simp only [blockTailLower]
  push_cast
  have m0 : (0 : ℝ) ≤ (blk 0).mult := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h0 m0]

end Model

section BinSpec

variable (tab : ℕ → Entry) (imax : ℕ) (blk : Fin 3 → BlockQ) (ETA : ℕ)

/-- Left end point of a bin. -/
noncomputable def binZl (B : Bin) : ℝ := (B.zl : ℝ) / H
/-- Right end point of a bin. -/
noncomputable def binZh (B : Bin) : ℝ := (B.zh : ℝ) / H
/-- The `j`-th cut-off of a bin. -/
noncomputable def binC (B : Bin) (j : ℕ) : ℝ := (B.cs.getD j 0 : ℝ) / H
/-- The lower-bracket cut-off of a bin. -/
noncomputable def binBc (B : Bin) : ℝ := (B.bc : ℝ) / H
/-- The certified lower bound for the null fraction rejected at the lower bracket. -/
noncomputable def binF (B : Bin) : ℝ :=
  ((GnullN tab imax blk B.zl B.zh B.bc - ETA : ℕ) : ℝ) / (D * Mtot blk)
/-- The slack `η`. -/
noncomputable def etaR : ℝ := (ETA : ℝ) / (D * Mtot blk)

variable {tab imax blk ETA} {αinv : ℕ} {s : Fin 3 → ℝ}

lemma uTail_bounds (hv : ∀ i ≤ imax, (tab i).Valid i) {ci : ℕ} (hci : ci ≤ imax) :
    (2 * ((tab ci).tailLo : ℝ)) ≤ D * uTail ((ci : ℝ) / H) ∧
      (D : ℝ) * uTail ((ci : ℝ) / H) ≤ 2 * (tab ci).tailHi := by
  obtain ⟨-, -, h3, h4⟩ := hv ci hci
  unfold uTail
  constructor <;> linarith

theorem bin_spec (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H)
    (hpar : paramsOK blk αinv ETA = true) (hs : ∀ g, 0 < s g)
    (hbs : ∀ g, (blk g).b ^ 2 + s g ^ 2 = 1) (B : Bin)
    (hB : binOK tab imax blk αinv ETA B = true) :
    binZl B < binZh B ∧ (∀ j, j ≤ B.cs.length - 1 → 0 < binC B j) ∧
    1 / (αinv : ℝ) ≤ uTail (binC B 0) ∧ 0 < binBc B ∧ uTail (binBc B) ≤ 1 / (αinv : ℝ) ∧
    0 ≤ binF tab imax blk ETA B ∧
    (∀ j, j < B.cs.length - 1 →
      blockGUpper (fun g => (blk g).mult) (fun g => (blk g).θ) (fun g => (blk g).b) s univ
        (binZl B) (binZh B) (binC B j) + etaR blk ETA ≤ uTail (binC B (j + 1)) / (1 / (αinv : ℝ))) ∧
    uTail (binBc B) / (1 / (αinv : ℝ)) + 2 * etaR blk ETA
      ≤ blockGLower (fun g => (blk g).mult) (fun g => (blk g).θ) (fun g => (blk g).b) s univ
        (binZl B) (binZh B) (binBc B) ∧
    binF tab imax blk ETA B + etaR blk ETA
      ≤ blockGLower (fun g => (blk g).mult) (fun g => (blk g).θ) (fun g => (blk g).b) s {0}
        (binZl B) (binZh B) (binBc B) ∧
    (binTerm tab imax blk ETA B : ℝ) / D
      ≤ binF tab imax blk ETA B / uTail (binC B (B.cs.length - 1))
        * (Φ (binZh B) - Φ (binZl B)) := by
  have hH := H_pos
  have hD := D_pos
  have hpar' := hpar
  simp only [paramsOK, Bool.and_eq_true, decide_eq_true_eq] at hpar'
  obtain ⟨⟨⟨-, hα⟩, hE⟩, hM⟩ := hpar'
  have hα' : (0 : ℝ) < αinv := by exact_mod_cast hα
  have hM' : (0 : ℝ) < Mtot blk := by exact_mod_cast hM
  have hDM : (0 : ℝ) < D * Mtot blk := mul_pos hD hM'
  simp only [binOK, Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := hB
  have hcells := cellsOK_spec h8
  have hcuts : ∀ j, j ≤ B.cs.length - 1 → 0 < B.cs.getD j 0 ∧ B.cs.getD j 0 ≤ imax := by
    intro j hj
    cases j with
    | zero => exact ⟨h5, h6⟩
    | succ j =>
      obtain ⟨a, b, -⟩ := hcells j (by omega)
      exact ⟨a, b⟩
  have h1r : (B.zl : ℝ) < B.zh := by exact_mod_cast h1
  refine ⟨div_lt_div_of_pos_right h1r hH, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have : (0 : ℝ) < (B.cs.getD j 0 : ℝ) := by exact_mod_cast (hcuts j hj).1
    exact div_pos this hH
  · obtain ⟨hlo, -⟩ := uTail_bounds hv h6
    have h7' : (D : ℝ) ≤ 2 * αinv * (tab (B.cs.getD 0 0)).tailLo := by exact_mod_cast h7
    rw [div_le_iff₀ hα']
    unfold binC
    nlinarith
  · have : (0 : ℝ) < B.bc := by exact_mod_cast h9
    exact div_pos this hH
  · obtain ⟨-, hhi⟩ := uTail_bounds hv h10
    have h11' : 2 * (αinv : ℝ) * (tab B.bc).tailHi ≤ D := by exact_mod_cast h11
    rw [le_div_iff₀ hα']
    unfold binBc
    nlinarith
  · unfold binF; positivity
  · intro j hj
    obtain ⟨-, hc', hcell⟩ := hcells j (by omega)
    have hcell' : (GupN tab imax blk B.zl B.zh (B.cs.getD j 0) : ℝ) + ETA
        ≤ 2 * αinv * Mtot blk * (tab (B.cs.getD (j + 1) 0)).tailLo := by exact_mod_cast hcell
    have hG := GupN_spec hv himax hpar hs hbs B.zl B.zh (B.cs.getD j 0)
    obtain ⟨hlo, -⟩ := uTail_bounds hv hc'
    rw [div_div_eq_mul_div, div_one]
    unfold etaR binC binZl binZh
    have hgoal : (D : ℝ) * Mtot blk * (blockGUpper (fun g => (blk g).mult) (fun g => (blk g).θ)
          (fun g => (blk g).b) s univ ((B.zl : ℝ) / H) ((B.zh : ℝ) / H)
          ((B.cs.getD j 0 : ℝ) / H) + (ETA : ℝ) / (D * Mtot blk))
        ≤ D * Mtot blk * (uTail ((B.cs.getD (j + 1) 0 : ℝ) / H) * αinv) := by
      rw [mul_add, mul_div_cancel₀ _ hDM.ne']
      nlinarith [mul_le_mul_of_nonneg_left hlo (mul_pos hα' hM').le]
    exact le_of_mul_le_mul_left hgoal hDM
  · have h12' : 2 * (αinv : ℝ) * Mtot blk * (tab B.bc).tailHi + 2 * ETA
        ≤ GlowN tab imax blk B.zl B.zh B.bc := by exact_mod_cast h12
    have hG := GlowN_spec hv himax hpar hs hbs B.zl B.zh B.bc
    obtain ⟨-, hhi⟩ := uTail_bounds hv h10
    rw [div_div_eq_mul_div, div_one]
    unfold etaR binBc binZl binZh
    have hgoal : (D : ℝ) * Mtot blk * (uTail ((B.bc : ℝ) / H) * αinv
          + 2 * ((ETA : ℝ) / (D * Mtot blk)))
        ≤ D * Mtot blk * blockGLower (fun g => (blk g).mult) (fun g => (blk g).θ)
          (fun g => (blk g).b) s univ ((B.zl : ℝ) / H) ((B.zh : ℝ) / H) ((B.bc : ℝ) / H) := by
      have e : (D : ℝ) * Mtot blk * (2 * ((ETA : ℝ) / (D * Mtot blk))) = 2 * ETA := by
        field_simp
      rw [mul_add, e]
      nlinarith [mul_le_mul_of_nonneg_left hhi (mul_pos hα' hM').le]
    exact le_of_mul_le_mul_left hgoal hDM
  · have hG := GnullN_spec hv himax hpar hs hbs B.zl B.zh B.bc
    unfold binF etaR binBc binZl binZh
    rw [Nat.cast_sub h13, ← add_div, sub_add_cancel, div_le_iff₀ hDM]
    linarith
  · -- the term
    set a := B.cs.getD (B.cs.length - 1) 0 with ha
    obtain ⟨-, haimax⟩ := hcuts (B.cs.length - 1) le_rfl
    obtain ⟨-, hhi⟩ := uTail_bounds hv haimax
    have huT := uTail_pos ((a : ℝ) / H)
    have hd := deltaN_spec hv h1 h2 h3 h4
    set fN : ℕ := GnullN tab imax blk B.zl B.zh B.bc - ETA with hfN
    set dN : ℕ := deltaN tab B.zl B.zh with hdN
    set tHa : ℕ := (tab a).tailHi with htHa
    have htHa0 : (0 : ℝ) < tHa := by nlinarith
    have hfloor : (binTerm tab imax blk ETA B : ℝ) ≤ (fN : ℝ) * dN / (2 * Mtot blk * tHa) := by
      unfold binTerm
      refine Nat.cast_div_le.trans (le_of_eq ?_)
      push_cast; rfl
    have hΔ : (0 : ℝ) ≤ Φ ((B.zh : ℝ) / H) - Φ ((B.zl : ℝ) / H) :=
      sub_nonneg.mpr (monotone_cdf _ (div_le_div_of_nonneg_right h1r.le hH.le))
    have hfN0 : (0 : ℝ) ≤ fN := Nat.cast_nonneg _
    unfold binF binC binZl binZh
    rw [div_le_iff₀ hD]
    refine hfloor.trans ?_
    have step1 : (fN : ℝ) * dN / (2 * Mtot blk * tHa)
        ≤ (fN : ℝ) * (D * (Φ ((B.zh : ℝ) / H) - Φ ((B.zl : ℝ) / H))) / (2 * Mtot blk * tHa) := by
      gcongr
    refine step1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have e : (fN : ℝ) / (D * Mtot blk) / uTail ((a : ℝ) / H)
          * (Φ ((B.zh : ℝ) / H) - Φ ((B.zl : ℝ) / H)) * D * (2 * Mtot blk * tHa)
        = (fN : ℝ) * (Φ ((B.zh : ℝ) / H) - Φ ((B.zl : ℝ) / H)) * (2 * tHa)
          / uTail ((a : ℝ) / H) := by
      field_simp
    rw [e, le_div_iff₀ huT]
    have hprod : (0 : ℝ) ≤ fN * (Φ ((B.zh : ℝ) / H) - Φ ((B.zl : ℝ) / H)) :=
      mul_nonneg hfN0 hΔ
    nlinarith [mul_le_mul_of_nonneg_left hhi hprod]

end BinSpec

section Final

lemma sum_fin_getD {β : Type*} (l : List β) (g : β → ℝ) (d : β) :
    ∑ k : Fin l.length, g (l.getD k d) = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    show ∑ k : Fin (l.length + 1), g ((x :: l).getD k d) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ, ih,
      List.map_cons, List.sum_cons]

lemma sortedOK_spec : ∀ (l : List Bin), sortedOK l = true → (∀ B ∈ l, B.zl < B.zh) →
    ∀ i j, i < j → j < l.length → (l.getD i default).zh ≤ (l.getD j default).zl
  | [], _, _, i, j, _, hj => by simp at hj
  | [_], _, _, i, j, hij, hj => by
    simp only [List.length_cons, List.length_nil] at hj; omega
  | B :: B' :: rest, h, hlt, i, j, hij, hj => by
    simp only [sortedOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hlt' : ∀ C ∈ B' :: rest, C.zl < C.zh := fun C hC => hlt C (List.mem_cons_of_mem _ hC)
    have ih := sortedOK_spec (B' :: rest) h2 hlt'
    cases j with
    | zero => omega
    | succ j =>
      have hj' : j < (B' :: rest).length := by simpa using hj
      cases i with
      | zero =>
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        cases j with
        | zero => simpa using h1
        | succ j =>
          have h3 := ih 0 (j + 1) (Nat.succ_pos _) hj'
          simp only [List.getD_cons_zero] at h3
          have h4 : B'.zl < B'.zh := hlt B' (by simp)
          have h5 : (((B' :: rest).getD (j + 1) default)).zl
              = ((B' :: rest).getD (j + 1) default).zl := rfl
          omega
      | succ i =>
        simp only [List.getD_cons_succ]
        exact ih i j (by omega) hj'

variable {tab : ℕ → Entry} {imax : ℕ} {blk : Fin 3 → BlockQ} {αinv ETA : ℕ} {s : Fin 3 → ℝ}

/-- **Soundness of the certificate check.** If the table is valid and `certOK` returns `true`,
then in the three-block model described by `blk` (residual standard deviations `s g > 0` with
`b g ^ 2 + s g ^ 2 = 1`; block `0` is the null block) the Benjamini–Hochberg procedure at level
`1 / αinv` applied to the two-sided p-values has false discovery rate strictly above
`1 / αinv`, for every sufficiently large replication number `N`. -/
theorem exists_fdr_gt_of_certOK (hv : ∀ i ≤ imax, (tab i).Valid i) (himax : imax ≤ H * H)
    (hs : ∀ g, 0 < s g) (hbs : ∀ g, (blk g).b ^ 2 + s g ^ 2 = 1) (bins : List Bin)
    (hcert : certOK tab imax blk αinv ETA bins = true) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ENNReal.ofReal (1 / (αinv : ℝ))
      < fdr (factorMeasure (blockIndex (fun g => (blk g).mult) N))
          (blockNulls (fun g => (blk g).mult) {0} N)
          (fun ω => bhReject (1 / (αinv : ℝ))
            (factorP (fun i : blockIndex (fun g => (blk g).mult) N => (blk i.1.1).θ)
              (fun i => (blk i.1.1).b) (fun i => s i.1.1) ω)) := by
  have hD := D_pos
  have hH := H_pos
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcert
  obtain ⟨⟨⟨hpar, hall⟩, hsorted⟩, hsum⟩ := hcert
  have hpar' := hpar
  simp only [paramsOK, Bool.and_eq_true, decide_eq_true_eq] at hpar'
  obtain ⟨⟨⟨-, hα⟩, hE⟩, hM⟩ := hpar'
  have hα' : (0 : ℝ) < αinv := by exact_mod_cast hα
  have hM' : (0 : ℝ) < Mtot blk := by exact_mod_cast hM
  have hE' : (0 : ℝ) < ETA := by exact_mod_cast hE
  set Bk : Fin bins.length → Bin := fun k => bins.getD k default with hBk
  have hmem : ∀ k, Bk k ∈ bins := by
    intro k
    have : bins.getD k default = bins[(k : ℕ)] := List.getD_eq_getElem _ _ k.2
    simp only [hBk, this]
    exact List.getElem_mem _
  have spec := fun k => bin_spec hv himax hpar hs hbs (Bk k) (hall _ (hmem k))
  set η : ℝ := etaR blk ETA with hη
  have hη0 : 0 < η := by rw [hη]; unfold etaR; positivity
  set S : ℝ := ∑ k, binF tab imax blk ETA (Bk k)
      / uTail (binC (Bk k) ((Bk k).cs.length - 1)) * (Φ (binZh (Bk k)) - Φ (binZl (Bk k)))
    with hSdef
  have hS : 1 < S := by
    have h1 : ∑ k : Fin bins.length, (binTerm tab imax blk ETA (Bk k) : ℝ) / D ≤ S :=
      Finset.sum_le_sum fun k _ => (spec k).2.2.2.2.2.2.2.2.2
    have h2 : ∑ k : Fin bins.length, (binTerm tab imax blk ETA (Bk k) : ℝ) / D
        = ((bins.map (binTerm tab imax blk ETA)).sum : ℝ) / D := by
      rw [← Finset.sum_div]
      congr 1
      rw [sum_fin_getD bins (fun B => (binTerm tab imax blk ETA B : ℝ)) default,
        Nat.cast_list_sum, List.map_map]
      rfl
    have h3 : (1 : ℝ) < ((bins.map (binTerm tab imax blk ETA)).sum : ℝ) / D := by
      rw [one_lt_div hD]; exact_mod_cast hsum
    linarith
  set nmax : ℕ := Finset.sup univ fun k : Fin bins.length => (Bk k).cs.length - 1 + 2 with hnmax
  have hMsum : ((∑ g : Fin 3, (blk g).mult : ℕ) : ℝ) = Mtot blk := by rw [sum_mult]
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (1 / (η * Mtot blk))
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (nmax * S / ((S - 1) * (η ^ 2 * Mtot blk)))
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have hNN₁ : (N₁ : ℝ) ≤ N := by exact_mod_cast (le_max_left _ _).trans hN
  have hNN₂ : (N₂ : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hdisj : Pairwise (Function.onFun Disjoint fun k : Fin bins.length =>
      Set.Ioc (binZl (Bk k)) (binZh (Bk k))) := by
    have hord : ∀ k k' : Fin bins.length, k < k' → binZh (Bk k) ≤ binZl (Bk k') := by
      intro k k' hkk
      have := sortedOK_spec bins hsorted (fun B hB => by
        have hb := hall B hB
        simp only [binOK, Bool.and_eq_true, decide_eq_true_eq] at hb
        exact hb.1.1.1.1.1.1.1.1.1.1.1.1) k k' hkk k'.2
      unfold binZh binZl
      exact div_le_div_of_nonneg_right (by exact_mod_cast this) hH.le
    intro k k' hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    rcases lt_or_gt_of_ne hne with h | h
    · have := hord k k' h
      linarith [hx.2, hx'.1]
    · have := hord k' k h
      linarith [hx'.2, hx.1]
  refine fdr_block_gt (fun g => (blk g).mult) (fun g => (blk g).θ) (fun g => (blk g).b) s
    (by positivity) hs {0} N (fun k => binZl (Bk k)) (fun k => binZh (Bk k))
    (fun k => (spec k).1.le) hdisj (fun k => (Bk k).cs.length - 1) (fun k j => binC (Bk k) j)
    (fun k => binBc (Bk k)) (fun k => binF tab imax blk ETA (Bk k)) hη0 ?_
    (fun k j hj => (spec k).2.1 j hj) (fun k => (spec k).2.2.1) (fun k => (spec k).2.2.2.1)
    (fun k => (spec k).2.2.2.2.1) (fun k => (spec k).2.2.2.2.2.1)
    (fun k j hj => (spec k).2.2.2.2.2.2.1 j hj) (fun k => (spec k).2.2.2.2.2.2.2.1)
    (fun k => (spec k).2.2.2.2.2.2.2.2.1) nmax
    (fun k => Finset.le_sup (f := fun k : Fin bins.length => (Bk k).cs.length - 1 + 2)
      (Finset.mem_univ k)) hS ?_
  · rw [hMsum]
    have h1 : 1 < η * Mtot blk * N₁ := by
      have hpos : 0 < η * Mtot blk := mul_pos hη0 hM'
      rw [div_lt_iff₀ hpos] at hN₁
      linarith
    nlinarith [mul_pos hη0 hM']
  · rw [hMsum]
    have hpos : 0 < (S - 1) * (η ^ 2 * Mtot blk) :=
      mul_pos (by linarith) (mul_pos (pow_pos hη0 2) hM')
    rw [div_lt_iff₀ hpos] at hN₂
    have : (S - 1) * (η ^ 2 * Mtot blk) * N₂ ≤ (S - 1) * (η ^ 2 * Mtot blk) * N :=
      mul_le_mul_of_nonneg_left hNN₂ hpos.le
    calc (nmax : ℝ) * S < N₂ * ((S - 1) * (η ^ 2 * Mtot blk)) := hN₂
      _ ≤ (S - 1) * (η ^ 2 * (Mtot blk * N)) := by nlinarith

end Final

end Applied.MultipleTesting.BlockCert
