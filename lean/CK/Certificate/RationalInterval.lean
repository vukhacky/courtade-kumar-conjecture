module

public import CK.Certificate.LogBounds

/-! Sound rational interval consumers for generated algebraic certificates.
Each rule checks exact rational arithmetic in Lean. In particular square
roots have nonnegative domains and reciprocals have positive denominators. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate
noncomputable section

def RationalBound (x : ℝ) (lo hi : ℚ) : Prop := (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)

theorem rationalBound_rat (q : ℚ) : RationalBound (q : ℝ) q q := ⟨le_rfl, le_rfl⟩

theorem rationalBound_widen {x : ℝ} {l u L U : ℚ}
    (h : RationalBound x l u) (hL : L ≤ l) (hU : u ≤ U) : RationalBound x L U := by
  have hL' : (L : ℝ) ≤ (l : ℝ) := by exact_mod_cast hL
  have hU' : (u : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
  exact ⟨hL'.trans h.1, h.2.trans hU'⟩

theorem rationalBound_add {x y : ℝ} {lx ux ly uy L U : ℚ}
    (hx : RationalBound x lx ux) (hy : RationalBound y ly uy)
    (hL : L ≤ lx+ly) (hU : ux+uy ≤ U) : RationalBound (x+y) L U := by
  have hL' : (L : ℝ) ≤ (lx : ℝ)+(ly : ℝ) := by exact_mod_cast hL
  have hU' : (ux : ℝ)+(uy : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem rationalBound_neg {x : ℝ} {l u L U : ℚ}
    (hx : RationalBound x l u) (hL : L ≤ -u) (hU : -l ≤ U) :
    RationalBound (-x) L U := by
  have hL' : (L : ℝ) ≤ -(u : ℝ) := by exact_mod_cast hL
  have hU' : -(l : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
  constructor <;> linarith [hx.1, hx.2]

theorem interval_linear_lower {a y ly uy L : ℝ} (hy : ly ≤ y ∧ y ≤ uy)
    (hl : L ≤ a*ly) (hu : L ≤ a*uy) : L ≤ a*y := by
  by_cases ha : 0 ≤ a
  · exact hl.trans (mul_le_mul_of_nonneg_left hy.1 ha)
  · exact hu.trans (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge ha))

theorem interval_linear_upper {a y ly uy U : ℝ} (hy : ly ≤ y ∧ y ≤ uy)
    (hl : a*ly ≤ U) (hu : a*uy ≤ U) : a*y ≤ U := by
  by_cases ha : 0 ≤ a
  · exact (mul_le_mul_of_nonneg_left hy.2 ha).trans hu
  · exact (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge ha)).trans hl

theorem rationalBound_mul {x y : ℝ} {lx ux ly uy L U : ℚ}
    (hx : RationalBound x lx ux) (hy : RationalBound y ly uy)
    (hL : L ≤ lx*ly ∧ L ≤ lx*uy ∧ L ≤ ux*ly ∧ L ≤ ux*uy)
    (hU : lx*ly ≤ U ∧ lx*uy ≤ U ∧ ux*ly ≤ U ∧ ux*uy ≤ U) :
    RationalBound (x*y) L U := by
  have hll : (L : ℝ) ≤ (lx : ℝ)*y := interval_linear_lower hy
    (by exact_mod_cast hL.1) (by exact_mod_cast hL.2.1)
  have hlu : (L : ℝ) ≤ (ux : ℝ)*y := interval_linear_lower hy
    (by exact_mod_cast hL.2.2.1) (by exact_mod_cast hL.2.2.2)
  have hul : (lx : ℝ)*y ≤ (U : ℝ) := interval_linear_upper hy
    (by exact_mod_cast hU.1) (by exact_mod_cast hU.2.1)
  have huu : (ux : ℝ)*y ≤ (U : ℝ) := interval_linear_upper hy
    (by exact_mod_cast hU.2.2.1) (by exact_mod_cast hU.2.2.2)
  by_cases hy0 : 0 ≤ y
  · exact ⟨hll.trans (mul_le_mul_of_nonneg_right hx.1 hy0),
      (mul_le_mul_of_nonneg_right hx.2 hy0).trans huu⟩
  · have hyn : y ≤ 0 := le_of_not_ge hy0
    exact ⟨hlu.trans (mul_le_mul_of_nonpos_right hx.2 hyn),
      (mul_le_mul_of_nonpos_right hx.1 hyn).trans hul⟩

theorem rationalBound_sqrt {x : ℝ} {l u L U : ℚ}
    (hx : RationalBound x l u) (hl : 0 ≤ l) (hL : 0 ≤ L ∧ L^2 ≤ l)
    (hU : 0 ≤ U ∧ u ≤ U^2) : RationalBound (Real.sqrt x) L U := by
  have hx0 : 0 ≤ x := (by exact_mod_cast hl : (0 : ℝ) ≤ (l : ℝ)).trans hx.1
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL.1
  have hL2 : (L : ℝ)^2 ≤ (l : ℝ) := by exact_mod_cast hL.2
  have hU0 : (0 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU.1
  have hU2 : (u : ℝ) ≤ (U : ℝ)^2 := by exact_mod_cast hU.2
  have hs := Real.sq_sqrt hx0
  have hs0 := Real.sqrt_nonneg x
  constructor <;> nlinarith [hx.1, hx.2]

theorem rationalBound_inv {x : ℝ} {l u L U : ℚ}
    (hx : RationalBound x l u) (hl : 0 < l) (hL : L ≤ 1/u) (hU : 1/l ≤ U) :
    RationalBound (1/x) L U := by
  have hl' : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hx0 : 0 < x := hl'.trans_le hx.1
  have hL' : (L : ℝ) ≤ 1/(u : ℝ) := by exact_mod_cast hL
  have hU' : 1/(l : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
  exact ⟨hL'.trans (one_div_le_one_div_of_le hx0 hx.2),
    (one_div_le_one_div_of_le hl' hx.1).trans hU'⟩

end
end CK.Certificate
