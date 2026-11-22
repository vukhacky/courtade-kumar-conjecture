module

public import CK.Functional.LogSobolev
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The sharp one-bit `L^p` to `L²` noise inequality for `1 ≤ p ≤ 2`.
All boundary values are obtained within closed intervals by continuity. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def symmetricPower (p t : ℝ) : ℝ := ((1+t)^p + (1-t)^p)/2

def bonamiRemainder (p t : ℝ) : ℝ := symmetricPower p t - 1 - p*(p-1)*t^2/2

def bonamiRemainderSlope (p t : ℝ) : ℝ :=
  p*((1+t)^(p-1)-(1-t)^(p-1))/2 - p*(p-1)*t

def bonamiRemainderCurvature (p t : ℝ) : ℝ :=
  p*(p-1)*((1+t)^(p-2)+(1-t)^(p-2)-2)/2

theorem inverse_symmetricPower_ge_one {q t : ℝ} (hq : q ≤ 0)
    (ht : t ∈ Ioo (-1 : ℝ) 1) : 2 ≤ (1+t)^q + (1-t)^q := by
  have hp : 0 < 1+t := by linarith [ht.1]
  have hm : 0 < 1-t := by linarith [ht.2]
  have hs : 0 < 1-t^2 := by nlinarith [ht.1,ht.2]
  have hprod : 1 ≤ (1+t)^q * (1-t)^q := by
    rw [← Real.mul_rpow hp.le hm.le, show (1+t)*(1-t) = 1-t^2 by ring]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs (by nlinarith [sq_nonneg t]) hq
  have hu := Real.rpow_pos_of_pos hp q
  have hv := Real.rpow_pos_of_pos hm q
  nlinarith [sq_nonneg ((1+t)^q-(1-t)^q)]

theorem hasDerivAt_bonamiRemainder {p t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (bonamiRemainder p) (bonamiRemainderSlope p t) t := by
  have hp := ((hasDerivAt_id t).const_add 1).rpow_const
    (p := p) (Or.inl (show 1+t ≠ 0 by linarith [ht.1]))
  have hm := ((hasDerivAt_id t).const_sub 1).rpow_const
    (p := p) (Or.inl (show 1-t ≠ 0 by linarith [ht.2]))
  have hd := (((hp.add hm).div_const 2).sub_const 1).sub
    (((hasDerivAt_pow 2 t).const_mul (p*(p-1))).div_const 2)
  apply hd.congr_deriv
  dsimp [bonamiRemainderSlope]
  ring

theorem hasDerivAt_bonamiRemainderSlope {p t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (bonamiRemainderSlope p) (bonamiRemainderCurvature p t) t := by
  have hp := ((hasDerivAt_id t).const_add 1).rpow_const
    (p := p-1) (Or.inl (show 1+t ≠ 0 by linarith [ht.1]))
  have hm := ((hasDerivAt_id t).const_sub 1).rpow_const
    (p := p-1) (Or.inl (show 1-t ≠ 0 by linarith [ht.2]))
  have hd := (((hp.sub hm).const_mul p).div_const 2).sub
    ((hasDerivAt_id t).const_mul (p*(p-1)))
  apply hd.congr_deriv
  dsimp [bonamiRemainderCurvature]
  rw [show p-1-1 = p-2 by ring]
  ring

theorem bonamiRemainder_convex {p : ℝ} (hp : p ∈ Icc (1 : ℝ) 2) :
    ConvexOn ℝ (Icc (-1 : ℝ) 1) (bonamiRemainder p) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (f' := bonamiRemainderSlope p) (f'' := bonamiRemainderCurvature p)
  · have hp0 : 0 ≤ p := by linarith [hp.1]
    unfold bonamiRemainder symmetricPower
    fun_prop
  · intro t ht
    exact (hasDerivAt_bonamiRemainder (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
  · intro t ht
    exact (hasDerivAt_bonamiRemainderSlope (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
  · intro t ht
    have h := inverse_symmetricPower_ge_one (show p-2 ≤ 0 by linarith [hp.2])
      (show t ∈ Ioo (-1 : ℝ) 1 by simpa only [interior_Icc] using ht)
    unfold bonamiRemainderCurvature
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith [hp.1]) (by linarith [hp.1]))
      (sub_nonneg.mpr h)) (by norm_num)

theorem bonamiRemainder_even (p t : ℝ) : bonamiRemainder p (-t) = bonamiRemainder p t := by
  unfold bonamiRemainder symmetricPower
  rw [show 1 + -t = 1-t by ring, show 1 - -t = 1+t by ring, neg_sq]
  ring

@[simp] theorem bonamiRemainder_zero (p : ℝ) : bonamiRemainder p 0 = 0 := by
  simp [bonamiRemainder, symmetricPower]

theorem symmetricPower_quadratic_lower {p t : ℝ} (hp : p ∈ Icc (1 : ℝ) 2)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    1+p*(p-1)*t^2/2 ≤ symmetricPower p t := by
  have hn : -t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h := (bonamiRemainder_convex hp).2 ht hn
    (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (0 : ℝ)≤1/2)
    (by norm_num : (1/2 : ℝ)+1/2=1)
  simp only [smul_eq_mul, bonamiRemainder_even] at h
  rw [show (1/2 : ℝ)*t+(1/2)*(-t)=0 by ring, bonamiRemainder_zero] at h
  unfold bonamiRemainder at h
  linarith

theorem bonami_normalized {p t : ℝ} (hp : p ∈ Icc (1 : ℝ) 2)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    (1+(p-1)*t^2)^(p/2) ≤ symmetricPower p t := by
  have h := rpow_one_add_le_one_add_mul_self
    (s := (p-1)*t^2) (by nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (sq_nonneg t)])
    (p := p/2) (by linarith [hp.1]) (by linarith [hp.2])
  have hq := symmetricPower_quadratic_lower hp ht
  nlinarith

/-- The one-bit inequality in homogeneous form for nonnegative entries. -/
theorem bonami_twoPoint {p a b : ℝ} (hp : p ∈ Icc (1 : ℝ) 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (((a+b)/2)^2 + (p-1)*((a-b)/2)^2)^(p/2) ≤ (a^p+b^p)/2 := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with hab | hab
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    have hp0 : p ≠ 0 := by linarith [hp.1]
    have hp2 : p/2 ≠ 0 := by linarith [hp.1]
    simp [ha0,hb0,Real.zero_rpow hp0,Real.zero_rpow hp2]
  let m := (a+b)/2
  let t := (a-b)/(a+b)
  have hm : 0 < m := by dsimp [m]; positivity
  have ht : t ∈ Icc (-1 : ℝ) 1 := pair_ratio_mem_Icc ha hb
  have h := mul_le_mul_of_nonneg_left (bonami_normalized hp ht) (Real.rpow_nonneg hm.le p)
  have hea : m*(1+t)=a := by dsimp [m,t]; field_simp; ring
  have heb : m*(1-t)=b := by dsimp [m,t]; field_simp; ring
  have hbase : 0 ≤ 1+(p-1)*t^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (sq_nonneg t)]
  have hexp : (m^2)^(p/2) = m^p := by
    rw [← Real.rpow_natCast m 2, ← Real.rpow_mul hm.le]
    congr 1
    ring
  have he : ((a+b)/2)^2+(p-1)*((a-b)/2)^2 = m^2*(1+(p-1)*t^2) := by
    dsimp [m,t]
    field_simp [ne_of_gt hab]
  rw [he, Real.mul_rpow (sq_nonneg m) hbase, hexp]
  have hra : m^p*(1+t)^p=a^p := by rw [← Real.mul_rpow hm.le (by linarith [ht.1]), hea]
  have hrb : m^p*(1-t)^p=b^p := by rw [← Real.mul_rpow hm.le (by linarith [ht.2]), heb]
  unfold symmetricPower at h
  nlinarith

end
end CK
