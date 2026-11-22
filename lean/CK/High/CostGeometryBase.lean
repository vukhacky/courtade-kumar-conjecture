module

public import CK.Profile.Elasticity
public import CK.High.Height
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The height profile F(v)=H(tanh v)/tanh v and convex reciprocal powers.
All derivatives are on the positive height domain. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def heightF (v : ℝ) : ℝ := Profile.meanEntropy (Real.tanh v)/Real.tanh v

theorem tanh_mem_Ioo_positive {v : ℝ} (hv : 0 < v) :
    Real.tanh v ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨?_,Real.tanh_lt_one v⟩
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hv) (Real.cosh_pos v)

theorem hasDerivAt_tanh_squared (v : ℝ) :
    HasDerivAt Real.tanh (1-Real.tanh v^2) v := by
  have h := (Real.hasDerivAt_sinh v).div (Real.hasDerivAt_cosh v) (ne_of_gt (Real.cosh_pos v))
  have hfun : (fun x => Real.sinh x/Real.cosh x)=Real.tanh := by
    funext x
    exact (Real.tanh_eq_sinh_div_cosh x).symm
  change HasDerivAt (fun x => Real.sinh x/Real.cosh x) _ v at h
  rw [hfun] at h
  apply h.congr_deriv
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos v)]

theorem heightF_pos {v : ℝ} (hv : 0 < v) : 0 < heightF v := by
  have ht := tanh_mem_Ioo_positive hv
  exact div_pos (Profile.meanEntropy_pos ⟨by linarith [ht.1],ht.2⟩) ht.1

theorem scaled_heightF_eq (v : ℝ) :
    v*heightF v=Profile.scaledProfile (Real.tanh v) := by
  unfold heightF Profile.scaledProfile
  rw [phiSlope_eq_artanh ⟨Real.neg_one_lt_tanh v,Real.tanh_lt_one v⟩,Real.artanh_tanh]
  ring

theorem hasDerivAt_scaled_heightF {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun z => z*heightF z)
      (v*heightF v*Profile.logScaledSlope (Real.tanh v)) v := by
  have ht := tanh_mem_Ioo_positive hv
  have hg := Profile.gap_pos ⟨by linarith [ht.1],ht.2⟩
  have h := (Profile.hasDerivAt_scaledProfile ht).comp v (hasDerivAt_tanh_squared v)
  have hfun : (fun z => Profile.scaledProfile (Real.tanh z))=(fun z => z*heightF z) :=
    funext (fun z => (scaled_heightF_eq z).symm)
  change HasDerivAt (fun z => Profile.scaledProfile (Real.tanh z)) _ v at h
  rw [hfun] at h
  apply h.congr_deriv
  rw [←scaled_heightF_eq v]
  field_simp [ne_of_gt hg]

theorem hasDerivAt_log_scaled_heightF {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun z => Real.log (z*heightF z))
      (Profile.logScaledSlope (Real.tanh v)) v := by
  have hp := mul_pos hv (heightF_pos hv)
  have h := (hasDerivAt_scaled_heightF hv).log (ne_of_gt hp)
  apply h.congr_deriv
  field_simp [ne_of_gt hv,ne_of_gt (heightF_pos hv)]

theorem log_scaled_heightF_concave :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun v => Real.log (v*heightF v)) := by
  let D := fun v : ℝ => Profile.logScaledSlope (Real.tanh v)
  let E := fun v : ℝ =>
    (-1/((1-Real.tanh v^2)*phiSlope (Real.tanh v)^2)+1/Real.tanh v^2+
      (Profile.profileAux (Real.tanh v)^2-phiSlope (Real.tanh v)^2-
        Profile.meanEntropy (Real.tanh v))/Profile.meanEntropy (Real.tanh v)^2)*
      (1-Real.tanh v^2)
  have hd (v : ℝ) (hv : 0 < v) : HasDerivAt D (E v) v :=
    (Profile.hasDerivAt_logScaledSlope (tanh_mem_Ioo_positive hv)).comp v (hasDerivAt_tanh_squared v)
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi 0)
    (fun v hv => (hasDerivAt_log_scaled_heightF hv).continuousAt.continuousWithinAt)
    (f' := D) (f'' := E)
  · intro v hv
    exact (hasDerivAt_log_scaled_heightF (by simpa using hv)).hasDerivWithinAt
  · intro v hv
    exact (hd v (by simpa using hv)).hasDerivWithinAt
  · intro v hv
    have hv' : 0 < v := by simpa using hv
    have ht := tanh_mem_Ioo_positive hv'
    exact (mul_neg_of_neg_of_pos (Profile.logScaledSlope_derivative_neg ht)
      (Profile.gap_pos ⟨by linarith [ht.1],ht.2⟩)).le

def reciprocalHeightPower (r v : ℝ) : ℝ := 1/(v*(heightF v)^r)

theorem reciprocalHeightPower_exp {r v : ℝ} (hv : 0 < v) :
    reciprocalHeightPower r v =
      Real.exp (-(1-r)*Real.log v-r*Real.log (v*heightF v)) := by
  have hF := heightF_pos hv
  have harg : -(1-r)*Real.log v-r*Real.log (v*heightF v)=
      -(Real.log v+Real.log (heightF v)*r) := by
    rw [Real.log_mul (ne_of_gt hv) (ne_of_gt hF)]
    ring
  rw [harg,Real.exp_neg,Real.exp_add,Real.exp_log hv,←Real.rpow_def_of_pos hF]
  simp only [reciprocalHeightPower,one_div]

theorem reciprocalHeightPower_convex {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (reciprocalHeightPower r) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy α β hα hβ hsum
  have hz : 0 < α*x+β*y := by
    have hm := lt_min hx hy
    have h₁ := mul_le_mul_of_nonneg_left (min_le_left x y) hα
    have h₂ := mul_le_mul_of_nonneg_left (min_le_right x y) hβ
    nlinarith only [hm,h₁,h₂,congrArg (fun z : ℝ => z*min x y) hsum]
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 hx hy hα hβ hsum
  have hF := log_scaled_heightF_concave.2 hx hy hα hβ hsum
  simp only [smul_eq_mul] at hlog hF ⊢
  have h₁ := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hr.2)
  have h₂ := mul_le_mul_of_nonneg_left hF hr.1
  have hL : -(1-r)*Real.log (α*x+β*y)-r*Real.log ((α*x+β*y)*heightF (α*x+β*y)) ≤
      α*(-(1-r)*Real.log x-r*Real.log (x*heightF x))+
      β*(-(1-r)*Real.log y-r*Real.log (y*heightF y)) := by nlinarith only [h₁,h₂]
  have he := convexOn_exp.2 (mem_univ (-(1-r)*Real.log x-r*Real.log (x*heightF x)))
    (mem_univ (-(1-r)*Real.log y-r*Real.log (y*heightF y))) hα hβ hsum
  simp only [smul_eq_mul] at he
  rw [reciprocalHeightPower_exp hz,reciprocalHeightPower_exp hx,reciprocalHeightPower_exp hy]
  exact (Real.exp_le_exp.mpr hL).trans he

end
end CK
