module

public import CK.High.Height
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The exact arcsine remainder. Its derivative is a square, and its
curvature is positive away from zero. The zero extension is justified by
an explicit squeeze, before using convexity on the closed half-line. -/

@[expose] public section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace CK
noncomputable section

theorem arctan_lt_self_pos {s : ℝ} (hs : 0 < s) : Real.arctan s < s := by
  let F : ℝ → ℝ := fun s => s-Real.arctan s
  have hd (x : ℝ) : HasDerivAt F (x^2/(1+x^2)) x := by
    apply ((hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)).congr_deriv
    field_simp
    ring
  have hm : StrictMonoOn F (Ici (0 : ℝ)) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fun x => x^2/(1+x^2)) (convex_Ici _)
    · intro x _
      exact (hd x).continuousAt.continuousWithinAt
    · intro x _
      exact (hd x).hasDerivWithinAt
    · intro x hx
      have hp : 0 < x := by simpa using hx
      exact div_pos (sq_pos_of_pos hp) (by positivity)
  have h := hm (by simp : (0 : ℝ) ∈ Ici (0 : ℝ)) hs.le hs
  simpa only [F,Real.arctan_zero,sub_self,sub_pos] using h

theorem self_div_one_add_sq_lt_arctan {s : ℝ} (hs : 0 < s) :
    s/(1+s^2) < Real.arctan s := by
  let F : ℝ → ℝ := fun s => Real.arctan s-s/(1+s^2)
  have hd (x : ℝ) : HasDerivAt F (2*x^2/(1+x^2)^2) x := by
    have h := (Real.hasDerivAt_arctan x).sub
      ((hasDerivAt_id x).div ((hasDerivAt_pow 2 x).const_add 1) (by positivity))
    apply h.congr_deriv
    norm_num
    field_simp
    ring
  have hm : StrictMonoOn F (Ici (0 : ℝ)) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fun x => 2*x^2/(1+x^2)^2) (convex_Ici _)
    · intro x _
      exact (hd x).continuousAt.continuousWithinAt
    · intro x _
      exact (hd x).hasDerivWithinAt
    · intro x hx
      have hp : 0 < x := by simpa using hx
      exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hp)) (by positivity)
  have h := hm (by simp : (0 : ℝ) ∈ Ici (0 : ℝ)) hs.le hs
  simpa only [F,Real.arctan_zero,zero_div,sub_self,sub_pos] using h

theorem arctan_le_self_nonneg {s : ℝ} (hs : 0 ≤ s) : Real.arctan s ≤ s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  · exact (arctan_lt_self_pos hs).le

def arctanRatio (s : ℝ) : ℝ := Real.arctan s/s

theorem hasDerivAt_arctanRatio {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt arctanRatio ((s/(1+s^2)-Real.arctan s)/s^2) s := by
  apply ((Real.hasDerivAt_arctan s).div (hasDerivAt_id s) hs).congr_deriv
  simp only [id_eq,mul_one]
  ring

theorem arctanRatio_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ arctanRatio s :=
  div_nonneg (Real.arctan_nonneg.mpr hs) hs

theorem arctanRatio_lt_one {s : ℝ} (hs : 0 < s) : arctanRatio s < 1 := by
  exact (div_lt_one hs).mpr (arctan_lt_self_pos hs)

theorem arctanRatio_strictAnti : StrictAntiOn arctanRatio (Ioi (0 : ℝ)) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg
    (f' := fun s => (s/(1+s^2)-Real.arctan s)/s^2) (convex_Ioi _)
  · intro s hs
    exact (hasDerivAt_arctanRatio (ne_of_gt hs)).continuousAt.continuousWithinAt
  · intro s hs
    have h : 0 < s := by simpa using hs
    exact (hasDerivAt_arctanRatio h.ne').hasDerivWithinAt
  · intro s hs
    have h : 0 < s := by simpa using hs
    exact div_neg_of_neg_of_pos (sub_neg.mpr (self_div_one_add_sq_lt_arctan h)) (sq_pos_of_pos h)

def arcsineRemainder (v : ℝ) : ℝ :=
  v-Real.arcsin (Real.tanh v)^2/Real.tanh v

def arcsineRemainderSlope (v : ℝ) : ℝ := (1-arctanRatio (Real.sinh v))^2

def arcsineRemainderCurvature (v : ℝ) : ℝ :=
  2*(1-arctanRatio (Real.sinh v))*
    ((Real.arctan (Real.sinh v)-Real.sinh v/(1+Real.sinh v^2))/Real.sinh v^2)*Real.cosh v

@[simp] theorem arcsineRemainder_zero : arcsineRemainder 0=0 := by simp [arcsineRemainder]

theorem arcsin_tanh_eq_arctan_sinh (v : ℝ) :
    Real.arcsin (Real.tanh v) = Real.arctan (Real.sinh v) := by
  rw [Real.arctan_eq_arcsin,←Real.cosh_sq',Real.sqrt_sq (Real.cosh_pos v).le,
    Real.tanh_eq_sinh_div_cosh]

theorem arcsineRemainder_eq (v : ℝ) :
    arcsineRemainder v = v-Real.arctan (Real.sinh v)^2*Real.cosh v/Real.sinh v := by
  unfold arcsineRemainder
  rw [arcsin_tanh_eq_arctan_sinh,Real.tanh_eq_sinh_div_cosh,div_div_eq_mul_div]

theorem hasDerivAt_arcsineRemainder {v : ℝ} (hv : 0 < v) :
    HasDerivAt arcsineRemainder (arcsineRemainderSlope v) v := by
  have hs : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hv
  have h := (hasDerivAt_id v).sub
    (((((Real.hasDerivAt_arctan (Real.sinh v)).comp v (Real.hasDerivAt_sinh v)).pow 2).mul
      (Real.hasDerivAt_cosh v)).div (Real.hasDerivAt_sinh v) hs.ne')
  rw [show arcsineRemainder = fun v => v-Real.arctan (Real.sinh v)^2*Real.cosh v/Real.sinh v from
    funext arcsineRemainder_eq]
  apply h.congr_deriv
  unfold arcsineRemainderSlope arctanRatio
  norm_num
  field_simp
  ring_nf
  rw [Real.cosh_sq]
  ring

theorem hasDerivAt_arcsineRemainderSlope {v : ℝ} (hv : 0 < v) :
    HasDerivAt arcsineRemainderSlope (arcsineRemainderCurvature v) v := by
  have hs : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hv
  have h := (((hasDerivAt_arctanRatio hs.ne').comp v (Real.hasDerivAt_sinh v)).const_sub 1).pow 2
  apply h.congr_deriv
  unfold arcsineRemainderCurvature
  norm_num
  ring

theorem arcsineRemainderSlope_pos {v : ℝ} (hv : 0 < v) : 0 < arcsineRemainderSlope v :=
  sq_pos_of_pos (sub_pos.mpr (arctanRatio_lt_one (Real.sinh_pos_iff.mpr hv)))

theorem arcsineRemainderCurvature_pos {v : ℝ} (hv : 0 < v) :
    0 < arcsineRemainderCurvature v := by
  have hs : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hv
  unfold arcsineRemainderCurvature
  exact mul_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr (arctanRatio_lt_one hs)))
    (div_pos (sub_pos.mpr (self_div_one_add_sq_lt_arctan hs)) (sq_pos_of_pos hs))) (Real.cosh_pos v)

theorem arcsineRemainder_bounds {v : ℝ} (hv : 0 ≤ v) :
    v-Real.sinh v*Real.cosh v ≤ arcsineRemainder v ∧ arcsineRemainder v ≤ v := by
  rcases hv.eq_or_lt with rfl | hv
  · simp
  have hs : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hv
  have hA := arctan_le_self_nonneg hs.le
  have hA0 : 0 ≤ Real.arctan (Real.sinh v) := Real.arctan_nonneg.mpr hs.le
  have hsq : Real.arctan (Real.sinh v)^2 ≤ Real.sinh v^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hsq (Real.cosh_pos v).le
  have hdiv : Real.arctan (Real.sinh v)^2*Real.cosh v/Real.sinh v ≤ Real.sinh v*Real.cosh v :=
    (div_le_iff₀ hs).mpr (by nlinarith only [hh])
  have hnonneg : 0 ≤ Real.arctan (Real.sinh v)^2*Real.cosh v/Real.sinh v := by positivity
  rw [arcsineRemainder_eq]
  constructor <;> linarith

theorem continuousWithinAt_arcsineRemainder_zero :
    ContinuousWithinAt arcsineRemainder (Ici (0 : ℝ)) 0 := by
  have hlo : Tendsto (fun v : ℝ => v-Real.sinh v*Real.cosh v) (𝓝[Ici (0 : ℝ)] 0) (𝓝 0) := by
    have hc : Continuous (fun v : ℝ => v-Real.sinh v*Real.cosh v) := by fun_prop
    have h : ContinuousWithinAt (fun v : ℝ => v-Real.sinh v*Real.cosh v) (Ici (0 : ℝ)) 0 :=
      hc.continuousWithinAt
    simpa only [ContinuousWithinAt,Real.sinh_zero,zero_mul,sub_zero] using h
  have hhi : Tendsto (fun v : ℝ => v) (𝓝[Ici (0 : ℝ)] 0) (𝓝 0) :=
    continuousWithinAt_id
  rw [ContinuousWithinAt,arcsineRemainder_zero]
  exact hlo.squeeze' hhi
    (by filter_upwards [self_mem_nhdsWithin] with v hv; exact (arcsineRemainder_bounds hv).1)
    (by filter_upwards [self_mem_nhdsWithin] with v hv; exact (arcsineRemainder_bounds hv).2)

theorem continuousOn_arcsineRemainder : ContinuousOn arcsineRemainder (Ici (0 : ℝ)) := by
  intro v hv
  rcases (show 0 ≤ v from hv).eq_or_lt with rfl | hv
  · exact continuousWithinAt_arcsineRemainder_zero
  · exact (hasDerivAt_arcsineRemainder hv).continuousAt.continuousWithinAt

theorem arcsineRemainder_strictMono : StrictMonoOn arcsineRemainder (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (f' := arcsineRemainderSlope) (convex_Ici _)
    continuousOn_arcsineRemainder
  · intro v hv
    exact (hasDerivAt_arcsineRemainder (by simpa using hv)).hasDerivWithinAt
  · intro v hv
    exact arcsineRemainderSlope_pos (by simpa using hv)

theorem arcsineRemainder_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ arcsineRemainder v := by
  simpa only [arcsineRemainder_zero] using arcsineRemainder_strictMono.monotoneOn (by simp) hv hv

theorem arcsineRemainder_convex : ConvexOn ℝ (Ici (0 : ℝ)) arcsineRemainder := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := arcsineRemainderSlope)
    (f'' := arcsineRemainderCurvature) (convex_Ici _) continuousOn_arcsineRemainder
  · intro v hv
    exact (hasDerivAt_arcsineRemainder (by simpa using hv)).hasDerivWithinAt
  · intro v hv
    exact (hasDerivAt_arcsineRemainderSlope (by simpa using hv)).hasDerivWithinAt
  · intro v hv
    exact (arcsineRemainderCurvature_pos (by simpa using hv)).le

theorem arcsineRemainder_ratio_mono {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) :
    arcsineRemainder v/v ≤ arcsineRemainder w/w := by
  have hw : 0 < w := hv.trans_le hvw
  have ha : 0 ≤ v/w := div_nonneg hv.le hw.le
  have hb : 0 ≤ 1-v/w := by
    exact sub_nonneg.mpr ((div_le_one hw).mpr hvw)
  have h := arcsineRemainder_convex.2 (show w ∈ Ici (0 : ℝ) from hw.le)
    (by simp : (0 : ℝ) ∈ Ici (0 : ℝ)) ha hb (by ring : v/w+(1-v/w)=1)
  simp only [smul_eq_mul,mul_zero,add_zero,arcsineRemainder_zero] at h
  rw [div_mul_cancel₀ _ hw.ne'] at h
  apply (div_le_div_iff₀ hv hw).mpr
  have hm := mul_le_mul_of_nonneg_right h hw.le
  field_simp at hm
  nlinarith only [hm]

theorem arcsineRemainder_ge_linear_after {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) :
    (arcsineRemainder v/v)*w ≤ arcsineRemainder w := by
  have h := arcsineRemainder_ratio_mono hv hvw
  exact (le_div_iff₀ (hv.trans_le hvw)).mp h

theorem arcsineRemainder_strictConvex : StrictConvexOn ℝ (Ici (0 : ℝ)) arcsineRemainder := by
  have hm : StrictMonoOn arcsineRemainderSlope (Ioi (0 : ℝ)) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (f' := arcsineRemainderCurvature) (convex_Ioi _)
    · intro v hv
      exact (hasDerivAt_arcsineRemainderSlope hv).continuousAt.continuousWithinAt
    · intro v hv
      exact (hasDerivAt_arcsineRemainderSlope (by simpa using hv)).hasDerivWithinAt
    · intro v hv
      exact arcsineRemainderCurvature_pos (by simpa using hv)
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici _) continuousOn_arcsineRemainder
  intro v hv w hw hvw
  have hv0 : 0 < v := by simpa using hv
  have hw0 : 0 < w := by simpa using hw
  rw [(hasDerivAt_arcsineRemainder hv0).deriv,(hasDerivAt_arcsineRemainder hw0).deriv]
  exact hm hv0 hw0 hvw

end
end CK
