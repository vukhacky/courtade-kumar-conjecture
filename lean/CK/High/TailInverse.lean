module

public import CK.High.TailEntropy
public import CK.High.ProfileInverse

/-! Uniform lower estimates for the inverse profile in the analytic tail. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem tail_heightF_root {u a : ℝ} (hu : (8 : ℝ) ≤ u) (ha : 0 < a) :
    a*heightF (profileHeight (Real.tanh u) a)=heightF u := by
  have hr := tail_tanh_mem hu
  have hv := profileHeight_pos hr ha
  have htv := tanh_mem_Ioo_positive hv
  have h := profileHeight_root hr ha
  change Profile.meanEntropy (Real.tanh u)*Real.tanh (profileHeight (Real.tanh u) a)=
    Real.tanh u*a*Profile.meanEntropy (Real.tanh (profileHeight (Real.tanh u) a)) at h
  unfold heightF
  field_simp [hr.1.ne',htv.1.ne']
  nlinarith only [h]

theorem tail_log_heightF_root {u a : ℝ} (hu : (8 : ℝ) ≤ u) (ha : 0 < a) :
    Real.log a+Real.log (heightF (profileHeight (Real.tanh u) a))=Real.log (heightF u) := by
  rw [←Real.log_mul ha.ne' (heightF_pos (profileHeight_pos (tail_tanh_mem hu) ha)).ne',
    tail_heightF_root hu ha]

theorem height_log_affine_strictAnti {s c : ℝ} (hs : 0 ≤ s)
    (hrate : ∀ v, s < v → c < heightDecayRate v) :
    StrictAntiOn (fun v => Real.log (heightF v)+c*v) (Ioi s) := by
  have hd (v : ℝ) (hv : s < v) :
      HasDerivAt (fun v => Real.log (heightF v)+c*v) (-heightDecayRate v+c) v := by
    have h := (hasDerivAt_log_heightF (show 0 < v by linarith)).add ((hasDerivAt_id v).const_mul c)
    apply h.congr_deriv
    simp
  apply strictAntiOn_of_hasDerivWithinAt_neg (f' := fun v => -heightDecayRate v+c) (convex_Ioi _)
  · intro v hv
    exact (hd v hv).continuousAt.continuousWithinAt
  · intro v hv
    exact (hd v (by simpa using hv)).hasDerivWithinAt
  · intro v hv
    have h := hrate v (by simpa using hv)
    linarith

theorem tail_inverse_coarse {u a : ℝ} (hu : (8 : ℝ) ≤ u) (ha : a ∈ Ioo (0 : ℝ) 1) :
    u+Real.log a < profileHeight (Real.tanh u) a := by
  have hr := tail_tanh_mem hu
  have hv := profileHeight_pos hr ha.1
  have hvu := profileHeight_le_artanh hr ⟨ha.1.le,ha.2.le⟩
  rw [Real.artanh_tanh] at hvu
  have hne : profileHeight (Real.tanh u) a ≠ u := by
    intro he
    have h := tail_heightF_root hu ha.1
    rw [he] at h
    have hp := heightF_pos (by linarith : 0 < u)
    nlinarith only [h, mul_pos (sub_pos.mpr ha.2) hp]
  have hm := height_log_affine_strictAnti (s := 0) (c := 1) (by norm_num)
    (fun v hv => heightDecayRate_gt_one hv) hv (show 0 < u by linarith)
    (lt_of_le_of_ne hvu hne)
  have he := tail_log_heightF_root hu ha.1
  linarith only [hm,he]

theorem tail_inverse_strong {u a : ℝ} (hu : (8 : ℝ) ≤ u) (ha : a ∈ Ioo (0 : ℝ) 1)
    (hv : (4 : ℝ) < profileHeight (Real.tanh u) a) :
    u+(4/7)*Real.log a < profileHeight (Real.tanh u) a := by
  have hr := tail_tanh_mem hu
  have hvu := profileHeight_le_artanh hr ⟨ha.1.le,ha.2.le⟩
  rw [Real.artanh_tanh] at hvu
  have hne : profileHeight (Real.tanh u) a ≠ u := by
    intro he
    have h := tail_heightF_root hu ha.1
    rw [he] at h
    have hp := heightF_pos (by linarith : 0 < u)
    nlinarith only [h, mul_pos (sub_pos.mpr ha.2) hp]
  have hm := height_log_affine_strictAnti (s := 4) (c := 7/4) (by norm_num)
    (fun v hv => heightDecayRate_gt_seven_fourths hv.le) hv (show (4 : ℝ) < u by linarith)
    (lt_of_le_of_ne hvu hne)
  have he := tail_log_heightF_root hu ha.1
  linarith only [hm,he]

theorem tail_inverse_one_eighth {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    u-6/5 < profileHeight (Real.tanh u) (1/8) := by
  have hlog : -(21/10 : ℝ) < Real.log (1/8 : ℝ) := by
    have he : Real.log (1/8 : ℝ)= -3*Real.log 2 := by
      rw [show (1/8 : ℝ)=(2^3)⁻¹ by norm_num,Real.log_inv,Real.log_pow]
      ring
    rw [he]
    linarith only [Certificate.log_two_coarse_bounds.2]
  have hc := tail_inverse_coarse hu (by norm_num : (1/8 : ℝ) ∈ Ioo 0 1)
  have hs := tail_inverse_strong hu (by norm_num : (1/8 : ℝ) ∈ Ioo 0 1)
    (by linarith : (4 : ℝ) < profileHeight (Real.tanh u) (1/8))
  linarith only [hs,hlog]

theorem tailAlpha_mem {u : ℝ} (hu : (8 : ℝ) ≤ u) : tailAlpha u ∈ Ioo (0 : ℝ) 1 := by
  have he := tail_epsilon_bounds hu
  unfold tailAlpha
  constructor <;> linarith only [he.1,he.2]

theorem tail_inverse_alpha {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    u-profileHeight (Real.tanh u) (tailAlpha u) < (7/4)*Real.exp (-u) := by
  have ha := tailAlpha_mem hu
  have he := tail_epsilon_bounds hu
  have hd : 0 < 1-3*Real.exp (-u) := ha.1
  have hlog := Real.one_sub_inv_le_log_of_pos ha.1
  have hloglo : -(3*Real.exp (-u)/(1-3*Real.exp (-u))) ≤ Real.log (tailAlpha u) := by
    convert hlog using 1
    unfold tailAlpha
    field_simp [hd.ne']
    ring
  have hfrac : 3*Real.exp (-u)/(1-3*Real.exp (-u)) < 1 := by
    apply (div_lt_one hd).mpr
    linarith only [he.2]
  have hc := tail_inverse_coarse hu ha
  have hs := tail_inverse_strong hu ha (by linarith : (4 : ℝ) < profileHeight (Real.tanh u) (tailAlpha u))
  have hfinal : (4/7)*(3*Real.exp (-u)/(1-3*Real.exp (-u))) < (7/4)*Real.exp (-u) := by
    apply (mul_lt_mul_iff_left₀ hd).mp
    have hid : (4/7)*(3*Real.exp (-u)/(1-3*Real.exp (-u)))*(1-3*Real.exp (-u))=(12/7)*Real.exp (-u) := by
      field_simp [hd.ne']
      ring
    rw [hid]
    nlinarith only [mul_pos he.1 (show 0 < (1/84 : ℝ)-(21/4)*Real.exp (-u) by linarith only [he.2])]
  linarith only [hs,hloglo,hfinal]

end
end CK
