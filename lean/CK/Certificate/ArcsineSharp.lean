module

public import CK.Certificate.ArcsineBounds

/-! The exact sharp-constant arcsine error inequality needed by the CK high
branch. Interior points use a finite certified polynomial. The two endpoint
neighborhoods use analytic entropy and trigonometric bounds. -/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace CK.Certificate
noncomputable section

theorem arcsine_error_interior {t : ℝ} (ht : t ∈ Icc (0:ℝ) (49/50)) :
    (Real.arcsin t-(Real.pi/2)*t)^2 ≤ arcsineSharpConstant*CK.entropyRemainder t := by
  let P : ℝ := ArcsineData.tail (t^2)
  let Q : ℝ := ArcsineData.entropyTail (t^2)
  let e : ℝ := Real.pi/2-1
  have ht1 : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,by linarith [ht.2]⟩
  have hx : t^2 ∈ Icc (0:ℝ) ((49/50:ℝ)^2) :=
    ⟨sq_nonneg _,pow_le_pow_left₀ ht.1 ht.2 2⟩
  have hx1 : t^2 ∈ Icc (0:ℝ) 1 := ⟨sq_nonneg _,by nlinarith [hx.2]⟩
  have hP : 0 ≤ P := ArcsineData.tail_nonneg hx1
  have hQ : 0 ≤ Q := ArcsineData.entropyTail_nonneg hx1
  have he : (57/100:ℝ) ≤ e := by dsimp [e]; linarith [Real.pi_gt_d2]
  have hpoly := ArcsineData.interior_polynomial_nonneg hx
  change 0 ≤ 2*(57/100:ℝ)*P-t^2*P^2-(12/7)*Q at hpoly
  have h1 := mul_le_mul_of_nonneg_right he hP
  have h2 := mul_le_mul_of_nonneg_right arcsineSharpConstant_bounds.2.le hQ
  have hactual : 0 ≤ 2*e*P-t^2*P^2-arcsineSharpConstant*Q := by
    nlinarith only [hpoly,h1,h2]
  have hmul := mul_nonneg (pow_nonneg ht.1 4) hactual
  have hprim := arcPrimitive_le_arcsin ht1
  rw [ArcsineData.primitive_eq] at hprim
  change t+t^3*P ≤ Real.arcsin t at hprim
  have herr0 : 0 ≤ (Real.pi/2)*t-Real.arcsin t := sub_nonneg.mpr (arcsin_le_chord ht1)
  have herr : (Real.pi/2)*t-Real.arcsin t ≤ e*t-t^3*P := by
    dsimp [e]
    nlinarith only [hprim]
  have hsq := pow_le_pow_left₀ herr0 herr 2
  have hphi := phi_upper_arcsine_interior ht
  change CK.phi t ≤ t^2/2+t^4*Q at hphi
  have hid := congrArg (fun z : ℝ => z*t^2) arcsineSharpConstant_identity
  change arcsineSharpConstant*(Real.log 2-1/2)*t^2=e^2*t^2 at hid
  calc
    (Real.arcsin t-(Real.pi/2)*t)^2 = ((Real.pi/2)*t-Real.arcsin t)^2 := by ring
    _ ≤ (e*t-t^3*P)^2 := hsq
    _ ≤ e^2*t^2-arcsineSharpConstant*t^4*Q := by nlinarith only [hmul]
    _ = arcsineSharpConstant*(t^2*Real.log 2-(t^2/2+t^4*Q)) := by nlinarith only [hid]
    _ ≤ arcsineSharpConstant*(t^2*Real.log 2-CK.phi t) :=
      mul_le_mul_of_nonneg_left (by linarith only [hphi]) arcsineSharpConstant_pos.le
    _ = arcsineSharpConstant*CK.entropyRemainder t := rfl

theorem arcsine_error_endpoint {t : ℝ} (ht : t ∈ Icc (49/50:ℝ) 1) :
    (Real.arcsin t-(Real.pi/2)*t)^2 ≤ arcsineSharpConstant*CK.entropyRemainder t := by
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · rw [heq,Real.arcsin_one,CK.entropyRemainder_one]
    norm_num
  let p : ℝ := (1-t)/2
  have ht0 : 0 < t := by linarith [ht.1]
  have hp : p ∈ Ioc (0:ℝ) (1/100) := by
    dsimp [p]
    constructor <;> linarith [ht.1]
  have hlog := Real.strictMonoOn_log.monotoneOn (show p ∈ Ioi (0:ℝ) from hp.1)
    (by norm_num : (1/100:ℝ) ∈ Ioi 0) hp.2
  have hlogid : Real.log (1/100:ℝ) = -Real.log (100:ℝ) := by
    rw [show (1/100:ℝ)=(100:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [hlogid] at hlog
  have hloglower : (23/5:ℝ) ≤ -Real.log p := by
    linarith [AndLogs.log_hundred_bounds.1]
  have hHb := CK.binEntropy_lower_log
    (show p ∈ Ico (0:ℝ) 1 from ⟨hp.1.le,by linarith [hp.2]⟩)
  have hHb' : p*(23/5+99/100:ℝ) ≤ Real.binEntropy p := by
    have hm := mul_le_mul_of_nonneg_left
      (show (23/5+99/100:ℝ) ≤ -Real.log p+1-p by linarith [hp.2]) hp.1.le
    exact hm.trans hHb
  have hH := CK.signEntropy_eq_log_two_sub_phi t
  change Real.binEntropy p=Real.log 2-CK.phi t at hH
  have htid : 1-t^2=4*p*(1-p) := by dsimp [p]; ring
  have hPsi : CK.entropyRemainder t = Real.binEntropy p-4*p*(1-p)*Real.log 2 := by
    unfold CK.entropyRemainder
    nlinarith only [hH,congrArg (fun z : ℝ => z*Real.log 2) htid]
  have hfac : 4*p*(1-p) ≤ 4*p := by nlinarith only [sq_nonneg p]
  have hl0 : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  have hcorr := (mul_le_mul_of_nonneg_right hfac hl0).trans
    (mul_le_mul_of_nonneg_left log_two_coarse_bounds.2 (by positivity : 0 ≤ 4*p))
  have hPsiLower : (14/5:ℝ)*p ≤ CK.entropyRemainder t := by
    rw [hPsi]
    nlinarith only [hHb',hcorr,hp.1]
  have ht1 : t ∈ Icc (0:ℝ) 1 := ⟨ht0.le,ht.2⟩
  have herr0 : 0 ≤ (Real.pi/2)*t-Real.arcsin t := sub_nonneg.mpr (arcsin_le_chord ht1)
  have herrcos : (Real.pi/2)*t-Real.arcsin t ≤ Real.arccos t := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    nlinarith only [Real.pi_pos,ht.2]
  have htan := Real.le_tan (Real.arccos_nonneg t) (Real.arccos_lt_pi_div_two.mpr ht0)
  rw [Real.tan_arccos] at htan
  have hsq := pow_le_pow_left₀ herr0 (herrcos.trans htan) 2
  rw [div_pow,Real.sq_sqrt (by nlinarith [ht0,ht.2] : 0 ≤ 1-t^2)] at hsq
  have hprod := (le_div_iff₀ (sq_pos_of_pos ht0)).mp hsq
  have ht2 : (49/50:ℝ)^2 ≤ t^2 := pow_le_pow_left₀ (by norm_num) ht.1 2
  have hscale := mul_le_mul_of_nonneg_left ht2 (sq_nonneg ((Real.pi/2)*t-Real.arcsin t))
  have herr : ((Real.pi/2)*t-Real.arcsin t)^2 ≤ (21/5:ℝ)*p := by
    nlinarith only [hprod,hscale,htid,hp.1,sq_nonneg p]
  calc
    (Real.arcsin t-(Real.pi/2)*t)^2 = ((Real.pi/2)*t-Real.arcsin t)^2 := by ring
    _ ≤ (21/5:ℝ)*p := herr
    _ ≤ (8/5:ℝ)*((14/5:ℝ)*p) := by nlinarith only [hp.1]
    _ ≤ arcsineSharpConstant*((14/5:ℝ)*p) :=
      mul_le_mul_of_nonneg_right arcsineSharpConstant_bounds.1.le (by positivity)
    _ ≤ arcsineSharpConstant*CK.entropyRemainder t :=
      mul_le_mul_of_nonneg_left hPsiLower arcsineSharpConstant_pos.le

theorem arcsine_error_sharp {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    (Real.arcsin t-(Real.pi/2)*t)^2 ≤ arcsineSharpConstant*CK.entropyRemainder t := by
  have hpos (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      (Real.arcsin x-(Real.pi/2)*x)^2 ≤ arcsineSharpConstant*CK.entropyRemainder x := by
    rcases le_total x (49/50:ℝ) with h | h
    · exact arcsine_error_interior ⟨hx.1,h⟩
    · exact arcsine_error_endpoint ⟨h,hx.2⟩
  rcases le_total 0 t with hp | hn
  · exact hpos t ⟨hp,ht.2⟩
  · have h := hpos (-t) ⟨by linarith,by linarith [ht.1]⟩
    rw [Real.arcsin_neg,CK.entropyRemainder_neg] at h
    convert h using 1 <;> ring

theorem arcsine_error_average {n : ℕ} (g : CK.Cube n → ℝ)
    (hg : ∀ x, g x ∈ Icc (-1:ℝ) 1) :
    CK.avg (fun x => (Real.arcsin (g x)-(Real.pi/2)*g x)^2) ≤
      arcsineSharpConstant*CK.entropyRemainderMean g := by
  have h := CK.avg_mono (fun x => arcsine_error_sharp (hg x))
  simpa only [CK.avg_smul,CK.entropyRemainderMean] using h

end
end CK.Certificate
