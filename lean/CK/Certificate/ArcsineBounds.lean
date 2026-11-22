module

public import CK.Certificate.ArcsineData
public import CK.High.SpectralTransfer
public import CK.High.BinaryBounds
public import CK.Certificate.AndRationalLogs
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! Analytic preliminaries for the sharp arcsine error bound, using finite polynomial certificates with the manuscript constant. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Certificate
noncomputable section

def arcsineSharpConstant : ℝ := (Real.pi/2-1)^2/(Real.log 2-1/2)

theorem arcsineSharpConstant_bounds :
    (8/5:ℝ) < arcsineSharpConstant ∧ arcsineSharpConstant < 12/7 := by
  have hl := log_two_coarse_bounds
  have hπl := Real.pi_gt_d2
  have hπu := Real.pi_lt_d4
  have hd : 0 < Real.log 2-1/2 := by linarith [hl.1]
  have he : (57/100:ℝ) < Real.pi/2-1 := by linarith
  have he' : Real.pi/2-1 < (5708/10000:ℝ) := by linarith
  have hs0 : (57/100:ℝ)^2 < (Real.pi/2-1)^2 := by nlinarith
  have hs1 : (Real.pi/2-1)^2 < (5708/10000:ℝ)^2 := by nlinarith
  unfold arcsineSharpConstant
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [hl.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [hl.1]

theorem arcsineSharpConstant_pos : 0 < arcsineSharpConstant :=
  lt_trans (by norm_num) arcsineSharpConstant_bounds.1

theorem arcsineSharpConstant_identity :
    arcsineSharpConstant*(Real.log 2-1/2)=(Real.pi/2-1)^2 := by
  unfold arcsineSharpConstant
  exact div_mul_cancel₀ _ (by linarith [log_two_coarse_bounds.1])

theorem arcsin_le_chord {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    Real.arcsin t ≤ (Real.pi/2)*t := by
  apply (Real.arcsin_le_iff_le_sin
    (show t ∈ Icc (-1:ℝ) 1 from ⟨by linarith [ht.1],ht.2⟩) ?_).2
  · exact Real.le_sin_mul ht.1 ht.2
  · constructor <;> nlinarith [Real.pi_pos,ht.1,ht.2]

theorem arcSlope_le_inverse_sqrt {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    ArcsineData.slope x ≤ 1/Real.sqrt (1-x) := by
  have hs : 0 < Real.sqrt (1-x) := Real.sqrt_pos.2 (by linarith [hx.2])
  have hss := Real.sq_sqrt (by linarith [hx.2] : 0 ≤ 1-x)
  have hb := ArcsineData.slope_squared_bound ⟨hx.1,hx.2.le⟩
  have hp : (ArcsineData.slope x*Real.sqrt (1-x))^2 ≤ 1 := by
    rw [mul_pow,hss]
    nlinarith only [hb]
  apply (le_div_iff₀ hs).2
  nlinarith only [hp]

theorem arcPrimitive_le_arcsin {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ArcsineData.primitive t ≤ Real.arcsin t := by
  have hm : MonotoneOn (fun x => Real.arcsin x-ArcsineData.primitive x) (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun x => 1/Real.sqrt (1-x^2)-ArcsineData.slope (x^2)) (convex_Icc _ _)
    · exact (Real.continuous_arcsin.sub (Dense.continuous_eval _)).continuousOn
    · intro x hx
      have hx' : x ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using hx
      exact ((Real.hasDerivAt_arcsin (by linarith [hx'.1]) (ne_of_lt hx'.2)).sub
        (ArcsineData.hasDerivAt_primitive x)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using hx
      exact sub_nonneg.mpr (arcSlope_le_inverse_sqrt
        ⟨sq_nonneg _,by nlinarith [hx'.1,hx'.2]⟩)
  have h := hm (by norm_num : (0:ℝ) ∈ Icc 0 1) ht ht.1
  simp only [Real.arcsin_zero,ArcsineData.primitive_eq,zero_pow (by decide : 3 ≠ 0),
    zero_mul,add_zero,sub_self] at h
  rw [ArcsineData.primitive_eq]
  linarith

theorem phi_upper_arcsine_interior {t : ℝ} (ht : t ∈ Icc (0:ℝ) (49/50)) :
    CK.phi t ≤ t^2/2+t^4*ArcsineData.entropyTail (t^2) := by
  have h := CK.phi_le_phiTaylor_bound 32 (by norm_num : (0:ℝ) ≤ 49/50)
    (by norm_num : (49/50:ℝ)<1)
    (show t ∈ Icc (-(49/50:ℝ)) (49/50) from ⟨by linarith [ht.1],ht.2⟩)
  rwa [ArcsineData.entropyTail_identity] at h

end
end CK.Certificate
