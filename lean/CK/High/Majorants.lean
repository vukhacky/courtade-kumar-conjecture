module

public import CK.High.ProfileInverse
public import CK.High.SpectralCost
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Convex height majorants for the spectral cost.  The logarithmic
majorant is defined by an integral of reciprocal profile powers, including
its removable singularity.  Its elementary formula is proved on the
coefficient range used by the spectral gate. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory
namespace CK
noncomputable section

theorem profileCoefficient_tanh_eq {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    profileCoefficient (Real.tanh u) v = heightF u/heightF v := by
  have htu := tanh_mem_Ioo_positive hu
  have htv := tanh_mem_Ioo_positive hv
  have hHu := Profile.meanEntropy_pos ⟨by linarith [htu.1],htu.2⟩
  have hHv := Profile.meanEntropy_pos ⟨by linarith [htv.1],htv.2⟩
  unfold profileCoefficient heightF
  change Profile.meanEntropy (Real.tanh u)*Real.tanh v/
    (Real.tanh u*Profile.meanEntropy (Real.tanh v)) = _
  field_simp [htu.1.ne',htv.1.ne',hHu.ne',hHv.ne']

theorem profileCoefficient_profileHeight {ρ a : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    profileCoefficient ρ (profileHeight ρ a) = a := by
  have hv := profileHeight_pos hρ ha
  apply (profileHeight_strictMono hρ).injOn
    (profileCoefficient_pos hρ hv).le ha.le
  exact profileHeight_profileCoefficient hρ hv

theorem profileHeight_heightF_ratio {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    profileHeight (Real.tanh u) (heightF u/heightF v) = v := by
  rw [←profileCoefficient_tanh_eq hu hv]
  exact profileHeight_profileCoefficient (tanh_mem_Ioo_positive hu) hv

theorem heightF_ratio_mem_Ioc {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) :
    heightF u/heightF v ∈ Ioc (0 : ℝ) 1 := by
  refine ⟨div_pos (heightF_pos hu) (heightF_pos hv),?_⟩
  exact (div_le_one (heightF_pos hv)).mpr (heightF_strictAnti.antitoneOn hv hu hvu)

theorem arcsineRemainder_tangent {c v : ℝ} (hc : 0 < c) (hv : 0 ≤ v) :
    arcsineRemainder c+arcsineRemainderSlope c*(v-c) ≤ arcsineRemainder v := by
  rcases lt_trichotomy v c with hvc | rfl | hcv
  · have h := arcsineRemainder_convex.slope_le_of_hasDerivAt hv hc.le hvc
      (hasDerivAt_arcsineRemainder hc)
    rw [slope_def_field] at h
    have h' := (div_le_iff₀ (sub_pos.mpr hvc)).mp h
    linarith only [h']
  · simp
  · have h := arcsineRemainder_convex.le_slope_of_hasDerivAt hc.le hv hcv
      (hasDerivAt_arcsineRemainder hc)
    rw [slope_def_field] at h
    have h' := (le_div_iff₀ (sub_pos.mpr hcv)).mp h
    linarith only [h']

theorem arcsineRemainder_tangent_intercept_nonneg {c : ℝ} (hc : 0 < c) :
    0 ≤ c*arcsineRemainderSlope c-arcsineRemainder c := by
  have h := arcsineRemainder_tangent hc (show (0 : ℝ) ≤ 0 by norm_num)
  rw [arcsineRemainder_zero] at h
  linarith only [h]

theorem convex_positive_height_le_endpoints {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi (0 : ℝ)) f) {l v r : ℝ}
    (hl : 0 < l) (hv : v ∈ Icc l r) : f v ≤ max (f l) (f r) := by
  apply hf.le_on_segment hl (hl.trans_le (hv.1.trans hv.2))
  rw [segment_eq_Icc (hv.1.trans hv.2)]
  exact hv

def logarithmicHeightKernel (K v : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, (K/4)^r*reciprocalHeightPower r v

theorem continuous_logarithmicHeightIntegrand {K v : ℝ} (hK : 0 < K) (hv : 0 < v) :
    Continuous (fun r : ℝ => (K/4)^r*reciprocalHeightPower r v) := by
  unfold reciprocalHeightPower
  exact (Real.continuous_const_rpow (by positivity : K/4 ≠ 0)).mul
    (continuous_const.div
      (continuous_const.mul (Real.continuous_const_rpow (heightF_pos hv).ne'))
      (fun r => mul_ne_zero hv.ne' (Real.rpow_pos_of_pos (heightF_pos hv) r).ne'))

theorem logarithmicHeightKernel_convex {K : ℝ} (hK : 0 < K) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (logarithmicHeightKernel K) := by
  refine ⟨convex_Ioi 0,?_⟩
  intro x hx y hy α β hα hβ hsum
  have hz : 0 < α*x+β*y := by
    have hm := lt_min hx hy
    have h₁ := mul_le_mul_of_nonneg_left (min_le_left x y) hα
    have h₂ := mul_le_mul_of_nonneg_left (min_le_right x y) hβ
    nlinarith only [hm,h₁,h₂,congrArg (fun z : ℝ => z*min x y) hsum]
  have hc (v : ℝ) (hv : 0 < v) := continuous_logarithmicHeightIntegrand hK hv
  have hi (v : ℝ) (hv : 0 < v) :
      IntervalIntegrable (fun r : ℝ => (K/4)^r*reciprocalHeightPower r v) volume 0 1 :=
    (hc v hv).intervalIntegrable (0 : ℝ) 1
  have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
    (hi _ hz) (((hi _ hx).const_mul α).add ((hi _ hy).const_mul β)) (fun r hr => by
      have hh := (reciprocalHeightPower_convex hr).2 hx hy hα hβ hsum
      simp only [smul_eq_mul] at hh
      have hp : 0 ≤ (K/4)^r := Real.rpow_nonneg (by positivity) r
      nlinarith only [mul_le_mul_of_nonneg_left hh hp])
  rw [intervalIntegral.integral_add ((hi _ hx).const_mul α) ((hi _ hy).const_mul β),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at h
  exact h

def quadraticCostMajorant (C Δ₁ Δ₂ K v : ℝ) : ℝ :=
  C/v+(Real.pi^2/4)*(Δ₂/(2*v)+(Δ₁-Δ₂/2)*K/(v*heightF v))

def logarithmicCostMajorant (C Δ₁ Δ₂ K v : ℝ) : ℝ :=
  C/v+(Real.pi^2/4)*(2*Δ₂*logarithmicHeightKernel K v+
    (Δ₁-Δ₂)*K/(v*heightF v))

theorem quadraticCostMajorant_convex {C Δ₁ Δ₂ K : ℝ}
    (hC : 0 ≤ C) (hΔ₂ : 0 ≤ Δ₂) (hΔ : Δ₂ ≤ Δ₁) (hK : 0 ≤ K) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (quadraticCostMajorant C Δ₁ Δ₂ K) := by
  have hzero := reciprocalHeightPower_convex (r := 0) (by norm_num)
  have hone := reciprocalHeightPower_convex (r := 1) (by norm_num)
  have hA : 0 ≤ Δ₁-Δ₂/2 := by linarith
  have h := (hzero.smul hC).add
    (((hzero.smul (div_nonneg hΔ₂ (by norm_num : (0 : ℝ) ≤ 2))).add
      (hone.smul (mul_nonneg hA hK))).smul (show 0 ≤ Real.pi^2/4 by positivity))
  convert h using 1
  ext v
  simp only [quadraticCostMajorant,reciprocalHeightPower,Real.rpow_zero,Real.rpow_one,
    mul_one,smul_eq_mul,Pi.add_apply]
  ring

theorem logarithmicCostMajorant_convex {C Δ₁ Δ₂ K : ℝ}
    (hC : 0 ≤ C) (hΔ₂ : 0 ≤ Δ₂) (hΔ : Δ₂ ≤ Δ₁) (hK : 0 < K) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (logarithmicCostMajorant C Δ₁ Δ₂ K) := by
  have hzero := reciprocalHeightPower_convex (r := 0) (by norm_num)
  have hone := reciprocalHeightPower_convex (r := 1) (by norm_num)
  have h := (hzero.smul hC).add
    ((((logarithmicHeightKernel_convex hK).smul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hΔ₂)).add
      (hone.smul (mul_nonneg (sub_nonneg.mpr hΔ) hK.le))).smul
        (show 0 ≤ Real.pi^2/4 by positivity))
  convert h using 1
  ext v
  simp only [logarithmicCostMajorant,reciprocalHeightPower,Real.rpow_zero,Real.rpow_one,
    mul_one,smul_eq_mul,Pi.add_apply]
  ring

end
end CK
