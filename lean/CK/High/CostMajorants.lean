module

public import CK.High.Majorants

/-! Elementary formulas and source-cost bounds for the convex majorants.
The first cost numerator can be bounded either by a constant or by the
affine tangent bound for the arcsine remainder. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory
namespace CK
noncomputable section

theorem integral_coefficient_power {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    (∫ r in (0 : ℝ)..1, (a/4)^r) = (1-a/4)/Real.log (4/a) := by
  have hp : 0 < a/4 := div_pos ha.1 (by norm_num)
  have hL : Real.log (a/4) = -Real.log (4/a) := by
    rw [Real.log_div ha.1.ne' (by norm_num),Real.log_div (by norm_num) ha.1.ne']
    ring
  have hLn : Real.log (a/4) ≠ 0 := by rw [hL]; exact neg_ne_zero.mpr (influence_log_pos ha).ne'
  simp_rw [Real.rpow_def_of_pos hp]
  rw [intervalIntegral.integral_comp_mul_left Real.exp hLn,integral_exp]
  simp only [mul_zero,mul_one,Real.exp_zero,smul_eq_mul]
  rw [Real.exp_log hp,hL]
  ring

theorem logarithmicHeightKernel_formula {K v : ℝ}
    (hK : 0 < K) (hv : 0 < v) (ha : K/heightF v ≤ 1) :
    logarithmicHeightKernel K v =
      (1-K/heightF v/4)/(v*Real.log (4/(K/heightF v))) := by
  have hF := heightF_pos hv
  have har : K/heightF v ∈ Ioc (0 : ℝ) 1 := ⟨div_pos hK hF,ha⟩
  have hid (r : ℝ) : (K/4)^r*reciprocalHeightPower r v =
      (K/heightF v/4)^r/v := by
    rw [show K/heightF v/4=(K/4)/heightF v by ring,
      Real.div_rpow (by positivity) hF.le r]
    unfold reciprocalHeightPower
    ring
  unfold logarithmicHeightKernel
  simp_rw [hid]
  rw [intervalIntegral.integral_div,integral_coefficient_power har]
  ring

theorem logarithmicCostMajorant_formula {C Δ₁ Δ₂ K v : ℝ}
    (hK : 0 < K) (hv : 0 < v) (ha : K/heightF v ≤ 1) :
    logarithmicCostMajorant C Δ₁ Δ₂ K v =
      C/v+(Real.pi^2/4)*(2*Δ₂*(1-K/heightF v/4)/
        (v*Real.log (4/(K/heightF v)))+(Δ₁-Δ₂)*K/(v*heightF v)) := by
  rw [logarithmicCostMajorant,logarithmicHeightKernel_formula hK hv ha]
  ring

theorem influencePsi_div_le_quadratic {a : ℝ} (ha : 0 < a) :
    influencePsi a/a ≤ (1+a)/2 := by
  have h := div_le_div_of_nonneg_right
    (min_le_left (influencePolynomial a) (influenceLogarithmic a)) ha.le
  change influencePsi a/a ≤ influencePolynomial a/a at h
  convert h using 1
  unfold influencePolynomial
  field_simp <;> ring

theorem influencePsi_div_le_logarithmic {a : ℝ} (ha : 0 < a) :
    influencePsi a/a ≤ 2*(1-a/4)/Real.log (4/a) := by
  have h := div_le_div_of_nonneg_right
    (min_le_right (influencePolynomial a) (influenceLogarithmic a)) ha.le
  change influencePsi a/a ≤ influenceLogarithmic a/a at h
  convert h using 1
  unfold influenceLogarithmic
  field_simp <;> ring

theorem spectralCost_le_quadraticCostMajorant {γ t u v C : ℝ}
    (hu : 0 < u) (hv : 0 < v)
    (hΔ₂ : 0 ≤ spectralDeltaTwo γ t (Real.tanh u))
    (hfirst : Real.tanh u*(v-arcsineRemainder v) ≤ C) :
    spectralCost γ t (Real.tanh u) (heightF u/heightF v) ≤
      quadraticCostMajorant C (spectralDeltaOne γ t (Real.tanh u))
        (spectralDeltaTwo γ t (Real.tanh u)) (heightF u) v := by
  have hF := heightF_pos hv
  have ha := div_pos (heightF_pos hu) hF
  have hpsi := influencePsi_div_le_quadratic ha
  have hP : 0 ≤ Real.pi^2/4 := by positivity
  have hm := mul_le_mul_of_nonneg_left hpsi (mul_nonneg hP hΔ₂)
  unfold spectralCost quadraticCostMajorant
  rw [profileHeight_heightF_ratio hu hv]
  apply (div_le_iff₀ hv).mpr
  have hid : (C/v+(Real.pi^2/4)*
      (spectralDeltaTwo γ t (Real.tanh u)/(2*v)+
        (spectralDeltaOne γ t (Real.tanh u)-spectralDeltaTwo γ t (Real.tanh u)/2)*
          heightF u/(v*heightF v)))*v =
      C+(Real.pi^2/4)*(spectralDeltaTwo γ t (Real.tanh u)*(1+heightF u/heightF v)/2+
        (spectralDeltaOne γ t (Real.tanh u)-spectralDeltaTwo γ t (Real.tanh u))*
          (heightF u/heightF v)) := by field_simp; ring
  rw [hid]
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hfirst,hm]

theorem spectralCost_le_logarithmicCostMajorant {γ t u v C : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u)
    (hΔ₂ : 0 ≤ spectralDeltaTwo γ t (Real.tanh u))
    (hfirst : Real.tanh u*(v-arcsineRemainder v) ≤ C) :
    spectralCost γ t (Real.tanh u) (heightF u/heightF v) ≤
      logarithmicCostMajorant C (spectralDeltaOne γ t (Real.tanh u))
        (spectralDeltaTwo γ t (Real.tanh u)) (heightF u) v := by
  have hF := heightF_pos hv
  have ha := heightF_ratio_mem_Ioc hu hv hvu
  have hpsi := influencePsi_div_le_logarithmic ha.1
  have hP : 0 ≤ Real.pi^2/4 := by positivity
  have hm := mul_le_mul_of_nonneg_left hpsi (mul_nonneg hP hΔ₂)
  rw [logarithmicCostMajorant_formula (heightF_pos hu) hv ha.2]
  unfold spectralCost
  rw [profileHeight_heightF_ratio hu hv]
  apply (div_le_iff₀ hv).mpr
  have hid : (C/v+(Real.pi^2/4)*
      (2*spectralDeltaTwo γ t (Real.tanh u)*(1-heightF u/heightF v/4)/
          (v*Real.log (4/(heightF u/heightF v)))+
        (spectralDeltaOne γ t (Real.tanh u)-spectralDeltaTwo γ t (Real.tanh u))*
          heightF u/(v*heightF v)))*v =
      C+(Real.pi^2/4)*
        (spectralDeltaTwo γ t (Real.tanh u)*(2*(1-heightF u/heightF v/4)/
          Real.log (4/(heightF u/heightF v)))+
        (spectralDeltaOne γ t (Real.tanh u)-spectralDeltaTwo γ t (Real.tanh u))*
          (heightF u/heightF v)) := by field_simp <;> ring
  rw [hid]
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hfirst,hm]

def quadraticTangentMajorant (ρ c Δ₁ Δ₂ K v : ℝ) : ℝ :=
  ρ*(1-arcsineRemainderSlope c)+
    quadraticCostMajorant (ρ*(c*arcsineRemainderSlope c-arcsineRemainder c)) Δ₁ Δ₂ K v

def logarithmicTangentMajorant (ρ c Δ₁ Δ₂ K v : ℝ) : ℝ :=
  ρ*(1-arcsineRemainderSlope c)+
    logarithmicCostMajorant (ρ*(c*arcsineRemainderSlope c-arcsineRemainder c)) Δ₁ Δ₂ K v

theorem quadraticTangentMajorant_convex {ρ c Δ₁ Δ₂ K : ℝ}
    (hρ : 0 ≤ ρ) (hc : 0 < c) (hΔ₂ : 0 ≤ Δ₂) (hΔ : Δ₂ ≤ Δ₁) (hK : 0 ≤ K) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (quadraticTangentMajorant ρ c Δ₁ Δ₂ K) := by
  exact (convexOn_const _ (convex_Ioi (0 : ℝ))).add
    (quadraticCostMajorant_convex
      (mul_nonneg hρ (arcsineRemainder_tangent_intercept_nonneg hc)) hΔ₂ hΔ hK)

theorem logarithmicTangentMajorant_convex {ρ c Δ₁ Δ₂ K : ℝ}
    (hρ : 0 ≤ ρ) (hc : 0 < c) (hΔ₂ : 0 ≤ Δ₂) (hΔ : Δ₂ ≤ Δ₁) (hK : 0 < K) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (logarithmicTangentMajorant ρ c Δ₁ Δ₂ K) := by
  exact (convexOn_const _ (convex_Ioi (0 : ℝ))).add
    (logarithmicCostMajorant_convex
      (mul_nonneg hρ (arcsineRemainder_tangent_intercept_nonneg hc)) hΔ₂ hΔ hK)

theorem spectralCost_le_quadraticTangentMajorant {γ t u v c : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hc : 0 < c)
    (hΔ₂ : 0 ≤ spectralDeltaTwo γ t (Real.tanh u)) :
    spectralCost γ t (Real.tanh u) (heightF u/heightF v) ≤
      quadraticTangentMajorant (Real.tanh u) c (spectralDeltaOne γ t (Real.tanh u))
        (spectralDeltaTwo γ t (Real.tanh u)) (heightF u) v := by
  have ht := arcsineRemainder_tangent hc hv.le
  have hρ := (tanh_mem_Ioo_positive hu).1
  have hmul := mul_le_mul_of_nonneg_left ht hρ.le
  have hb : Real.tanh u*(v-arcsineRemainder v) ≤
      Real.tanh u*(1-arcsineRemainderSlope c)*v+
        Real.tanh u*(c*arcsineRemainderSlope c-arcsineRemainder c) := by
    nlinarith only [hmul]
  have h := spectralCost_le_quadraticCostMajorant hu hv hΔ₂ hb
  convert h using 1
  unfold quadraticTangentMajorant quadraticCostMajorant
  field_simp <;> ring

theorem spectralCost_le_logarithmicTangentMajorant {γ t u v c : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) (hc : 0 < c)
    (hΔ₂ : 0 ≤ spectralDeltaTwo γ t (Real.tanh u)) :
    spectralCost γ t (Real.tanh u) (heightF u/heightF v) ≤
      logarithmicTangentMajorant (Real.tanh u) c (spectralDeltaOne γ t (Real.tanh u))
        (spectralDeltaTwo γ t (Real.tanh u)) (heightF u) v := by
  have ht := arcsineRemainder_tangent hc hv.le
  have hρ := (tanh_mem_Ioo_positive hu).1
  have hmul := mul_le_mul_of_nonneg_left ht hρ.le
  have hb : Real.tanh u*(v-arcsineRemainder v) ≤
      Real.tanh u*(1-arcsineRemainderSlope c)*v+
        Real.tanh u*(c*arcsineRemainderSlope c-arcsineRemainder c) := by
    nlinarith only [hmul]
  have h := spectralCost_le_logarithmicCostMajorant hu hv hvu hΔ₂ hb
  convert h using 1
  unfold logarithmicTangentMajorant logarithmicCostMajorant
  field_simp <;> ring

end
end CK
