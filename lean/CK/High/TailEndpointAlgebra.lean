module

public import CK.High.TailLosses
public import CK.High.Majorants

/-! Exact cancellation and rational bounds at the terminal retained endpoint.
The height estimate is explicit; the inverse-profile branch supplies it. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem shiftedMultiplier_one_defect {γ : ℝ} (hγ : 0 < γ) :
    1-shiftedMultiplier γ 1 < 1/γ := by
  have hid : 1-shiftedMultiplier γ 1=1/(γ+1) := by
    unfold shiftedMultiplier
    field_simp
    <;> ring
  rw [hid]
  exact one_div_lt_one_div_of_lt hγ (by linarith)

theorem shiftedMultiplier_half_step_defect {γ : ℝ} (hγ : 0 < γ) :
    shiftedMultiplier γ 1-shiftedMultiplier γ 2/2 < 1/γ := by
  have hid : shiftedMultiplier γ 1-shiftedMultiplier γ 2/2=
      γ/((γ+1)*(γ+2)) := by
    unfold shiftedMultiplier
    field_simp
    <;> ring
  rw [hid]
  apply (div_lt_div_iff₀ (mul_pos (by linarith) (by linarith)) hγ).mpr
  nlinarith only [hγ]

theorem quadratic_endpoint_remainder_bound {a d x k₁ k₂ p q : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (had : a+d=1)
    (hx : x ∈ Icc (0 : ℝ) 1)
    (hk₁ : k₁ ∈ Icc (0 : ℝ) 1) (hk₂ : k₂ ∈ Icc (0 : ℝ) 2)
    (h₁ : 1-k₁ ≤ p) (h₂ : k₁-k₂/2 ≤ p) (hq : 1-x ≤ q) :
    1-k₁*x*a-k₂*x^2*d/2 ≤ (1+d)*(p+q) := by
  have hx0 : 0 ≤ 1-x := by linarith only [hx.2]
  have hka := mul_le_mul_of_nonneg_right hk₁.2 ha
  have hkx := mul_le_mul_of_nonneg_left (show 1+x ≤ (2 : ℝ) by linarith only [hx.2])
    (show 0 ≤ k₂/2 by linarith only [hk₂.1])
  have hkd : (k₂/2)*(1+x)*d ≤ 2*d := by
    have hh : (k₂/2)*(1+x) ≤ 2 := by nlinarith only [hkx,hk₂.2]
    exact mul_le_mul_of_nonneg_right hh hd
  have hs : k₁*a+(k₂/2)*(1+x)*d ≤ 1+d := by nlinarith only [hka,hkd,had]
  have hmul := mul_le_mul_of_nonneg_left hs hx0
  have hp := mul_le_mul_of_nonneg_left h₂ hd
  have hqq := mul_le_mul_of_nonneg_right hq (show 0 ≤ 1+d by linarith only [hd])
  have hid : 1-k₁*x*a-k₂*x^2*d/2 =
      (1-k₁)+d*(k₁-k₂/2)+(1-x)*(k₁*a+(k₂/2)*(1+x)*d) := by
    nlinarith only [congrArg (fun z : ℝ => k₁*z) had]
  rw [hid]
  nlinarith only [h₁,hp,hmul,hqq]

theorem tail_near_endpoint_height_algebra {u v e x : ℝ}
    (hu : (8 : ℝ) ≤ u) (he : e ∈ Ioo (0 : ℝ) (1/2500))
    (hvu : v ≤ u) (hclose : u-v < 7*e/4) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < v ∧ 1 ≤ u/v ∧
      5*e/4 ≤ 1-(u/v)*((1-3*e)+x*(3*e)/2) ∧
      4*(u/v)*(1+4*e+3*e^2) < 101/25 := by
  have he0 : 0 < e := he.1
  have hu0 : 0 < u := by linarith only [hu]
  have hv : 0 < v := by linarith only [hu,he.2,hclose]
  have hq : 1 ≤ u/v := (le_div_iff₀ hv).mpr (by simpa using hvu)
  have hqu : u/v < (1001/1000 : ℝ) := by
    apply (div_lt_iff₀ hv).mpr
    nlinarith only [hu,he.2,hclose]
  have hA : 5*e/4 ≤ 1-(u/v)*((1-3*e)+x*(3*e)/2) := by
    have hr := mul_le_mul_of_nonneg_left hx.2 (show 0 ≤ u*(3*e)/2 by positivity)
    have hg := mul_nonneg (sub_nonneg.mpr hvu) he.1.le
    have heU := mul_le_mul_of_nonneg_right hu he.1.le
    apply (mul_le_mul_iff_right₀ hv).mp
    have hid : v*(1-(u/v)*((1-3*e)+x*(3*e)/2)) =
        v-u*((1-3*e)+x*(3*e)/2) := by field_simp <;> ring
    rw [hid]
    nlinarith only [hr,hg,heU,hclose,he0]
  have he2 : e^2 ≤ (1/2500 : ℝ)^2 := pow_le_pow_left₀ he.1.le he.2.le 2
  have hB : 1+4*e+3*e^2 < (501/500 : ℝ) := by nlinarith only [he.2,he2]
  have hm := mul_lt_mul_of_pos_left hB (show 0 < u/v by linarith only [hq])
  have hm' := mul_lt_mul_of_pos_right hqu (by norm_num : (0 : ℝ) < 501/500)
  exact ⟨hv,hq,hA,by nlinarith only [hm,hm']⟩

def tailEndpointQuadratic (u v : ℝ) : ℝ :=
  ((Real.pi^2/4)-4*Real.exp (-u)+(Real.pi^2/4)*
    (spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)/2+
      (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u)-
        spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)/2)*tailAlpha u))/v

theorem tail_endpoint_cancellation (u v : ℝ) :
    spectralNumerator (tailGamma u) (tailT u) (Real.tanh u)-u*tailEndpointQuadratic u v =
      (Real.pi^2/4)*shiftedMultiplier (tailGamma u) (tailT u)*Real.tanh u^2*
        (1-(u/v)*(tailAlpha u+Real.tanh u^2*(3*Real.exp (-u))/2))-
      (Real.pi^2/4)*(u/v)*
        (1-shiftedMultiplier (tailGamma u) 1*Real.tanh u^2*tailAlpha u-
          shiftedMultiplier (tailGamma u) 2*Real.tanh u^4*(3*Real.exp (-u))/2)-
      tailGamma u*Certificate.arcsineSharpConstant*entropyRemainder (Real.tanh u)+
      4*Real.exp (-u)*(u/v) := by
  unfold tailEndpointQuadratic spectralNumerator spectralDeltaOne spectralDeltaTwo tailAlpha
  ring

theorem tailGamma_reciprocal (u : ℝ) : 1/tailGamma u=4*Real.exp (-u) := by
  unfold tailGamma
  rw [Real.exp_neg]
  field_simp

theorem tail_endpoint_remainder {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    1-shiftedMultiplier (tailGamma u) 1*Real.tanh u^2*tailAlpha u-
      shiftedMultiplier (tailGamma u) 2*Real.tanh u^4*(3*Real.exp (-u))/2 ≤
    4*Real.exp (-u)*(1+4*Real.exp (-u)+3*Real.exp (-u)^2) := by
  have he := tail_epsilon_bounds hu
  have hg : 0 < tailGamma u := by unfold tailGamma; positivity
  have hr := tail_tanh_mem hu
  have hr2 : Real.tanh u^2 ∈ Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _,by nlinarith only [hr.1,hr.2]⟩
  have hk₁ := shiftedMultiplier_source_bounds hg (show (0 : ℝ) < 1 by norm_num)
  have hk₂ := shiftedMultiplier_source_bounds hg (show (0 : ℝ) < 2 by norm_num)
  have h := quadratic_endpoint_remainder_bound
    (a := tailAlpha u) (d := 3*Real.exp (-u)) (x := Real.tanh u^2)
    (k₁ := shiftedMultiplier (tailGamma u) 1) (k₂ := shiftedMultiplier (tailGamma u) 2)
    (p := 1/tailGamma u) (q := 4*Real.exp (-u)^2)
    (by unfold tailAlpha; linarith only [he.2]) (by positivity)
    (by unfold tailAlpha; ring) hr2 ⟨hk₁.1.le,hk₁.2.1.le⟩ ⟨hk₂.1.le,hk₂.2.1.le⟩
    (shiftedMultiplier_one_defect hg).le (shiftedMultiplier_half_step_defect hg).le
    (tanh_square_tail_bound u).le
  rw [tailGamma_reciprocal] at h
  convert h using 1 <;> ring

theorem tail_endpoint_quadratic_lt {u v : ℝ} (hu : (8 : ℝ) ≤ u)
    (hvu : v ≤ u) (hclose : u-v < 7*Real.exp (-u)/4) :
    tailEndpointQuadratic u v < spectralNumerator (tailGamma u) (tailT u) (Real.tanh u)/u := by
  let e := Real.exp (-u)
  let C := Real.pi^2/4
  let k := shiftedMultiplier (tailGamma u) (tailT u)*Real.tanh u^2
  let A := 1-(u/v)*(tailAlpha u+Real.tanh u^2*(3*e)/2)
  let R := 1-shiftedMultiplier (tailGamma u) 1*Real.tanh u^2*tailAlpha u-
    shiftedMultiplier (tailGamma u) 2*Real.tanh u^4*(3*e)/2
  have he : e ∈ Ioo (0 : ℝ) (1/2500) := tail_epsilon_bounds hu
  have he0 : 0 < e := he.1
  have hu0 : 0 < u := by linarith only [hu]
  have hr := tail_tanh_mem hu
  have hr2 : Real.tanh u^2 ∈ Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _,by nlinarith only [hr.1,hr.2]⟩
  obtain ⟨hv,hq,hA,hsmall⟩ := tail_near_endpoint_height_algebra hu he hvu hclose hr2
  change 5*e/4 ≤ A at hA
  have hk : u/2+9/10 < k := tail_multiplier_lower hu
  have hk0 : 0 ≤ k := by linarith only [hk,hu]
  have hC : (12/5 : ℝ) < C ∧ C < 5/2 := pi_square_quarter_bounds
  have hC0 : 0 < C := by linarith only [hC.1]
  have hfirst : 3*(u/2+9/10)*e < C*k*A := by
    have h₁ := mul_le_mul_of_nonneg_left hA (mul_nonneg hC0.le hk0)
    have h₂ := mul_le_mul_of_nonneg_right hC.1.le
      (mul_nonneg hk0 (show 0 ≤ 5*e/4 by positivity))
    have h₃ := mul_lt_mul_of_pos_right hk (show 0 < 3*e by positivity)
    nlinarith only [h₁,h₂,h₃]
  have hR : R ≤ 4*e*(1+4*e+3*e^2) := tail_endpoint_remainder hu
  have hq0 : 0 < u/v := by linarith only [hq]
  have hQR : (u/v)*R < (101/25)*e := by
    have h₁ := mul_le_mul_of_nonneg_left hR hq0.le
    have h₂ := mul_lt_mul_of_pos_right hsmall he0
    nlinarith only [h₁,h₂]
  have herror : C*(u/v)*R ≤ (101/10)*e := by
    have h₁ := mul_le_mul_of_nonneg_left hQR.le hC0.le
    have h₂ := mul_le_mul_of_nonneg_right hC.2.le (show 0 ≤ (101/25)*e by positivity)
    nlinarith only [h₁,h₂]
  have hpenalty := tail_entropy_penalty_le hu
  change tailGamma u*Certificate.arcsineSharpConstant*entropyRemainder (Real.tanh u) ≤
    (3/7)*(2*u+1)*e at hpenalty
  have hlast := mul_le_mul_of_nonneg_left hq (show 0 ≤ 4*e by positivity)
  have hscalar : 0 < (3*(u/2+9/10)-101/10-(3/7)*(2*u+1)+4)*e :=
    mul_pos (by linarith only [hu]) he0
  have hid : spectralNumerator (tailGamma u) (tailT u) (Real.tanh u)-u*tailEndpointQuadratic u v =
      C*k*A-C*(u/v)*R-
      tailGamma u*Certificate.arcsineSharpConstant*entropyRemainder (Real.tanh u)+4*e*(u/v) := by
    convert tail_endpoint_cancellation u v using 1 <;> dsimp [C,k,A,R,e] <;> ring
  have hpos : 0 < spectralNumerator (tailGamma u) (tailT u) (Real.tanh u)-u*tailEndpointQuadratic u v := by
    nlinarith only [hid,hfirst,herror,hpenalty,hlast,hscalar]
  apply (lt_div_iff₀ hu0).mpr
  nlinarith only [hpos]

theorem tail_quadratic_majorant_endpoint_lt {u v : ℝ} (hu : (8 : ℝ) ≤ u)
    (hv : 0 < v) (hvu : v ≤ u) (hclose : u-v < 7*Real.exp (-u)/4)
    (hroot : tailAlpha u*heightF v=heightF u) :
    quadraticCostMajorant (Real.pi^2/4-4*Real.exp (-u))
      (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u))
      (spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)) (heightF u) v <
      spectralNumerator (tailGamma u) (tailT u) (Real.tanh u)/u := by
  have hid : quadraticCostMajorant (Real.pi^2/4-4*Real.exp (-u))
      (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u))
      (spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)) (heightF u) v =
      tailEndpointQuadratic u v := by
    unfold quadraticCostMajorant tailEndpointQuadratic
    rw [←hroot]
    field_simp [hv.ne',(heightF_pos hv).ne']
    <;> ring
  rw [hid]
  exact tail_endpoint_quadratic_lt hu hvu hclose

end
end CK
