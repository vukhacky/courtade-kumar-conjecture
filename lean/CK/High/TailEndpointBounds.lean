module

public import CK.High.TailMajorants
public import CK.High.CostMajorants
public import CK.High.TailEndpointAlgebra

/-! Exact bounds for the three endpoint costs of the infinite-tail gate. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem tail_logarithmic_rational_comparison {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    (5/7)*(1+2*u/(3*u-5)+1/100) < 6/5+2/u := by
  have hu0 : 0 < u := by linarith
  have hd : 0 < 3*u-5 := by linarith
  have he : 6/5+2/u-(5/7)*(1+2*u/(3*u-5)+1/100)=
      (u^2+505*u-1400)/(140*u*(3*u-5)) := by
    generalize heq : 3*u-5=d
    have hd0 : d ≠ 0 := by rw [←heq]; exact hd.ne'
    field_simp [hu0.ne',hd0]
    rw [←heq]
    ring
  rw [←sub_pos,he]
  exact div_pos (by nlinarith only [hu,sq_nonneg (u-8)]) (by positivity)

theorem tail_quadratic_rational_comparison {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    (5/2)*(5/4+9*u/32)/(u-6/5) < 6/5+2/u := by
  have hu0 : 0 < u := by linarith
  have hd : 0 < u-6/5 := by linarith
  have hd' : 0 < 5*u-6 := by linarith
  have he : 6/5+2/u-(5/2)*(5/4+9*u/32)/(u-6/5)=
      3*(265*u^2-1368*u-1280)/(320*u*(5*u-6)) := by
    field_simp [hu0.ne',hd.ne',show 5*u-6 ≠ 0 by linarith]
    <;> ring
  rw [←sub_pos,he]
  exact div_pos (by nlinarith only [hu,sq_nonneg (u-8)]) (by positivity)

theorem tail_quadratic_one_eighth_lt {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    tailQuadraticMajorant u (profileHeight (Real.tanh u) (1/8)) <
      spectralNumerator (tailGamma u) (tailT u) (Real.tanh u)/u := by
  have hv := profileHeight_pos (tail_tanh_mem hu) (by norm_num : (0 : ℝ) < 1/8)
  have hvl := tail_inverse_one_eighth hu
  have hp : 0 ≤ Real.pi^2/4 := by positivity
  have hB : 1+spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)/2+
      (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u)-
        spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)/2)*(1/8) < 5/4+9*u/32 := by
    linarith only [tail_delta_two_lt hu,tail_delta_difference_lt hu]
  have hm := mul_le_mul_of_nonneg_left hB.le hp
  have hm2 := mul_le_mul_of_nonneg_right pi_square_quarter_bounds.2.le
    (show 0 ≤ 5/4+9*u/32 by linarith)
  have hN : tailArcsineConstant u+(Real.pi^2/4)*
      (spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)/2+
        (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u)-
          spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)/2)*(1/8)) <
      (5/2)*(5/4+9*u/32) := by
    unfold tailArcsineConstant
    nlinarith only [hm,hm2,Real.exp_pos (-u)]
  rw [tailQuadraticMajorant_at_height hu (by norm_num : (0 : ℝ) < 1/8)]
  have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ (5/2)*(5/4+9*u/32))
    (by linarith : 0 < u-6/5) hvl.le
  exact ((div_lt_div_of_pos_right hN hv).trans_le hdiv).trans
    (tail_quadratic_rational_comparison hu |>.trans (tail_numerator_div_lower hu))

theorem tail_quadratic_alpha_lt {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    tailQuadraticMajorant u (profileHeight (Real.tanh u) (tailAlpha u)) <
      spectralNumerator (tailGamma u) (tailT u) (Real.tanh u)/u := by
  have hr := tail_tanh_mem hu
  have ha := tailAlpha_mem hu
  have hv := profileHeight_pos hr ha.1
  have hvu := profileHeight_le_artanh hr ⟨ha.1.le,ha.2.le⟩
  rw [Real.artanh_tanh] at hvu
  exact tail_quadratic_majorant_endpoint_lt hu hv hvu
    (by nlinarith only [tail_inverse_alpha hu]) (tail_heightF_root hu ha.1)

theorem tailLogarithmicMajorant_formula {u v a : ℝ} (hu : (8 : ℝ) ≤ u)
    (hv : 0 < v) (ha : a ∈ Ioc (0 : ℝ) 1) (hroot : a*heightF v=heightF u) :
    tailLogarithmicMajorant u v =
      (tailArcsineConstant u+(Real.pi^2/4)*
        (2*spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)*(1-a/4)/Real.log (4/a)+
          (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u)-
            spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u))*a))/v := by
  have he : heightF u/heightF v=a := (div_eq_iff (heightF_pos hv).ne').mpr (by nlinarith only [hroot])
  unfold tailLogarithmicMajorant
  rw [logarithmicCostMajorant_formula (heightF_pos (by linarith : 0 < u)) hv
    (by rw [he]; exact ha.2),he]
  rw [←hroot]
  field_simp [hv.ne',(heightF_pos hv).ne']
  <;> ring

theorem tail_logarithmic_at_eighth_le_quadratic {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    tailLogarithmicMajorant u (profileHeight (Real.tanh u) (1/8)) ≤
      tailQuadraticMajorant u (profileHeight (Real.tanh u) (1/8)) := by
  have hv := profileHeight_pos (tail_tanh_mem hu) (by norm_num : (0 : ℝ) < 1/8)
  have hroot := tail_heightF_root hu (by norm_num : (0 : ℝ) < 1/8)
  rw [tailLogarithmicMajorant_formula hu hv (by norm_num : (1/8 : ℝ) ∈ Ioc 0 1) hroot,
    tailQuadraticMajorant_at_height hu (by norm_num : (0 : ℝ) < 1/8)]
  apply div_le_div_of_nonneg_right ?_ hv.le
  have hlog : Real.log (4/(1/8 : ℝ))=5*Real.log 2 := by
    rw [show (4/(1/8 : ℝ))=2^5 by norm_num,Real.log_pow]
    norm_num
  have hl : (31/45 : ℝ) < Real.log 2 := by linarith only [Certificate.log_two_coarse_bounds.1]
  have hp : 0 ≤ Real.pi^2/4 := by positivity
  have hD := spectralDeltaTwo_nonneg (ρ := Real.tanh u)
    (show 0 < tailGamma u by unfold tailGamma; positivity) (tail_parameter_domains hu).1
  have hsc : 2*(1-(1/8 : ℝ)/4)/Real.log (4/(1/8)) ≤ (1+(1/8))/2 := by
    rw [hlog]
    apply (div_le_iff₀ (by linarith : 0 < 5*Real.log 2)).mpr
    linarith only [hl]
  have hm := mul_le_mul_of_nonneg_left hsc (mul_nonneg hp hD)
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm]

theorem tail_logarithmic_at_cutoff_lt {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    tailLogarithmicMajorant u (7/2) <
      spectralNumerator (tailGamma u) (tailT u) (Real.tanh u)/u := by
  let β := profileCoefficient (Real.tanh u) (7/2)
  have hb0 : 0 < β := profileCoefficient_pos (tail_tanh_mem hu) (by norm_num)
  have hb : β < 1/200 := tail_beta_lt hu
  have hl : (3*u-5)/2 < Real.log (4/β) := tail_beta_log_lower hu
  have hl0 : 0 < Real.log (4/β) := by linarith
  have hroot : β*heightF (7/2)=heightF u := by
    dsimp [β]
    rw [profileCoefficient_tanh_eq (by linarith : 0 < u) (by norm_num)]
    exact div_mul_cancel₀ _ (heightF_pos (by norm_num : (0 : ℝ) < 7/2)).ne'
  have hD := spectralDeltaTwo_nonneg (ρ := Real.tanh u)
    (show 0 < tailGamma u by unfold tailGamma; positivity) (tail_parameter_domains hu).1
  have hDlt := tail_delta_two_lt hu
  have hdiff := tail_delta_difference_lt hu
  have hB1 : 2*spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)*(1-β/4)/Real.log (4/β) ≤
      2*u/(3*u-5) := by
    have hnum : 2*spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)*(1-β/4) ≤ u := by
      nlinarith only [hD,hDlt,mul_nonneg hD hb0.le]
    have h1 := div_le_div_of_nonneg_right hnum hl0.le
    have h2 := div_le_div_of_nonneg_left (show 0 ≤ u by linarith)
      (show 0 < (3*u-5)/2 by linarith) hl.le
    have hid : u/((3*u-5)/2)=2*u/(3*u-5) := by rw [div_div_eq_mul_div]; ring
    exact (h1.trans h2).trans_eq hid
  have hB2 : (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u)-
      spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u))*β < 1/100 := by
    have hm := mul_lt_mul_of_pos_right hdiff hb0
    nlinarith only [hm,hb]
  have hB : 1+2*spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)*(1-β/4)/Real.log (4/β)+
      (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u)-
        spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u))*β <
      1+2*u/(3*u-5)+1/100 := by linarith only [hB1,hB2]
  have hp : 0 ≤ Real.pi^2/4 := by positivity
  have hu0 : 0 ≤ u := by linarith
  have hden : 0 < 3*u-5 := by linarith
  have hm := mul_le_mul_of_nonneg_left hB.le hp
  have hm2 := mul_le_mul_of_nonneg_right pi_square_quarter_bounds.2.le
    (show 0 ≤ 1+2*u/(3*u-5)+1/100 by positivity)
  have hN : tailArcsineConstant u+(Real.pi^2/4)*
      (2*spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)*(1-β/4)/Real.log (4/β)+
        (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u)-
          spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u))*β) <
      (5/2)*(1+2*u/(3*u-5)+1/100) := by
    unfold tailArcsineConstant
    nlinarith only [hm,hm2,Real.exp_pos (-u)]
  rw [tailLogarithmicMajorant_formula hu (by norm_num : (0 : ℝ) < 7/2)
    ⟨hb0,by linarith⟩ hroot]
  have hfinal := div_lt_div_of_pos_right hN (by norm_num : (0 : ℝ) < 7/2)
  have hid : (5/2)*(1+2*u/(3*u-5)+1/100)/(7/2)=(5/7)*(1+2*u/(3*u-5)+1/100) := by ring
  rw [hid] at hfinal
  exact hfinal.trans (tail_logarithmic_rational_comparison hu |>.trans (tail_numerator_div_lower hu))

end
end CK
