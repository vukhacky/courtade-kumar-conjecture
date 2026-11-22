module

public import CK.Middle.CubicEnergy
public import CK.Certificate.EnergyPolynomial

/-! Elementary logarithm remainder bounds and the entropy quotient used in
cubic endpoint propagation. All bounds hold on intervals, including the
limits needed as rho approaches one; derivatives use strictly positive x. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem neg_log_one_sub_lower_cubic {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    u+u^2/2+u^3/3 ≤ -Real.log (1-u) := by
  let F : ℝ → ℝ := fun u => -Real.log (1-u)-(u+u^2/2+u^3/3)
  have hd (x : ℝ) (hx : x < 1) : HasDerivAt F (x^3/(1-x)) x := by
    have hn : 1-x ≠ 0 := by linarith
    have h := (((hasDerivAt_id x).const_sub 1).log hn).neg.sub
      (((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)).add
        ((hasDerivAt_pow 3 x).div_const 3))
    apply h.congr_deriv
    norm_num
    field_simp
    ring
  have hm : MonotoneOn F (Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => x^3/(1-x)) (convex_Ico _ _)
    · intro x hx
      exact (hd x hx.2).continuousAt.continuousWithinAt
    · intro x hx
      have h : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
      exact (hd x h.2).hasDerivWithinAt
    · intro x hx
      have h : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
      exact div_nonneg (pow_nonneg h.1.le 3) (by linarith [h.2])
  have h := hm (by norm_num : (0 : ℝ) ∈ Ico (0 : ℝ) 1) hu hu.1
  norm_num [F] at h
  linarith

theorem neg_log_one_sub_upper_cubic {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    -Real.log (1-u) ≤ u+u^2/2+u^3/(3*(1-u)) := by
  let F : ℝ → ℝ := fun u => u+u^2/2+u^3/(3*(1-u))+Real.log (1-u)
  have hd (x : ℝ) (hx : x < 1) : HasDerivAt F (x^3/(3*(1-x)^2)) x := by
    have hn : 1-x ≠ 0 := by linarith
    have h := (((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)).add
      ((hasDerivAt_pow 3 x).div (((hasDerivAt_id x).const_sub 1).const_mul 3)
        (mul_ne_zero (by norm_num) hn))).add (((hasDerivAt_id x).const_sub 1).log hn)
    apply h.congr_deriv
    norm_num
    field_simp
    ring
  have hm : MonotoneOn F (Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => x^3/(3*(1-x)^2)) (convex_Ico _ _)
    · intro x hx
      exact (hd x hx.2).continuousAt.continuousWithinAt
    · intro x hx
      have h : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
      exact (hd x h.2).hasDerivWithinAt
    · intro x hx
      have h : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
      exact div_nonneg (pow_nonneg h.1.le 3) (mul_nonneg (by norm_num) (sq_nonneg _))
  have h := hm (by norm_num : (0 : ℝ) ∈ Ico (0 : ℝ) 1) hu hu.1
  norm_num [F] at h
  linarith

def cubicEntropyQuotient (x : ℝ) : ℝ := signEntropy (1-x)/x
def cubicEntropyQuotientSlope (x : ℝ) : ℝ := Real.log (1-x/2)/x^2
def cubicEntropyQuotientCurvature (x : ℝ) : ℝ :=
  -1/(x^2*(2-x))-2*Real.log (1-x/2)/x^3

def cubicLogRemainderSlope (x : ℝ) : ℝ := -1/(2*x)-cubicEntropyQuotientSlope x
def cubicLogRemainderCurvature (x : ℝ) : ℝ := 1/(2*x^2)-cubicEntropyQuotientCurvature x

theorem cubicEntropyQuotient_eq (x : ℝ) :
    cubicEntropyQuotient x = binaryEntropyQuotient (x/2)/2 := by
  unfold cubicEntropyQuotient binaryEntropyQuotient signEntropy
  rw [show (1-(1-x))/2=x/2 by ring,div_div_eq_mul_div]
  ring

theorem hasDerivAt_cubicEntropyQuotient {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 2) :
    HasDerivAt cubicEntropyQuotient (cubicEntropyQuotientSlope x) x := by
  have h := ((hasDerivAt_binaryEntropyQuotient (show x/2 ∈ Ioo (0 : ℝ) 1 from
    ⟨by linarith [hx.1],by linarith [hx.2]⟩)).comp x ((hasDerivAt_id x).div_const 2)).div_const 2
  rw [show cubicEntropyQuotient = fun x => binaryEntropyQuotient (x/2)/2 from
    funext cubicEntropyQuotient_eq]
  apply h.congr_deriv
  unfold cubicEntropyQuotientSlope binaryEntropyQuotientSlope
  ring

theorem hasDerivAt_cubicEntropyQuotientSlope {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 2) :
    HasDerivAt cubicEntropyQuotientSlope (cubicEntropyQuotientCurvature x) x := by
  have hn : 1-x/2 ≠ 0 := by linarith [hx.2]
  have h := ((((hasDerivAt_id x).div_const 2).const_sub 1).log hn).div
    (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx.1.ne')
  apply h.congr_deriv
  unfold cubicEntropyQuotientCurvature
  norm_num
  field_simp [hx.1.ne',show 2-x ≠ 0 by linarith [hx.2]]
  all_goals ring

theorem cubicLogRemainderSlope_nonneg {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (43/500)) :
    0 ≤ cubicLogRemainderSlope x := by
  have h := neg_log_one_sub_lower_cubic (show x/2 ∈ Ico (0 : ℝ) 1 from
    ⟨by linarith [hx.1],by linarith [hx.2]⟩)
  have hlog : x/2 ≤ -Real.log (1-x/2) := by nlinarith [sq_nonneg x, pow_nonneg hx.1.le 3]
  unfold cubicLogRemainderSlope cubicEntropyQuotientSlope
  have heq : -1/(2*x) = -(x/2)/x^2 := by field_simp
  rw [heq]
  have hdiv := div_le_div_of_nonneg_right hlog (sq_nonneg x)
  simp only [neg_div] at hdiv ⊢
  linarith

theorem cubicLogRemainderSlope_le {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (43/500)) :
    cubicLogRemainderSlope x ≤ 13/100 := by
  have h := neg_log_one_sub_upper_cubic (show x/2 ∈ Ico (0 : ℝ) 1 from
    ⟨by linarith [hx.1],by linarith [hx.2]⟩)
  have hd : 0 < 2-x := by linarith [hx.2]
  have hb : x/(12*(2-x)) ≤ (1/200 : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 12) hd)).mpr
    linarith [hx.2]
  have hdiv := div_le_div_of_nonneg_right h (sq_nonneg x)
  have heq : (x/2+(x/2)^2/2+(x/2)^3/(3*(1-x/2)))/x^2-1/(2*x) =
      1/8+x/(12*(2-x)) := by
    field_simp [hx.1.ne',hd.ne']
    ring
  unfold cubicLogRemainderSlope cubicEntropyQuotientSlope
  rw [neg_div] at hdiv
  simp only [neg_div,mul_div_assoc] at heq ⊢
  linarith only [hdiv,heq,hb]

theorem cubicLogRemainderCurvature_le {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (43/500)) :
    cubicLogRemainderCurvature x ≤ 1/20 := by
  have h := neg_log_one_sub_lower_cubic (show x/2 ∈ Ico (0 : ℝ) 1 from
    ⟨by linarith [hx.1],by linarith [hx.2]⟩)
  have hd : 0 < 2-x := by linarith [hx.2]
  have hb : (1+x)/(12*(2-x)) ≤ (1/20 : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 12) hd)).mpr
    linarith [hx.2]
  have hdiv := div_le_div_of_nonneg_right h (pow_nonneg hx.1.le 3)
  have heq : 1/(2*x^2)+1/(x^2*(2-x))-2*(x/2+(x/2)^2/2+(x/2)^3/3)/x^3 =
      (1+x)/(12*(2-x)) := by
    field_simp [hx.1.ne',hd.ne']
    ring
  unfold cubicLogRemainderCurvature cubicEntropyQuotientCurvature
  rw [neg_div] at hdiv
  simp only [neg_div,mul_div_assoc] at heq ⊢
  linarith only [hdiv,heq,hb]

theorem signEntropy_cubic_endpoint_bounds :
    43/250 ≤ signEntropy (457/500) ∧ signEntropy (457/500) ≤ 9/50 := by
  have hlo := phiTaylor_le_phi 8 (show (457/500 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
  have hhi := phi_le_phiTaylor_bound 8 (r := (457/500 : ℝ)) (by norm_num) (by norm_num)
    (show (457/500 : ℝ) ∈ Icc (-(457/500)) (457/500) by norm_num)
  have hloglo := Certificate.P03.log_two_bounds.1
  have hloghi := Certificate.EnergyPolynomial.log_two_le
  norm_num [phiTaylor,phiTaylorTerm,Finset.sum_range_succ] at hlo hhi
  rw [signEntropy_eq_log_two_sub_phi]
  constructor <;> linarith

theorem signEntropy_le_cubic_endpoint {ρ : ℝ} (hρ : ρ ∈ Icc (457/500 : ℝ) 1) :
    signEntropy ρ ≤ 9/50 := by
  apply le_trans ?_ signEntropy_cubic_endpoint_bounds.2
  exact Real.binEntropy_strictMonoOn.monotoneOn
    ⟨by linarith [hρ.2],by linarith [hρ.1]⟩ (by norm_num)
    (by linarith [hρ.1])

theorem cubicEntropyQuotient_nonneg {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (43/500)) :
    0 ≤ cubicEntropyQuotient x := by
  exact div_nonneg (signEntropy_nonneg ⟨by linarith [hx.2],by linarith [hx.1]⟩) hx.1.le

theorem cubicEntropyQuotientSlope_nonpos {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (43/500)) :
    cubicEntropyQuotientSlope x ≤ 0 := by
  exact div_nonpos_of_nonpos_of_nonneg
    (Real.log_nonpos (by linarith [hx.2]) (by linarith [hx.1])) (sq_nonneg x)

theorem cubicEntropyQuotientCurvature_nonneg {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (43/500)) :
    0 ≤ cubicEntropyQuotientCurvature x := by
  have h := cubicLogRemainderCurvature_le hx
  have hi : (1/20 : ℝ) ≤ 1/(2*x^2) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hx.1))).mpr
    nlinarith [hx.1,hx.2]
  unfold cubicLogRemainderCurvature at h
  linarith

theorem cubicEntropyQuotient_ge_two {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (43/500)) :
    2 ≤ cubicEntropyQuotient x := by
  have hm : AntitoneOn cubicEntropyQuotient (Ioc (0 : ℝ) (43/500)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := cubicEntropyQuotientSlope) (convex_Ioc _ _)
    · intro y hy
      exact (hasDerivAt_cubicEntropyQuotient ⟨hy.1,by linarith [hy.2]⟩).continuousAt.continuousWithinAt
    · intro y hy
      have h : y ∈ Ioo (0 : ℝ) (43/500) := by simpa using hy
      exact (hasDerivAt_cubicEntropyQuotient ⟨h.1,by linarith [h.2]⟩).hasDerivWithinAt
    · intro y hy
      have h : y ∈ Ioo (0 : ℝ) (43/500) := by simpa using hy
      exact cubicEntropyQuotientSlope_nonpos ⟨h.1,h.2.le⟩
  have h := hm hx (show (43/500 : ℝ) ∈ Ioc (0 : ℝ) (43/500) by norm_num) hx.2
  have hlo := signEntropy_cubic_endpoint_bounds.1
  norm_num [cubicEntropyQuotient] at h
  change 2 ≤ signEntropy (1-x)/x
  linarith

theorem log_three_fourths_lower : -(3/10 : ℝ) ≤ Real.log (3/4) := by
  have h := neg_log_one_sub_upper_cubic (show (1/4 : ℝ) ∈ Ico (0 : ℝ) 1 by norm_num)
  norm_num at h
  linarith

end
end CK
