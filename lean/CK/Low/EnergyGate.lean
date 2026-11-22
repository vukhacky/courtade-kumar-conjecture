module

public import CK.Functional.SignEntropy
public import CK.Functional.PhiTaylor

/-! The scalar tangent gate from the STOC low/cubic energy argument.
All logarithm and quotient derivatives are restricted to their valid
domains; the endpoint `t=1` is evaluated separately. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def binaryEntropyQuotient (p : ℝ) : ℝ := Real.binEntropy p / p
def binaryEntropyQuotientSlope (p : ℝ) : ℝ := Real.log (1-p)/p^2
def binaryEntropyQuotientNumerator (p : ℝ) : ℝ := -p/(1-p)-2*Real.log (1-p)

theorem hasDerivAt_binaryEntropyQuotient {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt binaryEntropyQuotient (binaryEntropyQuotientSlope p) p := by
  have h := (Real.hasDerivAt_binEntropy (ne_of_gt hp.1) (ne_of_lt hp.2)).div
    (hasDerivAt_id p) (ne_of_gt hp.1)
  apply h.congr_deriv
  simp only [binaryEntropyQuotientSlope, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.negMulLog_def, mul_one, id_eq]
  ring

theorem hasDerivAt_binaryEntropyQuotientSlope {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt binaryEntropyQuotientSlope (binaryEntropyQuotientNumerator p/p^3) p := by
  have h := (((hasDerivAt_id p).const_sub 1).log (by simpa only [id_eq] using (show 1-p ≠ 0 by linarith [hp.2]))).div
    (hasDerivAt_pow 2 p) (pow_ne_zero 2 (ne_of_gt hp.1))
  apply h.congr_deriv
  unfold binaryEntropyQuotientNumerator
  norm_num
  field_simp [ne_of_gt hp.1, show 1-p ≠ 0 by linarith [hp.2]]
  all_goals ring

theorem hasDerivAt_binaryEntropyQuotientNumerator {p : ℝ} (hp : p ≠ 1) :
    HasDerivAt binaryEntropyQuotientNumerator ((1-2*p)/(1-p)^2) p := by
  have hn : 1-p ≠ 0 := by exact sub_ne_zero.mpr (Ne.symm hp)
  have h := (((hasDerivAt_id p).neg).div ((hasDerivAt_id p).const_sub 1) hn).sub
    ((((hasDerivAt_id p).const_sub 1).log hn).const_mul 2)
  apply h.congr_deriv
  norm_num
  field_simp
  ring

theorem binaryEntropyQuotientNumerator_nonneg {p : ℝ} (hp : p ∈ Icc (0 : ℝ) (1/2)) :
    0 ≤ binaryEntropyQuotientNumerator p := by
  have hm : MonotoneOn binaryEntropyQuotientNumerator (Icc (0 : ℝ) (1/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun p => (1-2*p)/(1-p)^2)
      (convex_Icc _ _)
    · intro x hx
      exact (hasDerivAt_binaryEntropyQuotientNumerator (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) (1/2) := by simpa only [interior_Icc] using hx
      exact (hasDerivAt_binaryEntropyQuotientNumerator (by linarith [hx'.2])).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) (1/2) := by simpa only [interior_Icc] using hx
      exact div_nonneg (by linarith [hx'.2]) (sq_nonneg _)
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc 0 (1/2)) hp hp.1
  simpa only [binaryEntropyQuotientNumerator, neg_zero, zero_div, mul_zero,
    sub_zero, Real.log_one] using h

def energyChi (c b t : ℝ) : ℝ := -2*signEntropy t/(1-t)+2*c*(1+t-b)
def energyChiSlope (c t : ℝ) : ℝ := binaryEntropyQuotientSlope ((1-t)/2)/2+2*c

theorem energyChi_eq_quotient (c b t : ℝ) :
    energyChi c b t = -binaryEntropyQuotient ((1-t)/2)+2*c*(1+t-b) := by
  unfold energyChi binaryEntropyQuotient signEntropy
  rw [div_div_eq_mul_div]
  ring

theorem energyChiSlope_eq (c t : ℝ) :
    energyChiSlope c t = Real.log ((1+t)/2)/(2*((1-t)/2)^2)+2*c := by
  unfold energyChiSlope binaryEntropyQuotientSlope
  rw [show 1-(1-t)/2 = (1+t)/2 by ring]
  rw [mul_comm 2 (((1-t)/2)^2), div_mul_eq_div_div]

theorem hasDerivAt_energyChi (c b : ℝ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (energyChi c b) (energyChiSlope c t) t := by
  have hp : (1-t)/2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h := (((hasDerivAt_binaryEntropyQuotient hp).comp t
    (((hasDerivAt_id t).const_sub 1).div_const 2)).neg).add
      ((((hasDerivAt_id t).const_add 1).sub_const b).const_mul (2*c))
  have hf : energyChi c b = fun x => -binaryEntropyQuotient ((1-x)/2)+2*c*(1+x-b) :=
    funext (energyChi_eq_quotient c b)
  rw [hf]
  apply h.congr_deriv
  unfold energyChiSlope
  ring

theorem hasDerivAt_energyChiSlope (c : ℝ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (energyChiSlope c)
      (-binaryEntropyQuotientNumerator ((1-t)/2)/(4*((1-t)/2)^3)) t := by
  have hp : (1-t)/2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h := (((hasDerivAt_binaryEntropyQuotientSlope hp).comp t
    (((hasDerivAt_id t).const_sub 1).div_const 2)).div_const 2).add_const (2*c)
  apply h.congr_deriv
  field_simp [show 1-t ≠ 0 by linarith [ht.2]]
  all_goals ring

theorem energyChi_concave (c b : ℝ) : ConcaveOn ℝ (Ico (0 : ℝ) 1) (energyChi c b) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := energyChiSlope c)
    (f'' := fun t => -binaryEntropyQuotientNumerator ((1-t)/2)/(4*((1-t)/2)^3)) (convex_Ico _ _)
  · intro t ht
    exact (hasDerivAt_energyChi c b ⟨by linarith [ht.1],ht.2⟩).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ico] using ht
    exact (hasDerivAt_energyChi c b ⟨by linarith [ht'.1],ht'.2⟩).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ico] using ht
    exact (hasDerivAt_energyChiSlope c ⟨by linarith [ht'.1],ht'.2⟩).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ico] using ht
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (binaryEntropyQuotientNumerator_nonneg
        ⟨by linarith [ht'.2], by linarith [ht'.1]⟩)
    · have h : 0 ≤ (1-t)/2 := by linarith [ht'.2]
      positivity

theorem energyChi_le_tangent (c b : ℝ) {t0 t : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ico (0 : ℝ) 1) :
    energyChi c b t ≤ energyChi c b t0+(t-t0)*energyChiSlope c t0 := by
  have hc := energyChi_concave c b
  have hd := hasDerivAt_energyChi c b ⟨by linarith [ht0.1],ht0.2⟩
  rcases lt_trichotomy t t0 with hlt | heq | hgt
  · have h := hc.le_slope_of_hasDerivAt ht ⟨ht0.1.le,ht0.2⟩ hlt hd
    rw [slope_def_field] at h
    have hm := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    nlinarith
  · subst t
    simp
  · have h := hc.slope_le_of_hasDerivAt ⟨ht0.1.le,ht0.2⟩ ht hgt hd
    rw [slope_def_field] at h
    have hm := (div_le_iff₀ (sub_pos.mpr hgt)).mp h
    nlinarith

theorem entropy_tangent_gate {c b t0 : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) 1)
    (h0 : energyChi c b t0-t0*energyChiSlope c t0 ≤ 0)
    (h1 : energyChi c b t0+(1-t0)*energyChiSlope c t0 ≤ 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, c*(1-t)*(1+t-b) ≤ signEntropy t := by
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · rw [heq]
    simp only [sub_self, mul_zero, zero_mul, signEntropy_one, le_refl]
  · have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1,hlt⟩
    have htan := energyChi_le_tangent c b ht0 ht'
    have hzero := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) h0
    have hone := mul_nonpos_of_nonneg_of_nonpos ht.1 h1
    have hchi : energyChi c b t ≤ 0 := by nlinarith only [htan,hzero,hone]
    have hm := mul_nonpos_of_nonpos_of_nonneg hchi (sub_nonneg.mpr ht.2)
    have hid : energyChi c b t*(1-t) = -2*signEntropy t+2*c*(1+t-b)*(1-t) := by
      unfold energyChi
      field_simp [show 1-t ≠ 0 by linarith]
    rw [hid] at hm
    nlinarith only [hm]

end
end CK
