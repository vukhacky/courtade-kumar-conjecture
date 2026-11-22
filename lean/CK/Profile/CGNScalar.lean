module

public import CK.Profile.Convex

/-! Scalar inequality underlying CGN Lemma 10 (natural logarithms).
The one-variable endpoint inequality is obtained from the proved quadratic
entropy bound; monotonicity gives the two-variable inequality. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

theorem meanEntropy_ge_quadratic {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Real.log 2*(1-t^2) ≤ meanEntropy t := by
  have hu : phi t ≤ t^2*Real.log 2 := by
    by_cases hp : 0 ≤ t
    · simpa only [mul_one, phi_one] using
        phi_mul_le_sq_mul ⟨hp, ht.2⟩ (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
    · have hh : -t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1]
      simpa only [mul_one, phi_neg, neg_sq, phi_one] using
        phi_mul_le_sq_mul hh (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
  change Real.log 2-meanEntropy t ≤ t^2*Real.log 2 at hu
  nlinarith only [hu]

def cgnBase (b : ℝ) : ℝ :=
  (1+b)^2*Real.log (1+b)-(b^2+b)*Real.log b-4*b*Real.log 2

theorem entropy_ratio_identity {b : ℝ} (hb : 0 < b) :
    (1+b)^2*meanEntropy ((1-b)/(1+b)) =
      (1+b)^2*Real.log (1+b)-(b^2+b)*Real.log b := by
  have hden : 1+b ≠ 0 := by positivity
  have hp : (1-(1-b)/(1+b))/2 = b/(1+b) := by field_simp; ring
  have hq : 1-b/(1+b) = 1/(1+b) := by field_simp; ring
  rw [meanEntropy, hp, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hq]
  simp only [Real.negMulLog_def, Real.log_div (ne_of_gt hb) hden,
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hden, Real.log_one]
  field_simp
  ring

theorem cgnBase_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ cgnBase b := by
  have hd : 0 < 1+b := by positivity
  have ht : (1-b)/(1+b) ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hd).2; linarith
    · apply (div_le_iff₀ hd).2; linarith
  have h := mul_le_mul_of_nonneg_left (meanEntropy_ge_quadratic ht) (sq_nonneg (1+b))
  rw [entropy_ratio_identity hb] at h
  have heq : (1+b)^2*(Real.log 2*(1-((1-b)/(1+b))^2)) = 4*b*Real.log 2 := by
    field_simp
    ring
  rw [heq] at h
  dsimp [cgnBase]
  linarith only [h]

def cgnComparison (a b : ℝ) : ℝ :=
  (1+2*a+b^2)*Real.log (1+2*a+b^2)-2*(a+b)*Real.log (2*(a+b))-
    2*b^2*Real.log b+2*b*Real.log b

theorem hasDerivAt_cgnComparison {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    HasDerivAt (fun s => cgnComparison s b)
      (2*(Real.log (1+2*a+b^2)-Real.log (2*(a+b)))) a := by
  have hx : 0 < 1+2*a+b^2 := by nlinarith [sq_nonneg b]
  have hy : 0 < 2*(a+b) := by linarith
  have dx : HasDerivAt (fun s : ℝ => 1+2*s+b^2) 2 a := by
    convert (((hasDerivAt_id a).const_mul 2).const_add 1).add_const (b^2) using 1 <;>
      first | rfl | (funext s; dsimp; ring) | ring
  have dy : HasDerivAt (fun s : ℝ => 2*(s+b)) 2 a := by
    convert ((hasDerivAt_id a).add_const b).const_mul 2 using 1 <;>
      first | rfl | (funext s; dsimp; ring) | ring
  have h := (((Real.hasDerivAt_mul_log hx.ne').comp a dx).sub
    ((Real.hasDerivAt_mul_log hy.ne').comp a dy)).sub_const (2*b^2*Real.log b)
  have hh := h.add_const (2*b*Real.log b)
  apply hh.congr_deriv
  ring

theorem cgnComparison_monotone {b : ℝ} (hb : 0 < b) :
    MonotoneOn (fun a => cgnComparison a b) (Ici b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici b)
    (fun a ha => (hasDerivAt_cgnComparison hb ha).continuousAt.continuousWithinAt)
  · intro a ha
    exact (hasDerivAt_cgnComparison hb (interior_subset ha)).hasDerivWithinAt
  · intro a ha
    have hab : b ≤ a := interior_subset ha
    have hy : 0 < 2*(a+b) := by linarith
    have hxy : 2*(a+b) ≤ 1+2*a+b^2 := by nlinarith [sq_nonneg (b-1)]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.log_le_log hy hxy))

theorem cgnComparison_diagonal {b : ℝ} (hb : 0 < b) :
    cgnComparison b b = 2*cgnBase b := by
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  unfold cgnComparison cgnBase
  rw [show 1+2*b+b^2 = (1+b)^2 by ring, Real.log_pow,
    show 2*(b+b) = 4*b by ring, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hb), h4]
  ring

theorem cgnComparison_nonneg {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    0 ≤ cgnComparison a b := by
  have hm := cgnComparison_monotone hb (show b ∈ Ici b from le_rfl) hab hab
  dsimp only at hm
  rw [cgnComparison_diagonal hb] at hm
  linarith [cgnBase_nonneg hb]

end
end CK.Profile
