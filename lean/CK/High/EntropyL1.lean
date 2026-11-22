module

public import CK.Functional.LogSobolev
public import CK.Functional.Hypercontractivity

/-! A finite entropy–L1 estimate with explicit treatment of zero values.
Only positive logarithm arguments are expanded. The affine version can
be summed over Doob increments without a separate log-sum theorem. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem avg_eq_zero_iff_of_nonneg {n : ℕ} (g : Cube n → ℝ) (hg : ∀ x, 0 ≤ g x) :
    avg g=0 ↔ ∀ x, g x=0 := by
  constructor
  · intro h
    unfold avg at h
    have hc : (Fintype.card (Cube n) : ℝ)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (card_cube_pos n))
    have hs : ∑ x, g x=0 := (mul_eq_zero.mp h).resolve_left hc
    exact fun x => (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hg y)).mp hs x (Finset.mem_univ x)
  · intro h
    have he : g=fun _ => 0 := funext h
    rw [he,avg_const]

theorem avg_abs_pos_of_avg_sq_pos {n : ℕ} (g : Cube n → ℝ)
    (hv : 0 < avg (fun x => g x^2)) : 0 < avg (fun x => |g x|) := by
  have ha := avg_nonneg (fun x => |g x|) (fun x => abs_nonneg _)
  apply lt_of_le_of_ne ha
  intro hz
  have hg := (avg_eq_zero_iff_of_nonneg (fun x => |g x|) (fun x => abs_nonneg _) ).mp hz.symm
  have hz2 : (fun x => g x^2) = fun _ => (0 : ℝ) := by
    funext x
    rw [abs_eq_zero.mp (hg x)]
    norm_num
  rw [hz2,avg_const] at hv
  exact lt_irrefl 0 hv

theorem square_log_abs (x : ℝ) : x^2*Real.log (x^2) = 2*(x^2*Real.log |x|) := by
  rw [Real.log_pow,Real.log_abs]
  ring

/-- Pointwise estimate used in the finite weighted logarithm argument.
At `x=0` the two sides vanish, so no reciprocal of a supported zero is
used in expanding a logarithm. -/
theorem square_log_support_bound {v a : ℝ} (hv : 0 < v) (ha : 0 < a) (x : ℝ) :
    x^2*(Real.log v-Real.log a-Real.log |x|) ≤ (v/a)*|x|-x^2 := by
  by_cases hx : x=0
  · simp [hx]
  · have hax : 0 < |x| := abs_pos.mpr hx
    have h := Real.log_le_sub_one_of_pos (div_pos hv (mul_pos ha hax))
    rw [Real.log_div (ne_of_gt hv) (ne_of_gt (mul_pos ha hax)),
      Real.log_mul (ne_of_gt ha) (ne_of_gt hax)] at h
    have hm := mul_le_mul_of_nonneg_left h (sq_nonneg x)
    have hid : x^2*(v/(a*|x|)-1)=(v/a)*|x|-x^2 := by
      have hs := sq_abs x
      field_simp [ne_of_gt ha,ne_of_gt hax]
      nlinarith only [congrArg (fun z : ℝ => v*z) hs]
    rw [hid] at hm
    nlinarith only [hm]

/-- The finite L1–L2 entropy comparison. -/
theorem entropyFunctional_square_log_lower {n : ℕ} (g : Cube n → ℝ)
    (hv : 0 < avg (fun x => g x^2)) :
    avg (fun x => g x^2)*Real.log
      (avg (fun x => g x^2)/(avg (fun x => |g x|))^2) ≤
        entropyFunctional (fun x => g x^2) := by
  let v := avg (fun x => g x^2)
  let a := avg (fun x => |g x|)
  have hv' : 0 < v := hv
  have ha : 0 < a := avg_abs_pos_of_avg_sq_pos g hv
  have hpoint := avg_mono (fun x => square_log_support_bound hv' ha (g x))
  have hl : (fun x => g x^2*(Real.log v-Real.log a-Real.log |g x|)) =
      fun x => (Real.log v-Real.log a)*g x^2-g x^2*Real.log |g x| := by
    funext x
    ring
  have hr : (fun x => (v/a)*|g x|-g x^2) = fun x => (v/a)*|g x|-g x^2 := rfl
  rw [hl,avg_sub,avg_smul,avg_sub,avg_smul] at hpoint
  change (Real.log v-Real.log a)*v-avg (fun x => g x^2*Real.log |g x|) ≤ (v/a)*a-v at hpoint
  rw [div_mul_cancel₀ _ (ne_of_gt ha)] at hpoint
  have hlog : Real.log (v/a^2) = Real.log v-2*Real.log a := by
    rw [Real.log_div (ne_of_gt hv') (ne_of_gt (sq_pos_of_pos ha)),Real.log_pow]
    norm_num
  change v*Real.log (v/a^2) ≤ avg (fun x => g x^2*Real.log (g x^2))-v*Real.log v
  rw [hlog]
  simp only [square_log_abs,avg_smul]
  nlinarith only [hpoint]

/-- Scalar Fenchel bound valid at zero as well as at positive inputs. -/
theorem mul_log_fenchel {x lam : ℝ} (hx : 0 ≤ x) :
    lam*x-Real.exp (lam-1) ≤ x*Real.log x := by
  by_cases hx0 : x=0
  · simp only [hx0,mul_zero,Real.log_zero,zero_mul,zero_sub]
    exact neg_nonpos.mpr (Real.exp_pos _).le
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have h := Real.add_one_le_exp (lam-1-Real.log x)
    have hm := mul_le_mul_of_nonneg_left h hx
    rw [Real.exp_sub,Real.exp_log hxp] at hm
    have he : x*(Real.exp (lam-1)/x)=Real.exp (lam-1) := by field_simp
    rw [he] at hm
    nlinarith only [hm]

/-- Uniform affine entropy–L1 bound for arbitrary real functions and
arbitrary real dual parameter, including the identically zero function. -/
theorem entropyFunctional_square_affine {n : ℕ} (g : Cube n → ℝ) (lam : ℝ) :
    lam*avg (fun x => g x^2) - Real.exp (lam-1)*(avg (fun x => |g x|))^2 ≤
      entropyFunctional (fun x => g x^2) := by
  have hv0 := avg_nonneg (fun x => g x^2) (fun x => sq_nonneg _)
  by_cases hv : avg (fun x => g x^2)=0
  · have hE := entropyFunctional_nonneg (fun x => sq_nonneg (g x))
    rw [hv,mul_zero]
    have hnon : 0 ≤ Real.exp (lam-1)*(avg (fun x => |g x|))^2 := by positivity
    linarith
  · have hvp : 0 < avg (fun x => g x^2) := lt_of_le_of_ne hv0 (Ne.symm hv)
    have ha := avg_abs_pos_of_avg_sq_pos g hvp
    have hs := mul_log_fenchel (lam := lam)
      (div_nonneg hv0 (sq_nonneg (avg (fun x => |g x|))))
    have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (avg (fun x => |g x|)))
    have hid : (avg (fun x => |g x|))^2*
        (avg (fun x => g x^2)/(avg (fun x => |g x|))^2) = avg (fun x => g x^2) := by
      field_simp
    have hE := entropyFunctional_square_log_lower g hvp
    have hsleft : (avg (fun x => |g x|))^2*(lam*(avg (fun x => g x^2)/(avg (fun x => |g x|))^2)-Real.exp (lam-1)) =
        lam*avg (fun x => g x^2)-Real.exp (lam-1)*(avg (fun x => |g x|))^2 := by
      rw [mul_sub]
      nlinarith only [congrArg (fun z : ℝ => lam*z) hid]
    have hsright : (avg (fun x => |g x|))^2*
        ((avg (fun x => g x^2)/(avg (fun x => |g x|))^2)*Real.log (avg (fun x => g x^2)/(avg (fun x => |g x|))^2)) =
        avg (fun x => g x^2)*Real.log (avg (fun x => g x^2)/(avg (fun x => |g x|))^2) := by
      rw [← mul_assoc,hid]
    rw [hsleft,hsright] at hm
    exact hm.trans hE

end
end CK
