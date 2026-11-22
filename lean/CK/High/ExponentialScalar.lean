module

public import CK.High.BinaryBounds

/-! A uniform analytic proof of the local entropy threshold for every
positive `d ≤ 1/9`.  The parameter is continuous; no sampling is used. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def localNoiseProbability (d : ℝ) : ℝ := d^2/(1+d^2)

theorem localNoiseProbability_bounds {d : ℝ} (hd : d ∈ Set.Ioc (0 : ℝ) (1/9)) :
    0 < localNoiseProbability d ∧ localNoiseProbability d ≤ d^2 ∧
      d^2*(1-d^2) ≤ localNoiseProbability d ∧ localNoiseProbability d < 1 := by
  have hd2 : 0 < d^2 := sq_pos_of_pos hd.1
  have hden : 0 < 1+d^2 := by positivity
  unfold localNoiseProbability
  refine ⟨div_pos hd2 hden, ?_, ?_, ?_⟩
  · exact (div_le_iff₀ hden).2 (by nlinarith only [sq_nonneg (d^2)])
  · apply (le_div_iff₀ hden).2
    nlinarith only [sq_nonneg (d^3)]
  · exact (div_lt_one hden).2 (by linarith)

theorem binEntropy_localNoiseProbability_upper {d : ℝ}
    (hd : d ∈ Set.Ioc (0 : ℝ) (1/9)) :
    Real.binEntropy (localNoiseProbability d) ≤
      localNoiseProbability d * (2*(-Real.log d)+d^2+1) := by
  have hp := localNoiseProbability_bounds hd
  have hlog : Real.log (localNoiseProbability d) =
      2*Real.log d - Real.log (1+d^2) := by
    rw [localNoiseProbability, Real.log_div (ne_of_gt (sq_pos_of_pos hd.1))
      (by positivity), Real.log_pow]
    norm_num
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1+d^2 by positivity)
  have hb := binEntropy_upper_log (show localNoiseProbability d ∈ Ico (0 : ℝ) 1 from ⟨hp.1.le,hp.2.2.2⟩)
  rw [hlog] at hb
  have hm := mul_le_mul_of_nonneg_left hl hp.1.le
  nlinarith only [hb,hm]

theorem binEntropy_local_endpoint_lower {d : ℝ}
    (hd : d ∈ Set.Ioc (0 : ℝ) (1/9)) :
    d * (-Real.log d+1-d + d*(1-d^2)*(1-2*d)*(-Real.log d-(7/3)*d)) ≤
      Real.binEntropy (d+localNoiseProbability d*(1-2*d)) := by
  let p := localNoiseProbability d
  let q := d+p*(1-2*d)
  have hp := localNoiseProbability_bounds hd
  have hd2 : d^2 ≤ (1/9 : ℝ)^2 := pow_le_pow_left₀ hd.1.le hd.2 2
  have hfac : 0 ≤ 1-2*d := by linarith [hd.2]
  have hq0 : d ≤ q := by
    have hm := mul_nonneg hp.1.le hfac
    dsimp [q,p]
    linarith only [hm]
  have hq1 : q ≤ d+d^2 := by
    have hm := mul_le_mul_of_nonneg_left hp.2.1 hfac
    have hf : p*(1-2*d) ≤ d^2 := by dsimp [p]; nlinarith only [hm,hd.1,hd2]
    dsimp [q]
    linarith
  have hq : q ∈ Icc d (d+d^2) := ⟨hq0,hq1⟩
  have hint (x : ℝ) (hx : x ∈ interior (Icc d (d+d^2))) : x ≠ 0 ∧ x ≠ 1 := by
    have hx' : x ∈ Icc d (d+d^2) := interior_subset hx
    constructor <;> nlinarith only [hx'.1,hx'.2,hd.1,hd.2,hd2]
  have hgrowth := (convex_Icc d (d+d^2)).mul_sub_le_image_sub_of_le_deriv
    Real.binEntropy_continuous.continuousOn
    (fun x hx => (Real.hasDerivAt_binEntropy (hint x hx).1 (hint x hx).2).differentiableAt.differentiableWithinAt)
    (C := -Real.log d-(7/3)*d)
    (fun x hx => by rw [Real.deriv_binEntropy]; exact binEntropy_deriv_small_lower hd (interior_subset hx))
    d (show d ∈ Icc d (d+d^2) by constructor; rfl; nlinarith only [sq_nonneg d])
    q hq hq0
  have hbase := binEntropy_lower_log (show d ∈ Ico (0 : ℝ) 1 by constructor; exact hd.1.le; linarith [hd.2])
  have hslope : 0 ≤ -Real.log d-(7/3)*d := by linarith [small_delta_log_lower hd,hd.2]
  have hm := mul_le_mul_of_nonneg_right hp.2.2.1 (mul_nonneg hfac hslope)
  dsimp [q,p] at hgrowth
  nlinarith only [hgrowth,hbase,hm]

/-- The polynomial remainder in the source's analytic local estimate is
nonnegative on the complete interval `0 ≤ d ≤ 1/9`, for every `u ≥ 0`. -/
theorem exponential_local_polynomial {d u : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (1/9)) (hu : 0 ≤ u) :
    1-(2*u+4)*d-4*d^2 ≤
      2*(1-d^2)*(u+1-d+d*(1-d^2)*(1-2*d)*(u-(7/3)*d)) -
        (1+2*d-4*d^2)*(2*u+d^2+1) := by
  have hd3 : d^3 ≤ (1/9 : ℝ)^3 := pow_le_pow_left₀ hd.1 hd.2 3
  have hd4 : d^4 ≤ (1/9 : ℝ)^4 := pow_le_pow_left₀ hd.1 hd.2 4
  have hc : 0 ≤ 1-2*d+4*d^2+d^3-2*d^4 := by
    nlinarith only [hd.2,hd4,sq_nonneg d,pow_nonneg hd.1 3]
  have hb : 0 ≤ 1+28*d+40*d^2-56*d^3-14*d^4+28*d^5 := by
    nlinarith only [hd.1,hd3,hd4,sq_nonneg d,pow_nonneg hd.1 5]
  have h := mul_nonneg (sq_nonneg d) (add_nonneg (mul_nonneg (by linarith : 0 ≤ 2*u) hc)
    (div_nonneg hb (by norm_num : (0 : ℝ) ≤ 3)))
  nlinarith only [h]

/-- Strictly positive local deficit at the exponential coefficient. -/
theorem localDeficit_exponential_parameter {d : ℝ}
    (hd : d ∈ Ioc (0 : ℝ) (1/9)) :
    0 < localDeficit (1-2*localNoiseProbability d) (1-2*d) := by
  let p := localNoiseProbability d
  let u := -Real.log d
  let A := u+1-d+d*(1-d^2)*(1-2*d)*(u-(7/3)*d)
  let B := 2*u+d^2+1
  have hp := localNoiseProbability_bounds hd
  have hd0 : 0 < d := hd.1
  have hp0 : 0 < p := hp.1
  have hp1 : p < 1 := hp.2.2.2
  have hcomp : 0 ≤ 1-p := by linarith
  have hp2 : p ≤ d^2 := hp.2.1
  have hd2 : d^2 ≤ (1/9 : ℝ)^2 := pow_le_pow_left₀ hd.1.le hd.2 2
  have hu : 2 ≤ u := small_delta_log_lower hd
  have hA : 0 ≤ A := by
    have ha := mul_nonneg (mul_nonneg (mul_nonneg hd.1.le
      (by nlinarith only [hd2] : 0 ≤ 1-d^2))
      (by linarith [hd.2] : 0 ≤ 1-2*d))
      (by linarith [hd.2] : 0 ≤ u-(7/3)*d)
    dsimp [A]
    linarith only [ha,hu,hd.2]
  have hB : 0 ≤ B := by dsimp [B]; nlinarith only [hu,sq_nonneg d]
  have hq := binEntropy_local_endpoint_lower hd
  change d*A ≤ Real.binEntropy (d+p*(1-2*d)) at hq
  have he := binEntropy_localNoiseProbability_upper hd
  change Real.binEntropy p ≤ p*B at he
  have hc0 : 0 ≤ 2*d+4*p*(1-p)*(1-2*d) := by
    have hfac : 0 ≤ 1-2*d := by linarith [hd.2]
    positivity
  have hqmul := mul_le_mul_of_nonneg_left hq
    (by positivity : 0 ≤ 4*p*(1-p))
  have hemul := mul_le_mul_of_nonneg_left he hc0
  have hpdelta : p*(1-p) ≤ d^2 := by
    have hpval : 0 ≤ p^2 := sq_nonneg p
    nlinarith only [hp2,hpval]
  have hcoef : 2*d+4*p*(1-p)*(1-2*d) ≤ 2*d*(1+2*d-4*d^2) := by
    have hm := mul_le_mul_of_nonneg_right hpdelta (by linarith [hd.2] : 0 ≤ 1-2*d)
    nlinarith only [hm]
  have hcoefmul := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hp0.le hB)
  have hAmul := mul_le_mul_of_nonneg_left (show 1-d^2 ≤ 1-p by linarith)
    (by positivity : 0 ≤ 4*p*d*A)
  have hpoly := exponential_local_polynomial ⟨hd.1.le,hd.2⟩ (by linarith : 0 ≤ u)
  change 1-(2*u+4)*d-4*d^2 ≤ 2*(1-d^2)*A-(1+2*d-4*d^2)*B at hpoly
  have hmargin := small_delta_margin hd
  change (17/1000 : ℝ) < 1-(2*u+4)*d-4*d^2 at hmargin
  have hstrict : 0 < 2*d*p*(2*(1-d^2)*A-(1+2*d-4*d^2)*B) := by
    exact mul_pos (by positivity) (by linarith)
  have hid : localDeficit (1-2*p) (1-2*d) =
      4*p*(1-p)*Real.binEntropy (d+p*(1-2*d)) -
        (2*d+4*p*(1-p)*(1-2*d))*Real.binEntropy p := by
    unfold localDeficit signEntropy
    rw [show (1-(1-2*p)*(1-2*d))/2 = d+p*(1-2*d) by ring,
      show (1-(1-2*p))/2 = p by ring]
    ring
  change 0 < localDeficit (1-2*p) (1-2*d)
  rw [hid]
  nlinarith only [hqmul,hemul,hcoefmul,hAmul,hstrict]

end
end CK
