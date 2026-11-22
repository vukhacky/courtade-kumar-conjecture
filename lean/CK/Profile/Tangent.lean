module

public import CK.Profile.Scalar

/-! The supporting-line bound in STOC `lem:clock-tangent`, in the source's
rational tangent parameter `t`. The proof differentiates a scalar potential
and proves its global minimum, rather than assuming inverse convexity. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

def profileAux (t : ℝ) : ℝ := Real.log 2 - Real.log (1-t^2) / 2

def tangentFactor (t : ℝ) : ℝ := t^2 / ((1-t^2) * profileAux t)

theorem gap_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < 1-t^2 := by
  nlinarith [ht.1, ht.2]

theorem profileAux_ge_half {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    (1/2 : ℝ) ≤ profileAux t := by
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hn : Real.log (1-t^2) ≤ 0 :=
    Real.log_nonpos (gap_pos ht).le (by nlinarith [sq_nonneg t])
  dsimp [profileAux]
  linarith

theorem profileAux_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 < profileAux t := by linarith [profileAux_ge_half ht]

theorem meanEntropy_add_slope {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    meanEntropy t + t*phiSlope t = profileAux t := by
  have hp : 1+t ≠ 0 := by linarith [ht.1]
  have hm : 1-t ≠ 0 := by linarith [ht.2]
  rw [meanEntropy, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    show 1-(1-t)/2 = (1+t)/2 by ring]
  simp only [Real.negMulLog_def, Real.log_div hp (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hm (by norm_num : (2 : ℝ) ≠ 0)]
  rw [profileAux, show 1-t^2 = (1+t)*(1-t) by ring, Real.log_mul hp hm]
  dsimp [phiSlope]
  ring

theorem hasDerivAt_profileAux {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt profileAux (t/(1-t^2)) t := by
  have h := ((((hasDerivAt_pow 2 t).const_sub 1).log
    (ne_of_gt (gap_pos ht))).div_const 2).const_sub (Real.log 2)
  apply h.congr_deriv
  simp
  ring

theorem hasDerivAt_tangentFactor {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt tangentFactor
      (t*(2*profileAux t-t^2)/((1-t^2)^2*(profileAux t)^2)) t := by
  have hdom : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have hg : 1-t^2 ≠ 0 := ne_of_gt (gap_pos hdom)
  have hL : profileAux t ≠ 0 := ne_of_gt (profileAux_pos hdom)
  have h := (hasDerivAt_pow 2 t).div
    (((hasDerivAt_pow 2 t).const_sub 1).mul (hasDerivAt_profileAux hdom))
    (mul_ne_zero hg hL)
  apply h.congr_deriv
  dsimp only [Pi.mul_apply]
  field_simp [hg, hL]
  ring

theorem tangentFactor_monotone : MonotoneOn tangentFactor (Ioo (0 : ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1)
    (fun t ht => (hasDerivAt_tangentFactor ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hasDerivAt_tangentFactor (by simpa only [interior_Ioo] using ht)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ioo] using ht
    have hL := profileAux_ge_half ⟨by linarith [ht'.1], ht'.2⟩
    apply div_nonneg
    · apply mul_nonneg ht'.1.le
      nlinarith [ht'.1, ht'.2]
    · positivity

def tangentPotential (t s : ℝ) : ℝ := phiSlope s + tangentFactor t * (meanEntropy s / s)

theorem hasDerivAt_tangentPotential (t : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (tangentPotential t)
      ((tangentFactor s-tangentFactor t)*profileAux s/s^2) s := by
  have hdom : s ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
  have hg : 1-s^2 ≠ 0 := ne_of_gt (gap_pos hdom)
  have hL : profileAux s ≠ 0 := ne_of_gt (profileAux_pos hdom)
  have hs0 : s ≠ 0 := ne_of_gt hs.1
  have h := (hasDerivAt_phiSlope hdom).add
    (((hasDerivAt_meanEntropy hdom).div (hasDerivAt_id s) hs0).const_mul (tangentFactor t))
  apply h.congr_deriv
  dsimp only [id_eq]
  simp only [mul_one]
  rw [show -phiSlope s*s-meanEntropy s = -profileAux s by
    nlinarith [meanEntropy_add_slope hdom]]
  change 1/(1-s^2)+tangentFactor t*(-profileAux s/s^2) =
    (s^2/((1-s^2)*profileAux s)-tangentFactor t)*profileAux s/s^2
  field_simp [hg, hL, hs0]
  ring

theorem tangentPotential_min {t s : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) : tangentPotential t t ≤ tangentPotential t s := by
  rcases le_total s t with hst | hts
  · have hdom : Icc s t ⊆ Ioo (0 : ℝ) 1 := fun u hu =>
      ⟨lt_of_lt_of_le hs.1 hu.1, lt_of_le_of_lt hu.2 ht.2⟩
    have hm : AntitoneOn (tangentPotential t) (Icc s t) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t)
        (fun u hu => (hasDerivAt_tangentPotential t (hdom hu)).continuousAt.continuousWithinAt)
      · intro u hu
        exact (hasDerivAt_tangentPotential t (hdom (interior_subset hu))).hasDerivWithinAt
      · intro u hu
        have hu' := interior_subset hu
        have huD := hdom hu'
        apply div_nonpos_of_nonpos_of_nonneg
        · apply mul_nonpos_of_nonpos_of_nonneg
          · exact sub_nonpos.mpr (tangentFactor_monotone huD ht hu'.2)
          · exact (profileAux_pos ⟨by linarith [huD.1], huD.2⟩).le
        · exact sq_nonneg u
    exact hm ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  · have hdom : Icc t s ⊆ Ioo (0 : ℝ) 1 := fun u hu =>
      ⟨lt_of_lt_of_le ht.1 hu.1, lt_of_le_of_lt hu.2 hs.2⟩
    have hm : MonotoneOn (tangentPotential t) (Icc t s) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t s)
        (fun u hu => (hasDerivAt_tangentPotential t (hdom hu)).continuousAt.continuousWithinAt)
      · intro u hu
        exact (hasDerivAt_tangentPotential t (hdom (interior_subset hu))).hasDerivWithinAt
      · intro u hu
        have hu' := interior_subset hu
        have huD := hdom hu'
        apply div_nonneg
        · apply mul_nonneg
          · exact sub_nonneg.mpr (tangentFactor_monotone ht huD hu'.1)
          · exact (profileAux_pos ⟨by linarith [huD.1], huD.2⟩).le
        · exact sq_nonneg u
    exact hm ⟨le_rfl, hts⟩ ⟨hts, le_rfl⟩ hts

/-- The supporting line parameterized by the sign mean `t`, with height `artanh t`. -/
theorem profile_tangent {e q t : ℝ} (he : 0 < e) (hq : 0 < q)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    q*Real.artanh t + (q*meanEntropy t/t-e)*tangentFactor t ≤ profile e q := by
  have hr := profilePoint_spec he hq
  have hpot := mul_le_mul_of_nonneg_left (tangentPotential_min ht hr.1) hq.le
  have hroot : q*(meanEntropy (profilePoint e q)/profilePoint e q) = e := by
    rw [← mul_div_assoc, ← hr.2]
    exact mul_div_cancel_right₀ e (ne_of_gt hr.1.1)
  dsimp [tangentPotential] at hpot
  rw [phiSlope_eq_artanh ⟨by linarith [ht.1], ht.2⟩,
    phiSlope_eq_artanh ⟨by linarith [hr.1.1], hr.1.2⟩] at hpot
  calc
    q*Real.artanh t + (q*meanEntropy t/t-e)*tangentFactor t =
        q*(Real.artanh t + tangentFactor t*(meanEntropy t/t))-tangentFactor t*e := by ring
    _ ≤ q*(Real.artanh (profilePoint e q) +
          tangentFactor t*(meanEntropy (profilePoint e q)/profilePoint e q))-
          tangentFactor t*e := sub_le_sub_right hpot _
    _ = profile e q := by
      unfold profile
      calc
        _ = q * Real.artanh (profilePoint e q) +
            tangentFactor t * (q * (meanEntropy (profilePoint e q) / profilePoint e q)) -
            tangentFactor t * e := by ring
        _ = _ := by rw [hroot]; ring

end
end CK.Profile
