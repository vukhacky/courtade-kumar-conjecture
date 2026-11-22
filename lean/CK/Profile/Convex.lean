module

public import CK.Profile.Tangent
public import Mathlib.Analysis.Convex.Jensen

/-! Joint convexity of the entropy profile follows directly from its
proved affine supporting planes. Zero edge sizes are handled explicitly. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

theorem tangentFactor_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < tangentFactor t := by
  have hd : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  exact div_pos (sq_pos_of_pos ht.1) (mul_pos (gap_pos hd) (profileAux_pos hd))

theorem profile_nonneg {e q : ℝ} (he : 0 < e) (hq : 0 ≤ q) : 0 ≤ profile e q := by
  obtain rfl | hq := hq.eq_or_lt
  · simp
  · exact (profile_pos he hq).le

theorem profile_tangent_nonneg {e q t : ℝ} (he : 0 < e) (hq : 0 ≤ q)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    q*Real.artanh t + (q*meanEntropy t/t-e)*tangentFactor t ≤ profile e q := by
  obtain rfl | hq := hq.eq_or_lt
  · simp only [zero_mul, zero_div, zero_sub, zero_add, profile_zero_right]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr he.le) (tangentFactor_pos ht).le
  · exact profile_tangent he hq ht

theorem profile_root_support {e q : ℝ} (he : 0 < e) (hq : 0 < q) :
    profile e q = q*Real.artanh (profilePoint e q) +
      (q*meanEntropy (profilePoint e q)/profilePoint e q-e)*
        tangentFactor (profilePoint e q) := by
  have hs := profilePoint_spec he hq
  have heq : q*meanEntropy (profilePoint e q)/profilePoint e q = e := by
    rw [← hs.2]
    exact mul_div_cancel_right₀ e (ne_of_gt hs.1.1)
  rw [heq, sub_self, zero_mul, add_zero]
  rfl

theorem profile_mono_right {e q r : ℝ} (he : 0 < e) (hq : 0 ≤ q) (hqr : q ≤ r) :
    profile e q ≤ profile e r := by
  obtain rfl | hq := hq.eq_or_lt
  · simpa using profile_nonneg he hqr
  have hs := (profilePoint_spec he hq).1
  have hline := profile_tangent_nonneg he (hq.le.trans hqr) hs
  have hv := (Real.artanh_pos hs).le
  have hH := (meanEntropy_pos ⟨by linarith [hs.1], hs.2⟩).le
  have hK := (tangentFactor_pos hs).le
  have hcoef : 0 ≤ Real.artanh (profilePoint e q) +
      meanEntropy (profilePoint e q)/profilePoint e q*tangentFactor (profilePoint e q) :=
    add_nonneg hv (mul_nonneg (div_nonneg hH hs.1.le) hK)
  have hh := mul_nonneg (sub_nonneg.mpr hqr) hcoef
  rw [profile_root_support he hq]
  simp only [div_eq_mul_inv] at hline hh ⊢
  nlinarith only [hline, hh]

theorem profile_convex_combination {e₁ e₂ q₁ q₂ a b : ℝ}
    (he₁ : 0 < e₁) (he₂ : 0 < e₂) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    profile (a*e₁+b*e₂) (a*q₁+b*q₂) ≤ a*profile e₁ q₁+b*profile e₂ q₂ := by
  have he : 0 < a*e₁+b*e₂ := by
    rcases lt_or_eq_of_le ha with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' he₁) (mul_nonneg hb he₂.le)
    · have ha0 : a = 0 := ha'.symm
      have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using he₂
  have hq : 0 ≤ a*q₁+b*q₂ := add_nonneg (mul_nonneg ha hq₁) (mul_nonneg hb hq₂)
  obtain hq0 | hq := hq.eq_or_lt
  · rw [← hq0, profile_zero_right]
    exact add_nonneg (mul_nonneg ha (profile_nonneg he₁ hq₁))
      (mul_nonneg hb (profile_nonneg he₂ hq₂))
  let t := profilePoint (a*e₁+b*e₂) (a*q₁+b*q₂)
  have ht : t ∈ Ioo (0 : ℝ) 1 := (profilePoint_spec he hq).1
  have h₁ := mul_le_mul_of_nonneg_left (profile_tangent_nonneg he₁ hq₁ ht) ha
  have h₂ := mul_le_mul_of_nonneg_left (profile_tangent_nonneg he₂ hq₂ ht) hb
  rw [profile_root_support he hq]
  change (a*q₁+b*q₂)*Real.artanh t +
    ((a*q₁+b*q₂)*meanEntropy t/t-(a*e₁+b*e₂))*tangentFactor t ≤ _
  simp only [div_eq_mul_inv] at h₁ h₂ ⊢
  nlinarith only [h₁, h₂]

theorem profile_signed_convex_combination {e₁ e₂ q₁ q₂ a b : ℝ}
    (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    profile (a*e₁+b*e₂) |a*q₁+b*q₂| ≤
      a*profile e₁ |q₁|+b*profile e₂ |q₂| := by
  have he : 0 < a*e₁+b*e₂ := by
    rcases lt_or_eq_of_le ha with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' he₁) (mul_nonneg hb he₂.le)
    · have ha0 : a = 0 := ha'.symm
      have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using he₂
  have hq : |a*q₁+b*q₂| ≤ a*|q₁|+b*|q₂| := by
    calc
      _ ≤ |a*q₁|+|b*q₂| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  exact (profile_mono_right he (abs_nonneg _) hq).trans
    (profile_convex_combination he₁ he₂ (abs_nonneg _) (abs_nonneg _) ha hb hab)

theorem convexOn_profile_signed :
    ConvexOn ℝ {z : ℝ × ℝ | 0 < z.1} (fun z => profile z.1 |z.2|) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    change 0 < a*x.1+b*y.1
    rcases lt_or_eq_of_le ha with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
    · have ha0 : a = 0 := ha'.symm
      have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hy
  · intro x hx y hy a b ha hb hab
    exact profile_signed_convex_combination hx hy ha hb hab

theorem profile_scaling {e c q : ℝ} (he : 0 < e) (hc : 0 < c) (hq : 0 ≤ q) :
    profile e (c*q) = c*profile (e/c) q := by
  obtain rfl | hq := hq.eq_or_lt
  · simp
  have hec : 0 < e/c := div_pos he hc
  have hs := profilePoint_spec hec hq
  have heq : profilePoint (e/c) q = profilePoint e (c*q) := by
    apply profilePoint_unique he (mul_pos hc hq) hs.1
    have h := congrArg (fun x : ℝ => c*x) hs.2
    field_simp [ne_of_gt hc] at h
    nlinarith only [h]
  unfold profile
  rw [← heq]
  ring

end
end CK.Profile
