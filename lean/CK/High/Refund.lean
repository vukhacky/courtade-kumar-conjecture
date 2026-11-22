module

public import CK.High.Remainder

/-! Joint convexity of the exact entropy-dependent arcsine refund.
The perspective inequality is obtained directly from the already-proved
entropy-profile convexity and the convex increasing remainder. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def edgeRefund (e d : ℝ) : ℝ := d*arcsineRemainder (edgeHeight e d)

@[simp] theorem edgeRefund_zero (e : ℝ) : edgeRefund e 0=0 := by simp [edgeRefund]

theorem edgeRefund_nonneg {e d : ℝ} (he : 0 < e) (hd : 0 ≤ d) : 0 ≤ edgeRefund e d :=
  mul_nonneg hd (arcsineRemainder_nonneg (edgeHeight_nonneg he hd))

theorem edgeRefund_antitone_left {e h d : ℝ} (he : 0 < e) (heh : e ≤ h) (hd : 0 ≤ d) :
    edgeRefund h d ≤ edgeRefund e d := by
  apply mul_le_mul_of_nonneg_left ?_ hd
  exact arcsineRemainder_strictMono.monotoneOn (edgeHeight_nonneg (he.trans_le heh) hd)
    (edgeHeight_nonneg he hd) (edgeHeight_antitone_left he heh hd)

theorem edgeRefund_mono_right {e d q : ℝ} (he : 0 < e) (hd : 0 ≤ d) (hdq : d ≤ q) :
    edgeRefund e d ≤ edgeRefund e q := by
  have hh := edgeHeight_mono_right he hd hdq
  have hR := arcsineRemainder_strictMono.monotoneOn (edgeHeight_nonneg he hd)
    (edgeHeight_nonneg he (hd.trans hdq)) hh
  exact mul_le_mul hdq hR (arcsineRemainder_nonneg (edgeHeight_nonneg he hd)) (hd.trans hdq)

theorem edgeRefund_convex_combination {e₁ e₂ d₁ d₂ a b : ℝ}
    (he₁ : 0 < e₁) (he₂ : 0 < e₂) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    edgeRefund (a*e₁+b*e₂) (a*d₁+b*d₂) ≤ a*edgeRefund e₁ d₁+b*edgeRefund e₂ d₂ := by
  have he : 0 < a*e₁+b*e₂ := by
    rcases ha.eq_or_lt with rfl | ha
    · have hb1 : b=1 := by linarith
      simpa [hb1] using he₂
    · exact add_pos_of_pos_of_nonneg (mul_pos ha he₁) (mul_nonneg hb he₂.le)
  have hd : 0 ≤ a*d₁+b*d₂ := add_nonneg (mul_nonneg ha hd₁) (mul_nonneg hb hd₂)
  rcases hd.eq_or_lt with hd0 | hd
  · rw [←hd0,edgeRefund_zero]
    exact add_nonneg (mul_nonneg ha (edgeRefund_nonneg he₁ hd₁))
      (mul_nonneg hb (edgeRefund_nonneg he₂ hd₂))
  let α := a*d₁/(a*d₁+b*d₂)
  let β := b*d₂/(a*d₁+b*d₂)
  have hα : 0 ≤ α := div_nonneg (mul_nonneg ha hd₁) hd.le
  have hβ : 0 ≤ β := div_nonneg (mul_nonneg hb hd₂) hd.le
  have hαβ : α+β=1 := by dsimp [α,β]; field_simp
  have hP := Profile.profile_convex_combination he₁ he₂ hd₁ hd₂ ha hb hab
  simp only [profile_eq_mul_edgeHeight] at hP
  have hheight : edgeHeight (a*e₁+b*e₂) (a*d₁+b*d₂) ≤
      α*edgeHeight e₁ d₁+β*edgeHeight e₂ d₂ := by
    apply le_of_mul_le_mul_left (a := a*d₁+b*d₂) ?_ hd
    dsimp [α,β]
    field_simp
    nlinarith only [hP]
  have hheight0 := edgeHeight_nonneg he hd.le
  have hheight10 := edgeHeight_nonneg he₁ hd₁
  have hheight20 := edgeHeight_nonneg he₂ hd₂
  have hheightavg0 : 0 ≤ α*edgeHeight e₁ d₁+β*edgeHeight e₂ d₂ := by positivity
  have hmono := arcsineRemainder_strictMono.monotoneOn hheight0 hheightavg0 hheight
  have hconv := arcsineRemainder_convex.2 hheight10 hheight20 hα hβ hαβ
  simp only [smul_eq_mul] at hconv
  have hmul := mul_le_mul_of_nonneg_left (hmono.trans hconv) hd.le
  unfold edgeRefund
  dsimp [α,β] at hmul
  have heq : (a*d₁+b*d₂)*(a*d₁/(a*d₁+b*d₂)*arcsineRemainder (edgeHeight e₁ d₁)+
      b*d₂/(a*d₁+b*d₂)*arcsineRemainder (edgeHeight e₂ d₂)) =
      a*(d₁*arcsineRemainder (edgeHeight e₁ d₁))+b*(d₂*arcsineRemainder (edgeHeight e₂ d₂)) := by
    field_simp
  rw [heq] at hmul
  exact hmul

theorem edgeRefund_signed_convex_combination {e₁ e₂ q₁ q₂ a b : ℝ}
    (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    edgeRefund (a*e₁+b*e₂) |a*q₁+b*q₂| ≤
      a*edgeRefund e₁ |q₁|+b*edgeRefund e₂ |q₂| := by
  have he : 0 < a*e₁+b*e₂ := by
    rcases ha.eq_or_lt with rfl | ha
    · have hb1 : b=1 := by linarith
      simpa [hb1] using he₂
    · exact add_pos_of_pos_of_nonneg (mul_pos ha he₁) (mul_nonneg hb he₂.le)
  have hq : |a*q₁+b*q₂| ≤ a*|q₁|+b*|q₂| := by
    calc
      _ ≤ |a*q₁|+|b*q₂| := abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
  exact (edgeRefund_mono_right he (abs_nonneg _) hq).trans
    (edgeRefund_convex_combination he₁ he₂ (abs_nonneg _) (abs_nonneg _) ha hb hab)

theorem convexOn_edgeRefund_signed :
    ConvexOn ℝ {z : ℝ × ℝ | 0 < z.1} (fun z => edgeRefund z.1 |z.2|) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    change 0 < a*x.1+b*y.1
    rcases ha.eq_or_lt with rfl | ha
    · have hb1 : b=1 := by linarith
      simpa [hb1] using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos ha hx) (mul_nonneg hb hy.le)
  · intro x hx y hy a b ha hb hab
    exact edgeRefund_signed_convex_combination hx hy ha hb hab

theorem edgeRefund_profileHeight (ρ a : ℝ) :
    edgeRefund (signEntropy ρ) (ρ*a) = ρ*a*arcsineRemainder (profileHeight ρ a) := rfl

/-- Joint continuity includes zero edge size, inside the positive-entropy strip. -/
theorem continuousOn_edgeRefund_signed :
    ContinuousOn (fun z : ℝ × ℝ => edgeRefund z.1 |z.2|) {z | 0 < z.1} := by
  exact ConvexOn.continuousOn (isOpen_lt continuous_const continuous_fst) convexOn_edgeRefund_signed

end
end CK
