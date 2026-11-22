module

public import CK.Profile.Clock
public import Mathlib.Analysis.Convex.Mul

/-! Convexity of integrated clocks for pointwise concave envelope families.
All improper-endpoint integrability obligations are discharged by Clock. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory
namespace CK.Profile
noncomputable section

theorem convexOn_clock_family {I : Set ℝ} (hI : Convex ℝ I)
    (Q : ℝ → ℝ → ℝ)
    (hconc : ∀ e, 0 < e → ConcaveOn ℝ I (fun x => Q x e))
    (hc : ∀ x ∈ I, ContinuousOn (Q x) (Ioi (0 : ℝ)))
    (ha : ∀ x ∈ I, AntitoneOn (Q x) (Ioi (0 : ℝ)))
    (hp : ∀ x ∈ I, ∀ e, 0 < e → 0 < Q x e)
    {Y : ℝ} (hY : 0 ≤ Y) : ConvexOn ℝ I (fun x => clock (Q x) Y) := by
  obtain rfl | hY := hY.eq_or_lt
  · simpa only [clock_zero] using (convexOn_const (c := (0 : ℝ)) hI)
  refine ⟨hI, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  have hz := hI hx hy hα hβ hαβ
  have hix := clock_integrable (hc x hx) (ha x hx) (hp x hx) hY
  have hiy := clock_integrable (hc y hy) (ha y hy) (hp y hy) hY
  have hiz := clock_integrable (hc _ hz) (ha _ hz) (hp _ hz) hY
  have hpoint (e : ℝ) (he : e ∈ Ioo (0 : ℝ) Y) :
      1/(e+Q (α*x+β*y) e) ≤ α*(1/(e+Q x e))+β*(1/(e+Q y e)) := by
    have hqx := hp x hx e he.1
    have hqy := hp y hy e he.1
    have hq := (hconc e he.1).2 hx hy hα hβ hαβ
    simp only [smul_eq_mul] at hq
    have hdenx : 0 < e+Q x e := add_pos he.1 hqx
    have hdeny : 0 < e+Q y e := add_pos he.1 hqy
    have hcombo : 0 < α*(e+Q x e)+β*(e+Q y e) := by
      have hmin : min (e+Q x e) (e+Q y e) > 0 := lt_min hdenx hdeny
      have h₁ := mul_le_mul_of_nonneg_left (min_le_left (e+Q x e) (e+Q y e)) hα
      have h₂ := mul_le_mul_of_nonneg_left (min_le_right (e+Q x e) (e+Q y e)) hβ
      nlinarith only [hmin, h₁, h₂, congrArg (fun z : ℝ => z*min (e+Q x e) (e+Q y e)) hαβ]
    have hs : α*(e+Q x e)+β*(e+Q y e) ≤ e+Q (α*x+β*y) e := by
      nlinarith only [hq, congrArg (fun z : ℝ => z*e) hαβ]
    have hinv := (convexOn_zpow (-1 : ℤ) :
      ConvexOn ℝ (Ioi (0 : ℝ)) (fun z : ℝ => z^(-1 : ℤ))).2
      hdenx hdeny hα hβ hαβ
    simp only [smul_eq_mul, zpow_neg_one, ← one_div] at hinv
    exact (one_div_le_one_div_of_le hcombo hs).trans hinv
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo hY.le hiz
    ((hix.const_mul α).add (hiy.const_mul β)) hpoint
  rw [intervalIntegral.integral_add (hix.const_mul α) (hiy.const_mul β),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  simpa only [clock, smul_eq_mul] using hi

/-- A convex clock family is bounded by the larger of its two endpoint
clocks. This is the exact finite-vertex reduction used by the middle bands. -/
theorem clock_family_le_endpoint_max {a b x Y : ℝ} (hab : a ≤ b)
    (hx : x ∈ Icc a b) {Q : ℝ → ℝ → ℝ}
    (hconv : ConvexOn ℝ (Icc a b) (fun x => clock (Q x) Y)) :
    clock (Q x) Y ≤ max (clock (Q a) Y) (clock (Q b) Y) := by
  obtain rfl | hab := hab.eq_or_lt
  · have hxa : x=a := le_antisymm hx.2 hx.1
    simp [hxa]
  have hd : 0 < b-a := sub_pos.mpr hab
  have hw₁ : 0 ≤ (b-x)/(b-a) := div_nonneg (sub_nonneg.mpr hx.2) hd.le
  have hw₂ : 0 ≤ (x-a)/(b-a) := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have hsum : (b-x)/(b-a)+(x-a)/(b-a)=1 := by field_simp; ring
  have harg : ((b-x)/(b-a))*a+((x-a)/(b-a))*b=x := by field_simp; ring
  have h := hconv.2 (show a ∈ Icc a b from ⟨le_rfl,hab.le⟩)
    (show b ∈ Icc a b from ⟨hab.le,le_rfl⟩) hw₁ hw₂ hsum
  simp only [smul_eq_mul, harg] at h
  have h₁ := mul_le_mul_of_nonneg_left (le_max_left (clock (Q a) Y) (clock (Q b) Y)) hw₁
  have h₂ := mul_le_mul_of_nonneg_left (le_max_right (clock (Q a) Y) (clock (Q b) Y)) hw₂
  nlinarith only [h,h₁,h₂,congrArg (fun z : ℝ => z*max (clock (Q a) Y) (clock (Q b) Y)) hsum]

end
end CK.Profile
