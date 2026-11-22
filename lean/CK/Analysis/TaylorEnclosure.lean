module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic

/-! A sound centered second-order Taylor enclosure. Bounds on the second
 derivative hold on the entire interval, including its endpoints. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Analysis
noncomputable section

theorem taylor_lower_bound {f f₁ f₂ : ℝ → ℝ} {c r L D M x : ℝ}
    (hr : 0 ≤ r)
    (hf : ∀ y ∈ Icc (c-r) (c+r), HasDerivAt f (f₁ y) y)
    (hf₁ : ∀ y ∈ Icc (c-r) (c+r), HasDerivAt f₁ (f₂ y) y)
    (hsecond : ∀ y ∈ Icc (c-r) (c+r), |f₂ y| ≤ M)
    (hvalue : L ≤ f c) (hfirst : |f₁ c| ≤ D)
    (hx : x ∈ Icc (c-r) (c+r)) :
    L-D*r-M*r^2/2 ≤ f x := by
  have hc : c ∈ Icc (c-r) (c+r) := ⟨by linarith,by linarith⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans (hsecond c hc)
  have hD : 0 ≤ D := (abs_nonneg _).trans hfirst
  let G : ℝ → ℝ := fun y => f y+M/2*(y-c)^2
  let G₁ : ℝ → ℝ := fun y => f₁ y+M*(y-c)
  have hd (y : ℝ) (hy : y ∈ Icc (c-r) (c+r)) : HasDerivAt G (G₁ y) y := by
    apply ((hf y hy).add ((((hasDerivAt_id y).sub_const c).pow 2).const_mul (M/2))).congr_deriv
    dsimp [G₁]
    ring
  have hdd (y : ℝ) (hy : y ∈ Icc (c-r) (c+r)) : HasDerivAt G₁ (f₂ y+M) y := by
    apply ((hf₁ y hy).add (((hasDerivAt_id y).sub_const c).const_mul M)).congr_deriv
    simp
  have hconv : ConvexOn ℝ (Icc (c-r) (c+r)) G := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt) (f' := G₁)
      (f'' := fun y => f₂ y+M)
    · intro y hy
      exact (hd y (interior_subset hy)).hasDerivWithinAt
    · intro y hy
      exact (hdd y (interior_subset hy)).hasDerivWithinAt
    · intro y hy
      have hh := (abs_le.mp (hsecond y (interior_subset hy))).1
      linarith only [hh]
  have hdc : HasDerivAt G (f₁ c) c := by simpa only [G₁,sub_self,mul_zero,add_zero] using hd c hc
  have htangent : f c+f₁ c*(x-c)-M/2*(x-c)^2 ≤ f x := by
    rcases lt_trichotomy c x with hcx | hcx | hxc
    · have hh := hconv.le_slope_of_hasDerivAt hc hx hcx hdc
      rw [slope_def_field] at hh
      have hh' := (le_div_iff₀ (sub_pos.mpr hcx)).mp hh
      dsimp only [G] at hh'
      nlinarith only [hh']
    · subst x
      simp
    · have hh := hconv.slope_le_of_hasDerivAt hx hc hxc hdc
      rw [slope_def_field] at hh
      have hh' := (div_le_iff₀ (sub_pos.mpr hxc)).mp hh
      dsimp only [G] at hh'
      nlinarith only [hh']
  have hdist : |x-c| ≤ r := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hprod : |f₁ c*(x-c)| ≤ D*r := by
    rw [abs_mul]
    exact mul_le_mul hfirst hdist (abs_nonneg _) hD
  have hlin := (abs_le.mp hprod).1
  have hsquare : (x-c)^2 ≤ r^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).mpr hdist
  have hquad := mul_le_mul_of_nonneg_left hsquare hM
  nlinarith only [htangent,hvalue,hlin,hquad]

theorem taylor_positive {f f₁ f₂ : ℝ → ℝ} {c r L D M : ℝ}
    (hr : 0 ≤ r)
    (hf : ∀ y ∈ Icc (c-r) (c+r), HasDerivAt f (f₁ y) y)
    (hf₁ : ∀ y ∈ Icc (c-r) (c+r), HasDerivAt f₁ (f₂ y) y)
    (hsecond : ∀ y ∈ Icc (c-r) (c+r), |f₂ y| ≤ M)
    (hvalue : L ≤ f c) (hfirst : |f₁ c| ≤ D)
    (hmargin : 0 < L-D*r-M*r^2/2) :
    ∀ x ∈ Icc (c-r) (c+r), 0 < f x := by
  intro x hx
  exact hmargin.trans_le (taylor_lower_bound hr hf hf₁ hsecond hvalue hfirst hx)

end
end CK.Analysis
