module

public import CK.Profile.Squared
public import CK.Profile.ClockDynamics
public import CK.Low.OddLift

/-! A capped-coefficient entropy envelope from concavity in the squared argument over the full coefficient interval. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Set
namespace CK.Profile
noncomputable section

theorem profile_ge_squared_chord {e a c : ℝ} (he : 0 < e) (hc : 0 < c)
    (ha : 0 ≤ a) (hac : a ≤ c) :
    (a^2/c^2)*profile e c ≤ profile e a := by
  have hc2 := sq_pos_of_pos hc
  have hasq : a^2 ≤ c^2 := sq_le_sq₀ ha hc.le |>.2 hac
  have hratio : a^2/c^2 ≤ 1 := (div_le_one hc2).2 hasq
  have h := (concaveOn_profile_sqrt he).2
    (show (0 : ℝ) ∈ Ici (0 : ℝ) from le_rfl)
    (show c^2 ∈ Ici (0 : ℝ) from hc2.le)
    (show 0 ≤ 1-a^2/c^2 by linarith) (div_nonneg (sq_nonneg a) hc2.le)
    (show (1-a^2/c^2)+(a^2/c^2)=1 by ring)
  have harg : (a^2/c^2)*c^2=a^2 := div_mul_cancel₀ _ (ne_of_gt hc2)
  simpa only [smul_eq_mul, harg, Real.sqrt_zero, profile_zero_right, mul_zero,
    zero_add, Real.sqrt_sq ha, Real.sqrt_sq hc.le] using h

theorem singletonProfile_ge_capped_weight {n : ℕ} (f : BooleanFunction n)
    {e c : ℝ} (he : 0 < e) (hc : 0 < c)
    (hcap : ∀ i : Fin n, |fourier (lift f) {i}| ≤ c) :
    fourierWeight (lift f) 1/c^2*profile e c ≤ singletonProfile f e := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    profile_ge_squared_chord he hc (abs_nonneg (fourier (lift f) {i})) (hcap i))
  simpa only [sq_abs, ← Finset.sum_mul, ← Finset.sum_div, ← fourierWeight_one,
    singletonProfile] using h

theorem singletonProfile_ge_capped_envelope {n : ℕ} (f : BooleanFunction n)
    {e c w : ℝ} (he : 0 < e) (hc : 0 < c)
    (hcap : ∀ i : Fin n, |fourier (lift f) {i}| ≤ c)
    (hW : w*c^2 ≤ fourierWeight (lift f) 1) :
    w*profile e c ≤ singletonProfile f e := by
  have hw : w ≤ fourierWeight (lift f) 1/c^2 := (le_div_iff₀ (sq_pos_of_pos hc)).2 hW
  exact (mul_le_mul_of_nonneg_right hw (profile_pos he hc).le).trans
    (singletonProfile_ge_capped_weight f he hc hcap)

end
end CK.Profile
