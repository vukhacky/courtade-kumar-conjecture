module

public import CK.Profile.Packing
public import CK.Profile.ClockPropagation

/-! Actual Shannon CK from the common capped-singleton clock. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

theorem mutualInformation_le_phi_capped_clock {n : ℕ} {ρ c w : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (f : BooleanFunction n)
    (hc : 0 < c) (hw : 0 < w)
    (hcap : ∀ i, |fourier (lift f) {i}| ≤ c)
    (hW : w*c^2 ≤ fourierWeight (lift f) 1)
    (hclock : clock (fun e => w*profile e c) (meanEntropy ρ/ρ) ≤ -Real.log ρ) :
    mutualInformation ρ f ≤ phi ρ := by
  exact mutualInformation_le_phi_of_profile_clock hρ f
    ((mul_pos hw (sq_pos_of_pos hc)).trans_le hW) (fun e => w*profile e c)
    (continuousOn_const.mul (continuousOn_profile hc))
    (fun e he d hd hed => mul_le_mul_of_nonneg_left (profile_antitone hc he hd hed) hw.le)
    (fun e he => mul_pos hw (profile_pos he hc))
    (fun e he => singletonProfile_ge_capped_envelope f he hc hcap hW) hclock

end
end CK.Profile
