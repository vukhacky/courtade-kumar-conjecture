module

public import CK.Profile.CellDomain
public import CK.Profile.ClockPropagation

/-! Shannon mutual information bound on a moving-profile cell with coefficient-domain bounds and endpoint clock inequalities. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Middle
noncomputable section
open CK.Profile

theorem movingCell_clock {L U x Y T A B : ℝ} (k : ℕ) (C : ℝ → ℝ)
    (hL : 0 < L) (hx : x ∈ Icc L U)
    (hC : ConvexOn ℝ (Icc L U) C)
    (hr : ∀ z ∈ Icc L U, A*z+B-(k : ℝ)*C z ∈ Icc (0 : ℝ) (C z))
    (hY : 0 ≤ Y)
    (hleft : clock (movingProfile k A B C L) Y ≤ T)
    (hright : clock (movingProfile k A B C U) Y ≤ T) :
    clock (movingProfile k A B C x) Y ≤ T := by
  have hconv := movingProfile_clock_convex (convex_Icc L U)
    (fun z hz => hL.trans_le hz.1) k A B C hC hr hY
  exact (clock_family_le_endpoint_max (hx.1.trans hx.2) hx hconv).trans
    (max_le hleft hright)

theorem mutualInformation_le_phi_movingCell {n : ℕ} {ρ L U a A B : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (f : BooleanFunction n) (i : Fin n)
    (hai : |fourier (lift f) {i}|=a) (ha : 0 < a)
    (k : ℕ) (C : ℝ → ℝ) (hL : 0 < L) (hx : a^2 ∈ Icc L U)
    (hC : ConvexOn ℝ (Icc L U) C)
    (hr : ∀ z ∈ Icc L U, A*z+B-(k : ℝ)*C z ∈ Icc (0 : ℝ) (C z))
    (hc : 0 < C (a^2))
    (hcap : ∀ j : Fin n, j ≠ i → |fourier (lift f) {j}| ≤ Real.sqrt (C (a^2)))
    (hW : (A+1)*a^2+B ≤ fourierWeight (lift f) 1)
    (hleft : clock (movingProfile k A B C L) (meanEntropy ρ/ρ) ≤ -Real.log ρ)
    (hright : clock (movingProfile k A B C U) (meanEntropy ρ/ρ) ≤ -Real.log ρ) :
    mutualInformation ρ f ≤ phi ρ := by
  have hsqc := Real.sq_sqrt hc.le
  have hsqai : fourier (lift f) {i}^2=a^2 := by rw [← hai,sq_abs]
  have hWa : a^2 ≤ fourierWeight (lift f) 1 := by
    rw [fourierWeight_one]
    simpa only [hsqai] using Finset.single_le_sum
      (f := fun j : Fin n => fourier (lift f) {j}^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hWpos : 0 < fourierWeight (lift f) 1 := (sq_pos_of_pos ha).trans_le hWa
  have hrem := hr (a^2) hx
  have henvelope (e : ℝ) (he : 0 < e) :
      movingProfile k A B C (a^2) e ≤ singletonProfile f e := by
    have h := retained_one_profile_le f i he (Real.sqrt_pos.mpr hc) hai hcap k
      (r := A*a^2+B-(k : ℝ)*C (a^2))
      (by simpa only [hsqc] using hrem)
      (by rw [hsqc]; nlinarith only [hW])
    simpa only [movingProfile,Real.sqrt_sq ha.le] using h
  exact mutualInformation_le_phi_of_profile_clock hρ f hWpos
    (movingProfile k A B C (a^2))
    (movingProfile_continuous k A B C (a^2))
    (movingProfile_antitone k A B C (a^2))
    (fun e he => movingProfile_pos k A B C (sq_pos_of_pos ha) he)
    henvelope (movingCell_clock k C hL hx hC hr
      (div_nonneg (meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩).le hρ.1.le) hleft hright)

end
end CK.Middle
