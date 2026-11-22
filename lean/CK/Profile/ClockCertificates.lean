module

public import CK.Profile.ClockPropagation

/-! Checked supporting-line certificates imply a propagated exact profile
clock. All numerical premises are supplied by generated certificate proofs. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

theorem fixed_clock_of_certificate {ι : Type*} [Fintype ι] (w q : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (hp : ∃ i, 0 < w i ∧ 0 < q i) {ρ₀ ρ Y ε : ℝ}
    (hρ₀ : ρ₀ ∈ Ioo (0 : ℝ) 1) (hρ : ρ ∈ Ico ρ₀ 1)
    (hY : meanEntropy ρ₀/ρ₀ < Y) (hε : 0 ≤ ε)
    (hcert : clock (sumProfile w q) Y+ε < Real.log (1/ρ₀)) :
    clock (sumProfile w q) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  apply fixed_profile_clock_propagates w q hw hq hp hρ₀ hρ
  have hy : 0 < meanEntropy ρ₀/ρ₀ :=
    div_pos (meanEntropy_pos ⟨by linarith [hρ₀.1],hρ₀.2⟩) hρ₀.1
  have hm := (strictMonoOn_clock (continuousOn_sumProfile w q (fun i => (hq i).1))
    (sumProfile_antitone w q hw (fun i => (hq i).1))
    (fun e he => sumProfile_pos w q hw (fun i => (hq i).1) hp he)).monotoneOn
    hy.le (hy.trans hY).le hY.le
  rw [one_div,Real.log_inv] at hcert
  linarith only [hm,hε,hcert]

end
end CK.Profile
