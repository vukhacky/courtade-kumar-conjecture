module

public import CK.Certificate.EntropyQuartic
public import CK.Certificate.LogBounds

/-! Finite-cube specialization of STOC `lem:mean-moments`. The mean is the
actual normalized cube expectation; all centered moments are expanded in
Lean. No balance hypothesis is imposed. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate
noncomputable section

def centered {n : ℕ} (g : Cube n → ℝ) (x : Cube n) : ℝ := g x - avg g
def centeredMoment {n : ℕ} (g : Cube n → ℝ) (k : ℕ) : ℝ :=
  avg (fun x => centered g x ^ k)

theorem avg_centered {n : ℕ} (g : Cube n → ℝ) : avg (centered g) = 0 := by
  unfold centered
  rw [avg_sub, avg_const]
  ring

theorem avg_square_eq_centered {n : ℕ} (g : Cube n → ℝ) :
    avg (fun x => g x ^ 2) = (avg g)^2 + centeredMoment g 2 := by
  have hfun : (fun x => g x ^ 2) = fun x =>
      (avg g)^2 + (2 * avg g) * centered g x + centered g x ^ 2 := by
    funext x
    dsimp [centered]
    ring
  rw [hfun, avg_add, avg_add, avg_const, avg_smul, avg_centered]
  simp only [mul_zero, add_zero]
  rfl

theorem avg_fourth_eq_centered {n : ℕ} (g : Cube n → ℝ) :
    avg (fun x => g x ^ 4) =
      (avg g)^4 + 6*(avg g)^2*centeredMoment g 2 +
        4*avg g*centeredMoment g 3 + centeredMoment g 4 := by
  have hfun : (fun x => g x ^ 4) = fun x =>
      (avg g)^4 + (4*(avg g)^3)*centered g x +
        (6*(avg g)^2)*centered g x^2 + (4*avg g)*centered g x^3 + centered g x^4 := by
    funext x
    dsimp [centered]
    ring
  rw [hfun]
  simp only [avg_add, avg_const, avg_smul, avg_centered, mul_zero, add_zero, centeredMoment]

theorem avg_mem_Icc_unit {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) : avg g ∈ Set.Icc (-1 : ℝ) 1 := by
  have hl := avg_mono (fun x => (hg x).1)
  have hu := avg_mono (fun x => (hg x).2)
  rw [avg_const] at hl hu
  exact ⟨hl, hu⟩

theorem centered_second_nonneg {n : ℕ} (g : Cube n → ℝ) : 0 ≤ centeredMoment g 2 := by
  have h := avg_mono (fun x => sq_nonneg (centered g x))
  rw [avg_const] at h
  exact h

theorem centered_second_le_one {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) : centeredMoment g 2 ≤ 1 := by
  have hsq : ∀ x, g x^2 ≤ 1 := by
    intro x
    nlinarith [(hg x).1, (hg x).2]
  have h := avg_mono hsq
  rw [avg_const, avg_square_eq_centered] at h
  nlinarith [sq_nonneg (avg g)]

theorem mean_moment_compensation {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1)
    {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) (1/20)) :
    lam * (Real.log 2 - centeredMoment g 2 / 2 -
      (Real.log 2 - 1/2) * centeredMoment g 4) -
        (2/5 : ℝ) * lam^2 * (centeredMoment g 3)^2 ≤
      lam * avg (fun x => signEntropy (g x)) + phi (avg g) := by
  have hlam0 : 0 ≤ lam := hlam.1
  let κ : ℝ := Real.log 2 - 1/2
  let μ : ℝ := avg g
  let m₂ : ℝ := centeredMoment g 2
  let m₃ : ℝ := centeredMoment g 3
  let m₄ : ℝ := centeredMoment g 4
  have hκ0 : 0 ≤ κ := by dsimp [κ]; linarith [log_two_coarse_bounds.1]
  have hκ1 : κ ≤ 1/5 := by dsimp [κ]; linarith [log_two_coarse_bounds.2]
  have hm₂0 : 0 ≤ m₂ := centered_second_nonneg g
  have hm₂1 : m₂ ≤ 1 := centered_second_le_one g hg
  have hprod0 : 0 ≤ lam*κ := mul_nonneg hlam.1 hκ0
  have hprod1 : lam*κ ≤ 1/100 := by
    have h := mul_le_mul hlam.2 hκ1 hκ0 (by norm_num : (0 : ℝ) ≤ 1/20)
    norm_num at h
    exact h
  have hprod2 : lam*κ*m₂ ≤ lam*κ := mul_le_of_le_one_right hprod0 hm₂1
  have hA : (2/5 : ℝ) ≤ (1-lam)/2 - 6*lam*κ*m₂ := by
    nlinarith [hlam.2]
  have hB : 0 ≤ 1/12 - lam*κ := by linarith
  have hH := avg_mono (fun x => signEntropy_quartic_lower (hg x))
  simp only [avg_sub, avg_const, avg_div, avg_smul] at hH
  have hphi := quartic_lower_phi (avg_mem_Icc_unit g hg)
  have hlamH := mul_le_mul_of_nonneg_left hH hlam.1
  rw [avg_square_eq_centered, avg_fourth_eq_centered] at hlamH
  change lam * (Real.log 2 - (μ^2+m₂)/2 -
    κ*(μ^4+6*μ^2*m₂+4*μ*m₃+m₄)) ≤ lam * avg (fun x => signEntropy (g x)) at hlamH
  change μ^2/2+μ^4/12 ≤ phi (avg g) at hphi
  have hraw : lam * (Real.log 2 - m₂/2 - κ*m₄) +
      ((1-lam)/2 - 6*lam*κ*m₂)*μ^2 - 4*lam*κ*μ*m₃ +
      (1/12-lam*κ)*μ^4 ≤ lam * avg (fun x => signEntropy (g x)) + phi (avg g) := by
    nlinarith only [hlamH, hphi]
  have hAμ := mul_le_mul_of_nonneg_right hA (sq_nonneg μ)
  have hBμ := mul_nonneg hB (show 0 ≤ μ^4 by positivity)
  have hcross1 : μ*m₃ ≤ |μ| * |m₃| := by simpa only [abs_mul] using le_abs_self (μ*m₃)
  have hcross2 : 4*lam*κ*(μ*m₃) ≤ 4*lam*κ*(|μ| * |m₃|) :=
    mul_le_mul_of_nonneg_left hcross1 (by positivity)
  have hcross3 : 4*lam*κ*(|μ| * |m₃|) ≤ (4/5 : ℝ)*lam* |μ| * |m₃| := by
    have h := mul_le_mul_of_nonneg_left hκ1 (show 0 ≤ 4*lam* |μ| * |m₃| by positivity)
    nlinarith only [h]
  have hsq : (0 : ℝ) ≤ (|μ| - lam* |m₃|)^2 := sq_nonneg _
  have hcomplete : -(2/5 : ℝ)*lam^2*m₃^2 ≤ (2/5 : ℝ)*μ^2 - (4/5 : ℝ)*lam* |μ| * |m₃| := by
    nlinarith only [hsq, sq_abs μ, sq_abs m₃]
  change lam * (Real.log 2 - m₂/2 - κ*m₄) - (2/5 : ℝ)*lam^2*m₃^2 ≤ _
  nlinarith only [hraw, hAμ, hBμ, hcross2, hcross3, hcomplete]

end
end CK.Certificate
