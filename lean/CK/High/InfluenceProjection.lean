module

public import CK.High.CoordinateNoise
public import CK.High.InfluenceLogScalar

/-! The complete variance–influence theorem used by the high-correlation
spectral bound, with both coordinatewise estimates and actual projection. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory Set
namespace CK
noncomputable section

theorem coordinateVarianceShare_le_logarithmic {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Icc (-1 : ℝ) 1) (i : Fin n) :
    coordinateVarianceShare g i ≤ influenceLogarithmic (coordinateL1 g i) := by
  have ha : coordinateL1 g i ∈ Icc (0 : ℝ) 1 :=
    ⟨coordinateL1_nonneg g i,coordinateL1_le_one g hg i⟩
  by_cases ha0 : coordinateL1 g i=0
  · have h := coordinateVarianceShare_le_polynomial g hg i
    simpa only [ha0,influencePolynomial,influenceLogarithmic_zero,zero_pow (by decide : 2 ≠ 0),zero_add,zero_div] using h
  · have hap : coordinateL1 g i ∈ Ioc (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ha.1 (Ne.symm ha0),ha.2⟩
    rw [coordinateVarianceShare_integral,← integral_influenceLogDerivative hap]
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (coordinateNoiseEnergy_continuous g i |>.intervalIntegrable _ _)
      ((influenceLogDerivative_continuousOn hap).intervalIntegrable_of_Icc (by norm_num))
    intro s hs
    exact (coordinateNoiseEnergy_le_rpow g hg i hs).trans (influence_rpow_le_logDerivative hap hs)

theorem coordinateVarianceShare_le_psi {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Icc (-1 : ℝ) 1) (i : Fin n) :
    coordinateVarianceShare g i ≤ influencePsi (coordinateL1 g i) :=
  le_min (coordinateVarianceShare_le_polynomial g hg i) (coordinateVarianceShare_le_logarithmic g hg i)

theorem variance_le_sum_influencePsi {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Icc (-1 : ℝ) 1) :
    variance g ≤ ∑ i : Fin n, influencePsi (coordinateL1 g i) := by
  rw [variance_eq_sum_coordinateVarianceShare]
  exact Finset.sum_le_sum (fun i _ => coordinateVarianceShare_le_psi g hg i)

/-- STOC `rt:source-projection`, including every bounded real cube
function, every retained set, and zero coordinate derivatives. -/
theorem variance_projection_le_influencePsi {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Icc (-1 : ℝ) 1) (K : Finset (Fin n)) :
    variance (coordinateProjection K g) ≤ ∑ i ∈ K, influencePsi (coordinateL1 g i) := by
  classical
  have hpg : ∀ x, coordinateProjection K g x ∈ Icc (-1 : ℝ) 1 := coordinateProjection_mem_Icc K hg
  calc
    _ ≤ ∑ i : Fin n, influencePsi (coordinateL1 (coordinateProjection K g) i) :=
      variance_le_sum_influencePsi _ hpg
    _ ≤ ∑ i : Fin n, if i∈K then influencePsi (coordinateL1 g i) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i∈K
      · rw [ite_eq_left hi]
        exact influencePsi_monotoneOn
          ⟨coordinateL1_nonneg _ i,coordinateL1_le_one _ hpg i⟩
          ⟨coordinateL1_nonneg _ i,coordinateL1_le_one _ hg i⟩
          (coordinateL1_projection_le K g i)
      · rw [ite_eq_right hi,coordinateL1,coordinatePartial_projection_of_not_mem K g i hi]
        simp only [abs_zero,avg_const,influencePsi_zero]
        exact le_rfl
    _ = _ := by simp

theorem coordinateL1_eq_singleton_of_monotone {n : ℕ} (g : Cube n → ℝ)
    (hg : Monotone g) (i : Fin n) : coordinateL1 g i = fourier g {i} :=
  (fourier_singleton_eq_avg_abs_partial hg i).symm

theorem variance_projection_le_influencePsi_monotone {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Icc (-1 : ℝ) 1) (hm : Monotone g) (K : Finset (Fin n)) :
    variance (coordinateProjection K g) ≤ ∑ i ∈ K, influencePsi (fourier g {i}) := by
  have h := variance_projection_le_influencePsi g hg K
  simpa only [coordinateL1_eq_singleton_of_monotone g hm] using h

end
end CK
