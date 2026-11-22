module

public import CK.High.ExponentialScalar
public import CK.Basic.ShannonBridge
public import CK.Fourier.Parseval

/-! The actual Shannon CK conclusion in the exponential neighborhood of a
signed dictator, uniformly for every `u ≥ log 9`. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem exp_neg_mem_small_delta {u : ℝ} (hu : Real.log 9 ≤ u) :
    Real.exp (-u) ∈ Ioc (0 : ℝ) (1/9) := by
  refine ⟨Real.exp_pos _, ?_⟩
  have h := Real.exp_le_exp.mpr (show -u ≤ -Real.log 9 by linarith)
  simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 9), one_div] using h

theorem tanh_eq_localNoiseProbability (u : ℝ) :
    Real.tanh u = 1-2*localNoiseProbability (Real.exp (-u)) := by
  rw [Real.tanh_eq, localNoiseProbability, Real.exp_neg]
  have he : Real.exp u ≠ 0 := Real.exp_ne_zero _
  have hp : 0 < Real.exp u := Real.exp_pos _
  field_simp
  <;> ring

theorem tanh_mem_unit_of_log_nine {u : ℝ} (hu : Real.log 9 ≤ u) :
    Real.tanh u ∈ Icc (0 : ℝ) 1 := by
  have hd := exp_neg_mem_small_delta hu
  have hp := localNoiseProbability_bounds hd
  have hsq : Real.exp (-u)^2 ≤ (1/9 : ℝ)^2 := pow_le_pow_left₀ hd.1.le hd.2 2
  rw [tanh_eq_localNoiseProbability]
  constructor <;> nlinarith only [hp.1,hp.2.1,hsq]

theorem localDeficit_exponential {u : ℝ} (hu : Real.log 9 ≤ u) :
    0 < localDeficit (Real.tanh u) (1-2*Real.exp (-u)) := by
  rw [tanh_eq_localNoiseProbability]
  exact localDeficit_exponential_parameter (exp_neg_mem_small_delta hu)

/-- A specified coordinate meeting the exponential coefficient threshold
proves CK with the actual finite Shannon mutual information. -/
theorem mutualInformation_le_phi_exponential_coordinate {n : ℕ} {u : ℝ}
    (hu : Real.log 9 ≤ u) (f : BooleanFunction n) (i : Fin n)
    (hi : 1-2*Real.exp (-u) ≤ |fourier (lift f) {i}|) :
    mutualInformation (Real.tanh u) f ≤ phi (Real.tanh u) := by
  have hρ := tanh_mem_unit_of_log_nine hu
  have hd := exp_neg_mem_small_delta hu
  have hA : 1-2*Real.exp (-u) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hd.1,hd.2]
  rw [mutualInformation_eq_information hρ]
  exact information_le_phi_of_local_threshold hρ hA f i hi (localDeficit_exponential hu).le

/-- STOC `ub:exponential-local`, including zero dictator distance. -/
theorem mutualInformation_le_phi_exponential_local {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu : Real.log 9 ≤ u) (f : BooleanFunction n)
    (hδ : minSignedDictatorDistance hn f ≤ Real.exp (-u)) :
    mutualInformation (Real.tanh u) f ≤ phi (Real.tanh u) := by
  obtain ⟨i, hi⟩ := exists_max_singleton hn f
  apply mutualInformation_le_phi_exponential_coordinate hu f i
  rw [minSignedDictatorDistance_eq, hi] at hδ
  linarith

end
end CK
