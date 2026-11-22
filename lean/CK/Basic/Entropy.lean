module

public import CK.Basic.Cube
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! Entropy convention for the CK formalization: all quantities use natural
logarithms. The mean correction is retained for unbalanced functions. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

def phi (t : ℝ) : ℝ := Real.log 2 - Real.binEntropy ((1 - t) / 2)

/-- Finite conditional-entropy expression, in nats. Equivalence to actual
Shannon mutual information is proved in `CK.Basic.ShannonBridge`. -/
def information {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) : ℝ :=
  avg (fun x => phi (noise ρ (lift f) x)) - phi (mean f)

@[simp] theorem phi_zero : phi 0 = 0 := by
  simp only [phi, sub_zero, one_div, Real.binEntropy_two_inv, sub_self]

@[simp] theorem phi_one : phi 1 = Real.log 2 := by norm_num [phi]

theorem binEntropy_sign_conventions (t : ℝ) :
    Real.binEntropy ((1+t)/2) = Real.binEntropy ((1-t)/2) := by
  rw [show (1+t)/2 = 1-(1-t)/2 by ring, Real.binEntropy_one_sub]

theorem phi_neg (t : ℝ) : phi (-t) = phi t := by
  unfold phi
  rw [show (1 - -t) / 2 = 1 - (1 - t) / 2 by ring, Real.binEntropy_one_sub]

@[simp] theorem phi_neg_one : phi (-1) = Real.log 2 := by rw [phi_neg, phi_one]

theorem phi_nonneg (t : ℝ) : 0 ≤ phi t :=
  sub_nonneg.mpr Real.binEntropy_le_log_two

theorem phi_eq_zero_iff (t : ℝ) : phi t = 0 ↔ t = 0 := by
  rw [phi, sub_eq_zero, eq_comm, Real.binEntropy_eq_log_two]
  constructor <;> intro h <;> linarith

theorem phi_le_log_two {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : phi t ≤ Real.log 2 := by
  have hp0 : 0 ≤ (1-t)/2 := by linarith [ht.2]
  have hp1 : (1-t)/2 ≤ 1 := by linarith [ht.1]
  exact sub_le_self _ (Real.binEntropy_nonneg hp0 hp1)

theorem phi_sign (b : Bool) : phi (sign b) = Real.log 2 := by
  cases b <;> simp

theorem information_eq_entropy_difference {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) :
    information ρ f = Real.binEntropy ((1 - mean f) / 2) -
      avg (fun x => Real.binEntropy ((1 - noise ρ (lift f) x) / 2)) := by
  unfold information phi
  rw [avg_sub, avg_const]
  ring

theorem information_zero {n : ℕ} (f : BooleanFunction n) : information 0 f = 0 := by
  simp [information, noise_zero, mean]

theorem information_one {n : ℕ} (f : BooleanFunction n) :
    information 1 f = Real.binEntropy ((1 - mean f) / 2) := by
  unfold information
  simp only [noise_one, lift, phi_sign, avg_const]
  unfold phi
  ring

theorem information_one_le {n : ℕ} (f : BooleanFunction n) : information 1 f ≤ phi 1 := by
  rw [information_one, phi_one]
  exact Real.binEntropy_le_log_two

theorem information_one_eq_iff_balanced {n : ℕ} (f : BooleanFunction n) :
    information 1 f = phi 1 ↔ Balanced f := by
  rw [information_one, phi_one, Real.binEntropy_eq_log_two]
  unfold Balanced
  constructor <;> intro h <;> linarith

theorem information_complement {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) :
    information ρ (fun x => !(f x)) = information ρ f := by
  have hl : lift (fun x => !(f x)) = fun x => -lift f x := by
    funext x
    exact sign_not (f x)
  simp only [information, mean, hl, noise_neg, avg_neg, phi_neg]

end
end CK
