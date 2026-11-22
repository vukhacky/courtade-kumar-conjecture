module

public import CK.Functional.Product

/-! Exact even moments of a finite Rademacher sum. Every identity is
proved by finite-cube induction and polynomial identities in the kernel. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def rademacher {n : ℕ} (c : Fin n → ℝ) (x : Cube n) : ℝ :=
  ∑ i, c i * sign (x i)

def coefficientPower {n : ℕ} (c : Fin n → ℝ) (k : ℕ) : ℝ := ∑ i, c i ^ k

theorem rademacher_cons {n : ℕ} (c : Fin (n+1) → ℝ) (b : Bool) (x : Cube n) :
    rademacher c (Fin.cons b x) = c 0 * sign b + rademacher (fun i => c i.succ) x := by
  simp only [rademacher, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem coefficientPower_cons {n : ℕ} (c : Fin (n+1) → ℝ) (k : ℕ) :
    coefficientPower c k = c 0 ^ k + coefficientPower (fun i => c i.succ) k :=
  Fin.sum_univ_succ _

theorem rademacher_moment_two {n : ℕ} (c : Fin n → ℝ) :
    avg (fun x => rademacher c x^2) = (coefficientPower c 2) := by
  induction n with
  | zero => simp [rademacher, coefficientPower, avg_cube_zero]
  | succ n ih =>
    rw [avg_cube_cons]
    have hp (z : ℝ) : ((-(c 0)+z)^2+((c 0)+z)^2)/2 = (c 0)^2+z^2 := by ring
    simp only [rademacher_cons, sign_false, sign_true, mul_neg_one, mul_one, hp,
      avg_add, avg_const, ih, coefficientPower_cons]

theorem rademacher_moment_four {n : ℕ} (c : Fin n → ℝ) :
    avg (fun x => rademacher c x^4) = 3*(coefficientPower c 2)^2-2*(coefficientPower c 4) := by
  induction n with
  | zero => simp [rademacher, coefficientPower, avg_cube_zero]
  | succ n ih =>
    rw [avg_cube_cons]
    have hp (z : ℝ) : ((-(c 0)+z)^4+((c 0)+z)^4)/2 = (c 0)^4+6*(c 0)^2*z^2+z^4 := by ring
    simp only [rademacher_cons, sign_false, sign_true, mul_neg_one, mul_one, hp,
      avg_add, avg_smul, avg_const, ih, rademacher_moment_two, coefficientPower_cons]
    ring

theorem rademacher_moment_six {n : ℕ} (c : Fin n → ℝ) :
    avg (fun x => rademacher c x^6) = 15*(coefficientPower c 2)^3-30*(coefficientPower c 2)*(coefficientPower c 4)+16*(coefficientPower c 6) := by
  induction n with
  | zero => simp [rademacher, coefficientPower, avg_cube_zero]
  | succ n ih =>
    rw [avg_cube_cons]
    have hp (z : ℝ) : ((-(c 0)+z)^6+((c 0)+z)^6)/2 = (c 0)^6+15*(c 0)^4*z^2+15*(c 0)^2*z^4+z^6 := by ring
    simp only [rademacher_cons, sign_false, sign_true, mul_neg_one, mul_one, hp,
      avg_add, avg_smul, avg_const, ih, rademacher_moment_two, rademacher_moment_four, coefficientPower_cons]
    ring

theorem rademacher_moment_eight {n : ℕ} (c : Fin n → ℝ) :
    avg (fun x => rademacher c x^8) = 105*(coefficientPower c 2)^4-420*(coefficientPower c 2)^2*(coefficientPower c 4)+448*(coefficientPower c 2)*(coefficientPower c 6)+140*(coefficientPower c 4)^2-272*(coefficientPower c 8) := by
  induction n with
  | zero => simp [rademacher, coefficientPower, avg_cube_zero]
  | succ n ih =>
    rw [avg_cube_cons]
    have hp (z : ℝ) : ((-(c 0)+z)^8+((c 0)+z)^8)/2 = (c 0)^8+28*(c 0)^6*z^2+70*(c 0)^4*z^4+28*(c 0)^2*z^6+z^8 := by ring
    simp only [rademacher_cons, sign_false, sign_true, mul_neg_one, mul_one, hp,
      avg_add, avg_smul, avg_const, ih, rademacher_moment_two, rademacher_moment_four, rademacher_moment_six, coefficientPower_cons]
    ring

theorem rademacher_moment_ten {n : ℕ} (c : Fin n → ℝ) :
    avg (fun x => rademacher c x^10) = 945*(coefficientPower c 2)^5-6300*(coefficientPower c 2)^3*(coefficientPower c 4)+10080*(coefficientPower c 2)^2*(coefficientPower c 6)+6300*(coefficientPower c 2)*(coefficientPower c 4)^2-12240*(coefficientPower c 2)*(coefficientPower c 8)-6720*(coefficientPower c 4)*(coefficientPower c 6)+7936*(coefficientPower c 10) := by
  induction n with
  | zero => simp [rademacher, coefficientPower, avg_cube_zero]
  | succ n ih =>
    rw [avg_cube_cons]
    have hp (z : ℝ) : ((-(c 0)+z)^10+((c 0)+z)^10)/2 = (c 0)^10+45*(c 0)^8*z^2+210*(c 0)^6*z^4+210*(c 0)^4*z^6+45*(c 0)^2*z^8+z^10 := by ring
    simp only [rademacher_cons, sign_false, sign_true, mul_neg_one, mul_one, hp,
      avg_add, avg_smul, avg_const, ih, rademacher_moment_two, rademacher_moment_four, rademacher_moment_six, rademacher_moment_eight, coefficientPower_cons]
    ring

end
end CK
