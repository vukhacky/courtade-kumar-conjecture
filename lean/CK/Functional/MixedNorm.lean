module

public import CK.Functional.Product
public import Mathlib.Analysis.MeanInequalities

/-! Finite Minkowski/Jensen inequality for a normalized two-point power
mean. This is the mixed-norm step in tensorizing one-bit hypercontractivity. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def pairPowerMean (q a b : ℝ) : ℝ := ((a^q+b^q)/2)^(1/q)

theorem pairPowerMean_nonneg (q : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ pairPowerMean q a b :=
  Real.rpow_nonneg (div_nonneg (add_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _))
    (by norm_num)) _

theorem pairPowerMean_smul {q c a b : ℝ} (hq : 0 < q) (hc : 0 ≤ c)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    pairPowerMean q (c*a) (c*b) = c*pairPowerMean q a b := by
  unfold pairPowerMean
  rw [Real.mul_rpow hc ha, Real.mul_rpow hc hb,
    show (c^q*a^q+c^q*b^q)/2=c^q*((a^q+b^q)/2) by ring,
    Real.mul_rpow (Real.rpow_nonneg hc _) (by positivity), ← Real.rpow_mul hc]
  simp only [mul_one_div_cancel (ne_of_gt hq), Real.rpow_one]

theorem pairPowerMean_add_le {q a b c d : ℝ} (hq : 1 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    pairPowerMean q (a+c) (b+d) ≤ pairPowerMean q a b + pairPowerMean q c d := by
  have h := Real.Lp_add_le_of_nonneg (Finset.univ : Finset (Fin 2))
    (f := ![a,b]) (g := ![c,d]) hq
    (fun i _ => by fin_cases i <;> assumption)
    (fun i _ => by fin_cases i <;> assumption)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  unfold pairPowerMean
  rw [Real.div_rpow (by positivity) (by norm_num),
    Real.div_rpow (by positivity) (by norm_num),
    Real.div_rpow (by positivity) (by norm_num)]
  have hh := div_le_div_of_nonneg_right h (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (1/q))
  simpa only [add_div] using hh

@[simp] theorem pairPowerMean_zero {q : ℝ} (hq : 0 < q) : pairPowerMean q 0 0 = 0 := by
  simp [pairPowerMean, Real.zero_rpow (ne_of_gt hq), Real.zero_rpow (inv_ne_zero (ne_of_gt hq))]

theorem pairPowerMean_sum_le {ι : Type*} (s : Finset ι) {q : ℝ} (hq : 1 ≤ q)
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    pairPowerMean q (∑ i ∈ s, a i) (∑ i ∈ s, b i) ≤
      ∑ i ∈ s, pairPowerMean q (a i) (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairPowerMean_zero (by linarith : 0 < q)]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    exact (pairPowerMean_add_le hq (ha i) (hb i)
      (Finset.sum_nonneg (fun j _ => ha j)) (Finset.sum_nonneg (fun j _ => hb j))).trans
      (add_le_add le_rfl ih)

theorem pairPowerMean_avg_le {n : ℕ} {q : ℝ} (hq : 1 ≤ q)
    (a b : Cube n → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) :
    pairPowerMean q (avg a) (avg b) ≤ avg (fun x => pairPowerMean q (a x) (b x)) := by
  unfold avg
  rw [pairPowerMean_smul (by linarith : 0 < q)
    (inv_nonneg.mpr (card_cube_pos n).le)
    (Finset.sum_nonneg (fun x _ => ha x)) (Finset.sum_nonneg (fun x _ => hb x))]
  exact mul_le_mul_of_nonneg_left (pairPowerMean_sum_le Finset.univ hq a b ha hb)
    (inv_nonneg.mpr (card_cube_pos n).le)

end
end CK
