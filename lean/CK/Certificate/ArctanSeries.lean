module
public import CK.Certificate.IntervalBox
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Finite alternating-series certificates for arctangent. -/
@[expose] public section
set_option autoImplicit false
open scoped BigOperators Topology
open Filter
namespace CK.Certificate.Interval
noncomputable section

def atanSeries (q : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (-1)^i*q^(2*i+1)/(2*i+1)

theorem atanSeries_cast (q : ℚ) (n : ℕ) :
    (atanSeries q n : ℝ)=∑ i ∈ Finset.range n, (-1:ℝ)^i*(q:ℝ)^(2*i+1)/(2*i+1) := by
  simp [atanSeries]

theorem atanSeries_bounds {q : ℚ} (hq : 0≤q ∧ q<1) (n : ℕ) :
    (atanSeries q (2*n):ℝ)≤Real.arctan (q:ℝ) ∧
    Real.arctan (q:ℝ)≤(atanSeries q (2*n+1):ℝ) := by
  have hq0 : (0:ℝ)≤(q:ℝ) := by exact_mod_cast hq.1
  have hq1 : (q:ℝ)<1 := by exact_mod_cast hq.2
  have ha : Antitone (fun i:ℕ => (q:ℝ)^(2*i+1)/(2*i+1)) := by
    intro i j hij
    apply div_le_div₀
    · positivity
    · exact pow_le_pow_of_le_one hq0 hq1.le (by omega)
    · positivity
    · exact_mod_cast (show 2*i+1≤2*j+1 by omega)
  have hnorm : ‖(q:ℝ)‖<1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg hq0]
    exact hq1
  have hs := (Real.hasSum_arctan hnorm).tendsto_sum_nat
  have hsf : Tendsto (fun n => ∑ i ∈ Finset.range n, (-1:ℝ)^i*((q:ℝ)^(2*i+1)/(2*i+1))) atTop (𝓝 (Real.arctan (q:ℝ))) := by
    simpa only [mul_div_assoc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hs
  rw [atanSeries_cast,atanSeries_cast]
  constructor
  · simpa only [mul_div_assoc] using ha.alternating_series_le_tendsto hsf n
  · simpa only [mul_div_assoc] using ha.tendsto_le_alternating_series hsf n

theorem arctan_middle {x : ℝ} (hx : 0<x) :
    Real.arctan x = Real.pi/4+Real.arctan ((x-1)/(x+1)) := by
  have hp : 0<x+1 := by linarith
  have hlt : (1:ℝ)*((x-1)/(x+1))<1 := by
    rw [one_mul,div_lt_one hp]; linarith
  have h := Real.arctan_add hlt
  rw [Real.arctan_one] at h
  rw [show (1+(x-1)/(x+1))/(1-1*((x-1)/(x+1)))=x by field_simp; ring] at h
  exact h.symm

end
end CK.Certificate.Interval
