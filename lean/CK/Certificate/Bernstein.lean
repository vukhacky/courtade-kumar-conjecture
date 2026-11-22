module

public import Mathlib.Tactic

/-! A small tensor Bernstein certificate consumer. It accepts a finite list
of rational coefficients, proves nonnegativity of its real interpretation
on the entire unit cube, and leaves the polynomial identity to `ring`.
No data generator is trusted. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate
noncomputable section

abbrev BernsteinTerm3 := ℚ × ℕ × ℕ × ℕ

def evalBernsteinTerm3 (d : ℕ) (term : BernsteinTerm3) (u v w : ℝ) : ℝ :=
  (term.1 : ℝ) * u ^ term.2.1 * (1 - u) ^ (d - term.2.1) *
    v ^ term.2.2.1 * (1 - v) ^ (d - term.2.2.1) *
    w ^ term.2.2.2 * (1 - w) ^ (d - term.2.2.2)

def evalBernstein3 (d : ℕ) (data : List BernsteinTerm3) (u v w : ℝ) : ℝ :=
  (data.map (fun term => evalBernsteinTerm3 d term u v w)).sum

def checkBernsteinNonneg (data : List BernsteinTerm3) : Bool :=
  data.all (fun term => decide (0 ≤ term.1))

theorem evalBernsteinTerm3_nonneg {d : ℕ} {term : BernsteinTerm3} {u v w : ℝ}
    (ht : 0 ≤ term.1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ evalBernsteinTerm3 d term u v w := by
  have ht' : (0 : ℝ) ≤ (term.1 : ℝ) := by exact_mod_cast ht
  have hu0 := hu.1
  have hv0 := hv.1
  have hw0 := hw.1
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hv1 : 0 ≤ 1 - v := sub_nonneg.mpr hv.2
  have hw1 : 0 ≤ 1 - w := sub_nonneg.mpr hw.2
  unfold evalBernsteinTerm3
  positivity

/-- Soundness over every point of the unit cube, not only a finite grid. -/
theorem checkBernsteinNonneg_sound {d : ℕ} {data : List BernsteinTerm3} {u v w : ℝ}
    (hcheck : checkBernsteinNonneg data = true)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hw : w ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ evalBernstein3 d data u v w := by
  induction data with
  | nil => simp [evalBernstein3]
  | cons term data ih =>
    have hparts : decide (0 ≤ term.1) = true ∧ checkBernsteinNonneg data = true := by
      simpa only [checkBernsteinNonneg, List.all_cons, Bool.and_eq_true] using hcheck
    have ht : 0 ≤ term.1 := by
      exact of_decide_eq_true hparts.1
    have htail : checkBernsteinNonneg data = true := hparts.2
    simpa only [evalBernstein3, List.map_cons, List.sum_cons] using
      add_nonneg (evalBernsteinTerm3_nonneg ht hu hv hw) (ih htail)

theorem unitParameter_mem {lo hi x : ℝ} (hlohi : lo < hi) (hx : x ∈ Set.Icc lo hi) :
    (x - lo) / (hi - lo) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hlohi).le
  · apply (div_le_iff₀ (sub_pos.mpr hlohi)).2
    linarith [hx.2]

theorem interpolate_unitParameter {lo hi x : ℝ} (hlohi : lo < hi) :
    lo + (hi - lo) * ((x - lo) / (hi - lo)) = x := by
  have hn : hi - lo ≠ 0 := (sub_pos.mpr hlohi).ne'
  field_simp
  ring

end
end CK.Certificate
