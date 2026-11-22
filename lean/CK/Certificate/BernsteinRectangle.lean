module

public import CK.Certificate.Bernstein

/-! Tensor Bernstein certificates with independent degrees on a rectangle. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate
noncomputable section

abbrev BernsteinTerm2 := ℚ × ℕ × ℕ

def evalBernsteinTerm2 (du dv : ℕ) (term : BernsteinTerm2) (u v : ℝ) : ℝ :=
  (term.1:ℝ)*u^term.2.1*(1-u)^(du-term.2.1)*v^term.2.2*(1-v)^(dv-term.2.2)

def evalBernstein2 (du dv : ℕ) (data : List BernsteinTerm2) (u v : ℝ) : ℝ :=
  (data.map (fun term => evalBernsteinTerm2 du dv term u v)).sum

def checkBernstein2 (data : List BernsteinTerm2) : Bool :=
  data.all (fun term => decide (0 ≤ term.1))

theorem evalBernsteinTerm2_nonneg {du dv : ℕ} {term : BernsteinTerm2} {u v : ℝ}
    (hc : 0 ≤ term.1) (hu : u ∈ Set.Icc (0:ℝ) 1) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ evalBernsteinTerm2 du dv term u v := by
  have hc' : (0:ℝ) ≤ (term.1:ℝ) := by exact_mod_cast hc
  have hu0 := hu.1
  have hv0 := hv.1
  have hu1 : 0 ≤ 1-u := sub_nonneg.mpr hu.2
  have hv1 : 0 ≤ 1-v := sub_nonneg.mpr hv.2
  unfold evalBernsteinTerm2
  positivity

theorem checkBernstein2_sound {du dv : ℕ} {data : List BernsteinTerm2} {u v : ℝ}
    (hcheck : checkBernstein2 data = true)
    (hu : u ∈ Set.Icc (0:ℝ) 1) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ evalBernstein2 du dv data u v := by
  induction data with
  | nil => simp [evalBernstein2]
  | cons term data ih =>
    have hp : decide (0 ≤ term.1) = true ∧ checkBernstein2 data = true := by
      simpa only [checkBernstein2,List.all_cons,Bool.and_eq_true] using hcheck
    have hc : 0 ≤ term.1 := of_decide_eq_true hp.1
    simpa only [evalBernstein2,List.map_cons,List.sum_cons] using
      add_nonneg (evalBernsteinTerm2_nonneg hc hu hv) (ih hp.2)

end
end CK.Certificate
