module

public import CK.Certificate.DenseTaylor

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate.Dense
noncomputable section

def squareVariable : List ℚ → List ℚ
  | [] => []
  | c::cs => c::0::squareVariable cs

def phiCoeffs (N : ℕ) : List ℚ := 0::0::squareVariable (baseCoeffs N)

def quadraticMul (a b : ℚ) (cs : List ℚ) : List ℚ :=
  add (scale a cs) (0::0::scale b cs)

def energyCoeffs (N : ℕ) (C L margin : ℚ) : List ℚ :=
  add [1-(76/57)*L-margin,0,-(1+C)+(49/57)*L,C]
    (quadraticMul (76/57) (-49/57) (phiCoeffs N))

theorem eval_squareVariable (cs : List ℚ) (x : ℝ) :
    eval (squareVariable cs) x = eval cs (x^2) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [squareVariable,eval,Rat.cast_zero,zero_add,ih]
    ring

theorem eval_phiCoeffs (N : ℕ) (x : ℝ) :
    eval (phiCoeffs N) x = CK.phiTaylor N x := by
  simp only [phiCoeffs,eval,Rat.cast_zero,zero_add,eval_squareVariable,eval_baseCoeffs]
  rw [CK.phiTaylor_eq_sq_base]
  ring

theorem eval_quadraticMul (a b : ℚ) (cs : List ℚ) (x : ℝ) :
    eval (quadraticMul a b cs) x = ((a:ℝ)+(b:ℝ)*x^2)*eval cs x := by
  simp only [quadraticMul,eval_add,eval_scale,eval,Rat.cast_zero,zero_add]
  ring

theorem eval_energyCoeffs (N : ℕ) (C L margin : ℚ) (x : ℝ) :
    eval (energyCoeffs N C L margin) x =
      (1-x)*(1+x-(C:ℝ)*x^2)-((76-49*x^2)/57)*((L:ℝ)-CK.phiTaylor N x)-(margin:ℝ) := by
  simp only [energyCoeffs,eval_add,eval_quadraticMul,eval_phiCoeffs,eval]
  push_cast
  ring

end
end CK.Certificate.Dense
