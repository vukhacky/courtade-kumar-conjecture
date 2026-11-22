module

public import CK.Certificate.HornerBernstein
public import CK.Functional.PhiTaylor

/-! Exact dense rational coefficient constructors and their semantic link to
the finite Taylor envelopes in the source proof. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK.Certificate.Dense
noncomputable section

def variableScale (s : ℚ) : List ℚ → List ℚ
  | [] => []
  | c::cs => c::scale s (variableScale s cs)

def linearMul (a b : ℚ) (cs : List ℚ) : List ℚ :=
  add (scale a cs) (0::scale b cs)

def monomial (n : ℕ) (c : ℚ) : List ℚ := List.replicate n 0 ++ [c]

def baseCoeffs (N : ℕ) : List ℚ :=
  List.ofFn (fun k : Fin N => (1 : ℚ)/((2*(k:ℚ)+2)*(2*k+1)))

def localCoeffs (N M : ℕ) (a R L : ℚ) : List ℚ :=
  add [((a-1)*L)]
    (add (linearMul 1 (-a) (baseCoeffs N))
      (scale (-1) (linearMul 1 (-1)
        (add (scale (a^2) (variableScale (a^2) (baseCoeffs M)))
          (monomial M ((1/(1-(a*R)^2))*a^(2*M+2)/((2*(M:ℚ)+2)*(2*M+1))))))))

theorem eval_variableScale (s : ℚ) (cs : List ℚ) (x : ℝ) :
    eval (variableScale s cs) x = eval cs ((s:ℝ)*x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [variableScale,eval,eval_scale,ih]
    ring

theorem eval_linearMul (a b : ℚ) (cs : List ℚ) (x : ℝ) :
    eval (linearMul a b cs) x = ((a:ℝ)+(b:ℝ)*x)*eval cs x := by
  simp only [linearMul,eval_add,eval_scale,eval,Rat.cast_zero,zero_add]
  ring

theorem eval_monomial (n : ℕ) (c : ℚ) (x : ℝ) :
    eval (monomial n c) x = (c:ℝ)*x^n := by
  induction n with
  | zero => simp [monomial,eval]
  | succ n ih =>
    simp only [monomial,List.replicate_succ,List.cons_append,eval,Rat.cast_zero,zero_add] at *
    rw [ih,pow_succ]
    ring

theorem eval_ofFn {N : ℕ} (f : Fin N → ℚ) (x : ℝ) :
    eval (List.ofFn f) x = ∑ i : Fin N, (f i:ℝ)*x^(i:ℕ) := by
  induction N with
  | zero => simp [eval]
  | succ N ih =>
    rw [List.ofFn_succ,eval,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem eval_baseCoeffs (N : ℕ) (x : ℝ) :
    eval (baseCoeffs N) x = CK.phiTaylorBase N x := by
  rw [baseCoeffs,eval_ofFn,CK.phiTaylorBase,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

theorem eval_localCoeffs (N M : ℕ) (a R L : ℚ) (x : ℝ) :
    eval (localCoeffs N M a R L) x = CK.localTaylorPolynomial N M a R L x := by
  simp only [localCoeffs,eval_add,eval_linearMul,eval_scale,eval_variableScale,
    eval_monomial,eval_baseCoeffs,eval,CK.localTaylorPolynomial]
  push_cast
  ring

end
end CK.Certificate.Dense
