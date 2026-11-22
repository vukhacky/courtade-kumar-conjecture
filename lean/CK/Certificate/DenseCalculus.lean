module

public import CK.Certificate.DenseEnergy

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate.Dense
noncomputable section

def mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | c::cs, ds => add (scale c ds) (0::mul cs ds)

def derivative : List ℚ → List ℚ
  | [] => []
  | _::cs => add cs (0::derivative cs)

theorem eval_mul (cs ds : List ℚ) (x : ℝ) :
    eval (mul cs ds) x = eval cs x*eval ds x := by
  induction cs with
  | nil => simp [mul,eval]
  | cons c cs ih =>
    simp only [mul,eval_add,eval_scale,eval,Rat.cast_zero,zero_add,ih]
    ring

theorem hasDerivAt_eval (cs : List ℚ) (x : ℝ) :
    HasDerivAt (eval cs) (eval (derivative cs) x) x := by
  induction cs with
  | nil => simpa only [eval,derivative] using hasDerivAt_const x (0:ℝ)
  | cons c cs ih =>
    have h := (hasDerivAt_const x (c:ℝ)).add ((hasDerivAt_id x).mul ih)
    apply h.congr_deriv
    simp only [derivative,eval_add,eval,Rat.cast_zero,zero_add,one_mul,id_eq]

theorem continuous_eval (cs : List ℚ) : Continuous (eval cs) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_eval cs x).continuousAt)

end
end CK.Certificate.Dense
