module
public import CK.Certificate.CompactJet

/-! Sound evaluation of a finite straight-line program with exact rational
second-order interval certificates. Invalid references denote zero; final
source identities are proved separately, so references cannot act as oracles. -/
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000
namespace CK.Certificate.CompactCircuit
open CK.Certificate.Interval CK.Certificate.CompactJet

inductive Op where
  | lit (q : ℚ) | pi | logTwo | arg
  | plus (i j : ℕ) | minus (i : ℕ) | times (i j : ℕ)
  | inverse (i : ℕ) | logarithm (i : ℕ) | exponential (i : ℕ) | arctangent (i : ℕ)
  deriving DecidableEq, Repr

structure Data where
  out : Bounds
  lower : LogWitness := ⟨0,⟨0,0⟩,0⟩
  upper : LogWitness := ⟨0,⟨0,0⟩,0⟩
  terms : ℕ := 0
  deriving DecidableEq, Repr

def nth {α : Type} (zero : α) : List α → ℕ → α
  | [], _ => zero
  | a::_, 0 => a
  | _::as, n+1 => nth zero as n

def zeroBounds : Bounds := boxConst (point 0)
def getB (env : List Bounds) (i : ℕ) : Bounds := nth zeroBounds env i
noncomputable def getJ (env : List Jet) (i : ℕ) : Jet := nth (constant 0) env i

noncomputable def eval (env : List Jet) : Op → Jet
  | .lit q => constant (q:ℝ)
  | .pi => constant Real.pi
  | .logTwo => constant (Real.log 2)
  | .arg => variableJet
  | .plus i j => plus (getJ env i) (getJ env j)
  | .minus i => minus (getJ env i)
  | .times i j => times (getJ env i) (getJ env j)
  | .inverse i => inverse (getJ env i)
  | .logarithm i => logarithm (getJ env i)
  | .exponential i => exponential (getJ env i)
  | .arctangent i => arctangent (getJ env i)

def CheckStep (input : Box) (env : List Bounds) (op : Op) (r : Data) : Prop :=
  match op with
  | .lit q => narrow (boxConst (point q)) r.out
  | .pi => narrow (boxConst piBox) r.out
  | .logTwo => narrow (boxConst logTwoBox) r.out
  | .arg => narrow (boxVar input) r.out
  | .plus i j => narrow (boxPlus (getB env i) (getB env j)) r.out
  | .minus i => narrow (boxMinus (getB env i)) r.out
  | .times i j => narrow (boxTimes (getB env i) (getB env j)) r.out
  | .inverse i => 0<(getB env i).val.lo ∧ narrow (boxInverse (getB env i)) r.out
  | .logarithm i => CheckLogRange (getB env i).val r.out.val r.lower r.upper ∧
      0<(getB env i).val.lo ∧ narrow (boxLogarithm (getB env i) r.out.val) r.out
  | .exponential i => CheckExpRange (getB env i).val r.out.val r.lower r.upper ∧
      narrow (boxExponential (getB env i) r.out.val) r.out
  | .arctangent i => CheckAtanRange (getB env i).val r.out.val r.terms ∧
      0<(add (point 1) (sq (getB env i).val)).lo ∧
      narrow (boxArctangent (getB env i) r.out.val) r.out

instance (input : Box) (env : List Bounds) (op : Op) (r : Data) :
    Decidable (CheckStep input env op r) := by
  cases op <;> unfold CheckStep <;> infer_instance

def StateSound (bs : List Bounds) (js : List Jet) (x : ℝ) : Prop :=
  ∀ i, ValidAt (getJ js i) x ∧ Encloses (getB bs i) (getJ js i) x

theorem state_nil (x : ℝ) : StateSound [] [] x := by
  intro i
  exact ⟨valid_constant 0 x,encloses_constant holds_zero⟩

theorem state_cons {bs : List Bounds} {js : List Jet} {x : ℝ} {b : Bounds} {j : Jet}
    (h : StateSound bs js x) (hj : ValidAt j x ∧ Encloses b j x) :
    StateSound (b::bs) (j::js) x := by
  intro i
  cases i with
  | zero => exact hj
  | succ i => exact h i

theorem step_sound {input : Box} {bs : List Bounds} {js : List Jet} {x : ℝ}
    (hx : Holds input x) (hs : StateSound bs js x) (op : Op) (r : Data)
    (h : CheckStep input bs op r) :
    ValidAt (eval js op) x ∧ Encloses r.out (eval js op) x := by
  cases op with
  | lit q => exact ⟨valid_constant _ _,encloses_narrow (encloses_constant (holds_point q)) h⟩
  | pi => exact ⟨valid_constant _ _,encloses_narrow (encloses_constant holds_pi) h⟩
  | logTwo => exact ⟨valid_constant _ _,encloses_narrow (encloses_constant holds_logTwo) h⟩
  | arg => exact ⟨valid_variable _,encloses_narrow (encloses_variable hx) h⟩
  | plus i j => exact ⟨valid_plus (hs i).1 (hs j).1,
      encloses_narrow (encloses_plus (hs i).2 (hs j).2) h⟩
  | minus i => exact ⟨valid_minus (hs i).1,encloses_narrow (encloses_minus (hs i).2) h⟩
  | times i j => exact ⟨valid_times (hs i).1 (hs j).1,
      encloses_narrow (encloses_times (hs i).2 (hs j).2) h⟩
  | inverse i =>
      exact ⟨valid_inverse (hs i).1 (holds_pos (hs i).2.1 h.1).ne',
        encloses_narrow (encloses_inverse (hs i).2 h.1) h.2⟩
  | logarithm i =>
      exact ⟨valid_logarithm (hs i).1 (holds_pos (hs i).2.1 h.2.1).ne',
        encloses_narrow (encloses_logarithm (hs i).2 h.2.1
          (checkLogRange_sound h.1 (hs i).2.1)) h.2.2⟩
  | exponential i =>
      exact ⟨valid_exponential (hs i).1,
        encloses_narrow (encloses_exponential (hs i).2
          (checkExpRange_sound h.1 (hs i).2.1)) h.2⟩
  | arctangent i =>
      exact ⟨valid_arctangent (hs i).1,
        encloses_narrow (encloses_arctangent (hs i).2
          (checkAtanRange_sound h.1 (hs i).2.1) h.2.1) h.2.2⟩

noncomputable def run (ops : List Op) (env : List Jet := []) : List Jet :=
  match ops with
  | [] => env
  | op::ops => run ops (eval env op::env)

def runBounds (data : List Data) (env : List Bounds := []) : List Bounds :=
  match data with
  | [] => env
  | d::ds => runBounds ds (d.out::env)

def checkRun (input : Box) : List Op → List Data → List Bounds → Bool
  | [], [], _ => true
  | op::ops, r::rs, env => decide (CheckStep input env op r) && checkRun input ops rs (r.out::env)
  | _, _, _ => false

theorem run_sound {input : Box} {x : ℝ} (hx : Holds input x)
    (ops : List Op) (data : List Data) (bs : List Bounds) (js : List Jet)
    (hs : StateSound bs js x) (h : checkRun input ops data bs = true) :
    StateSound (runBounds data bs) (run ops js) x := by
  induction ops generalizing data bs js with
  | nil =>
      cases data with
      | nil => exact hs
      | cons r rs => simp [checkRun] at h
  | cons op ops ih =>
      cases data with
      | nil => simp [checkRun] at h
      | cons r rs =>
          have hh : decide (CheckStep input bs op r) = true ∧ checkRun input ops rs (r.out::bs)=true := by
            simpa only [checkRun,Bool.and_eq_true] using h
          have ht : CheckStep input bs op r := of_decide_eq_true hh.1
          exact ih rs (r.out::bs) (eval js op::js)
            (state_cons hs (step_sound hx hs op r ht)) hh.2

theorem closed_sound {input : Box} {x : ℝ} (hx : Holds input x)
    (ops : List Op) (data : List Data) (h : checkRun input ops data [] = true) (i : ℕ) :
    ValidAt (getJ (run ops) i) x ∧ Encloses (getB (runBounds data) i) (getJ (run ops) i) x :=
  run_sound hx ops data [] [] (state_nil x) h i

/-- A certified value/first derivative at the centre plus a certified second
 derivative on the whole interval implies positivity everywhere in the interval. -/
theorem taylor_positive (ops : List Op) (wide center : List Data) (lo hi : ℚ) (i : ℕ)
    (horder : lo≤hi)
    (hwide : checkRun ⟨lo,hi⟩ ops wide [] = true)
    (hcenter : checkRun (point ((lo+hi)/2)) ops center [] = true)
    (hmargin : 0 < (getB (runBounds center) i).val.lo-
      magnitude (getB (runBounds center) i).d1*((hi-lo)/2)-
      magnitude (getB (runBounds wide) i).d2*((hi-lo)/2)^2/2) :
    ∀ x ∈ Set.Icc (lo:ℝ) (hi:ℝ), 0<(getJ (run ops) i).val x := by
  let c : ℝ := ((lo+hi)/2:ℚ)
  let r : ℝ := ((hi-lo)/2:ℚ)
  have hl : c-r=(lo:ℝ) := by dsimp [c,r]; push_cast; ring
  have hu : c+r=(hi:ℝ) := by dsimp [c,r]; push_cast; ring
  have hr : 0≤r := by dsimp [r]; exact_mod_cast (div_nonneg (sub_nonneg.mpr horder) (by norm_num : (0:ℚ)≤2))
  have hci : Holds (point ((lo+hi)/2)) c := holds_point _
  have hc := closed_sound hci ops center hcenter i
  have hw (x : ℝ) (hx : x ∈ Set.Icc (c-r) (c+r)) :=
    closed_sound (input:=⟨lo,hi⟩) (x:=x) (by simpa only [hl,hu,Holds,RationalBound,Set.mem_Icc] using hx) ops wide hwide i
  have hh := CK.Analysis.taylor_positive hr (fun x hx => (hw x hx).1.1)
    (fun x hx => (hw x hx).1.2) (fun x hx => holds_abs (hw x hx).2.2.2)
    hc.2.1.1 (holds_abs hc.2.2.1)
    (show (0:ℝ)<((getB (runBounds center) i).val.lo:ℝ)-
      (magnitude (getB (runBounds center) i).d1:ℝ)*r-
      (magnitude (getB (runBounds wide) i).d2:ℝ)*r^2/2 by dsimp only [r]; exact_mod_cast hmargin)
  simpa only [hl,hu] using hh

end CK.Certificate.CompactCircuit
