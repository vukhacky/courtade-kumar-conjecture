module
public import CK.Certificate.PointCertificates
public import CK.Analysis.TaylorEnclosure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! Second order real jets and exact rational interval enclosures.
The enclosure algebra is independent of the data producer. -/
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4000
namespace CK.Certificate.CompactJet
open CK.Certificate.Interval

structure Jet where
  val : ℝ → ℝ
  d1 : ℝ → ℝ
  d2 : ℝ → ℝ

noncomputable section

def ValidAt (a : Jet) (x : ℝ) : Prop :=
  HasDerivAt a.val (a.d1 x) x ∧ HasDerivAt a.d1 (a.d2 x) x

def constant (r : ℝ) : Jet := ⟨fun _ => r,fun _ => 0,fun _ => 0⟩
def variableJet : Jet := ⟨id,fun _ => 1,fun _ => 0⟩
def plus (a b : Jet) : Jet :=
  ⟨fun x => a.val x+b.val x,fun x => a.d1 x+b.d1 x,fun x => a.d2 x+b.d2 x⟩
def minus (a : Jet) : Jet := ⟨fun x => -a.val x,fun x => -a.d1 x,fun x => -a.d2 x⟩
def times (a b : Jet) : Jet := ⟨fun x => a.val x*b.val x,
  fun x => a.d1 x*b.val x+a.val x*b.d1 x,
  fun x => a.d2 x*b.val x+2*a.d1 x*b.d1 x+a.val x*b.d2 x⟩
def inverse (a : Jet) : Jet := ⟨fun x => (a.val x)⁻¹,
  fun x => -a.d1 x/(a.val x)^2,
  fun x => (2*(a.d1 x)^2-a.val x*a.d2 x)/(a.val x)^3⟩
def logarithm (a : Jet) : Jet := ⟨fun x => Real.log (a.val x),
  fun x => a.d1 x/a.val x,
  fun x => (a.d2 x*a.val x-(a.d1 x)^2)/(a.val x)^2⟩
def exponential (a : Jet) : Jet := ⟨fun x => Real.exp (a.val x),
  fun x => a.d1 x*Real.exp (a.val x),
  fun x => (a.d2 x+(a.d1 x)^2)*Real.exp (a.val x)⟩
def arctangent (a : Jet) : Jet := ⟨fun x => Real.arctan (a.val x),
  fun x => a.d1 x/(1+(a.val x)^2),
  fun x => (a.d2 x*(1+(a.val x)^2)-2*a.val x*(a.d1 x)^2)/(1+(a.val x)^2)^2⟩

theorem valid_constant (r x : ℝ) : ValidAt (constant r) x :=
  ⟨hasDerivAt_const x r,hasDerivAt_const x 0⟩
theorem valid_variable (x : ℝ) : ValidAt variableJet x :=
  ⟨hasDerivAt_id x,hasDerivAt_const x 1⟩
theorem valid_plus {a b : Jet} {x : ℝ} (ha : ValidAt a x) (hb : ValidAt b x) :
    ValidAt (plus a b) x := ⟨ha.1.add hb.1,ha.2.add hb.2⟩
theorem valid_minus {a : Jet} {x : ℝ} (ha : ValidAt a x) :
    ValidAt (minus a) x := ⟨ha.1.neg,ha.2.neg⟩
theorem valid_times {a b : Jet} {x : ℝ} (ha : ValidAt a x) (hb : ValidAt b x) :
    ValidAt (times a b) x := by
  refine ⟨ha.1.mul hb.1,?_⟩
  apply ((ha.2.mul hb.1).add (ha.1.mul hb.2)).congr_deriv
  dsimp [times]
  ring

theorem valid_inverse {a : Jet} {x : ℝ} (ha : ValidAt a x) (hp : a.val x ≠ 0) :
    ValidAt (inverse a) x := by
  refine ⟨ha.1.inv hp,?_⟩
  apply (ha.2.neg.div (ha.1.pow 2) (pow_ne_zero 2 hp)).congr_deriv
  dsimp [inverse]
  field_simp
  ring

theorem valid_logarithm {a : Jet} {x : ℝ} (ha : ValidAt a x) (hp : a.val x ≠ 0) :
    ValidAt (logarithm a) x := by
  refine ⟨ha.1.log hp,?_⟩
  apply (ha.2.div ha.1 hp).congr_deriv
  dsimp [logarithm]
  ring

theorem valid_exponential {a : Jet} {x : ℝ} (ha : ValidAt a x) :
    ValidAt (exponential a) x := by
  refine ⟨?_,?_⟩
  · apply ha.1.exp.congr_deriv
    dsimp [exponential]
    ring
  · apply (ha.2.mul ha.1.exp).congr_deriv
    dsimp [exponential]
    ring

theorem valid_arctangent {a : Jet} {x : ℝ} (ha : ValidAt a x) :
    ValidAt (arctangent a) x := by
  have hp : 1+(a.val x)^2 ≠ 0 := by positivity
  refine ⟨?_,?_⟩
  · apply ha.1.arctan.congr_deriv
    dsimp [arctangent]
    ring
  · apply (ha.2.div ((ha.1.pow 2).const_add 1) hp).congr_deriv
    dsimp [arctangent]
    ring

end

structure Bounds where
  val : Box
  d1 : Box
  d2 : Box
  deriving DecidableEq, Repr

def Encloses (a : Bounds) (j : Jet) (x : ℝ) : Prop :=
  Holds a.val (j.val x) ∧ Holds a.d1 (j.d1 x) ∧ Holds a.d2 (j.d2 x)

def narrow (a b : Bounds) : Prop :=
  subset a.val b.val ∧ subset a.d1 b.d1 ∧ subset a.d2 b.d2
instance (a b : Bounds) : Decidable (narrow a b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem holds_zero : Holds (point 0) (0:ℝ) := by norm_num [Holds,point,RationalBound]
theorem holds_one : Holds (point 1) (1:ℝ) := by norm_num [Holds,point,RationalBound]
theorem holds_two : Holds (point 2) (2:ℝ) := by norm_num [Holds,point,RationalBound]

def boxConst (v : Box) : Bounds := ⟨v,point 0,point 0⟩
def boxVar (v : Box) : Bounds := ⟨v,point 1,point 0⟩
def boxPlus (a b : Bounds) : Bounds := ⟨add a.val b.val,add a.d1 b.d1,add a.d2 b.d2⟩
def boxMinus (a : Bounds) : Bounds := ⟨neg a.val,neg a.d1,neg a.d2⟩
def boxTimes (a b : Bounds) : Bounds := ⟨mul a.val b.val,
  add (mul a.d1 b.val) (mul a.val b.d1),
  add (add (mul a.d2 b.val) (mul (mul (point 2) a.d1) b.d1)) (mul a.val b.d2)⟩
def boxInverse (a : Bounds) : Bounds := ⟨inv a.val,
  div (neg a.d1) (sq a.val),
  div (sub (mul (point 2) (sq a.d1)) (mul a.val a.d2)) (mul (sq a.val) a.val)⟩
def boxLogarithm (a : Bounds) (out : Box) : Bounds := ⟨out,
  div a.d1 a.val,div (sub (mul a.d2 a.val) (sq a.d1)) (sq a.val)⟩
def boxExponential (a : Bounds) (out : Box) : Bounds := ⟨out,
  mul a.d1 out,mul (add a.d2 (sq a.d1)) out⟩
def boxArctangent (a : Bounds) (out : Box) : Bounds :=
  let den := add (point 1) (sq a.val)
  ⟨out,div a.d1 den,
    div (sub (mul a.d2 den) (mul (mul (point 2) a.val) (sq a.d1))) (sq den)⟩

theorem encloses_narrow {a b : Bounds} {j : Jet} {x : ℝ}
    (h : Encloses a j x) (hn : narrow a b) : Encloses b j x :=
  ⟨holds_subset h.1 hn.1,holds_subset h.2.1 hn.2.1,holds_subset h.2.2 hn.2.2⟩

theorem encloses_constant {v : Box} {r x : ℝ} (h : Holds v r) :
    Encloses (boxConst v) (constant r) x := ⟨h,holds_zero,holds_zero⟩
theorem encloses_variable {v : Box} {x : ℝ} (h : Holds v x) :
    Encloses (boxVar v) variableJet x := ⟨h,holds_one,holds_zero⟩
theorem encloses_plus {a b : Bounds} {j k : Jet} {x : ℝ}
    (ha : Encloses a j x) (hb : Encloses b k x) :
    Encloses (boxPlus a b) (plus j k) x :=
  ⟨holds_add ha.1 hb.1,holds_add ha.2.1 hb.2.1,holds_add ha.2.2 hb.2.2⟩
theorem encloses_minus {a : Bounds} {j : Jet} {x : ℝ} (ha : Encloses a j x) :
    Encloses (boxMinus a) (minus j) x :=
  ⟨holds_neg ha.1,holds_neg ha.2.1,holds_neg ha.2.2⟩
theorem encloses_times {a b : Bounds} {j k : Jet} {x : ℝ}
    (ha : Encloses a j x) (hb : Encloses b k x) :
    Encloses (boxTimes a b) (times j k) x :=
  ⟨holds_mul ha.1 hb.1,
   holds_add (holds_mul ha.2.1 hb.1) (holds_mul ha.1 hb.2.1),
   holds_add (holds_add (holds_mul ha.2.2 hb.1)
     (holds_mul (holds_mul (holds_two) ha.2.1) hb.2.1)) (holds_mul ha.1 hb.2.2)⟩

theorem square_lo_pos {a : Box} (h : 0<a.lo) (hab : a.lo≤a.hi) : 0<(sq a).lo := by
  have hh : 0<a.hi := h.trans_le hab
  simp only [Interval.sq,Interval.mul,lt_min_iff]
  exact ⟨⟨mul_pos h h,mul_pos h hh⟩,⟨mul_pos hh h,mul_pos hh hh⟩⟩

theorem cube_lo_pos {a : Box} (h : 0<a.lo) (hab : a.lo≤a.hi) :
    0<(mul (sq a) a).lo := by
  have hs := square_lo_pos h hab
  have hh : 0<a.hi := h.trans_le hab
  have hsh : 0<(sq a).hi := by
    apply lt_of_lt_of_le (mul_pos h h)
    simp only [Interval.sq,Interval.mul,le_max_iff]
    exact Or.inl (Or.inl le_rfl)
  simp only [Interval.mul,lt_min_iff]
  exact ⟨⟨mul_pos hs h,mul_pos hs hh⟩,⟨mul_pos hsh h,mul_pos hsh hh⟩⟩

theorem encloses_inverse {a : Bounds} {j : Jet} {x : ℝ}
    (ha : Encloses a j x) (hp : 0<a.val.lo) :
    Encloses (boxInverse a) (inverse j) x := by
  have hab : a.val.lo≤a.val.hi := by exact_mod_cast ha.1.1.trans ha.1.2
  dsimp only [Encloses,boxInverse,inverse]
  refine ⟨?_,holds_div (holds_neg ha.2.1) (holds_sq ha.1) (square_lo_pos hp hab),?_⟩
  · simpa only [one_div] using holds_inv ha.1 hp
  · have h := holds_div (holds_sub (holds_mul (holds_two) (holds_sq ha.2.1))
      (holds_mul ha.1 ha.2.2)) (holds_mul (holds_sq ha.1) ha.1) (cube_lo_pos hp hab)
    convert h using 1
    ring

theorem encloses_logarithm {a : Bounds} {out : Box} {j : Jet} {x : ℝ}
    (ha : Encloses a j x) (hp : 0<a.val.lo) (ho : Holds out (Real.log (j.val x))) :
    Encloses (boxLogarithm a out) (logarithm j) x := by
  have hab : a.val.lo≤a.val.hi := by exact_mod_cast ha.1.1.trans ha.1.2
  exact ⟨ho,holds_div ha.2.1 ha.1 hp,
    holds_div (holds_sub (holds_mul ha.2.2 ha.1) (holds_sq ha.2.1))
      (holds_sq ha.1) (square_lo_pos hp hab)⟩

theorem encloses_exponential {a : Bounds} {out : Box} {j : Jet} {x : ℝ}
    (ha : Encloses a j x) (ho : Holds out (Real.exp (j.val x))) :
    Encloses (boxExponential a out) (exponential j) x :=
  ⟨ho,holds_mul ha.2.1 ho,holds_mul (holds_add ha.2.2 (holds_sq ha.2.1)) ho⟩

theorem encloses_arctangent {a : Bounds} {out : Box} {j : Jet} {x : ℝ}
    (ha : Encloses a j x) (ho : Holds out (Real.arctan (j.val x)))
    (hp : 0<(add (point 1) (sq a.val)).lo) :
    Encloses (boxArctangent a out) (arctangent j) x := by
  have hd := holds_add (holds_one) (holds_sq ha.1)
  have hab : (add (point 1) (sq a.val)).lo≤(add (point 1) (sq a.val)).hi := by
    exact_mod_cast hd.1.trans hd.2
  exact ⟨ho,holds_div ha.2.1 hd hp,
    holds_div (holds_sub (holds_mul ha.2.2 hd)
      (holds_mul (holds_mul (holds_two) ha.1) (holds_sq ha.2.1)))
      (holds_sq hd) (square_lo_pos hp hab)⟩

end CK.Certificate.CompactJet
