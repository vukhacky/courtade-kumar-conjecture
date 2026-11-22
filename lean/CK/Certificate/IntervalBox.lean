module
public import CK.Certificate.RationalInterval
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Rational interval arithmetic used by the reflected compact certificate.
The executable rules have proved enclosure semantics; proposed intervals are
validated by exact rational comparison, never by floating point. -/
@[expose] public section
set_option autoImplicit false
namespace CK.Certificate.Interval

structure Box where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def Holds (b : Box) (x : ℝ) : Prop := RationalBound x b.lo b.hi

def point (q : ℚ) : Box := ⟨q,q⟩
def add (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩
def neg (a : Box) : Box := ⟨-a.hi,-a.lo⟩
def sub (a b : Box) : Box := add a (neg b)
def mul (a b : Box) : Box :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
def inv (a : Box) : Box := ⟨1/a.hi,1/a.lo⟩
def div (a b : Box) : Box := mul a (inv b)
def sq (a : Box) : Box := mul a a
def subset (a b : Box) : Prop := b.lo≤a.lo ∧ a.hi≤b.hi
instance (a b : Box) : Decidable (subset a b) := inferInstanceAs (Decidable (_ ∧ _))
def magnitude (a : Box) : ℚ := max (-a.lo) a.hi

theorem holds_point (q : ℚ) : Holds (point q) (q : ℝ) := ⟨le_rfl,le_rfl⟩
theorem holds_add {a b : Box} {x y : ℝ} (ha : Holds a x) (hb : Holds b y) :
    Holds (add a b) (x+y) := rationalBound_add ha hb le_rfl le_rfl
theorem holds_neg {a : Box} {x : ℝ} (ha : Holds a x) : Holds (neg a) (-x) :=
  rationalBound_neg ha le_rfl le_rfl
theorem holds_sub {a b : Box} {x y : ℝ} (ha : Holds a x) (hb : Holds b y) :
    Holds (sub a b) (x-y) := by simpa [sub,sub_eq_add_neg] using holds_add ha (holds_neg hb)
theorem holds_mul {a b : Box} {x y : ℝ} (ha : Holds a x) (hb : Holds b y) :
    Holds (mul a b) (x*y) := by
  apply rationalBound_mul ha hb
  · simp only [mul, min_le_iff]; exact ⟨Or.inl (Or.inl le_rfl),Or.inl (Or.inr le_rfl),Or.inr (Or.inl le_rfl),Or.inr (Or.inr le_rfl)⟩
  · simp only [mul, le_max_iff]; exact ⟨Or.inl (Or.inl le_rfl),Or.inl (Or.inr le_rfl),Or.inr (Or.inl le_rfl),Or.inr (Or.inr le_rfl)⟩
theorem holds_inv {a : Box} {x : ℝ} (ha : Holds a x) (hpos : 0<a.lo) :
    Holds (inv a) (1/x) := rationalBound_inv ha hpos le_rfl le_rfl
theorem holds_div {a b : Box} {x y : ℝ} (ha : Holds a x) (hb : Holds b y) (hp : 0<b.lo) :
    Holds (div a b) (x/y) := by simpa [div,div_eq_mul_inv] using holds_mul ha (holds_inv hb hp)
theorem holds_sq {a : Box} {x : ℝ} (ha : Holds a x) : Holds (sq a) (x^2) := by
  simpa [sq,pow_two] using holds_mul ha ha

theorem holds_subset {a b : Box} {x : ℝ} (ha : Holds a x) (hab : subset a b) : Holds b x :=
  rationalBound_widen ha hab.1 hab.2

theorem holds_pos {a : Box} {x : ℝ} (ha : Holds a x) (hp : 0<a.lo) : 0<x :=
  lt_of_lt_of_le (by exact_mod_cast hp) ha.1

theorem holds_abs {a : Box} {x : ℝ} (ha : Holds a x) : |x|≤(magnitude a : ℝ) := by
  rw [abs_le]
  have h₁ : -(a.lo:ℝ)≤(magnitude a:ℝ) := by exact_mod_cast (le_max_left (-a.lo) a.hi)
  have h₂ : (a.hi:ℝ)≤(magnitude a:ℝ) := by exact_mod_cast (le_max_right (-a.lo) a.hi)
  constructor <;> linarith [ha.1,ha.2]

def piBox : Box := ⟨314159265358979323846/100000000000000000000,
  314159265358979323847/100000000000000000000⟩

theorem holds_pi : Holds piBox Real.pi := by
  have hl := Real.pi_gt_d20.le
  have hu := Real.pi_lt_d20.le
  norm_num at hl hu
  norm_num [Holds,RationalBound,piBox]
  exact ⟨hl,hu⟩

end CK.Certificate.Interval
