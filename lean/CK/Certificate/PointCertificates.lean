module
public import CK.Certificate.ArctanSeries

/-! Point certificates for logarithm, exponential (by the inverse logarithm),
and arctangent. Only rational arithmetic is executed by the checker. -/
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace CK.Certificate.Interval

def logTwoBox : Box := ⟨693147180559945309417232121458/1000000000000000000000000000000,
  693147180559945309417232121459/1000000000000000000000000000000⟩

theorem holds_logTwo : Holds logTwoBox (Real.log 2) := by
  exact logCertificate_sound (q:=2) (n:=32)
    (lower:=693147180559945309417232121458/1000000000000000000000000000000)
    (upper:=693147180559945309417232121459/1000000000000000000000000000000)
    (by unfold logCertificate; decide +kernel)

structure LogWitness where
  scale : ℤ
  base : Box
  terms : ℕ
  deriving DecidableEq, Repr

def logArgument (q : ℚ) (w : LogWitness) : ℚ := q / (2:ℚ)^w.scale
def logBox (w : LogWitness) : Box := add (mul (point (w.scale:ℚ)) logTwoBox) w.base

def CheckLog (q : ℚ) (w : LogWitness) : Prop :=
  0<q ∧ logCertificate (logArgument q w) w.base.lo w.base.hi w.terms
instance (q : ℚ) (w : LogWitness) : Decidable (CheckLog q w) :=
  by unfold CheckLog logCertificate; infer_instance

theorem checkLog_sound {q : ℚ} {w : LogWitness} (h : CheckLog q w) :
    Holds (logBox w) (Real.log (q:ℝ)) := by
  have hb := logCertificate_sound h.2
  have hq : (0:ℝ)<(q:ℝ) := by exact_mod_cast h.1
  have harg : (0:ℝ)<(logArgument q w:ℝ) := by
    change (0:ℝ)<((q/(2:ℚ)^w.scale:ℚ):ℝ)
    simp only [Rat.cast_div,Rat.cast_zpow,Rat.cast_ofNat]
    positivity
  have heq : Real.log (q:ℝ)=(w.scale:ℝ)*Real.log 2+Real.log (logArgument q w:ℝ) := by
    rw [show (q:ℝ)=(2:ℝ)^w.scale*(logArgument q w:ℝ) by
      simp only [logArgument,Rat.cast_div,Rat.cast_zpow,Rat.cast_ofNat]
      field_simp]
    rw [Real.log_mul (by positivity) harg.ne',Real.log_zpow]
  rw [heq]
  simpa [logBox,point] using holds_add (holds_mul (holds_point (w.scale:ℚ)) holds_logTwo) hb

def CheckLogRange (a out : Box) (wl wu : LogWitness) : Prop :=
  CheckLog a.lo wl ∧ CheckLog a.hi wu ∧ out.lo≤(logBox wl).lo ∧ (logBox wu).hi≤out.hi
instance (a out : Box) (wl wu : LogWitness) : Decidable (CheckLogRange a out wl wu) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem checkLogRange_sound {a out : Box} {wl wu : LogWitness} {x : ℝ}
    (h : CheckLogRange a out wl wu) (ha : Holds a x) : Holds out (Real.log x) := by
  have hl := checkLog_sound h.1
  have hu := checkLog_sound h.2.1
  have hp : (0:ℝ)<(a.lo:ℝ) := by exact_mod_cast h.1.1
  have hpx := hp.trans_le ha.1
  constructor
  · have hh : (out.lo:ℝ)≤((logBox wl).lo:ℝ) := by exact_mod_cast h.2.2.1
    exact hh.trans (hl.1.trans (Real.log_le_log hp ha.1))
  · have hh : ((logBox wu).hi:ℝ)≤(out.hi:ℝ) := by exact_mod_cast h.2.2.2
    exact (Real.log_le_log hpx ha.2).trans (hu.2.trans hh)

def CheckExpRange (a out : Box) (wl wu : LogWitness) : Prop :=
  CheckLog out.lo wl ∧ CheckLog out.hi wu ∧ (logBox wl).hi≤a.lo ∧ a.hi≤(logBox wu).lo
instance (a out : Box) (wl wu : LogWitness) : Decidable (CheckExpRange a out wl wu) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem checkExpRange_sound {a out : Box} {wl wu : LogWitness} {x : ℝ}
    (h : CheckExpRange a out wl wu) (ha : Holds a x) : Holds out (Real.exp x) := by
  have hl := checkLog_sound h.1
  have hu := checkLog_sound h.2.1
  have hpl : (0:ℝ)<(out.lo:ℝ) := by exact_mod_cast h.1.1
  have hpu : (0:ℝ)<(out.hi:ℝ) := by exact_mod_cast h.2.1.1
  constructor
  · apply (Real.log_le_iff_le_exp hpl).mp
    have hh : ((logBox wl).hi:ℝ)≤(a.lo:ℝ) := by exact_mod_cast h.2.2.1
    exact hl.2.trans (hh.trans ha.1)
  · apply (Real.le_log_iff_exp_le hpu).mp
    have hh : (a.hi:ℝ)≤((logBox wu).lo:ℝ) := by exact_mod_cast h.2.2.2
    exact ha.2.trans (hh.trans hu.1)

def atanSmallBox (q : ℚ) (n : ℕ) : Box :=
  if 0≤q then ⟨atanSeries q (2*n),atanSeries q (2*n+1)⟩
  else neg ⟨atanSeries (-q) (2*n),atanSeries (-q) (2*n+1)⟩

theorem holds_atanSmallBox {q : ℚ} (hq : |q|<1) (n : ℕ) :
    Holds (atanSmallBox q n) (Real.arctan (q:ℝ)) := by
  unfold atanSmallBox
  split_ifs with hpos
  · exact atanSeries_bounds ⟨hpos,(le_abs_self q).trans_lt hq⟩ n
  · have hb : Holds ⟨atanSeries (-q) (2*n), atanSeries (-q) (2*n+1)⟩ (Real.arctan (((-q):ℚ):ℝ)) :=
      atanSeries_bounds (q := -q) ⟨by linarith,(neg_le_abs q).trans_lt hq⟩ n
    have h := holds_neg hb
    simpa only [Rat.cast_neg,Real.arctan_neg,neg_neg] using h

def atanBox (q : ℚ) (n : ℕ) : Box :=
  if q≤1/2 then atanSmallBox q n
  else if 2≤q then sub (mul piBox (point (1/2))) (atanSmallBox (1/q) n)
  else add (mul piBox (point (1/4))) (atanSmallBox ((q-1)/(q+1)) n)

theorem holds_atanBox {q : ℚ} (hq : 0≤q) (n : ℕ) : Holds (atanBox q n) (Real.arctan (q:ℝ)) := by
  unfold atanBox
  split_ifs with hsmall hlarge
  · exact holds_atanSmallBox (by rw [abs_of_nonneg hq]; linarith) n
  · have hp : (0:ℝ)<(q:ℝ) := by exact_mod_cast (show (0:ℚ)<q by linarith)
    have hbox := holds_sub (holds_mul holds_pi (holds_point (1/2)))
      (holds_atanSmallBox (q:=1/q) (by rw [abs_of_pos (by positivity)]; apply (div_lt_one (by linarith)).mpr; linarith) n)
    have heq : Real.pi*((1/2:ℚ):ℝ)-Real.arctan ((1/q:ℚ):ℝ)=Real.arctan (q:ℝ) := by
      norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
      simp only [div_eq_mul_inv,one_mul]
      rw [Real.arctan_inv_of_pos hp]
      ring
    rw [heq] at hbox
    exact hbox
  · have hp : (0:ℝ)<(q:ℝ) := by exact_mod_cast (show (0:ℚ)<q by linarith)
    have habs : |(q-1)/(q+1)|<1 := by
      rw [abs_lt]
      constructor
      · apply (lt_div_iff₀ (by linarith : (0:ℚ)<q+1)).mpr; linarith
      · apply (div_lt_one (by linarith : (0:ℚ)<q+1)).mpr; linarith
    have hbox := holds_add (holds_mul holds_pi (holds_point (1/4))) (holds_atanSmallBox habs n)
    simpa only [Rat.cast_div,Rat.cast_sub,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat,
      mul_one_div,← arctan_middle hp] using hbox

def CheckAtanRange (a out : Box) (n : ℕ) : Prop :=
  0≤a.lo ∧ out.lo≤(atanBox a.lo n).lo ∧ (atanBox a.hi n).hi≤out.hi
instance (a out : Box) (n : ℕ) : Decidable (CheckAtanRange a out n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem checkAtanRange_sound {a out : Box} {n : ℕ} {x : ℝ}
    (h : CheckAtanRange a out n) (ha : Holds a x) : Holds out (Real.arctan x) := by
  have hlu : a.lo≤a.hi := by exact_mod_cast ha.1.trans ha.2
  have hl := holds_atanBox h.1 n
  have hu := holds_atanBox (h.1.trans hlu) n
  constructor
  · have hh : (out.lo:ℝ)≤((atanBox a.lo n).lo:ℝ) := by exact_mod_cast h.2.1
    exact hh.trans (hl.1.trans (Real.arctan_le_arctan_iff.mpr ha.1))
  · have hh : ((atanBox a.hi n).hi:ℝ)≤(out.hi:ℝ) := by exact_mod_cast h.2.2
    exact (Real.arctan_le_arctan_iff.mpr ha.2).trans (hu.2.trans hh)

end CK.Certificate.Interval
