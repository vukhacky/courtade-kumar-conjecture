module

public import CK.Certificate.Bernstein
public import Mathlib.Analysis.Real.Sqrt

/-! Exact full-interval high branch of the Yu scalar cap, expressed via
p=(1-a)/2. The quartic comparison is proved by a Bernstein certificate;
its passage to the square-root expression includes positivity hypotheses. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate
noncomputable section

def fourierCapQuartic (u : ℝ) : ℝ :=
  ((193027/250000 : ℝ)-1+2*u+u^2)^2-8*u^3

def fourierCapBernstein : List BernsteinTerm3 :=
  [(70713/7812500000, 0, 0, 0),
    (187031601/3906250000, 1, 0, 0),
    (2469615931/15625000000, 2, 0, 0),
    (2399623979/15625000000, 3, 0, 0),
    (2793422729/62500000000, 4, 0, 0)]

theorem fourierCapBernstein_checked : checkBernsteinNonneg fourierCapBernstein = true := by
  norm_num [checkBernsteinNonneg, fourierCapBernstein]

theorem fourierCapBernstein_identity (t : ℝ) :
    fourierCapQuartic ((31/100 : ℝ)+(19/100)*t)-(1/100000 : ℝ) =
      evalBernstein3 4 fourierCapBernstein t 0 0 := by
  norm_num [fourierCapQuartic, evalBernstein3, evalBernsteinTerm3, fourierCapBernstein]
  ring

theorem fourierCapQuartic_pos {u : ℝ} (hu : u ∈ Set.Icc (31/100 : ℝ) (1/2)) :
    0 < fourierCapQuartic u := by
  let t : ℝ := (u-31/100)/(1/2-31/100)
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := unitParameter_mem (by norm_num) hu
  have hid : (31/100 : ℝ)+(19/100)*t = u := by dsimp [t]; ring
  have h := checkBernsteinNonneg_sound (d := 4) fourierCapBernstein_checked ht
    (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
  rw [← fourierCapBernstein_identity, hid] at h
  linarith

theorem fourierCap_high_lt {a : ℝ} (ha : a ∈ Set.Icc (1/2 : ℝ) (69/100)) :
    a^2 + 8*((1-a)/2)*Real.sqrt ((1-a)/2) - 8*((1-a)/2)^2 < 193027/250000 := by
  let u : ℝ := 1-a
  let p : ℝ := (1-a)/2
  have hu : u ∈ Set.Icc (31/100 : ℝ) (1/2) := by dsimp [u]; constructor <;> linarith [ha.1,ha.2]
  have hp : 0 ≤ p := by dsimp [p]; linarith [ha.2]
  have hB : 0 < (193027/250000 : ℝ)-1+2*u+u^2 := by nlinarith [hu.1]
  have hP := fourierCapQuartic_pos hu
  unfold fourierCapQuartic at hP
  have hs : (8*p*Real.sqrt p)^2 = 8*u^3 := by
    rw [mul_pow, Real.sq_sqrt hp]
    dsimp [p,u]
    ring
  have hlt : 8*p*Real.sqrt p < (193027/250000 : ℝ)-1+2*u+u^2 := by
    nlinarith only [hs,hP,hB]
  dsimp [p,u] at hlt
  nlinarith only [hlt]

end
end CK.Certificate
