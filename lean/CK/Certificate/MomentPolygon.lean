module

public import CK.Certificate.MomentData
public import CK.Certificate.Pilot

/-! The moment polygon is parametrized by the unit square, and the squared correlation by the unit interval. A kernel-checked Bernstein identity proves the lower bound throughout this domain. -/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace CK.Certificate
noncomputable section

def localMomentQSquared (r a b : ℝ) : ℝ :=
  (17 / 12 : ℝ) * (r * (a + b) - 1) - r * b / 5 + 9 / 13 -
    (r * (a^2 + b^2) + r^2 * b^2) / 2 -
    (r^2 * (a^4 + b^4 + 6 * a^2 * b^2) +
      6 * r^3 * b^2 * (a^2 + b^2) + r^4 * b^4) / 5 - 1 / 198

theorem localMomentQ_eq_squared (ρ a b : ℝ) :
    localMomentQ ρ a b = localMomentQSquared (ρ^2) a b := by
  unfold localMomentQ localMomentQSquared
  ring

namespace P01

def polygonA (u : ℝ) : ℝ := 2/3 + (76043/100000 - 2/3) * u
def polygonLower (a : ℝ) : ℝ := (64/25 - 3*a) / 7
def polygonUpper (a : ℝ) : ℝ := 1 - a
def polygonB (u v : ℝ) : ℝ :=
  polygonLower (polygonA u) + (polygonUpper (polygonA u) - polygonLower (polygonA u)) * v
def correlationSquared (w : ℝ) : ℝ :=
  (39/40 : ℝ)^2 + ((49/50 : ℝ)^2 - (39/40 : ℝ)^2) * w
def parameterPolynomial (u v w : ℝ) : ℝ :=
  localMomentQSquared (correlationSquared w) (polygonA u) (polygonB u v)

/-- The moment polynomial in Bernstein form. -/
theorem momentBernstein_identity (u v w : ℝ) :
    parameterPolynomial u v w - 1/1000 =
      evalBernstein3 4 momentBernsteinData u v w := by
  norm_num [parameterPolynomial, localMomentQSquared, correlationSquared,
    polygonA, polygonB, polygonLower, polygonUpper,
    evalBernstein3, evalBernsteinTerm3, momentBernsteinData]
  ring

theorem parameterPolynomial_lower_bound {u v w : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hw : w ∈ Set.Icc (0 : ℝ) 1) : 1/1000 ≤ parameterPolynomial u v w := by
  have h := checkBernsteinNonneg_sound (d := 4) momentBernsteinData_checked hu hv hw
  rw [← momentBernstein_identity] at h
  linarith

/-- Exact coverage of the source polygon and of the complete rho band. -/
theorem source_domain_parameterization {ρ a b : ℝ}
    (hρ : ρ ∈ Set.Icc (39/40 : ℝ) (49/50))
    (ha : a ∈ Set.Icc (2/3 : ℝ) (76043/100000))
    (hab : a + b ≤ 1) (hl : (64/25 : ℝ) ≤ 3*a + 7*b) :
    ∃ u ∈ Set.Icc (0 : ℝ) 1, ∃ v ∈ Set.Icc (0 : ℝ) 1,
      ∃ w ∈ Set.Icc (0 : ℝ) 1,
        polygonA u = a ∧ polygonB u v = b ∧ correlationSquared w = ρ^2 := by
  let u := (a - 2/3) / (76043/100000 - 2/3)
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := unitParameter_mem (by norm_num) ha
  have hau : polygonA u = a := interpolate_unitParameter (by norm_num)
  have hwidth : polygonLower a < polygonUpper a := by
    dsimp [polygonLower, polygonUpper]
    linarith [ha.2]
  have hb : b ∈ Set.Icc (polygonLower a) (polygonUpper a) := by
    dsimp [polygonLower, polygonUpper]
    constructor <;> linarith
  let v := (b - polygonLower a) / (polygonUpper a - polygonLower a)
  have hv : v ∈ Set.Icc (0 : ℝ) 1 := unitParameter_mem hwidth hb
  have hbv : polygonB u v = b := by
    unfold polygonB
    rw [hau]
    exact interpolate_unitParameter hwidth
  have hr : ρ^2 ∈ Set.Icc ((39/40 : ℝ)^2) ((49/50 : ℝ)^2) := by
    constructor <;> nlinarith [hρ.1, hρ.2]
  let w := (ρ^2 - (39/40 : ℝ)^2) / ((49/50 : ℝ)^2 - (39/40 : ℝ)^2)
  have hw : w ∈ Set.Icc (0 : ℝ) 1 := unitParameter_mem (by norm_num) hr
  have hrw : correlationSquared w = ρ^2 := interpolate_unitParameter (by norm_num)
  exact ⟨u, hu, v, hv, w, hw, hau, hbv, hrw⟩

end P01

/-- The moment polynomial is positive throughout the source polygon, uniformly on the correlation interval [39/40,49/50]. -/
theorem localMomentQ_lower_bound {ρ a b : ℝ}
    (hρ : ρ ∈ Set.Icc (39/40 : ℝ) (49/50))
    (ha : a ∈ Set.Icc (2/3 : ℝ) (76043/100000))
    (hab : a + b ≤ 1) (hl : (64/25 : ℝ) ≤ 3*a + 7*b) :
    (1/1000 : ℝ) ≤ localMomentQ ρ a b := by
  obtain ⟨u, hu, v, hv, w, hw, hau, hbv, hrw⟩ :=
    P01.source_domain_parameterization hρ ha hab hl
  have h := P01.parameterPolynomial_lower_bound hu hv hw
  simpa only [P01.parameterPolynomial, hau, hbv, hrw, localMomentQ_eq_squared] using h

theorem localMomentQ_pos {ρ a b : ℝ}
    (hρ : ρ ∈ Set.Icc (39/40 : ℝ) (49/50))
    (ha : a ∈ Set.Icc (2/3 : ℝ) (76043/100000))
    (hab : a + b ≤ 1) (hl : (64/25 : ℝ) ≤ 3*a + 7*b) :
    0 < localMomentQ ρ a b := by
  linarith [localMomentQ_lower_bound hρ ha hab hl]

end
end CK.Certificate
