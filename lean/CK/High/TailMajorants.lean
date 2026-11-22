module

public import CK.High.TailBetaLog
public import CK.High.TailArcsine
public import CK.High.Majorants

/-! Convex majorants with the strict arcsine correction used in the tail. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def tailArcsineConstant (u : ℝ) : ℝ := Real.pi^2/4-4*Real.exp (-u)

def tailQuadraticMajorant (u v : ℝ) : ℝ :=
  quadraticCostMajorant (tailArcsineConstant u)
    (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u))
    (spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)) (heightF u) v

def tailLogarithmicMajorant (u v : ℝ) : ℝ :=
  logarithmicCostMajorant (tailArcsineConstant u)
    (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u))
    (spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)) (heightF u) v

theorem tailArcsineConstant_pos {u : ℝ} (hu : (8 : ℝ) ≤ u) : 0 < tailArcsineConstant u := by
  unfold tailArcsineConstant
  linarith only [pi_square_quarter_bounds.1,(tail_epsilon_bounds hu).2]

theorem tailQuadraticMajorant_convex {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (tailQuadraticMajorant u) := by
  have hγ : 0 < tailGamma u := by unfold tailGamma; positivity
  have hr := tail_tanh_mem hu
  exact quadraticCostMajorant_convex (tailArcsineConstant_pos hu).le
    (spectralDeltaTwo_nonneg hγ (tail_parameter_domains hu).1)
    (spectralDeltaOne_ge_two hγ (tail_parameter_domains hu).1 ⟨hr.1.le,hr.2.le⟩)
    (heightF_pos (by linarith : 0 < u)).le

theorem tailLogarithmicMajorant_convex {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (tailLogarithmicMajorant u) := by
  have hγ : 0 < tailGamma u := by unfold tailGamma; positivity
  have hr := tail_tanh_mem hu
  exact logarithmicCostMajorant_convex (tailArcsineConstant_pos hu).le
    (spectralDeltaTwo_nonneg hγ (tail_parameter_domains hu).1)
    (spectralDeltaOne_ge_two hγ (tail_parameter_domains hu).1 ⟨hr.1.le,hr.2.le⟩)
    (heightF_pos (by linarith : 0 < u))

theorem tailQuadraticMajorant_formula {u v a : ℝ} (hv : 0 < v)
    (hroot : a*heightF v=heightF u) :
    tailQuadraticMajorant u v =
      (tailArcsineConstant u+(Real.pi^2/4)*
        (spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)/2+
          (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u)-
            spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)/2)*a))/v := by
  unfold tailQuadraticMajorant quadraticCostMajorant
  rw [←hroot]
  field_simp [(heightF_pos hv).ne',hv.ne']
  <;> ring

theorem tailQuadraticMajorant_at_height {u a : ℝ} (hu : (8 : ℝ) ≤ u) (ha : 0 < a) :
    tailQuadraticMajorant u (profileHeight (Real.tanh u) a) =
      (tailArcsineConstant u+(Real.pi^2/4)*
        (spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)/2+
          (spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u)-
            spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u)/2)*a))/
              profileHeight (Real.tanh u) a :=
  tailQuadraticMajorant_formula (profileHeight_pos (tail_tanh_mem hu) ha) (tail_heightF_root hu ha)

end
end CK
