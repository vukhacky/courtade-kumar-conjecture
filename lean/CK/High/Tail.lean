module

public import CK.High.TailEndpointBounds
public import CK.High.SpectralGate

/-! The complete analytic spectral tail for every dimension and every
height `u ≥ 8`. The finite endpoint maximum below supplies a genuine common
spectral bound, with no supremum or numerical assumptions. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def tailRetainedBound (u : ℝ) : ℝ :=
  max (tailLogarithmicMajorant u (7/2))
    (max (tailQuadraticMajorant u (profileHeight (Real.tanh u) (1/8)))
      (tailQuadraticMajorant u (profileHeight (Real.tanh u) (tailAlpha u))))

def tailGateBound (u : ℝ) : ℝ :=
  max (Real.tanh u+(Real.pi^2/4)*spectralTau (tailGamma u) (tailT u) (Real.tanh u) (7/2))
    (tailRetainedBound u)

theorem tail_retained_bound_lt {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    tailRetainedBound u < spectralNumerator (tailGamma u) (tailT u) (Real.tanh u)/u := by
  unfold tailRetainedBound
  exact max_lt (tail_logarithmic_at_cutoff_lt hu)
    (max_lt (tail_quadratic_one_eighth_lt hu) (tail_quadratic_alpha_lt hu))

theorem tail_gate_bound_lt {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    u*tailGateBound u < spectralNumerator (tailGamma u) (tailT u) (Real.tanh u) := by
  have hu0 : 0 < u := by linarith
  have hfirst : Real.tanh u+(Real.pi^2/4)*
      spectralTau (tailGamma u) (tailT u) (Real.tanh u) (7/2) <
      spectralNumerator (tailGamma u) (tailT u) (Real.tanh u)/u :=
    (lt_div_iff₀ hu0).mpr (by nlinarith only [tail_discarded_gate hu])
  have h := max_lt hfirst (tail_retained_bound_lt hu)
  have hm := (lt_div_iff₀ hu0).mp h
  unfold tailGateBound
  nlinarith only [hm]

theorem tail_retained_cost_le {u a : ℝ} (hu : (8 : ℝ) ≤ u)
    (ha : a ∈ Icc (profileCoefficient (Real.tanh u) (7/2)) (tailAlpha u)) :
    spectralCost (tailGamma u) (tailT u) (Real.tanh u) a ≤ tailRetainedBound u := by
  have hr := tail_tanh_mem hu
  have hu0 : 0 < u := by linarith
  have ha0 : 0 < a := (profileCoefficient_pos hr (by norm_num : (0 : ℝ) < 7/2)).trans_le ha.1
  have ha1 : a ≤ 1 := ha.2.trans (tailAlpha_mem hu).2.le
  have hv := profileHeight_pos hr ha0
  have hvu := profileHeight_le_artanh hr ⟨ha0.le,ha1⟩
  rw [Real.artanh_tanh] at hvu
  have hratio : heightF u/heightF (profileHeight (Real.tanh u) a)=a := by
    exact (div_eq_iff (heightF_pos hv).ne').mpr (by nlinarith only [tail_heightF_root hu ha0])
  have hΔ := spectralDeltaTwo_nonneg (ρ := Real.tanh u)
    (show 0 < tailGamma u by unfold tailGamma; positivity) (tail_parameter_domains hu).1
  have hfirst : Real.tanh u*(profileHeight (Real.tanh u) a-
      arcsineRemainder (profileHeight (Real.tanh u) a)) ≤ tailArcsineConstant u :=
    (tail_arcsine_loss hu hv hvu).le
  by_cases ha8 : a ≤ (1/8 : ℝ)
  · have hvz : (7/2 : ℝ) ≤ profileHeight (Real.tanh u) a :=
      (profileHeight_cutoff_iff hr (by norm_num) ha0.le).mpr ha.1
    have hv8 := profileHeight_mono hr ha0.le ha8
    have hmajor := spectralCost_le_logarithmicCostMajorant hu0 hv hvu hΔ hfirst
    rw [hratio] at hmajor
    change spectralCost (tailGamma u) (tailT u) (Real.tanh u) a ≤
      tailLogarithmicMajorant u (profileHeight (Real.tanh u) a) at hmajor
    have hend := convex_positive_height_le_endpoints (tailLogarithmicMajorant_convex hu)
      (by norm_num : (0 : ℝ) < 7/2) ⟨hvz,hv8⟩
    apply (hmajor.trans hend).trans
    unfold tailRetainedBound
    apply max_le (le_max_left _ _)
    exact (tail_logarithmic_at_eighth_le_quadratic hu).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · have hv8 := profileHeight_mono hr (by norm_num : (0 : ℝ) ≤ 1/8) (le_of_not_ge ha8)
    have hvalpha := profileHeight_mono hr ha0.le ha.2
    have hmajor := spectralCost_le_quadraticCostMajorant hu0 hv hΔ hfirst
    rw [hratio] at hmajor
    change spectralCost (tailGamma u) (tailT u) (Real.tanh u) a ≤
      tailQuadraticMajorant u (profileHeight (Real.tanh u) a) at hmajor
    have hend := convex_positive_height_le_endpoints (tailQuadraticMajorant_convex hu)
      (profileHeight_pos hr (by norm_num : (0 : ℝ) < 1/8)) ⟨hv8,hvalpha⟩
    exact (hmajor.trans hend).trans (le_max_right _ _)

/-- STOC `qual:tail-derivative`, proved uniformly on the unbounded tail. -/
theorem analytic_tail_derivative {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu : (8 : ℝ) ≤ u) (f : BooleanFunction n) (hf : Monotone (lift f))
    (hδ : (3/2)*Real.exp (-u) ≤ minSignedDictatorDistance hn f)
    (hgap : 0 < informationGap (Real.tanh u) f) :
    0 < deriv (fun r => informationGap r f) (Real.tanh u) := by
  have hnc : ∃ x y, f x ≠ f y := by
    by_contra hh
    push Not at hh
    have hc : f=(fun _ : Cube n => f (fun _ => false)) := funext (fun x => hh x _)
    rw [informationGap,hc,information_const] at hgap
    have hp := phi_nonneg (Real.tanh u)
    linarith only [hgap,hp]
  have hcoeff (i : Fin n) : |fourier (lift f) {i}| ≤ tailAlpha u := by
    have hmax := singleton_le_max hn f i
    rw [minSignedDictatorDistance_eq] at hδ
    unfold tailAlpha
    linarith only [hmax,hδ]
  apply uniform_spectral_derivative (tail_parameter_domains hu).2 (tail_parameter_domains hu).1
    (tail_tanh_mem hu) (by norm_num : (0 : ℝ) < 7/2) f hf hnc hgap
    (tail_mean_transfer_pos hu).le (le_max_left _ _) hcoeff
    (fun a ha => (tail_retained_cost_le hu ha).trans (le_max_right _ _))
  rw [Real.artanh_tanh]
  exact tail_gate_bound_lt hu

end
end CK
