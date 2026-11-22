module

public import CK.High.CostMajorants
public import CK.High.ProfileInverseBounds
public import CK.High.CompactOverlap
public import CK.High.SpectralGate

/-! Analytic compact-range consumer.  Four strict endpoint bounds and the
discarded-coordinate bound imply the actual positive-gap derivative. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def quadraticCoefficientValue (ρ c Δ₁ Δ₂ a v : ℝ) : ℝ :=
  ρ*(1-arcsineRemainderSlope c)+
    (ρ*(c*arcsineRemainderSlope c-arcsineRemainder c)+
      (Real.pi^2/4)*(Δ₂/2+(Δ₁-Δ₂/2)*a))/v

def logarithmicCoefficientValue (ρ c Δ₁ Δ₂ a v : ℝ) : ℝ :=
  ρ*(1-arcsineRemainderSlope c)+
    (ρ*(c*arcsineRemainderSlope c-arcsineRemainder c)+
      (Real.pi^2/4)*(2*Δ₂*(1-a/4)/Real.log (4/a)+(Δ₁-Δ₂)*a))/v

theorem quadraticTangentMajorant_eq_coefficient (ρ c Δ₁ Δ₂ K v : ℝ) :
    quadraticTangentMajorant ρ c Δ₁ Δ₂ K v =
      quadraticCoefficientValue ρ c Δ₁ Δ₂ (K/heightF v) v := by
  unfold quadraticTangentMajorant quadraticCostMajorant quadraticCoefficientValue
  ring

theorem logarithmicTangentMajorant_eq_coefficient {ρ c Δ₁ Δ₂ K v : ℝ}
    (hK : 0 < K) (hv : 0 < v) (ha : K/heightF v ≤ 1) :
    logarithmicTangentMajorant ρ c Δ₁ Δ₂ K v =
      logarithmicCoefficientValue ρ c Δ₁ Δ₂ (K/heightF v) v := by
  rw [logarithmicTangentMajorant,logarithmicCostMajorant_formula hK hv ha]
  unfold logarithmicCoefficientValue
  ring

theorem quadraticCoefficientValue_mono {ρ c Δ₁ Δ₂ a b v : ℝ}
    (hv : 0 < v) (hΔ₂ : 0 ≤ Δ₂) (hΔ : Δ₂ ≤ Δ₁) (hab : a ≤ b) :
    quadraticCoefficientValue ρ c Δ₁ Δ₂ a v ≤ quadraticCoefficientValue ρ c Δ₁ Δ₂ b v := by
  have hc : 0 ≤ Δ₁-Δ₂/2 := by linarith only [hΔ₂,hΔ]
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hab hc)
    (show 0 ≤ Real.pi^2/4 by positivity)
  have hd := div_le_div_of_nonneg_right hm hv.le
  unfold quadraticCoefficientValue
  simp only [div_eq_mul_inv] at hd ⊢
  nlinarith only [hd]

def compactUpperCoefficient (u : ℝ) : ℝ :=
  Real.exp (-2*(u-compactTop u))*(2*u+1)/(2*compactTop u+1)

def compactLogLow (u : ℝ) : ℝ :=
  logarithmicTangentMajorant (Real.tanh u) (compactZ u)
    (spectralDeltaOne (compactGamma u) (compactT u) (Real.tanh u))
    (spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u)) (heightF u) (compactZ u)

def compactLogMiddle (u : ℝ) : ℝ :=
  logarithmicTangentMajorant (Real.tanh u) (compactZ u)
    (spectralDeltaOne (compactGamma u) (compactT u) (Real.tanh u))
    (spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u)) (heightF u) (2*u/3)

def compactQuadMiddle (u : ℝ) : ℝ :=
  quadraticTangentMajorant (Real.tanh u) (compactTop u)
    (spectralDeltaOne (compactGamma u) (compactT u) (Real.tanh u))
    (spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u)) (heightF u) (2*u/3)

def compactQuadTop (u : ℝ) : ℝ :=
  quadraticCoefficientValue (Real.tanh u) (compactTop u)
    (spectralDeltaOne (compactGamma u) (compactT u) (Real.tanh u))
    (spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u))
      (compactUpperCoefficient u) (compactTop u)

def compactDiscardedCost (u : ℝ) : ℝ :=
  Real.tanh u+(Real.pi^2/4)*
    spectralTau (compactGamma u) (compactT u) (Real.tanh u) (compactZ u)

def compactNumerator (u : ℝ) : ℝ :=
  spectralNumerator (compactGamma u) (compactT u) (Real.tanh u)

theorem compact_profile_inverse {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    profileHeight (Real.tanh u) (compactAlpha u) ≤ compactTop u ∧
      heightF u/heightF (compactTop u) ≤ compactUpperCoefficient u := by
  have ha := compactAlpha_mem hu
  have h := explicit_profile_inverse (by linarith only [hu] : (2 : ℝ) < u)
    ⟨ha.1,ha.2.le⟩ (compactAlpha_inverse_domain hu)
  exact ⟨h.1,h.2.2⟩

theorem compact_top_majorant_le {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    quadraticTangentMajorant (Real.tanh u) (compactTop u)
      (spectralDeltaOne (compactGamma u) (compactT u) (Real.tanh u))
      (spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u))
        (heightF u) (compactTop u) ≤ compactQuadTop u := by
  have hd := compact_height_domains hu
  have hr := tanh_mem_Ioo_positive (show 0 < u by linarith only [hu])
  rw [quadraticTangentMajorant_eq_coefficient]
  exact quadraticCoefficientValue_mono (hd.1.trans (hd.2.1.trans hd.2.2.1))
    (spectralDeltaTwo_nonneg (compactGamma_pos _) (compact_parameter_domains hu).1)
    (spectralDeltaOne_ge_two (compactGamma_pos _) (compact_parameter_domains hu).1 ⟨hr.1.le,hr.2.le⟩)
    (compact_profile_inverse hu).2

theorem compact_cost_bound_of_endpoints {u b : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (hLL : compactLogLow u ≤ b) (hLM : compactLogMiddle u ≤ b)
    (hQM : compactQuadMiddle u ≤ b) (hQT : compactQuadTop u ≤ b) :
    ∀ a ∈ Icc (profileCoefficient (Real.tanh u) (compactZ u)) (compactAlpha u),
      spectralCost (compactGamma u) (compactT u) (Real.tanh u) a ≤ b := by
  have hu0 : 0 < u := by linarith only [hu]
  have hr := tanh_mem_Ioo_positive hu0
  have hd := compact_height_domains hu
  have hD2 := spectralDeltaTwo_nonneg (ρ := Real.tanh u)
    (compactGamma_pos u) (compact_parameter_domains hu).1
  have hD := spectralDeltaOne_ge_two (compactGamma_pos u)
    (compact_parameter_domains hu).1 ⟨hr.1.le,hr.2.le⟩
  intro a ha
  have ha0 : 0 < a := (profileCoefficient_pos hr hd.1).trans_le ha.1
  have hv0 := profileHeight_pos hr ha0
  have hvl : compactZ u ≤ profileHeight (Real.tanh u) a :=
    (profileHeight_cutoff_iff hr hd.1 ha0.le).mpr ha.1
  have hvh : profileHeight (Real.tanh u) a ≤ compactTop u :=
    (profileHeight_mono hr ha0.le ha.2).trans (compact_profile_inverse hu).1
  have hid : a=heightF u/heightF (profileHeight (Real.tanh u) a) := by
    rw [←profileCoefficient_tanh_eq hu0 hv0,profileCoefficient_profileHeight hr ha0]
  by_cases hmid : profileHeight (Real.tanh u) a ≤ 2*u/3
  · have hc := logarithmicTangentMajorant_convex hr.1.le hd.1 hD2 hD (heightF_pos hu0)
    have he := convex_positive_height_le_endpoints hc hd.1 ⟨hvl,hmid⟩
    have hb := he.trans (max_le hLL hLM)
    have hcost := spectralCost_le_logarithmicTangentMajorant hu0 hv0
      (hvh.trans hd.2.2.2) hd.1 hD2
    rw [←hid] at hcost
    exact hcost.trans hb
  · have hm0 : 0 < 2*u/3 := by linarith only [hu]
    have ht0 := hd.1.trans (hd.2.1.trans hd.2.2.1)
    have hc := quadraticTangentMajorant_convex hr.1.le ht0 hD2 hD (heightF_pos hu0).le
    have he := convex_positive_height_le_endpoints hc hm0 ⟨le_of_not_ge hmid,hvh⟩
    have hb := he.trans (max_le hQM ((compact_top_majorant_le hu).trans hQT))
    have hcost := spectralCost_le_quadraticTangentMajorant hu0 hv0 ht0 hD2
    rw [←hid] at hcost
    exact hcost.trans hb

theorem compact_spectral_derivative_of_endpoints {n : ℕ} {u : ℝ}
    (hu : (9/4 : ℝ) ≤ u)
    (hB : compactDiscardedCost u < compactNumerator u/u)
    (hLL : compactLogLow u < compactNumerator u/u)
    (hLM : compactLogMiddle u < compactNumerator u/u)
    (hQM : compactQuadMiddle u < compactNumerator u/u)
    (hQT : compactQuadTop u < compactNumerator u/u)
    (f : BooleanFunction n) (hm : Monotone (lift f)) (hf : ∃ x y, f x ≠ f y)
    (hgap : 0 < informationGap (Real.tanh u) f) :
    0 < deriv (fun ρ => informationGap ρ f) (Real.tanh u) := by
  let b := max (compactDiscardedCost u)
    (max (compactLogLow u) (max (compactLogMiddle u) (max (compactQuadMiddle u) (compactQuadTop u))))
  have hb : b < compactNumerator u/u := max_lt hB (max_lt hLL (max_lt hLM (max_lt hQM hQT)))
  have hcost := compact_cost_bound_of_endpoints (b := b) hu
    ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hu0 : 0 < u := by linarith only [hu]
  apply uniform_spectral_derivative (compact_parameter_domains hu).2 (compact_parameter_domains hu).1
    (tanh_mem_Ioo_positive hu0) (compact_height_domains hu).1 f hm hf hgap
    (compact_mean_transfer_pos hu).le (le_max_left _ _)
    (fun i => (positive_gap_compact_singleton hu f hgap i).le) hcost
  rw [Real.artanh_tanh]
  change u*b < compactNumerator u
  have h := (lt_div_iff₀ hu0).mp hb
  nlinarith only [h]

end
end CK
