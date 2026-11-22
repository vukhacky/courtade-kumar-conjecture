module

public import CK.High.SpectralCost
public import CK.Functional.Harris
public import CK.High.EdgeRefinement

/-! Finite spectral loss bounds and their connection to the edge-refund inequality. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Set
namespace CK
noncomputable section

def retainedSpectralCost {n : ℕ} (γ t ρ z : ℝ) (g : Cube n → ℝ) : ℝ :=
  ∑ i ∈ spectralRetainedSet ρ z g, |fourier g {i}| *profileHeight ρ |fourier g {i}| *
    spectralCost γ t ρ |fourier g {i}|

def retainedArcsineRefund {n : ℕ} (ρ z : ℝ) (g : Cube n → ℝ) : ℝ :=
  ∑ i ∈ spectralRetainedSet ρ z g, |fourier g {i}| *arcsineRemainder (profileHeight ρ |fourier g {i}|)

theorem spectralCost_weighted_identity {γ t ρ a : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    a*profileHeight ρ a*spectralCost γ t ρ a =
      ρ*(a*profileHeight ρ a)-ρ*(a*arcsineRemainder (profileHeight ρ a)) +
        (Real.pi^2/4)*spectralDeltaTwo γ t ρ*influencePsi a +
        (Real.pi^2/4)*(spectralDeltaOne γ t ρ-spectralDeltaTwo γ t ρ)*a^2 := by
  have h := congrArg (fun x : ℝ => a*x) (spectralCost_mul_height (γ := γ) (t := t) hρ ha)
  field_simp [ha.ne'] at h
  nlinarith only [h]

theorem retainedSpectralCost_identity {n : ℕ} {γ t ρ z : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hz : 0 < z) (g : Cube n → ℝ) :
    retainedSpectralCost γ t ρ z g =
      ρ*retainedHeightBudget (spectralRetainedSet ρ z g) ρ g-
        ρ*retainedArcsineRefund ρ z g +
      (Real.pi^2/4)*spectralDeltaTwo γ t ρ*
        (∑ i ∈ spectralRetainedSet ρ z g, influencePsi |fourier g {i}|) +
      (Real.pi^2/4)*(spectralDeltaOne γ t ρ-spectralDeltaTwo γ t ρ)*
        insideSingletonEnergy (spectralRetainedSet ρ z g) g := by
  unfold retainedSpectralCost retainedHeightBudget retainedArcsineRefund insideSingletonEnergy
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,
    ← Finset.sum_sub_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [sq_abs] using spectralCost_weighted_identity (γ := γ) (t := t) hρ
    (spectralRetainedSet_pos hρ hz g hi)

theorem projection_variance_le_abs_psi {n : ℕ}
    (f : BooleanFunction n) (hm : Monotone (lift f)) (K : Finset (Fin n)) :
    variance (coordinateProjection K (lift f)) ≤ ∑ i ∈ K, influencePsi |fourier (lift f) {i}| := by
  have h := variance_projection_le_influencePsi_monotone (lift f) (fun x => sign_mem_Icc (f x)) hm K
  simpa only [abs_of_nonneg (singleton_nonneg_of_monotone hm _)] using h

theorem spectral_dirichlet_transfer {n : ℕ} {γ t ρ : ℝ}
    (hγ : max 0 (Real.exp (2*t-3)/2-t) < γ) (ht : (2 : ℝ) ≤ t)
    (hρ : ρ ∈ Icc (0 : ℝ) 1) (f : BooleanFunction n) (hm : Monotone (lift f))
    (K : Finset (Fin n)) :
    (Real.pi^2/4)*spectralQuadratic
      (fun S => shiftedMultiplier γ (signedSpectralWeight K t S)) (noise ρ (lift f))-
      γ*Certificate.arcsineSharpConstant*entropyRemainderMean (noise ρ (lift f)) ≤
        dirichlet (fun x => Real.arcsin (noise ρ (lift f) x)) := by
  have hg := noise_mem_Icc (show ρ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hρ.1],hρ.2⟩)
    (lift f) (fun x => sign_mem_Icc (f x))
  exact (spectral_arcsine_transfer (signedSpectralWeight K t)
    ((le_max_left _ _).trans_lt hγ).le (signedSpectralWeight_shift_pos K ht hγ) _ hg).trans
    (signedSpectralQuadratic_le_dirichlet K t _ (Real.monotone_arcsin.comp (noise_monotone hρ hm)))

private theorem spectral_master_ledger_of_refinement {n : ℕ} {γ t ρ z : ℝ}
    (hγ : max 0 (Real.exp (2*t-3)/2-t) < γ) (ht : (2 : ℝ) ≤ t)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hz : 0 < z)
    (f : BooleanFunction n) (hm : Monotone (lift f)) (hf : ∃ u v, f u ≠ f v)
    (hgap : 0 < informationGap ρ f)
    (hRefund : dirichlet (fun x => Real.arcsin (noise ρ (lift f) x))+
      ρ*retainedArcsineRefund ρ z (lift f) ≤ entropyProduction (noise ρ (lift f))) :
    (Real.pi^2/4)*shiftedMultiplier γ t*variance (noise ρ (lift f))-
      γ*Certificate.arcsineSharpConstant*entropyRemainderMean (noise ρ (lift f)) ≤
      (ρ+(Real.pi^2/4)*spectralTau γ t ρ z)*
        (entropyProduction (noise ρ (lift f))/ρ-
          retainedHeightBudget (spectralRetainedSet ρ z (lift f)) ρ (lift f))+
        retainedSpectralCost γ t ρ z (lift f) := by
  let K := spectralRetainedSet ρ z (lift f)
  have hr : ρ ∈ Icc (0 : ℝ) 1 := ⟨hρ.1.le,hρ.2.le⟩
  have hC : 0 ≤ Real.pi^2/4 := by positivity
  have hD2 := spectralDeltaTwo_nonneg (ρ := ρ) ((le_max_left _ _).trans_lt hγ) ht
  have hloss := mul_le_mul_of_nonneg_left (shifted_spectral_loss_bound hγ ht hr K (lift f)) hC
  have hprojection := mul_le_mul_of_nonneg_left (projection_variance_le_abs_psi f hm K)
    (mul_nonneg hC hD2)
  have hout := mul_le_mul_of_nonneg_left (outside_singleton_cost hγ hρ hz f hf hgap) hC
  have htransfer := spectral_dirichlet_transfer hγ ht hr f hm K
  rw [retainedSpectralCost_identity hρ hz]
  dsimp [K] at hloss hprojection htransfer
  have hquot : ρ*(entropyProduction (noise ρ (lift f))/ρ)=entropyProduction (noise ρ (lift f)) := by
    field_simp [hρ.1.ne']
  nlinarith only [hloss,hprojection,hout,htransfer,hRefund,hquot]

/-- The full master ledger, in its equivalent cost-budget form. The
arcsine refund and every Fourier loss are proved within the project. -/
theorem spectral_master_ledger {n : ℕ} {γ t ρ z : ℝ}
    (hγ : max 0 (Real.exp (2*t-3)/2-t) < γ) (ht : (2 : ℝ) ≤ t)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hz : 0 < z)
    (f : BooleanFunction n) (hm : Monotone (lift f)) (hf : ∃ u v, f u ≠ f v)
    (hgap : 0 < informationGap ρ f) :
    (Real.pi^2/4)*shiftedMultiplier γ t*variance (noise ρ (lift f))-
      γ*Certificate.arcsineSharpConstant*entropyRemainderMean (noise ρ (lift f)) ≤
      (ρ+(Real.pi^2/4)*spectralTau γ t ρ z)*
        (entropyProduction (noise ρ (lift f))/ρ-
          retainedHeightBudget (spectralRetainedSet ρ z (lift f)) ρ (lift f))+
        retainedSpectralCost γ t ρ z (lift f) :=
  spectral_master_ledger_of_refinement hγ ht hρ hz f hm hf hgap
    (arcsine_refinement_positive_gap hρ f hf hgap (spectralRetainedSet ρ z (lift f)))

end
end CK
