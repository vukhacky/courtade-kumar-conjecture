module

public import CK.High.JunctionScalar
public import CK.High.ExponentialLocal

/-! The near-dictator junction of the STOC argument, with the actual finite
Shannon mutual information and the full correlation interval. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem tanh_log_junction {d : ℝ} (hd : 0 < d) :
    Real.tanh (Real.log (3/(2*d)))=1-2*junctionProbability d := by
  have hq : 0 < 3/(2*d) := by positivity
  have he : Real.exp (-Real.log (3/(2*d)))=2*d/3 := by
    rw [Real.exp_neg,Real.exp_log hq]
    field_simp [hd.ne']
  rw [tanh_eq_localNoiseProbability,he]
  unfold localNoiseProbability junctionProbability
  field_simp
  <;> ring

theorem localDeficit_junction_interval {d ρ : ℝ}
    (hd : d ∈ Ioc (0 : ℝ) (1/64))
    (hρ : ρ ∈ Icc (0 : ℝ) (Real.tanh (Real.log (3/(2*d))))) :
    0 ≤ localDeficit ρ (1-2*d) := by
  have hu := hρ.2
  rw [tanh_log_junction hd.1] at hu
  have hp : (1-ρ)/2 ∈ Icc (junctionProbability d) (1/2) :=
    ⟨by linarith only [hu],by linarith only [hρ.1]⟩
  simpa only [show 1-2*((1-ρ)/2)=ρ by ring] using localDeficit_junction_parameter hd hp

theorem mutualInformation_le_phi_junction_coordinate {n : ℕ} {d ρ : ℝ}
    (hd : d ∈ Ioc (0 : ℝ) (1/64))
    (hρ : ρ ∈ Icc (0 : ℝ) (Real.tanh (Real.log (3/(2*d)))))
    (f : BooleanFunction n) (i : Fin n) (hi : 1-2*d ≤ |fourier (lift f) {i}|) :
    mutualInformation ρ f ≤ phi ρ := by
  have hr : ρ ∈ Icc (0 : ℝ) 1 := ⟨hρ.1,hρ.2.trans (Real.tanh_lt_one _).le⟩
  rw [mutualInformation_eq_information hr]
  exact information_le_phi_of_local_threshold hr
    (show 1-2*d ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hd.1,hd.2])
    f i hi (localDeficit_junction_interval hd hρ)

/-- STOC `rt:local-junction`: every Boolean function at distance in `(0,1/64]`
from a signed dictator satisfies CK throughout the stated interval. -/
theorem mutualInformation_le_phi_local_junction {n : ℕ} (hn : 0 < n) {ρ : ℝ}
    (f : BooleanFunction n)
    (hδ : minSignedDictatorDistance hn f ∈ Ioc (0 : ℝ) (1/64))
    (hρ : ρ ∈ Icc (0 : ℝ)
      (Real.tanh (Real.log (3/(2*minSignedDictatorDistance hn f))))) :
    mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨i,hi⟩ := exists_max_singleton hn f
  apply mutualInformation_le_phi_junction_coordinate hδ hρ f i
  rw [minSignedDictatorDistance_eq,hi]
  linarith

end
end CK
