module

public import CK.High.TailEntropy
public import CK.High.Junction
public import CK.Analysis.Production
public import CK.Results.MiddleRange
public import CK.Results.BaseCases

/-! Assembly from the lower correlation range and a derivative criterion, including the local comparison in the terminal range. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem informationGap_pos_nonconstant {n : ℕ} {ρ : ℝ} (f : BooleanFunction n)
    (hgap : 0 < informationGap ρ f) : ∃ x y, f x ≠ f y := by
  by_contra hf
  push Not at hf
  have hc : f=(fun _ : Cube n => f (fun _ => false)) := funext (fun x => hf x _)
  rw [informationGap,hc,information_const] at hgap
  have hphi := phi_nonneg ρ
  linarith only [hgap,hphi]

/-- The whole near-dictator part of the tail, including distance zero. -/
theorem mutualInformation_le_phi_tail_local {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu : (8 : ℝ) ≤ u) (f : BooleanFunction n)
    (hδ : minSignedDictatorDistance hn f ≤ (3/2)*Real.exp (-u)) :
    mutualInformation (Real.tanh u) f ≤ phi (Real.tanh u) := by
  have he := tail_epsilon_bounds hu
  have hd : (3/2)*Real.exp (-u) ∈ Ioc (0 : ℝ) (1/64) :=
    ⟨by positivity,by linarith only [he.2]⟩
  have hid : Real.log (3/(2*((3/2)*Real.exp (-u))))=u := by
    have heq : 3/(2*((3/2)*Real.exp (-u)))=Real.exp u := by
      rw [Real.exp_neg]
      field_simp
    rw [heq,Real.log_exp]
  have ht : Real.tanh u ∈ Icc (0 : ℝ)
      (Real.tanh (Real.log (3/(2*((3/2)*Real.exp (-u)))))) := by
    rw [hid]
    exact ⟨(tail_tanh_mem hu).1.le,le_rfl⟩
  obtain ⟨i,hi⟩ := exists_max_singleton hn f
  apply mutualInformation_le_phi_junction_coordinate hd ht f i
  rw [minSignedDictatorDistance_eq,hi] at hδ
  linarith only [hδ]

theorem positive_gap_tail_distance {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu : (8 : ℝ) ≤ u) (f : BooleanFunction n)
    (hgap : 0 < informationGap (Real.tanh u) f) :
    (3/2)*Real.exp (-u) < minSignedDictatorDistance hn f := by
  by_contra hh
  have hc := mutualInformation_le_phi_tail_local hn hu f (le_of_not_gt hh)
  have hr := tail_tanh_mem hu
  rw [mutualInformation_eq_information ⟨hr.1.le,hr.2.le⟩] at hc
  exact (not_lt_of_ge (sub_nonpos.mpr hc)) hgap

/-- The positive-gap barrier with a nonnegative derivative wherever the gap is positive. -/
theorem information_le_phi_terminal_derivative {n : ℕ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (f : BooleanFunction n)
    (hderiv : ∀ ρ ∈ Ioo a 1, 0 < informationGap ρ f →
      0 ≤ deriv (fun r => informationGap r f) ρ) :
    ∀ ρ ∈ Icc a 1, information ρ f ≤ phi ρ := by
  by_cases hf : ∃ x y, f x ≠ f y
  · have hg := positive_gap_barrier ha1 (continuous_informationGap f).continuousOn
      (G := fun r => informationGap r f)
      (fun r hr => (hasDerivAt_informationGap
        ⟨lt_of_le_of_lt ha0 hr.1,hr.2⟩ f hf).differentiableAt.differentiableWithinAt)
      (informationGap_one_nonpos f) hderiv
    intro r hr
    exact sub_nonpos.mp (hg r hr)
  · push Not at hf
    have hc : f=(fun _ : Cube n => f (fun _ => false)) := funext (fun x => hf x _)
    intro r _
    rw [hc,information_const]
    exact phi_nonneg r

/-- The global Shannon inequality and signed-dictator attainment follow from the lower correlation range and the terminal derivative criterion. -/
theorem mainStatement_of_terminal_derivative
    (hterminal : ∀ (n : ℕ), 0 < n → ∀ (f : BooleanFunction n),
      Monotone (lift f) → ∀ ρ ∈ Ioo (49/50 : ℝ) 1,
      0 < informationGap ρ f → 0 < deriv (fun r => informationGap r f) ρ) :
    MainStatement := by
  constructor
  · intro n hn ρ hρ f
    by_cases hl : ρ ≤ (49/50 : ℝ)
    · exact mutualInformation_le_phi_through_098 hn ⟨hρ.1,hl⟩ f
    obtain ⟨g,hg,hmean,hinfo,hcoeff,hdist⟩ := exists_monotone_compression_shannon hn f
    apply (hinfo ρ hρ).trans
    rw [mutualInformation_eq_information hρ]
    apply information_le_phi_terminal_derivative (a := 49/50)
      (by norm_num) (by norm_num) g
      (fun r hr hp => (hterminal n hn g hg r hr hp).le)
    exact ⟨(lt_of_not_ge hl).le,hρ.2⟩
  · intro n _ ρ hρ
    exact dictatorAttainmentAt n hρ

end
end CK
