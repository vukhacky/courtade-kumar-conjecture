module

public import CK.Results.HighAssembly
public import CK.High.Tail

/-! Unconditional all-dimensional CK on the closed terminal interval.
Compression is performed once, before applying the positive-gap barrier. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem positive_gap_high_tail_derivative {n : ℕ} (hn : 0 < n) {ρ : ℝ}
    (hρ : ρ ∈ Ico (Real.tanh 8) 1) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (hgap : 0 < informationGap ρ f) :
    0 < deriv (fun r => informationGap r f) ρ := by
  have hu : (8 : ℝ) ≤ Real.artanh ρ := by
    have h := Real.artanh_le_artanh (Real.neg_one_lt_tanh 8) hρ.2 hρ.1
    rwa [Real.artanh_tanh] at h
  have hid : Real.tanh (Real.artanh ρ)=ρ :=
    Real.tanh_artanh ⟨lt_of_lt_of_le (Real.neg_one_lt_tanh 8) hρ.1,hρ.2⟩
  have hp : 0 < informationGap (Real.tanh (Real.artanh ρ)) f := by rw [hid]; exact hgap
  have hd := analytic_tail_derivative hn hu f hf (positive_gap_tail_distance hn hu f hp).le hp
  rwa [hid] at hd

/-- Actual finite Shannon CK on `[tanh 8,1]`, all Boolean means and all
positive finite dimensions. -/
theorem mutualInformation_le_phi_high_tail {n : ℕ} (hn : 0 < n) {ρ : ℝ}
    (hρ : ρ ∈ Icc (Real.tanh 8) 1) (f : BooleanFunction n) :
    mutualInformation ρ f ≤ phi ρ := by
  have ht0 : 0 ≤ Real.tanh (8 : ℝ) := (tail_tanh_mem (by norm_num : (8 : ℝ) ≤ 8)).1.le
  have hρ01 : ρ ∈ Icc (0 : ℝ) 1 := ⟨ht0.trans hρ.1,hρ.2⟩
  obtain ⟨g,hg,hmean,hinfo,hcoeff,hdist⟩ := exists_monotone_compression_shannon hn f
  apply (hinfo ρ hρ01).trans
  rw [mutualInformation_eq_information hρ01]
  exact information_le_phi_terminal_derivative ht0 (Real.tanh_lt_one 8) g
    (fun r hr hp => (positive_gap_high_tail_derivative hn ⟨hr.1.le,hr.2⟩ g hg hp).le) ρ hρ

theorem mutualInformation_le_binaryEntropy_high_tail {n : ℕ} (hn : 0 < n) {ρ : ℝ}
    (hρ : ρ ∈ Icc (Real.tanh 8) 1) (f : BooleanFunction n) :
    mutualInformation ρ f ≤ Real.log 2-Real.binEntropy ((1-ρ)/2) :=
  mutualInformation_le_phi_high_tail hn hρ f

end
end CK
