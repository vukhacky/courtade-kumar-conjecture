module

public import CK.Middle.OneCoordinateCells
public import CK.Middle.CubicBands
public import CK.Certificate.ClockGeometryBand0

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Middle
noncomputable section

open CK.Certificate.ClockGeometry.Band0

theorem mutualInformation_le_phi_band0_segment0 {n : ℕ} {ρ a : ℝ}
    (hρ : ρ ∈ Icc (457/500 : ℝ) (19/20)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i : Fin n)
    (hai : fourier (lift f) {i}=a) (hmax : ∀ j, fourier (lift f) {j} ≤ a)
    (ha : a ∈ Icc a0 a1) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨hl,hlu,hu,hA,hside,hrl,hru,hmethod⟩ := segment0_domain
  have ha0 : 0 < a := hl.trans_le ha.1
  have hρ01 : ρ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hρclock : ρ ∈ Ico (457/500 : ℝ) 1 := ⟨hρ.1,hρ01.2⟩
  by_cases hW : fourierWeight (lift f) 1 ≤ (((-1:ℝ)+1)*a^2+(353357479/523750000:ℝ))
  · apply mutualInformation_le_phi_cubic_band0 hρ f

    exact cubicWeight_le_of_parseval_cell hρ01.1.le hρ.2 (by norm_num) f hW
      (by norm_num [cubicBeta])

  · exact mutualInformation_le_phi_low_cap_cell hρ01 f hf i hai hmax hl ha 3 hA
      (by simpa only [Nat.cast_one,Nat.cast_ofNat] using hrl.2) (by simpa only [Nat.cast_one,Nat.cast_ofNat] using hru.1) ((lt_of_not_ge hW).le) (segment0_lower_clock hρclock) (segment0_upper_clock hρclock)

theorem mutualInformation_le_phi_band0_segment1 {n : ℕ} {ρ a : ℝ}
    (hρ : ρ ∈ Icc (457/500 : ℝ) (19/20)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i : Fin n)
    (hai : fourier (lift f) {i}=a) (hmax : ∀ j, fourier (lift f) {j} ≤ a)
    (ha : a ∈ Icc a1 a2) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨hl,hlu,hu,hA,hside,hrl,hru,hmethod⟩ := segment1_domain
  have ha0 : 0 < a := hl.trans_le ha.1
  have hρ01 : ρ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hρclock : ρ ∈ Ico (457/500 : ℝ) 1 := ⟨hρ.1,hρ01.2⟩
  by_cases hW : fourierWeight (lift f) 1 ≤ (((-1:ℝ)+1)*a^2+(353357479/523750000:ℝ))
  · apply mutualInformation_le_phi_cubic_band0 hρ f

    exact cubicWeight_le_of_parseval_cell hρ01.1.le hρ.2 (by norm_num) f hW
      (by norm_num [cubicBeta])

  · exact mutualInformation_le_phi_low_cap_cell hρ01 f hf i hai hmax hl ha 2 hA
      (by simpa only [Nat.cast_one,Nat.cast_ofNat] using hrl.2) (by simpa only [Nat.cast_one,Nat.cast_ofNat] using hru.1) ((lt_of_not_ge hW).le) (segment1_lower_clock hρclock) (segment1_upper_clock hρclock)

theorem mutualInformation_le_phi_band0_segment2 {n : ℕ} {ρ a : ℝ}
    (hρ : ρ ∈ Icc (457/500 : ℝ) (19/20)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i : Fin n)
    (hai : fourier (lift f) {i}=a) (hmax : ∀ j, fourier (lift f) {j} ≤ a)
    (ha : a ∈ Icc a2 a3) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨hl,hlu,hu,hA,hside,hrl,hru,hmethod⟩ := segment2_domain
  have ha0 : 0 < a := hl.trans_le ha.1
  have hρ01 : ρ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hρclock : ρ ∈ Ico (457/500 : ℝ) 1 := ⟨hρ.1,hρ01.2⟩
  by_cases hW : fourierWeight (lift f) 1 ≤ (((-1:ℝ)+1)*a^2+(353357479/523750000:ℝ))
  · apply mutualInformation_le_phi_cubic_band0 hρ f

    exact cubicWeight_le_of_parseval_cell hρ01.1.le hρ.2 (by norm_num) f hW
      (by norm_num [cubicBeta])

  · exact mutualInformation_le_phi_low_cap_cell hρ01 f hf i hai hmax hl ha 1 hA
      (by simpa only [Nat.cast_one,Nat.cast_ofNat] using hrl.2) (by simpa only [Nat.cast_one,Nat.cast_ofNat] using hru.1) ((lt_of_not_ge hW).le) (segment2_lower_clock hρclock) (segment2_upper_clock hρclock)

theorem mutualInformation_le_phi_band0_segment3 {n : ℕ} {ρ a : ℝ}
    (hρ : ρ ∈ Icc (457/500 : ℝ) (19/20)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i : Fin n)
    (hai : fourier (lift f) {i}=a) (hmax : ∀ j, fourier (lift f) {j} ≤ a)
    (ha : a ∈ Icc a3 a4) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨hl,hlu,hu,hA,hside,hrl,hru,hmethod⟩ := segment3_domain
  have ha0 : 0 < a := hl.trans_le ha.1
  have hρ01 : ρ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hρclock : ρ ∈ Ico (457/500 : ℝ) 1 := ⟨hρ.1,hρ01.2⟩
  by_cases hW : fourierWeight (lift f) 1 ≤ (((-1:ℝ)+1)*a^2+(353357479/523750000:ℝ))
  · apply mutualInformation_le_phi_cubic_band0 hρ f

    exact cubicWeight_le_of_parseval_cell hρ01.1.le hρ.2 (by norm_num) f hW
      (by norm_num [cubicBeta])

  · exact mutualInformation_le_phi_high_cap_cell hρ01 f hf i hai hl hu ha 1 hA
      hmethod (by simpa only [Nat.cast_one,Nat.cast_ofNat] using hrl.1) (by simpa only [Nat.cast_one,Nat.cast_ofNat] using hru.2) ((lt_of_not_ge hW).le) (segment3_lower_clock hρclock) (segment3_upper_clock hρclock)

theorem mutualInformation_le_phi_band0_segment4 {n : ℕ} {ρ a : ℝ}
    (hρ : ρ ∈ Icc (457/500 : ℝ) (19/20)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i : Fin n)
    (hai : fourier (lift f) {i}=a) (hmax : ∀ j, fourier (lift f) {j} ≤ a)
    (ha : a ∈ Icc a4 a5) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨hl,hlu,hu,hA,hside,hrl,hru,hmethod⟩ := segment4_domain
  have ha0 : 0 < a := hl.trans_le ha.1
  have hρ01 : ρ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hρclock : ρ ∈ Ico (457/500 : ℝ) 1 := ⟨hρ.1,hρ01.2⟩
  by_cases hW : fourierWeight (lift f) 1 ≤ (((-1199/1560:ℝ)+1)*a^2+(578982479/975000000:ℝ))
  · apply mutualInformation_le_phi_cubic_band0 hρ f

    apply cubicWeight_le_of_harris_singleton_cell hρ01.1.le hρ.2
      (by norm_num : (1:ℝ) ∈ Ioc (0:ℝ) 1) ha0.le f hf i
      (by rw [hai]) hW
    norm_num [cubicBeta]
    nlinarith only []

  · exact mutualInformation_le_phi_high_cap_cell hρ01 f hf i hai hl hu ha 1 hA
      hmethod (by simpa only [Nat.cast_one,Nat.cast_ofNat] using hrl.1) (by simpa only [Nat.cast_one,Nat.cast_ofNat] using hru.2) ((lt_of_not_ge hW).le) (segment4_lower_clock hρclock) (segment4_upper_clock hρclock)

theorem mutualInformation_le_phi_band0_segment5 {n : ℕ} {ρ a : ℝ}
    (hρ : ρ ∈ Icc (457/500 : ℝ) (19/20)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i : Fin n)
    (hai : fourier (lift f) {i}=a) (hmax : ∀ j, fourier (lift f) {j} ≤ a)
    (ha : a ∈ Icc a5 a6) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨hl,hlu,hu,hA,hside,hrl,hru,hmethod⟩ := segment5_domain
  have ha0 : 0 < a := hl.trans_le ha.1
  have hρ01 : ρ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hρclock : ρ ∈ Ico (457/500 : ℝ) 1 := ⟨hρ.1,hρ01.2⟩
  by_cases hW : fourierWeight (lift f) 1 ≤ (((-1199/1560:ℝ)+1)*a^2+(578982479/975000000:ℝ))
  · apply mutualInformation_le_phi_cubic_band0 hρ f

    apply cubicWeight_le_of_harris_singleton_cell hρ01.1.le hρ.2
      (by norm_num : (1:ℝ) ∈ Ioc (0:ℝ) 1) ha0.le f hf i
      (by rw [hai]) hW
    norm_num [cubicBeta]
    nlinarith only []

  · exact mutualInformation_le_phi_high_cap_cell hρ01 f hf i hai hl hu ha 2 hA
      hmethod (by simpa only [Nat.cast_one,Nat.cast_ofNat] using hrl.1) (by simpa only [Nat.cast_one,Nat.cast_ofNat] using hru.2) ((lt_of_not_ge hW).le) (segment5_lower_clock hρclock) (segment5_upper_clock hρclock)


end
end CK.Middle
