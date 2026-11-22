module

public import CK.Middle.MovingBand0
public import CK.Middle.MovingBand1
public import CK.Middle.MovingBand2
public import CK.Middle.MovingBand3
public import CK.Middle.MovingBand4
public import CK.Middle.SmallCapBands
public import CK.Middle.OrderedCoordinates
public import CK.Middle.LastLargeCoordinate
public import CK.Low.LocalMiddleIntervals
public import CK.Reduction.Compression
public import CK.Results.LowRange
public import CK.Basic.BaseCases

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Middle
noncomputable section

section Band0
open CK.Certificate.ClockGeometry.Band0
theorem mutualInformation_le_phi_band0_monotone {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ}
    (hρ : ρ ∈ Icc (457/500 : ℝ) (19/20)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨i,hmax⟩ := exists_largest_singleton (by omega : 0<n) f
  by_cases hs : fourier (lift f) {i} ≤ (2/5 : ℝ)
  · apply mutualInformation_le_phi_band0_small_singletons hρ f
    intro j
    rw [abs_of_nonneg (singleton_nonneg_of_monotone hf j)]
    exact (hmax j).trans hs
  by_cases hlast : a6 ≤ fourier (lift f) {i}

  · apply mutualInformation_le_phi_middle0_large_singleton ⟨by linarith [hρ.1],hρ.2⟩ f i
    rw [abs_of_nonneg (singleton_nonneg_of_monotone hf i)]
    simpa only [a6] using hlast

  by_cases hseg0 : fourier (lift f) {i} ≤ a1
  · apply mutualInformation_le_phi_band0_segment0 hρ f hf i rfl hmax
    constructor

    · change (2/5 : ℝ) ≤ fourier (lift f) {i}
      exact (lt_of_not_ge hs).le

    · exact hseg0

  by_cases hseg1 : fourier (lift f) {i} ≤ a2
  · apply mutualInformation_le_phi_band0_segment1 hρ f hf i rfl hmax
    constructor

    · exact (lt_of_not_ge hseg0).le

    · exact hseg1

  by_cases hseg2 : fourier (lift f) {i} ≤ a3
  · apply mutualInformation_le_phi_band0_segment2 hρ f hf i rfl hmax
    constructor

    · exact (lt_of_not_ge hseg1).le

    · exact hseg2

  by_cases hseg3 : fourier (lift f) {i} ≤ a4
  · apply mutualInformation_le_phi_band0_segment3 hρ f hf i rfl hmax
    constructor

    · exact (lt_of_not_ge hseg2).le

    · exact hseg3

  by_cases hseg4 : fourier (lift f) {i} ≤ a5
  · apply mutualInformation_le_phi_band0_segment4 hρ f hf i rfl hmax
    constructor

    · exact (lt_of_not_ge hseg3).le

    · exact hseg4

  apply mutualInformation_le_phi_band0_segment5 hρ f hf i rfl hmax
  constructor

  · exact (lt_of_not_ge hseg4).le

  · exact (lt_of_not_ge hlast).le

end Band0

section Band1
open CK.Certificate.ClockGeometry.Band1
theorem mutualInformation_le_phi_band1_monotone {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ}
    (hρ : ρ ∈ Icc (19/20 : ℝ) (97/100)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨i,hmax⟩ := exists_largest_singleton (by omega : 0<n) f
  by_cases hs : fourier (lift f) {i} ≤ (2/5 : ℝ)
  · apply mutualInformation_le_phi_band1_small_singletons hρ f
    intro j
    rw [abs_of_nonneg (singleton_nonneg_of_monotone hf j)]
    exact (hmax j).trans hs
  by_cases hlast : a4 ≤ fourier (lift f) {i}

  · apply mutualInformation_le_phi_middle1_large_singleton ⟨by linarith [hρ.1],hρ.2⟩ f i
    rw [abs_of_nonneg (singleton_nonneg_of_monotone hf i)]
    simpa only [a4] using hlast

  by_cases hseg0 : fourier (lift f) {i} ≤ a1
  · apply mutualInformation_le_phi_band1_segment0 hρ f hf i rfl hmax
    constructor

    · change (2/5 : ℝ) ≤ fourier (lift f) {i}
      exact (lt_of_not_ge hs).le

    · exact hseg0

  by_cases hseg1 : fourier (lift f) {i} ≤ a2
  · apply mutualInformation_le_phi_band1_segment1 hρ f hf i rfl hmax
    constructor

    · exact (lt_of_not_ge hseg0).le

    · exact hseg1

  by_cases hseg2 : fourier (lift f) {i} ≤ a3
  · apply mutualInformation_le_phi_band1_segment2 hρ f hf i rfl hmax
    constructor

    · exact (lt_of_not_ge hseg1).le

    · exact hseg2

  apply mutualInformation_le_phi_band1_segment3 hρ f hf i rfl hmax
  constructor

  · exact (lt_of_not_ge hseg2).le

  · exact (lt_of_not_ge hlast).le

end Band1

section Band2
open CK.Certificate.ClockGeometry.Band2
theorem mutualInformation_le_phi_band2_monotone {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ}
    (hρ : ρ ∈ Icc (97/100 : ℝ) (487/500)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨i,hmax⟩ := exists_largest_singleton (by omega : 0<n) f
  by_cases hs : fourier (lift f) {i} ≤ (2/5 : ℝ)
  · apply mutualInformation_le_phi_band2_small_singletons hρ f
    intro j
    rw [abs_of_nonneg (singleton_nonneg_of_monotone hf j)]
    exact (hmax j).trans hs
  by_cases hlast : a3 ≤ fourier (lift f) {i}

  · apply mutualInformation_le_phi_middle2_large_singleton ⟨by linarith [hρ.1],hρ.2⟩ f i
    rw [abs_of_nonneg (singleton_nonneg_of_monotone hf i)]
    simpa only [a3] using hlast

  by_cases hseg0 : fourier (lift f) {i} ≤ a1
  · apply mutualInformation_le_phi_band2_segment0 hρ f hf i rfl hmax
    constructor

    · change (2/5 : ℝ) ≤ fourier (lift f) {i}
      exact (lt_of_not_ge hs).le

    · exact hseg0

  by_cases hseg1 : fourier (lift f) {i} ≤ a2
  · apply mutualInformation_le_phi_band2_segment1 hρ f hf i rfl hmax
    constructor

    · exact (lt_of_not_ge hseg0).le

    · exact hseg1

  apply mutualInformation_le_phi_band2_segment2 hρ f hf i rfl hmax
  constructor

  · exact (lt_of_not_ge hseg1).le

  · exact (lt_of_not_ge hlast).le

end Band2

section Band3
open CK.Certificate.ClockGeometry.Band3
theorem mutualInformation_le_phi_band3_monotone {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ}
    (hρ : ρ ∈ Icc (487/500 : ℝ) (39/40)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨i,hmax⟩ := exists_largest_singleton (by omega : 0<n) f
  by_cases hs : fourier (lift f) {i} ≤ (2/5 : ℝ)
  · apply mutualInformation_le_phi_band3_small_singletons hρ f
    intro j
    rw [abs_of_nonneg (singleton_nonneg_of_monotone hf j)]
    exact (hmax j).trans hs
  by_cases hlast : a3 ≤ fourier (lift f) {i}

  · apply mutualInformation_le_phi_middle3_large_singleton ⟨by linarith [hρ.1],hρ.2⟩ f i
    rw [abs_of_nonneg (singleton_nonneg_of_monotone hf i)]
    simpa only [a3] using hlast

  by_cases hseg0 : fourier (lift f) {i} ≤ a1
  · apply mutualInformation_le_phi_band3_segment0 hρ f hf i rfl hmax
    constructor

    · change (2/5 : ℝ) ≤ fourier (lift f) {i}
      exact (lt_of_not_ge hs).le

    · exact hseg0

  by_cases hseg1 : fourier (lift f) {i} ≤ a2
  · apply mutualInformation_le_phi_band3_segment1 hρ f hf i rfl hmax
    constructor

    · exact (lt_of_not_ge hseg0).le

    · exact hseg1

  apply mutualInformation_le_phi_band3_segment2 hρ f hf i rfl hmax
  constructor

  · exact (lt_of_not_ge hseg1).le

  · exact (lt_of_not_ge hlast).le

end Band3

section Band4
open CK.Certificate.ClockGeometry.Band4
theorem mutualInformation_le_phi_band4_monotone {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ}
    (hρ : ρ ∈ Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨i,hmax⟩ := exists_largest_singleton (by omega : 0<n) f
  by_cases hs : fourier (lift f) {i} ≤ (2/5 : ℝ)
  · apply mutualInformation_le_phi_band4_small_singletons hρ f
    intro j
    rw [abs_of_nonneg (singleton_nonneg_of_monotone hf j)]
    exact (hmax j).trans hs
  by_cases hlast : a3 ≤ fourier (lift f) {i}

  · by_cases hlarge : (76043/100000 : ℝ) ≤ fourier (lift f) {i}
    · exact mutualInformation_le_phi_upper_large_singleton ⟨by linarith [hρ.1],hρ.2⟩ f i
        (by rw [abs_of_nonneg (singleton_nonneg_of_monotone hf i)]; exact hlarge)
    · obtain ⟨j,hij,hsecond⟩ := exists_second_singleton hn f i
      apply mutualInformation_le_phi_last_large_coordinate hρ f hf i j hij ?_ hsecond
      constructor
      · simpa only [a3] using hlast
      · exact (lt_of_not_ge hlarge).le

  by_cases hseg0 : fourier (lift f) {i} ≤ a1
  · apply mutualInformation_le_phi_band4_segment0 hρ f hf i rfl hmax
    constructor

    · change (2/5 : ℝ) ≤ fourier (lift f) {i}
      exact (lt_of_not_ge hs).le

    · exact hseg0

  by_cases hseg1 : fourier (lift f) {i} ≤ a2
  · apply mutualInformation_le_phi_band4_segment1 hρ f hf i rfl hmax
    constructor

    · exact (lt_of_not_ge hseg0).le

    · exact hseg1

  apply mutualInformation_le_phi_band4_segment2 hρ f hf i rfl hmax
  constructor

  · exact (lt_of_not_ge hseg1).le

  · exact (lt_of_not_ge hlast).le

end Band4

end
end CK.Middle

namespace CK
noncomputable section

/-- Complete middle interval, in finite Shannon semantics, without coefficient premises. -/
theorem mutualInformation_le_phi_middle_range {n : ℕ} (hn : 0 < n) {ρ : ℝ}
    (hρ : ρ ∈ Icc (457/500 : ℝ) (49/50)) (f : BooleanFunction n) :
    mutualInformation ρ f ≤ phi ρ := by
  have hρ01 : ρ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  by_cases hn1 : n=1
  · subst n
    exact mutualInformation_one_dimension hρ01 f
  have hn2 : 2 ≤ n := by omega
  obtain ⟨g,hg,hmean,hinfo,hcoeff,hdist⟩ := exists_monotone_compression_shannon hn f
  apply (hinfo ρ hρ01).trans
  by_cases h0 : ρ ≤ (19/20 : ℝ)
  · exact Middle.mutualInformation_le_phi_band0_monotone hn2 ⟨hρ.1,h0⟩ g hg
  by_cases h1 : ρ ≤ (97/100 : ℝ)
  · exact Middle.mutualInformation_le_phi_band1_monotone hn2 ⟨(lt_of_not_ge h0).le,h1⟩ g hg
  by_cases h2 : ρ ≤ (487/500 : ℝ)
  · exact Middle.mutualInformation_le_phi_band2_monotone hn2 ⟨(lt_of_not_ge h1).le,h2⟩ g hg
  by_cases h3 : ρ ≤ (39/40 : ℝ)
  · exact Middle.mutualInformation_le_phi_band3_monotone hn2 ⟨(lt_of_not_ge h2).le,h3⟩ g hg
  exact Middle.mutualInformation_le_phi_band4_monotone hn2 ⟨(lt_of_not_ge h3).le,hρ.2⟩ g hg

/-- CK through correlation `49/50`, with all Boolean means retained. -/
theorem mutualInformation_le_phi_through_098 {n : ℕ} (hn : 0 < n) {ρ : ℝ}
    (hρ : ρ ∈ Icc (0 : ℝ) (49/50)) (f : BooleanFunction n) :
    mutualInformation ρ f ≤ phi ρ := by
  by_cases hl : ρ ≤ (457/500 : ℝ)
  · exact mutualInformation_le_phi_low_range ⟨hρ.1,hl⟩ f
  · exact mutualInformation_le_phi_middle_range hn ⟨(lt_of_not_ge hl).le,hρ.2⟩ f

theorem mutualInformation_le_binaryEntropy_through_098 {n : ℕ} (hn : 0 < n) {ρ : ℝ}
    (hρ : ρ ∈ Icc (0 : ℝ) (49/50)) (f : BooleanFunction n) :
    mutualInformation ρ f ≤ Real.log 2-Real.binEntropy ((1-ρ)/2) :=
  mutualInformation_le_phi_through_098 hn hρ f

end
end CK
