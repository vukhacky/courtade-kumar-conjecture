module
public import CK.Certificate.CompactBoxes.B000
public import CK.Certificate.CompactBoxes.B001
public import CK.Certificate.CompactBoxes.B002
public import CK.Certificate.CompactBoxes.B003
public import CK.Certificate.CompactBoxes.B004
public import CK.Certificate.CompactBoxes.B005
public import CK.Certificate.CompactBoxes.B006
public import CK.Certificate.CompactBoxes.B007
public import CK.Certificate.CompactBoxes.B008
public import CK.Certificate.CompactBoxes.B009
public import CK.Certificate.CompactBoxes.B010
public import CK.Certificate.CompactBoxes.B011
public import CK.Certificate.CompactBoxes.B012
public import CK.Certificate.CompactBoxes.B013
public import CK.Certificate.CompactBoxes.B014
public import CK.Certificate.CompactBoxes.B015
public import CK.Certificate.CompactBoxes.B016
public import CK.Certificate.CompactBoxes.B017
public import CK.Certificate.CompactBoxes.B018
public import CK.Certificate.CompactBoxes.B019
public import CK.Certificate.CompactBoxes.B020
public import CK.Certificate.CompactBoxes.B021
public import CK.Certificate.CompactBoxes.B022
public import CK.Certificate.CompactBoxes.B023
public import CK.Certificate.CompactBoxes.B024
public import CK.Certificate.CompactBoxes.B025
public import CK.Certificate.CompactBoxes.B026
public import CK.Certificate.CompactBoxes.B027
public import CK.Certificate.CompactBoxes.B028
public import CK.Certificate.CompactBoxes.B029
public import CK.Certificate.CompactBoxes.B030
public import CK.Certificate.CompactBoxes.B031
public import CK.Certificate.CompactBoxes.B032
public import CK.Certificate.CompactBoxes.B033
public import CK.Certificate.CompactBoxes.B034
public import CK.Certificate.CompactBoxes.B035
public import CK.Certificate.CompactBoxes.B036
public import CK.Certificate.CompactBoxes.B037
public import CK.Certificate.CompactBoxes.B038
public import CK.Certificate.CompactBoxes.B039
public import CK.Certificate.CompactBoxes.B040
public import CK.Certificate.CompactBoxes.B041
public import CK.Certificate.CompactBoxes.B042
public import CK.Certificate.CompactBoxes.B043
public import CK.Certificate.CompactBoxes.B044
public import CK.Certificate.CompactBoxes.B045
public import CK.Certificate.CompactBoxes.B046
public import CK.Certificate.CompactBoxes.B047
public import CK.Certificate.CompactBoxes.B048
public import CK.Certificate.CompactBoxes.B049

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate.CompactData
open Set

def AllMarginsPositive (u : ℝ) : Prop :=
  0<Compact.master u ∧ 0<Compact.lowerLogMargin u ∧ 0<Compact.middleLogMargin u ∧
  0<Compact.middleQuadMargin u ∧ 0<Compact.upperQuadMargin u

theorem B000_all : ∀ u ∈ Icc (B000.lo:ℝ) (B000.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B000.master_positive u hu,B000.lowerLogMargin_positive u hu,B000.middleLogMargin_positive u hu,B000.middleQuadMargin_positive u hu,B000.upperQuadMargin_positive u hu⟩

theorem B001_all : ∀ u ∈ Icc (B001.lo:ℝ) (B001.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B001.master_positive u hu,B001.lowerLogMargin_positive u hu,B001.middleLogMargin_positive u hu,B001.middleQuadMargin_positive u hu,B001.upperQuadMargin_positive u hu⟩

theorem B002_all : ∀ u ∈ Icc (B002.lo:ℝ) (B002.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B002.master_positive u hu,B002.lowerLogMargin_positive u hu,B002.middleLogMargin_positive u hu,B002.middleQuadMargin_positive u hu,B002.upperQuadMargin_positive u hu⟩

theorem B003_all : ∀ u ∈ Icc (B003.lo:ℝ) (B003.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B003.master_positive u hu,B003.lowerLogMargin_positive u hu,B003.middleLogMargin_positive u hu,B003.middleQuadMargin_positive u hu,B003.upperQuadMargin_positive u hu⟩

theorem B004_all : ∀ u ∈ Icc (B004.lo:ℝ) (B004.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B004.master_positive u hu,B004.lowerLogMargin_positive u hu,B004.middleLogMargin_positive u hu,B004.middleQuadMargin_positive u hu,B004.upperQuadMargin_positive u hu⟩

theorem B005_all : ∀ u ∈ Icc (B005.lo:ℝ) (B005.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B005.master_positive u hu,B005.lowerLogMargin_positive u hu,B005.middleLogMargin_positive u hu,B005.middleQuadMargin_positive u hu,B005.upperQuadMargin_positive u hu⟩

theorem B006_all : ∀ u ∈ Icc (B006.lo:ℝ) (B006.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B006.master_positive u hu,B006.lowerLogMargin_positive u hu,B006.middleLogMargin_positive u hu,B006.middleQuadMargin_positive u hu,B006.upperQuadMargin_positive u hu⟩

theorem B007_all : ∀ u ∈ Icc (B007.lo:ℝ) (B007.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B007.master_positive u hu,B007.lowerLogMargin_positive u hu,B007.middleLogMargin_positive u hu,B007.middleQuadMargin_positive u hu,B007.upperQuadMargin_positive u hu⟩

theorem B008_all : ∀ u ∈ Icc (B008.lo:ℝ) (B008.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B008.master_positive u hu,B008.lowerLogMargin_positive u hu,B008.middleLogMargin_positive u hu,B008.middleQuadMargin_positive u hu,B008.upperQuadMargin_positive u hu⟩

theorem B009_all : ∀ u ∈ Icc (B009.lo:ℝ) (B009.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B009.master_positive u hu,B009.lowerLogMargin_positive u hu,B009.middleLogMargin_positive u hu,B009.middleQuadMargin_positive u hu,B009.upperQuadMargin_positive u hu⟩

theorem B010_all : ∀ u ∈ Icc (B010.lo:ℝ) (B010.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B010.master_positive u hu,B010.lowerLogMargin_positive u hu,B010.middleLogMargin_positive u hu,B010.middleQuadMargin_positive u hu,B010.upperQuadMargin_positive u hu⟩

theorem B011_all : ∀ u ∈ Icc (B011.lo:ℝ) (B011.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B011.master_positive u hu,B011.lowerLogMargin_positive u hu,B011.middleLogMargin_positive u hu,B011.middleQuadMargin_positive u hu,B011.upperQuadMargin_positive u hu⟩

theorem B012_all : ∀ u ∈ Icc (B012.lo:ℝ) (B012.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B012.master_positive u hu,B012.lowerLogMargin_positive u hu,B012.middleLogMargin_positive u hu,B012.middleQuadMargin_positive u hu,B012.upperQuadMargin_positive u hu⟩

theorem B013_all : ∀ u ∈ Icc (B013.lo:ℝ) (B013.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B013.master_positive u hu,B013.lowerLogMargin_positive u hu,B013.middleLogMargin_positive u hu,B013.middleQuadMargin_positive u hu,B013.upperQuadMargin_positive u hu⟩

theorem B014_all : ∀ u ∈ Icc (B014.lo:ℝ) (B014.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B014.master_positive u hu,B014.lowerLogMargin_positive u hu,B014.middleLogMargin_positive u hu,B014.middleQuadMargin_positive u hu,B014.upperQuadMargin_positive u hu⟩

theorem B015_all : ∀ u ∈ Icc (B015.lo:ℝ) (B015.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B015.master_positive u hu,B015.lowerLogMargin_positive u hu,B015.middleLogMargin_positive u hu,B015.middleQuadMargin_positive u hu,B015.upperQuadMargin_positive u hu⟩

theorem B016_all : ∀ u ∈ Icc (B016.lo:ℝ) (B016.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B016.master_positive u hu,B016.lowerLogMargin_positive u hu,B016.middleLogMargin_positive u hu,B016.middleQuadMargin_positive u hu,B016.upperQuadMargin_positive u hu⟩

theorem B017_all : ∀ u ∈ Icc (B017.lo:ℝ) (B017.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B017.master_positive u hu,B017.lowerLogMargin_positive u hu,B017.middleLogMargin_positive u hu,B017.middleQuadMargin_positive u hu,B017.upperQuadMargin_positive u hu⟩

theorem B018_all : ∀ u ∈ Icc (B018.lo:ℝ) (B018.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B018.master_positive u hu,B018.lowerLogMargin_positive u hu,B018.middleLogMargin_positive u hu,B018.middleQuadMargin_positive u hu,B018.upperQuadMargin_positive u hu⟩

theorem B019_all : ∀ u ∈ Icc (B019.lo:ℝ) (B019.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B019.master_positive u hu,B019.lowerLogMargin_positive u hu,B019.middleLogMargin_positive u hu,B019.middleQuadMargin_positive u hu,B019.upperQuadMargin_positive u hu⟩

theorem B020_all : ∀ u ∈ Icc (B020.lo:ℝ) (B020.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B020.master_positive u hu,B020.lowerLogMargin_positive u hu,B020.middleLogMargin_positive u hu,B020.middleQuadMargin_positive u hu,B020.upperQuadMargin_positive u hu⟩

theorem B021_all : ∀ u ∈ Icc (B021.lo:ℝ) (B021.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B021.master_positive u hu,B021.lowerLogMargin_positive u hu,B021.middleLogMargin_positive u hu,B021.middleQuadMargin_positive u hu,B021.upperQuadMargin_positive u hu⟩

theorem B022_all : ∀ u ∈ Icc (B022.lo:ℝ) (B022.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B022.master_positive u hu,B022.lowerLogMargin_positive u hu,B022.middleLogMargin_positive u hu,B022.middleQuadMargin_positive u hu,B022.upperQuadMargin_positive u hu⟩

theorem B023_all : ∀ u ∈ Icc (B023.lo:ℝ) (B023.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B023.master_positive u hu,B023.lowerLogMargin_positive u hu,B023.middleLogMargin_positive u hu,B023.middleQuadMargin_positive u hu,B023.upperQuadMargin_positive u hu⟩

theorem B024_all : ∀ u ∈ Icc (B024.lo:ℝ) (B024.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B024.master_positive u hu,B024.lowerLogMargin_positive u hu,B024.middleLogMargin_positive u hu,B024.middleQuadMargin_positive u hu,B024.upperQuadMargin_positive u hu⟩

theorem B025_all : ∀ u ∈ Icc (B025.lo:ℝ) (B025.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B025.master_positive u hu,B025.lowerLogMargin_positive u hu,B025.middleLogMargin_positive u hu,B025.middleQuadMargin_positive u hu,B025.upperQuadMargin_positive u hu⟩

theorem B026_all : ∀ u ∈ Icc (B026.lo:ℝ) (B026.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B026.master_positive u hu,B026.lowerLogMargin_positive u hu,B026.middleLogMargin_positive u hu,B026.middleQuadMargin_positive u hu,B026.upperQuadMargin_positive u hu⟩

theorem B027_all : ∀ u ∈ Icc (B027.lo:ℝ) (B027.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B027.master_positive u hu,B027.lowerLogMargin_positive u hu,B027.middleLogMargin_positive u hu,B027.middleQuadMargin_positive u hu,B027.upperQuadMargin_positive u hu⟩

theorem B028_all : ∀ u ∈ Icc (B028.lo:ℝ) (B028.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B028.master_positive u hu,B028.lowerLogMargin_positive u hu,B028.middleLogMargin_positive u hu,B028.middleQuadMargin_positive u hu,B028.upperQuadMargin_positive u hu⟩

theorem B029_all : ∀ u ∈ Icc (B029.lo:ℝ) (B029.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B029.master_positive u hu,B029.lowerLogMargin_positive u hu,B029.middleLogMargin_positive u hu,B029.middleQuadMargin_positive u hu,B029.upperQuadMargin_positive u hu⟩

theorem B030_all : ∀ u ∈ Icc (B030.lo:ℝ) (B030.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B030.master_positive u hu,B030.lowerLogMargin_positive u hu,B030.middleLogMargin_positive u hu,B030.middleQuadMargin_positive u hu,B030.upperQuadMargin_positive u hu⟩

theorem B031_all : ∀ u ∈ Icc (B031.lo:ℝ) (B031.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B031.master_positive u hu,B031.lowerLogMargin_positive u hu,B031.middleLogMargin_positive u hu,B031.middleQuadMargin_positive u hu,B031.upperQuadMargin_positive u hu⟩

theorem B032_all : ∀ u ∈ Icc (B032.lo:ℝ) (B032.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B032.master_positive u hu,B032.lowerLogMargin_positive u hu,B032.middleLogMargin_positive u hu,B032.middleQuadMargin_positive u hu,B032.upperQuadMargin_positive u hu⟩

theorem B033_all : ∀ u ∈ Icc (B033.lo:ℝ) (B033.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B033.master_positive u hu,B033.lowerLogMargin_positive u hu,B033.middleLogMargin_positive u hu,B033.middleQuadMargin_positive u hu,B033.upperQuadMargin_positive u hu⟩

theorem B034_all : ∀ u ∈ Icc (B034.lo:ℝ) (B034.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B034.master_positive u hu,B034.lowerLogMargin_positive u hu,B034.middleLogMargin_positive u hu,B034.middleQuadMargin_positive u hu,B034.upperQuadMargin_positive u hu⟩

theorem B035_all : ∀ u ∈ Icc (B035.lo:ℝ) (B035.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B035.master_positive u hu,B035.lowerLogMargin_positive u hu,B035.middleLogMargin_positive u hu,B035.middleQuadMargin_positive u hu,B035.upperQuadMargin_positive u hu⟩

theorem B036_all : ∀ u ∈ Icc (B036.lo:ℝ) (B036.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B036.master_positive u hu,B036.lowerLogMargin_positive u hu,B036.middleLogMargin_positive u hu,B036.middleQuadMargin_positive u hu,B036.upperQuadMargin_positive u hu⟩

theorem B037_all : ∀ u ∈ Icc (B037.lo:ℝ) (B037.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B037.master_positive u hu,B037.lowerLogMargin_positive u hu,B037.middleLogMargin_positive u hu,B037.middleQuadMargin_positive u hu,B037.upperQuadMargin_positive u hu⟩

theorem B038_all : ∀ u ∈ Icc (B038.lo:ℝ) (B038.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B038.master_positive u hu,B038.lowerLogMargin_positive u hu,B038.middleLogMargin_positive u hu,B038.middleQuadMargin_positive u hu,B038.upperQuadMargin_positive u hu⟩

theorem B039_all : ∀ u ∈ Icc (B039.lo:ℝ) (B039.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B039.master_positive u hu,B039.lowerLogMargin_positive u hu,B039.middleLogMargin_positive u hu,B039.middleQuadMargin_positive u hu,B039.upperQuadMargin_positive u hu⟩

theorem B040_all : ∀ u ∈ Icc (B040.lo:ℝ) (B040.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B040.master_positive u hu,B040.lowerLogMargin_positive u hu,B040.middleLogMargin_positive u hu,B040.middleQuadMargin_positive u hu,B040.upperQuadMargin_positive u hu⟩

theorem B041_all : ∀ u ∈ Icc (B041.lo:ℝ) (B041.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B041.master_positive u hu,B041.lowerLogMargin_positive u hu,B041.middleLogMargin_positive u hu,B041.middleQuadMargin_positive u hu,B041.upperQuadMargin_positive u hu⟩

theorem B042_all : ∀ u ∈ Icc (B042.lo:ℝ) (B042.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B042.master_positive u hu,B042.lowerLogMargin_positive u hu,B042.middleLogMargin_positive u hu,B042.middleQuadMargin_positive u hu,B042.upperQuadMargin_positive u hu⟩

theorem B043_all : ∀ u ∈ Icc (B043.lo:ℝ) (B043.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B043.master_positive u hu,B043.lowerLogMargin_positive u hu,B043.middleLogMargin_positive u hu,B043.middleQuadMargin_positive u hu,B043.upperQuadMargin_positive u hu⟩

theorem B044_all : ∀ u ∈ Icc (B044.lo:ℝ) (B044.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B044.master_positive u hu,B044.lowerLogMargin_positive u hu,B044.middleLogMargin_positive u hu,B044.middleQuadMargin_positive u hu,B044.upperQuadMargin_positive u hu⟩

theorem B045_all : ∀ u ∈ Icc (B045.lo:ℝ) (B045.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B045.master_positive u hu,B045.lowerLogMargin_positive u hu,B045.middleLogMargin_positive u hu,B045.middleQuadMargin_positive u hu,B045.upperQuadMargin_positive u hu⟩

theorem B046_all : ∀ u ∈ Icc (B046.lo:ℝ) (B046.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B046.master_positive u hu,B046.lowerLogMargin_positive u hu,B046.middleLogMargin_positive u hu,B046.middleQuadMargin_positive u hu,B046.upperQuadMargin_positive u hu⟩

theorem B047_all : ∀ u ∈ Icc (B047.lo:ℝ) (B047.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B047.master_positive u hu,B047.lowerLogMargin_positive u hu,B047.middleLogMargin_positive u hu,B047.middleQuadMargin_positive u hu,B047.upperQuadMargin_positive u hu⟩

theorem B048_all : ∀ u ∈ Icc (B048.lo:ℝ) (B048.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B048.master_positive u hu,B048.lowerLogMargin_positive u hu,B048.middleLogMargin_positive u hu,B048.middleQuadMargin_positive u hu,B048.upperQuadMargin_positive u hu⟩

theorem B049_all : ∀ u ∈ Icc (B049.lo:ℝ) (B049.hi:ℝ), AllMarginsPositive u := by
  intro u hu
  exact ⟨B049.master_positive u hu,B049.lowerLogMargin_positive u hu,B049.middleLogMargin_positive u hu,B049.middleQuadMargin_positive u hu,B049.upperQuadMargin_positive u hu⟩

theorem all_margins_positive {u : ℝ} (hu : u ∈ Icc (45951/20000:ℝ) 8) :
    AllMarginsPositive u := by
  by_cases h0 : u≤(B000.hi:ℝ)
  · apply B000_all u
    constructor
    · simpa only [B000.lo,Rat.cast_div,Rat.cast_ofNat] using hu.1
    · exact h0
  by_cases h1 : u≤(B001.hi:ℝ)
  · apply B001_all u
    constructor
    · have hlo := (lt_of_not_ge h0).le
      simpa only [B000.hi,B001.lo] using hlo
    · exact h1
  by_cases h2 : u≤(B002.hi:ℝ)
  · apply B002_all u
    constructor
    · have hlo := (lt_of_not_ge h1).le
      simpa only [B001.hi,B002.lo] using hlo
    · exact h2
  by_cases h3 : u≤(B003.hi:ℝ)
  · apply B003_all u
    constructor
    · have hlo := (lt_of_not_ge h2).le
      simpa only [B002.hi,B003.lo] using hlo
    · exact h3
  by_cases h4 : u≤(B004.hi:ℝ)
  · apply B004_all u
    constructor
    · have hlo := (lt_of_not_ge h3).le
      simpa only [B003.hi,B004.lo] using hlo
    · exact h4
  by_cases h5 : u≤(B005.hi:ℝ)
  · apply B005_all u
    constructor
    · have hlo := (lt_of_not_ge h4).le
      simpa only [B004.hi,B005.lo] using hlo
    · exact h5
  by_cases h6 : u≤(B006.hi:ℝ)
  · apply B006_all u
    constructor
    · have hlo := (lt_of_not_ge h5).le
      simpa only [B005.hi,B006.lo] using hlo
    · exact h6
  by_cases h7 : u≤(B007.hi:ℝ)
  · apply B007_all u
    constructor
    · have hlo := (lt_of_not_ge h6).le
      simpa only [B006.hi,B007.lo] using hlo
    · exact h7
  by_cases h8 : u≤(B008.hi:ℝ)
  · apply B008_all u
    constructor
    · have hlo := (lt_of_not_ge h7).le
      simpa only [B007.hi,B008.lo] using hlo
    · exact h8
  by_cases h9 : u≤(B009.hi:ℝ)
  · apply B009_all u
    constructor
    · have hlo := (lt_of_not_ge h8).le
      simpa only [B008.hi,B009.lo] using hlo
    · exact h9
  by_cases h10 : u≤(B010.hi:ℝ)
  · apply B010_all u
    constructor
    · have hlo := (lt_of_not_ge h9).le
      simpa only [B009.hi,B010.lo] using hlo
    · exact h10
  by_cases h11 : u≤(B011.hi:ℝ)
  · apply B011_all u
    constructor
    · have hlo := (lt_of_not_ge h10).le
      simpa only [B010.hi,B011.lo] using hlo
    · exact h11
  by_cases h12 : u≤(B012.hi:ℝ)
  · apply B012_all u
    constructor
    · have hlo := (lt_of_not_ge h11).le
      simpa only [B011.hi,B012.lo] using hlo
    · exact h12
  by_cases h13 : u≤(B013.hi:ℝ)
  · apply B013_all u
    constructor
    · have hlo := (lt_of_not_ge h12).le
      simpa only [B012.hi,B013.lo] using hlo
    · exact h13
  by_cases h14 : u≤(B014.hi:ℝ)
  · apply B014_all u
    constructor
    · have hlo := (lt_of_not_ge h13).le
      simpa only [B013.hi,B014.lo] using hlo
    · exact h14
  by_cases h15 : u≤(B015.hi:ℝ)
  · apply B015_all u
    constructor
    · have hlo := (lt_of_not_ge h14).le
      simpa only [B014.hi,B015.lo] using hlo
    · exact h15
  by_cases h16 : u≤(B016.hi:ℝ)
  · apply B016_all u
    constructor
    · have hlo := (lt_of_not_ge h15).le
      simpa only [B015.hi,B016.lo] using hlo
    · exact h16
  by_cases h17 : u≤(B017.hi:ℝ)
  · apply B017_all u
    constructor
    · have hlo := (lt_of_not_ge h16).le
      simpa only [B016.hi,B017.lo] using hlo
    · exact h17
  by_cases h18 : u≤(B018.hi:ℝ)
  · apply B018_all u
    constructor
    · have hlo := (lt_of_not_ge h17).le
      simpa only [B017.hi,B018.lo] using hlo
    · exact h18
  by_cases h19 : u≤(B019.hi:ℝ)
  · apply B019_all u
    constructor
    · have hlo := (lt_of_not_ge h18).le
      simpa only [B018.hi,B019.lo] using hlo
    · exact h19
  by_cases h20 : u≤(B020.hi:ℝ)
  · apply B020_all u
    constructor
    · have hlo := (lt_of_not_ge h19).le
      simpa only [B019.hi,B020.lo] using hlo
    · exact h20
  by_cases h21 : u≤(B021.hi:ℝ)
  · apply B021_all u
    constructor
    · have hlo := (lt_of_not_ge h20).le
      simpa only [B020.hi,B021.lo] using hlo
    · exact h21
  by_cases h22 : u≤(B022.hi:ℝ)
  · apply B022_all u
    constructor
    · have hlo := (lt_of_not_ge h21).le
      simpa only [B021.hi,B022.lo] using hlo
    · exact h22
  by_cases h23 : u≤(B023.hi:ℝ)
  · apply B023_all u
    constructor
    · have hlo := (lt_of_not_ge h22).le
      simpa only [B022.hi,B023.lo] using hlo
    · exact h23
  by_cases h24 : u≤(B024.hi:ℝ)
  · apply B024_all u
    constructor
    · have hlo := (lt_of_not_ge h23).le
      simpa only [B023.hi,B024.lo] using hlo
    · exact h24
  by_cases h25 : u≤(B025.hi:ℝ)
  · apply B025_all u
    constructor
    · have hlo := (lt_of_not_ge h24).le
      simpa only [B024.hi,B025.lo] using hlo
    · exact h25
  by_cases h26 : u≤(B026.hi:ℝ)
  · apply B026_all u
    constructor
    · have hlo := (lt_of_not_ge h25).le
      simpa only [B025.hi,B026.lo] using hlo
    · exact h26
  by_cases h27 : u≤(B027.hi:ℝ)
  · apply B027_all u
    constructor
    · have hlo := (lt_of_not_ge h26).le
      simpa only [B026.hi,B027.lo] using hlo
    · exact h27
  by_cases h28 : u≤(B028.hi:ℝ)
  · apply B028_all u
    constructor
    · have hlo := (lt_of_not_ge h27).le
      simpa only [B027.hi,B028.lo] using hlo
    · exact h28
  by_cases h29 : u≤(B029.hi:ℝ)
  · apply B029_all u
    constructor
    · have hlo := (lt_of_not_ge h28).le
      simpa only [B028.hi,B029.lo] using hlo
    · exact h29
  by_cases h30 : u≤(B030.hi:ℝ)
  · apply B030_all u
    constructor
    · have hlo := (lt_of_not_ge h29).le
      simpa only [B029.hi,B030.lo] using hlo
    · exact h30
  by_cases h31 : u≤(B031.hi:ℝ)
  · apply B031_all u
    constructor
    · have hlo := (lt_of_not_ge h30).le
      simpa only [B030.hi,B031.lo] using hlo
    · exact h31
  by_cases h32 : u≤(B032.hi:ℝ)
  · apply B032_all u
    constructor
    · have hlo := (lt_of_not_ge h31).le
      simpa only [B031.hi,B032.lo] using hlo
    · exact h32
  by_cases h33 : u≤(B033.hi:ℝ)
  · apply B033_all u
    constructor
    · have hlo := (lt_of_not_ge h32).le
      simpa only [B032.hi,B033.lo] using hlo
    · exact h33
  by_cases h34 : u≤(B034.hi:ℝ)
  · apply B034_all u
    constructor
    · have hlo := (lt_of_not_ge h33).le
      simpa only [B033.hi,B034.lo] using hlo
    · exact h34
  by_cases h35 : u≤(B035.hi:ℝ)
  · apply B035_all u
    constructor
    · have hlo := (lt_of_not_ge h34).le
      simpa only [B034.hi,B035.lo] using hlo
    · exact h35
  by_cases h36 : u≤(B036.hi:ℝ)
  · apply B036_all u
    constructor
    · have hlo := (lt_of_not_ge h35).le
      simpa only [B035.hi,B036.lo] using hlo
    · exact h36
  by_cases h37 : u≤(B037.hi:ℝ)
  · apply B037_all u
    constructor
    · have hlo := (lt_of_not_ge h36).le
      simpa only [B036.hi,B037.lo] using hlo
    · exact h37
  by_cases h38 : u≤(B038.hi:ℝ)
  · apply B038_all u
    constructor
    · have hlo := (lt_of_not_ge h37).le
      simpa only [B037.hi,B038.lo] using hlo
    · exact h38
  by_cases h39 : u≤(B039.hi:ℝ)
  · apply B039_all u
    constructor
    · have hlo := (lt_of_not_ge h38).le
      simpa only [B038.hi,B039.lo] using hlo
    · exact h39
  by_cases h40 : u≤(B040.hi:ℝ)
  · apply B040_all u
    constructor
    · have hlo := (lt_of_not_ge h39).le
      simpa only [B039.hi,B040.lo] using hlo
    · exact h40
  by_cases h41 : u≤(B041.hi:ℝ)
  · apply B041_all u
    constructor
    · have hlo := (lt_of_not_ge h40).le
      simpa only [B040.hi,B041.lo] using hlo
    · exact h41
  by_cases h42 : u≤(B042.hi:ℝ)
  · apply B042_all u
    constructor
    · have hlo := (lt_of_not_ge h41).le
      simpa only [B041.hi,B042.lo] using hlo
    · exact h42
  by_cases h43 : u≤(B043.hi:ℝ)
  · apply B043_all u
    constructor
    · have hlo := (lt_of_not_ge h42).le
      simpa only [B042.hi,B043.lo] using hlo
    · exact h43
  by_cases h44 : u≤(B044.hi:ℝ)
  · apply B044_all u
    constructor
    · have hlo := (lt_of_not_ge h43).le
      simpa only [B043.hi,B044.lo] using hlo
    · exact h44
  by_cases h45 : u≤(B045.hi:ℝ)
  · apply B045_all u
    constructor
    · have hlo := (lt_of_not_ge h44).le
      simpa only [B044.hi,B045.lo] using hlo
    · exact h45
  by_cases h46 : u≤(B046.hi:ℝ)
  · apply B046_all u
    constructor
    · have hlo := (lt_of_not_ge h45).le
      simpa only [B045.hi,B046.lo] using hlo
    · exact h46
  by_cases h47 : u≤(B047.hi:ℝ)
  · apply B047_all u
    constructor
    · have hlo := (lt_of_not_ge h46).le
      simpa only [B046.hi,B047.lo] using hlo
    · exact h47
  by_cases h48 : u≤(B048.hi:ℝ)
  · apply B048_all u
    constructor
    · have hlo := (lt_of_not_ge h47).le
      simpa only [B047.hi,B048.lo] using hlo
    · exact h48
  apply B049_all u
  constructor
  · have hlo := (lt_of_not_ge h48).le
    simpa only [B048.hi,B049.lo] using hlo
  · simpa only [B049.hi,Rat.cast_ofNat] using hu.2

end CK.Certificate.CompactData
