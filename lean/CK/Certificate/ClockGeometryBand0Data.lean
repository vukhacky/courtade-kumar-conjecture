module
public import CK.Profile.MovingFamily
public import CK.Certificate.ClockBatch.Domains

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
open Set
open scoped BigOperators
namespace CK.Certificate.ClockGeometry.Band0
noncomputable section

def rhoLower : ℝ := (457/500)
def rhoUpper : ℝ := (19/20)
def M : ℝ := (20630961/25000000)
def constantEnergy : ℝ := (353357479/523750000)
def affineIntercept : ℝ := (578982479/975000000)
def affineSlope : ℝ := (361/1560)

def a0 : ℝ := (2/5)

theorem a0_nonneg : 0 ≤ a0 := by
  norm_num [a0]
  all_goals nlinarith only []

theorem a0_parameter : CK.Certificate.ClockBatch.C00.parameters 0 = a0 := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C00.v000 := by
    have h := CK.Certificate.ClockBatch.C00.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C00.v001 = a0
  dsimp only [CK.Certificate.ClockBatch.C00.v000, CK.Certificate.ClockBatch.C00.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a0_nonneg).2
  norm_num [a0]
  all_goals nlinarith only []

theorem a0_bounds : ((2/5):ℝ) ≤ a0 ∧ a0 ≤ ((2/5):ℝ) := by
  have h := CK.Certificate.ClockBatch.C00.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C00.parameters 0) (2/5) (2/5) at h
  rw [a0_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> norm_num [a0]

theorem a0_profile (e : ℝ) : CK.Certificate.ClockBatch.C00.profile e = ((353357479/83800000):ℝ)*CK.Profile.profile e a0 := by
  norm_num [CK.Certificate.ClockBatch.C00.profile,CK.Certificate.ClockBatch.C00.weights,Fin.sum_univ_succ,a0_parameter]

def a1 : ℝ := ((1/2095000) * Real.sqrt (740283918505))

theorem a1_nonneg : 0 ≤ a1 := by
  have hs0 : (Real.sqrt (740283918505:ℝ))^2=(740283918505:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (740283918505:ℝ)
  norm_num [a1]
  all_goals nlinarith only [hs0,hn0]

theorem a1_parameter : CK.Certificate.ClockBatch.C01.parameters 0 = a1 := by
  have hs0 : (Real.sqrt (740283918505:ℝ))^2=(740283918505:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (740283918505:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C01.v000 := by
    have h := CK.Certificate.ClockBatch.C01.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C01.v001 = a1
  dsimp only [CK.Certificate.ClockBatch.C01.v000, CK.Certificate.ClockBatch.C01.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a1_nonneg).2
  norm_num [a1]
  all_goals nlinarith only [hs0,hn0]

theorem a1_bounds : ((41069/100000):ℝ) ≤ a1 ∧ a1 ≤ ((410691/1000000):ℝ) := by
  have h := CK.Certificate.ClockBatch.C01.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C01.parameters 0) (410690947569184269/1000000000000000000) (41069094756918427/100000000000000000) at h
  rw [a1_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> linarith

def r1 : ℝ := 0

theorem a1_cap_parameter : CK.Certificate.ClockBatch.C01.parameters 1 = a1 := by
  have hs0 : (Real.sqrt (740283918505:ℝ))^2=(740283918505:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (740283918505:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C01.v000 := by
    have h := CK.Certificate.ClockBatch.C01.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C01.v001 = a1
  dsimp only [CK.Certificate.ClockBatch.C01.v000, CK.Certificate.ClockBatch.C01.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a1_bounds.1,a1_bounds.2])).2
  norm_num [a1]
  all_goals nlinarith only [hs0,hn0]

theorem a1_profile (e : ℝ) : CK.Certificate.ClockBatch.C01.profile e =
    CK.Profile.profile e a1+(3:ℝ)*CK.Profile.profile e a1+CK.Profile.profile e (Real.sqrt r1) := by
  norm_num [CK.Certificate.ClockBatch.C01.profile, CK.Certificate.ClockBatch.C01.weights, Fin.sum_univ_succ, a1_parameter, a1_cap_parameter, r1]
  all_goals ring

def a2 : ℝ := ((1/3142500) * Real.sqrt (2220851755515))

theorem a2_nonneg : 0 ≤ a2 := by
  have hs0 : (Real.sqrt (2220851755515:ℝ))^2=(2220851755515:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (2220851755515:ℝ)
  norm_num [a2]
  all_goals nlinarith only [hs0,hn0]

theorem a2_parameter : CK.Certificate.ClockBatch.C02.parameters 0 = a2 := by
  have hs0 : (Real.sqrt (2220851755515:ℝ))^2=(2220851755515:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (2220851755515:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C02.v000 := by
    have h := CK.Certificate.ClockBatch.C02.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C02.v001 = a2
  dsimp only [CK.Certificate.ClockBatch.C02.v000, CK.Certificate.ClockBatch.C02.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a2_nonneg).2
  norm_num [a2]
  all_goals nlinarith only [hs0,hn0]

theorem a2_bounds : ((18969/40000):ℝ) ≤ a2 ∧ a2 ≤ ((237113/500000):ℝ) := by
  have h := CK.Certificate.ClockBatch.C02.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C02.parameters 0) (237112529132811019/500000000000000000) (474225058265622039/1000000000000000000) at h
  rw [a2_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> linarith

def r2 : ℝ := 0

theorem a2_cap_parameter : CK.Certificate.ClockBatch.C02.parameters 1 = a2 := by
  have hs0 : (Real.sqrt (2220851755515:ℝ))^2=(2220851755515:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (2220851755515:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C02.v000 := by
    have h := CK.Certificate.ClockBatch.C02.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C02.v001 = a2
  dsimp only [CK.Certificate.ClockBatch.C02.v000, CK.Certificate.ClockBatch.C02.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a2_bounds.1,a2_bounds.2])).2
  norm_num [a2]
  all_goals nlinarith only [hs0,hn0]

theorem a2_profile (e : ℝ) : CK.Certificate.ClockBatch.C02.profile e =
    CK.Profile.profile e a2+(2:ℝ)*CK.Profile.profile e a2+CK.Profile.profile e (Real.sqrt r2) := by
  norm_num [CK.Certificate.ClockBatch.C02.profile, CK.Certificate.ClockBatch.C02.weights, Fin.sum_univ_succ, a2_parameter, a2_cap_parameter, r2]
  all_goals ring

def a3 : ℝ := (1/2)

theorem a3_nonneg : 0 ≤ a3 := by
  norm_num [a3]
  all_goals nlinarith only []

theorem a3_parameter : CK.Certificate.ClockBatch.C03.parameters 0 = a3 := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C03.v000 := by
    have h := CK.Certificate.ClockBatch.C03.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C03.v001 = a3
  dsimp only [CK.Certificate.ClockBatch.C03.v000, CK.Certificate.ClockBatch.C03.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a3_nonneg).2
  norm_num [a3]
  all_goals nlinarith only []

theorem a3_bounds : ((1/2):ℝ) ≤ a3 ∧ a3 ≤ ((1/2):ℝ) := by
  have h := CK.Certificate.ClockBatch.C03.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C03.parameters 0) (1/2) (1/2) at h
  rw [a3_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> norm_num [a3]

def r3 : ℝ := (91482479/523750000)

theorem a3_cap_parameter : CK.Certificate.ClockBatch.C03.parameters 1 = a3 := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C03.v000 := by
    have h := CK.Certificate.ClockBatch.C03.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C03.v001 = a3
  dsimp only [CK.Certificate.ClockBatch.C03.v000, CK.Certificate.ClockBatch.C03.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a3_bounds.1,a3_bounds.2])).2
  norm_num [a3]
  all_goals nlinarith only []

theorem a3_rest_parameter : CK.Certificate.ClockBatch.C03.parameters 2 = Real.sqrt r3 := by
  change CK.Certificate.ClockBatch.C03.v003 = Real.sqrt r3
  dsimp only [CK.Certificate.ClockBatch.C03.v002, CK.Certificate.ClockBatch.C03.v003, r3]
  all_goals congr 1
  all_goals ring

theorem a3_profile (e : ℝ) : CK.Certificate.ClockBatch.C03.profile e =
    CK.Profile.profile e a3+(1:ℝ)*CK.Profile.profile e a3+CK.Profile.profile e (Real.sqrt r3) := by
  norm_num [CK.Certificate.ClockBatch.C03.profile, CK.Certificate.ClockBatch.C03.weights, Fin.sum_univ_succ, a3_parameter, a3_cap_parameter, r3, a3_rest_parameter]
  all_goals ring

def a4 : ℝ := ((1/1047500) * Real.sqrt (383311587010))

theorem a4_nonneg : 0 ≤ a4 := by
  have hs0 : (Real.sqrt (383311587010:ℝ))^2=(383311587010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (383311587010:ℝ)
  norm_num [a4]
  all_goals nlinarith only [hs0,hn0]

theorem a4_parameter : CK.Certificate.ClockBatch.C04.parameters 0 = a4 := by
  have hs0 : (Real.sqrt (383311587010:ℝ))^2=(383311587010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (383311587010:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C04.v000 := by
    have h := CK.Certificate.ClockBatch.C04.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C04.v001 = a4
  dsimp only [CK.Certificate.ClockBatch.C04.v000, CK.Certificate.ClockBatch.C04.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a4_nonneg).2
  norm_num [a4]
  all_goals nlinarith only [hs0,hn0]

theorem a4_bounds : ((295523/500000):ℝ) ≤ a4 ∧ a4 ≤ ((591047/1000000):ℝ) := by
  have h := CK.Certificate.ClockBatch.C04.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C04.parameters 0) (295523448867511909/500000000000000000) (591046897735023819/1000000000000000000) at h
  rw [a4_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> linarith

def r4 : ℝ := ((-536322437/523750000) + ((1/523750) * Real.sqrt (383311587010)))

theorem a4_cap_parameter : CK.Certificate.ClockBatch.C04.parameters 1 = (1-a4) := by
  have hs0 : (Real.sqrt (383311587010:ℝ))^2=(383311587010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (383311587010:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C04.v008 := by
    have h := CK.Certificate.ClockBatch.C04.v008_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C04.v009 = (1-a4)
  dsimp only [CK.Certificate.ClockBatch.C04.v002, CK.Certificate.ClockBatch.C04.v003, CK.Certificate.ClockBatch.C04.v004, CK.Certificate.ClockBatch.C04.v005, CK.Certificate.ClockBatch.C04.v006, CK.Certificate.ClockBatch.C04.v007, CK.Certificate.ClockBatch.C04.v008, CK.Certificate.ClockBatch.C04.v009] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a4_bounds.1,a4_bounds.2])).2
  norm_num [a4]
  all_goals nlinarith only [hs0,hn0]

theorem a4_rest_parameter : CK.Certificate.ClockBatch.C04.parameters 2 = Real.sqrt r4 := by
  change CK.Certificate.ClockBatch.C04.v016 = Real.sqrt r4
  dsimp only [CK.Certificate.ClockBatch.C04.v004, CK.Certificate.ClockBatch.C04.v005, CK.Certificate.ClockBatch.C04.v010, CK.Certificate.ClockBatch.C04.v011, CK.Certificate.ClockBatch.C04.v012, CK.Certificate.ClockBatch.C04.v013, CK.Certificate.ClockBatch.C04.v014, CK.Certificate.ClockBatch.C04.v015, CK.Certificate.ClockBatch.C04.v016, r4]
  all_goals congr 1
  all_goals ring

theorem a4_profile (e : ℝ) : CK.Certificate.ClockBatch.C04.profile e =
    CK.Profile.profile e a4+(1:ℝ)*CK.Profile.profile e (1-a4)+CK.Profile.profile e (Real.sqrt r4) := by
  norm_num [CK.Certificate.ClockBatch.C04.profile, CK.Certificate.ClockBatch.C04.weights, Fin.sum_univ_succ, a4_parameter, a4_cap_parameter, r4, a4_rest_parameter]
  all_goals ring

def a5 : ℝ := ((3120/4319) + ((-1/10797500) * Real.sqrt (1625753268010)))

theorem a5_nonneg : 0 ≤ a5 := by
  have hs0 : (Real.sqrt (1625753268010:ℝ))^2=(1625753268010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (1625753268010:ℝ)
  norm_num [a5]
  all_goals nlinarith only [hs0,hn0]

theorem a5_parameter : CK.Certificate.ClockBatch.C05.parameters 0 = a5 := by
  have hs0 : (Real.sqrt (1625753268010:ℝ))^2=(1625753268010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (1625753268010:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C05.v006 := by
    have h := CK.Certificate.ClockBatch.C05.v006_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C05.v007 = a5
  dsimp only [CK.Certificate.ClockBatch.C05.v000, CK.Certificate.ClockBatch.C05.v001, CK.Certificate.ClockBatch.C05.v002, CK.Certificate.ClockBatch.C05.v003, CK.Certificate.ClockBatch.C05.v004, CK.Certificate.ClockBatch.C05.v005, CK.Certificate.ClockBatch.C05.v006, CK.Certificate.ClockBatch.C05.v007] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a5_nonneg).2
  norm_num [a5]
  all_goals nlinarith only [hs0,hn0]

theorem a5_bounds : ((604301/1000000):ℝ) ≤ a5 ∧ a5 ≤ ((302151/500000):ℝ) := by
  have h := CK.Certificate.ClockBatch.C05.v007_bound
  change RationalBound (CK.Certificate.ClockBatch.C05.parameters 0) (302150946969752601/500000000000000000) (604301893939505203/1000000000000000000) at h
  rw [a5_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> linarith

def r5 : ℝ := 0

theorem a5_cap_parameter : CK.Certificate.ClockBatch.C05.parameters 1 = (1-a5) := by
  have hs0 : (Real.sqrt (1625753268010:ℝ))^2=(1625753268010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (1625753268010:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C05.v011 := by
    have h := CK.Certificate.ClockBatch.C05.v011_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C05.v012 = (1-a5)
  dsimp only [CK.Certificate.ClockBatch.C05.v000, CK.Certificate.ClockBatch.C05.v002, CK.Certificate.ClockBatch.C05.v003, CK.Certificate.ClockBatch.C05.v008, CK.Certificate.ClockBatch.C05.v009, CK.Certificate.ClockBatch.C05.v010, CK.Certificate.ClockBatch.C05.v011, CK.Certificate.ClockBatch.C05.v012] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a5_bounds.1,a5_bounds.2])).2
  norm_num [a5]
  all_goals nlinarith only [hs0,hn0]

theorem a5_profile (e : ℝ) : CK.Certificate.ClockBatch.C05.profile e =
    CK.Profile.profile e a5+(2:ℝ)*CK.Profile.profile e (1-a5)+CK.Profile.profile e (Real.sqrt r5) := by
  norm_num [CK.Certificate.ClockBatch.C05.profile, CK.Certificate.ClockBatch.C05.weights, Fin.sum_univ_succ, a5_parameter, a5_cap_parameter, r5]
  all_goals ring

def a6 : ℝ := (16749/25000)

theorem a6_nonneg : 0 ≤ a6 := by
  norm_num [a6]
  all_goals nlinarith only []

theorem a6_parameter : CK.Certificate.ClockBatch.C06.parameters 0 = a6 := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C06.v000 := by
    have h := CK.Certificate.ClockBatch.C06.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C06.v001 = a6
  dsimp only [CK.Certificate.ClockBatch.C06.v000, CK.Certificate.ClockBatch.C06.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a6_nonneg).2
  norm_num [a6]
  all_goals nlinarith only []

theorem a6_bounds : ((16749/25000):ℝ) ≤ a6 ∧ a6 ≤ ((16749/25000):ℝ) := by
  have h := CK.Certificate.ClockBatch.C06.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C06.parameters 0) (16749/25000) (16749/25000) at h
  rw [a6_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> norm_num [a6]

def r6 : ℝ := (30221723681/975000000000)

theorem a6_cap_parameter : CK.Certificate.ClockBatch.C06.parameters 1 = (1-a6) := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C06.v002 := by
    have h := CK.Certificate.ClockBatch.C06.v002_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C06.v003 = (1-a6)
  dsimp only [CK.Certificate.ClockBatch.C06.v002, CK.Certificate.ClockBatch.C06.v003] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a6_bounds.1,a6_bounds.2])).2
  norm_num [a6]
  all_goals nlinarith only []

theorem a6_rest_parameter : CK.Certificate.ClockBatch.C06.parameters 2 = Real.sqrt r6 := by
  change CK.Certificate.ClockBatch.C06.v005 = Real.sqrt r6
  dsimp only [CK.Certificate.ClockBatch.C06.v004, CK.Certificate.ClockBatch.C06.v005, r6]
  all_goals congr 1
  all_goals ring

theorem a6_profile (e : ℝ) : CK.Certificate.ClockBatch.C06.profile e =
    CK.Profile.profile e a6+(2:ℝ)*CK.Profile.profile e (1-a6)+CK.Profile.profile e (Real.sqrt r6) := by
  norm_num [CK.Certificate.ClockBatch.C06.profile, CK.Certificate.ClockBatch.C06.weights, Fin.sum_univ_succ, a6_parameter, a6_cap_parameter, r6, a6_rest_parameter]
  all_goals ring

theorem segment0_domain :
    0 < a0 ∧ a0 ≤ a1 ∧ a1 < 1 ∧ (-1:ℝ) ≤ 0 ∧
    a1 ≤ (1/2:ℝ) ∧
    ((-1)*a0^2+((353357479/523750000))-(3:ℝ)*a0^2) ∈ Icc (0:ℝ) (a0^2) ∧
    ((-1)*a1^2+((353357479/523750000))-(3:ℝ)*a1^2) ∈ Icc (0:ℝ) (a1^2) ∧
    0 ≤ ((353357479/523750000))+(-1)*a1 := by
  have hl := a0_bounds
  have hu := a1_bounds
  have hs0 : (Real.sqrt (740283918505:ℝ))^2=(740283918505:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (740283918505:ℝ)
  dsimp only [a0,a1] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2,hs0,hn0]

theorem segment0_upper_residual : ((-1)*a1^2+((353357479/523750000))-(3:ℝ)*a1^2) = r1 := by
  have hs0 : (Real.sqrt (740283918505:ℝ))^2=(740283918505:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a1,r1]
  all_goals nlinarith only [hs0]

theorem segment1_domain :
    0 < a1 ∧ a1 ≤ a2 ∧ a2 < 1 ∧ (-1:ℝ) ≤ 0 ∧
    a2 ≤ (1/2:ℝ) ∧
    ((-1)*a1^2+((353357479/523750000))-(2:ℝ)*a1^2) ∈ Icc (0:ℝ) (a1^2) ∧
    ((-1)*a2^2+((353357479/523750000))-(2:ℝ)*a2^2) ∈ Icc (0:ℝ) (a2^2) ∧
    0 ≤ ((353357479/523750000))+(-1)*a2 := by
  have hl := a1_bounds
  have hu := a2_bounds
  have hs0 : (Real.sqrt (740283918505:ℝ))^2=(740283918505:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (740283918505:ℝ)
  have hs1 : (Real.sqrt (2220851755515:ℝ))^2=(2220851755515:ℝ) := Real.sq_sqrt (by norm_num)
  have hn1 := Real.sqrt_nonneg (2220851755515:ℝ)
  dsimp only [a1,a2] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2,hs0,hn0, hs1,hn1]

theorem segment1_lower_residual : ((-1)*a1^2+((353357479/523750000))-(2:ℝ)*a1^2) = a1^2 := by
  have hs0 : (Real.sqrt (740283918505:ℝ))^2=(740283918505:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a1,r1]
  all_goals nlinarith only [hs0]

theorem segment1_upper_residual : ((-1)*a2^2+((353357479/523750000))-(2:ℝ)*a2^2) = r2 := by
  have hs0 : (Real.sqrt (2220851755515:ℝ))^2=(2220851755515:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a2,r2]
  all_goals nlinarith only [hs0]

theorem segment2_domain :
    0 < a2 ∧ a2 ≤ a3 ∧ a3 < 1 ∧ (-1:ℝ) ≤ 0 ∧
    a3 ≤ (1/2:ℝ) ∧
    ((-1)*a2^2+((353357479/523750000))-(1:ℝ)*a2^2) ∈ Icc (0:ℝ) (a2^2) ∧
    ((-1)*a3^2+((353357479/523750000))-(1:ℝ)*a3^2) ∈ Icc (0:ℝ) (a3^2) ∧
    0 ≤ ((353357479/523750000))+(-1)*a3 := by
  have hl := a2_bounds
  have hu := a3_bounds
  have hs0 : (Real.sqrt (2220851755515:ℝ))^2=(2220851755515:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (2220851755515:ℝ)
  dsimp only [a2,a3] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2,hs0,hn0]

theorem segment2_lower_residual : ((-1)*a2^2+((353357479/523750000))-(1:ℝ)*a2^2) = a2^2 := by
  have hs0 : (Real.sqrt (2220851755515:ℝ))^2=(2220851755515:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a2,r2]
  all_goals nlinarith only [hs0]

theorem segment2_upper_residual : ((-1)*a3^2+((353357479/523750000))-(1:ℝ)*a3^2) = r3 := by
  norm_num [a3,r3]
  all_goals nlinarith only []

theorem segment3_domain :
    0 < a3 ∧ a3 ≤ a4 ∧ a4 < 1 ∧ (-1:ℝ) ≤ 0 ∧
    (1/2:ℝ) ≤ a3 ∧
    ((-1)*a3^2+((353357479/523750000))-(1:ℝ)*(1-a3)^2) ∈ Icc (0:ℝ) ((1-a3)^2) ∧
    ((-1)*a4^2+((353357479/523750000))-(1:ℝ)*(1-a4)^2) ∈ Icc (0:ℝ) ((1-a4)^2) ∧
    0 ≤ ((353357479/523750000))+(-1)*a4 := by
  have hl := a3_bounds
  have hu := a4_bounds
  have hs0 : (Real.sqrt (383311587010:ℝ))^2=(383311587010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (383311587010:ℝ)
  dsimp only [a3,a4] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2,hs0,hn0]

theorem segment3_lower_residual : ((-1)*a3^2+((353357479/523750000))-(1:ℝ)*(1-a3)^2) = r3 := by
  norm_num [a3,r3]
  all_goals nlinarith only []

theorem segment3_upper_residual : ((-1)*a4^2+((353357479/523750000))-(1:ℝ)*(1-a4)^2) = r4 := by
  have hs0 : (Real.sqrt (383311587010:ℝ))^2=(383311587010:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a4,r4]
  all_goals nlinarith only [hs0]

theorem segment4_domain :
    0 < a4 ∧ a4 ≤ a5 ∧ a5 < 1 ∧ ((-1199/1560):ℝ) ≤ 0 ∧
    (1/2:ℝ) ≤ a4 ∧
    (((-1199/1560))*a4^2+((578982479/975000000))-(1:ℝ)*(1-a4)^2) ∈ Icc (0:ℝ) ((1-a4)^2) ∧
    (((-1199/1560))*a5^2+((578982479/975000000))-(1:ℝ)*(1-a5)^2) ∈ Icc (0:ℝ) ((1-a5)^2) ∧
    0 ≤ ((578982479/975000000))+((-1199/1560))*a5 := by
  have hl := a4_bounds
  have hu := a5_bounds
  have hs0 : (Real.sqrt (383311587010:ℝ))^2=(383311587010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (383311587010:ℝ)
  have hs1 : (Real.sqrt (1625753268010:ℝ))^2=(1625753268010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn1 := Real.sqrt_nonneg (1625753268010:ℝ)
  dsimp only [a4,a5] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2,hs0,hn0, hs1,hn1]

theorem segment4_lower_residual : (((-1199/1560))*a4^2+((578982479/975000000))-(1:ℝ)*(1-a4)^2) = r4 := by
  have hs0 : (Real.sqrt (383311587010:ℝ))^2=(383311587010:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a4,r4]
  all_goals nlinarith only [hs0]

theorem segment4_upper_residual : (((-1199/1560))*a5^2+((578982479/975000000))-(1:ℝ)*(1-a5)^2) = (1-a5)^2 := by
  have hs0 : (Real.sqrt (1625753268010:ℝ))^2=(1625753268010:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a5,r5]
  all_goals nlinarith only [hs0]

theorem segment5_domain :
    0 < a5 ∧ a5 ≤ a6 ∧ a6 < 1 ∧ ((-1199/1560):ℝ) ≤ 0 ∧
    (1/2:ℝ) ≤ a5 ∧
    (((-1199/1560))*a5^2+((578982479/975000000))-(2:ℝ)*(1-a5)^2) ∈ Icc (0:ℝ) ((1-a5)^2) ∧
    (((-1199/1560))*a6^2+((578982479/975000000))-(2:ℝ)*(1-a6)^2) ∈ Icc (0:ℝ) ((1-a6)^2) ∧
    0 ≤ ((578982479/975000000))+((-1199/1560))*a6 := by
  have hl := a5_bounds
  have hu := a6_bounds
  have hs0 : (Real.sqrt (1625753268010:ℝ))^2=(1625753268010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (1625753268010:ℝ)
  dsimp only [a5,a6] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2,hs0,hn0]

theorem segment5_lower_residual : (((-1199/1560))*a5^2+((578982479/975000000))-(2:ℝ)*(1-a5)^2) = r5 := by
  have hs0 : (Real.sqrt (1625753268010:ℝ))^2=(1625753268010:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a5,r5]
  all_goals nlinarith only [hs0]

theorem segment5_upper_residual : (((-1199/1560))*a6^2+((578982479/975000000))-(2:ℝ)*(1-a6)^2) = r6 := by
  norm_num [a6,r6]
  all_goals nlinarith only []

end
end CK.Certificate.ClockGeometry.Band0
