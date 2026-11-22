module
public import CK.Profile.MovingFamily
public import CK.Certificate.ClockBatch.Domains

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
open Set
open scoped BigOperators
namespace CK.Certificate.ClockGeometry.Band1
noncomputable section

def rhoLower : ℝ := (19/20)
def rhoUpper : ℝ := (97/100)
def M : ℝ := (24615813/31250000)
def constantEnergy : ℝ := (1909002661/3215937500)
def affineIntercept : ℝ := (3379158911/6156250000)
def affineSlope : ℝ := (9409/39400)

def a0 : ℝ := (2/5)

theorem a0_nonneg : 0 ≤ a0 := by
  norm_num [a0]
  all_goals nlinarith only []

theorem a0_parameter : CK.Certificate.ClockBatch.C07.parameters 0 = a0 := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C07.v000 := by
    have h := CK.Certificate.ClockBatch.C07.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C07.v001 = a0
  dsimp only [CK.Certificate.ClockBatch.C07.v000, CK.Certificate.ClockBatch.C07.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a0_nonneg).2
  norm_num [a0]
  all_goals nlinarith only []

theorem a0_bounds : ((2/5):ℝ) ≤ a0 ∧ a0 ≤ ((2/5):ℝ) := by
  have h := CK.Certificate.ClockBatch.C07.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C07.parameters 0) (2/5) (2/5) at h
  rw [a0_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> norm_num [a0]

theorem a0_profile (e : ℝ) : CK.Certificate.ClockBatch.C07.profile e = ((1909002661/514550000):ℝ)*CK.Profile.profile e a0 := by
  norm_num [CK.Certificate.ClockBatch.C07.profile,CK.Certificate.ClockBatch.C07.weights,Fin.sum_univ_succ,a0_parameter]

def a1 : ℝ := ((1/12863750) * Real.sqrt (30979399781010))

theorem a1_nonneg : 0 ≤ a1 := by
  have hs0 : (Real.sqrt (30979399781010:ℝ))^2=(30979399781010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (30979399781010:ℝ)
  norm_num [a1]
  all_goals nlinarith only [hs0,hn0]

theorem a1_parameter : CK.Certificate.ClockBatch.C08.parameters 0 = a1 := by
  have hs0 : (Real.sqrt (30979399781010:ℝ))^2=(30979399781010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (30979399781010:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C08.v000 := by
    have h := CK.Certificate.ClockBatch.C08.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C08.v001 = a1
  dsimp only [CK.Certificate.ClockBatch.C08.v000, CK.Certificate.ClockBatch.C08.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a1_nonneg).2
  norm_num [a1]
  all_goals nlinarith only [hs0,hn0]

theorem a1_bounds : ((216341/500000):ℝ) ≤ a1 ∧ a1 ≤ ((432683/1000000):ℝ) := by
  have h := CK.Certificate.ClockBatch.C08.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C08.parameters 0) (216341039786871049/500000000000000000) (432682079573742099/1000000000000000000) at h
  rw [a1_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> linarith

def r1 : ℝ := (20559839/643187500)

theorem a1_cap_parameter : CK.Certificate.ClockBatch.C08.parameters 1 = a1 := by
  have hs0 : (Real.sqrt (30979399781010:ℝ))^2=(30979399781010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (30979399781010:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C08.v000 := by
    have h := CK.Certificate.ClockBatch.C08.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C08.v001 = a1
  dsimp only [CK.Certificate.ClockBatch.C08.v000, CK.Certificate.ClockBatch.C08.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a1_bounds.1,a1_bounds.2])).2
  norm_num [a1]
  all_goals nlinarith only [hs0,hn0]

theorem a1_rest_parameter : CK.Certificate.ClockBatch.C08.parameters 2 = Real.sqrt r1 := by
  change CK.Certificate.ClockBatch.C08.v003 = Real.sqrt r1
  dsimp only [CK.Certificate.ClockBatch.C08.v002, CK.Certificate.ClockBatch.C08.v003, r1]
  all_goals congr 1
  all_goals ring

theorem a1_profile (e : ℝ) : CK.Certificate.ClockBatch.C08.profile e =
    CK.Profile.profile e a1+(2:ℝ)*CK.Profile.profile e a1+CK.Profile.profile e (Real.sqrt r1) := by
  norm_num [CK.Certificate.ClockBatch.C08.profile, CK.Certificate.ClockBatch.C08.weights, Fin.sum_univ_succ, a1_parameter, a1_cap_parameter, r1, a1_rest_parameter]
  all_goals ring

def a2 : ℝ := ((19/135988750) * Real.sqrt (10183437038410))

theorem a2_nonneg : 0 ≤ a2 := by
  have hs0 : (Real.sqrt (10183437038410:ℝ))^2=(10183437038410:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (10183437038410:ℝ)
  norm_num [a2]
  all_goals nlinarith only [hs0,hn0]

theorem a2_parameter : CK.Certificate.ClockBatch.C09.parameters 0 = a2 := by
  have hs0 : (Real.sqrt (10183437038410:ℝ))^2=(10183437038410:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (10183437038410:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C09.v000 := by
    have h := CK.Certificate.ClockBatch.C09.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C09.v001 = a2
  dsimp only [CK.Certificate.ClockBatch.C09.v000, CK.Certificate.ClockBatch.C09.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a2_nonneg).2
  norm_num [a2]
  all_goals nlinarith only [hs0,hn0]

theorem a2_bounds : ((445859/1000000):ℝ) ≤ a2 ∧ a2 ≤ ((22293/50000):ℝ) := by
  have h := CK.Certificate.ClockBatch.C09.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C09.parameters 0) (445859280104313757/1000000000000000000) (222929640052156879/500000000000000000) at h
  rw [a2_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> linarith

def r2 : ℝ := 0

theorem a2_cap_parameter : CK.Certificate.ClockBatch.C09.parameters 1 = a2 := by
  have hs0 : (Real.sqrt (10183437038410:ℝ))^2=(10183437038410:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (10183437038410:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C09.v000 := by
    have h := CK.Certificate.ClockBatch.C09.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C09.v001 = a2
  dsimp only [CK.Certificate.ClockBatch.C09.v000, CK.Certificate.ClockBatch.C09.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a2_bounds.1,a2_bounds.2])).2
  norm_num [a2]
  all_goals nlinarith only [hs0,hn0]

theorem a2_profile (e : ℝ) : CK.Certificate.ClockBatch.C09.profile e =
    CK.Profile.profile e a2+(2:ℝ)*CK.Profile.profile e a2+CK.Profile.profile e (Real.sqrt r2) := by
  norm_num [CK.Certificate.ClockBatch.C09.profile, CK.Certificate.ClockBatch.C09.weights, Fin.sum_univ_succ, a2_parameter, a2_cap_parameter, r2]
  all_goals ring

def a3 : ℝ := (1/2)

theorem a3_nonneg : 0 ≤ a3 := by
  norm_num [a3]
  all_goals nlinarith only []

theorem a3_parameter : CK.Certificate.ClockBatch.C10.parameters 0 = a3 := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C10.v000 := by
    have h := CK.Certificate.ClockBatch.C10.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C10.v001 = a3
  dsimp only [CK.Certificate.ClockBatch.C10.v000, CK.Certificate.ClockBatch.C10.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a3_nonneg).2
  norm_num [a3]
  all_goals nlinarith only []

theorem a3_bounds : ((1/2):ℝ) ≤ a3 ∧ a3 ≤ ((1/2):ℝ) := by
  have h := CK.Certificate.ClockBatch.C10.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C10.parameters 0) (1/2) (1/2) at h
  rw [a3_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> norm_num [a3]

def r3 : ℝ := (1337145947/12312500000)

theorem a3_cap_parameter : CK.Certificate.ClockBatch.C10.parameters 1 = a3 := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C10.v000 := by
    have h := CK.Certificate.ClockBatch.C10.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C10.v001 = a3
  dsimp only [CK.Certificate.ClockBatch.C10.v000, CK.Certificate.ClockBatch.C10.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a3_bounds.1,a3_bounds.2])).2
  norm_num [a3]
  all_goals nlinarith only []

theorem a3_rest_parameter : CK.Certificate.ClockBatch.C10.parameters 2 = Real.sqrt r3 := by
  change CK.Certificate.ClockBatch.C10.v003 = Real.sqrt r3
  dsimp only [CK.Certificate.ClockBatch.C10.v002, CK.Certificate.ClockBatch.C10.v003, r3]
  all_goals congr 1
  all_goals ring

theorem a3_profile (e : ℝ) : CK.Certificate.ClockBatch.C10.profile e =
    CK.Profile.profile e a3+(1:ℝ)*CK.Profile.profile e a3+CK.Profile.profile e (Real.sqrt r3) := by
  norm_num [CK.Certificate.ClockBatch.C10.profile, CK.Certificate.ClockBatch.C10.weights, Fin.sum_univ_succ, a3_parameter, a3_cap_parameter, r3, a3_rest_parameter]
  all_goals ring

def a4 : ℝ := (14449/20000)

theorem a4_nonneg : 0 ≤ a4 := by
  norm_num [a4]
  all_goals nlinarith only []

theorem a4_parameter : CK.Certificate.ClockBatch.C11.parameters 0 = a4 := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C11.v000 := by
    have h := CK.Certificate.ClockBatch.C11.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C11.v001 = a4
  dsimp only [CK.Certificate.ClockBatch.C11.v000, CK.Certificate.ClockBatch.C11.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a4_nonneg).2
  norm_num [a4]
  all_goals nlinarith only []

theorem a4_bounds : ((14449/20000):ℝ) ≤ a4 ∧ a4 ≤ ((14449/20000):ℝ) := by
  have h := CK.Certificate.ClockBatch.C11.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C11.parameters 0) (14449/20000) (14449/20000) at h
  rw [a4_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> norm_num [a4]

def r4 : ℝ := (1175261865169/15760000000000)

theorem a4_cap_parameter : CK.Certificate.ClockBatch.C11.parameters 1 = (1-a4) := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C11.v002 := by
    have h := CK.Certificate.ClockBatch.C11.v002_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C11.v003 = (1-a4)
  dsimp only [CK.Certificate.ClockBatch.C11.v002, CK.Certificate.ClockBatch.C11.v003] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a4_bounds.1,a4_bounds.2])).2
  norm_num [a4]
  all_goals nlinarith only []

theorem a4_rest_parameter : CK.Certificate.ClockBatch.C11.parameters 2 = Real.sqrt r4 := by
  change CK.Certificate.ClockBatch.C11.v005 = Real.sqrt r4
  dsimp only [CK.Certificate.ClockBatch.C11.v004, CK.Certificate.ClockBatch.C11.v005, r4]
  all_goals congr 1
  all_goals ring

theorem a4_profile (e : ℝ) : CK.Certificate.ClockBatch.C11.profile e =
    CK.Profile.profile e a4+(1:ℝ)*CK.Profile.profile e (1-a4)+CK.Profile.profile e (Real.sqrt r4) := by
  norm_num [CK.Certificate.ClockBatch.C11.profile, CK.Certificate.ClockBatch.C11.weights, Fin.sum_univ_succ, a4_parameter, a4_cap_parameter, r4, a4_rest_parameter]
  all_goals ring

theorem segment0_domain :
    0 < a0 ∧ a0 ≤ a1 ∧ a1 < 1 ∧ (-1:ℝ) ≤ 0 ∧
    a1 ≤ (1/2:ℝ) ∧
    ((-1)*a0^2+((1909002661/3215937500))-(2:ℝ)*a0^2) ∈ Icc (0:ℝ) (a0^2) ∧
    ((-1)*a1^2+((1909002661/3215937500))-(2:ℝ)*a1^2) ∈ Icc (0:ℝ) (a1^2) ∧
    0 ≤ ((1909002661/3215937500))+(-1)*a1 := by
  have hl := a0_bounds
  have hu := a1_bounds
  have hs0 : (Real.sqrt (30979399781010:ℝ))^2=(30979399781010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (30979399781010:ℝ)
  dsimp only [a0,a1] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2,hs0,hn0]

theorem segment0_upper_residual : ((-1)*a1^2+((1909002661/3215937500))-(2:ℝ)*a1^2) = r1 := by
  have hs0 : (Real.sqrt (30979399781010:ℝ))^2=(30979399781010:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a1,r1]
  all_goals nlinarith only [hs0]

theorem segment1_domain :
    0 < a1 ∧ a1 ≤ a2 ∧ a2 < 1 ∧ ((-29991/39400):ℝ) ≤ 0 ∧
    a2 ≤ (1/2:ℝ) ∧
    (((-29991/39400))*a1^2+((3379158911/6156250000))-(2:ℝ)*a1^2) ∈ Icc (0:ℝ) (a1^2) ∧
    (((-29991/39400))*a2^2+((3379158911/6156250000))-(2:ℝ)*a2^2) ∈ Icc (0:ℝ) (a2^2) ∧
    0 ≤ ((3379158911/6156250000))+((-29991/39400))*a2 := by
  have hl := a1_bounds
  have hu := a2_bounds
  have hs0 : (Real.sqrt (30979399781010:ℝ))^2=(30979399781010:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (30979399781010:ℝ)
  have hs1 : (Real.sqrt (10183437038410:ℝ))^2=(10183437038410:ℝ) := Real.sq_sqrt (by norm_num)
  have hn1 := Real.sqrt_nonneg (10183437038410:ℝ)
  dsimp only [a1,a2] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2,hs0,hn0, hs1,hn1]

theorem segment1_lower_residual : (((-29991/39400))*a1^2+((3379158911/6156250000))-(2:ℝ)*a1^2) = r1 := by
  have hs0 : (Real.sqrt (30979399781010:ℝ))^2=(30979399781010:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a1,r1]
  all_goals nlinarith only [hs0]

theorem segment1_upper_residual : (((-29991/39400))*a2^2+((3379158911/6156250000))-(2:ℝ)*a2^2) = r2 := by
  have hs0 : (Real.sqrt (10183437038410:ℝ))^2=(10183437038410:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a2,r2]
  all_goals nlinarith only [hs0]

theorem segment2_domain :
    0 < a2 ∧ a2 ≤ a3 ∧ a3 < 1 ∧ ((-29991/39400):ℝ) ≤ 0 ∧
    a3 ≤ (1/2:ℝ) ∧
    (((-29991/39400))*a2^2+((3379158911/6156250000))-(1:ℝ)*a2^2) ∈ Icc (0:ℝ) (a2^2) ∧
    (((-29991/39400))*a3^2+((3379158911/6156250000))-(1:ℝ)*a3^2) ∈ Icc (0:ℝ) (a3^2) ∧
    0 ≤ ((3379158911/6156250000))+((-29991/39400))*a3 := by
  have hl := a2_bounds
  have hu := a3_bounds
  have hs0 : (Real.sqrt (10183437038410:ℝ))^2=(10183437038410:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (10183437038410:ℝ)
  dsimp only [a2,a3] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2,hs0,hn0]

theorem segment2_lower_residual : (((-29991/39400))*a2^2+((3379158911/6156250000))-(1:ℝ)*a2^2) = a2^2 := by
  have hs0 : (Real.sqrt (10183437038410:ℝ))^2=(10183437038410:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a2,r2]
  all_goals nlinarith only [hs0]

theorem segment2_upper_residual : (((-29991/39400))*a3^2+((3379158911/6156250000))-(1:ℝ)*a3^2) = r3 := by
  norm_num [a3,r3]
  all_goals nlinarith only []

theorem segment3_domain :
    0 < a3 ∧ a3 ≤ a4 ∧ a4 < 1 ∧ ((-29991/39400):ℝ) ≤ 0 ∧
    (1/2:ℝ) ≤ a3 ∧
    (((-29991/39400))*a3^2+((3379158911/6156250000))-(1:ℝ)*(1-a3)^2) ∈ Icc (0:ℝ) ((1-a3)^2) ∧
    (((-29991/39400))*a4^2+((3379158911/6156250000))-(1:ℝ)*(1-a4)^2) ∈ Icc (0:ℝ) ((1-a4)^2) ∧
    ((3379158911/6156250000))*((1:ℝ)+1-((-29991/39400)))+((-29991/39400))*((1:ℝ)+1) ≤ 0 := by
  have hl := a3_bounds
  have hu := a4_bounds
  dsimp only [a3,a4] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2]

theorem segment3_lower_residual : (((-29991/39400))*a3^2+((3379158911/6156250000))-(1:ℝ)*(1-a3)^2) = r3 := by
  norm_num [a3,r3]
  all_goals nlinarith only []

theorem segment3_upper_residual : (((-29991/39400))*a4^2+((3379158911/6156250000))-(1:ℝ)*(1-a4)^2) = r4 := by
  norm_num [a4,r4]
  all_goals nlinarith only []

end
end CK.Certificate.ClockGeometry.Band1
