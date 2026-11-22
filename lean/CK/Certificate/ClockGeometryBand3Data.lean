module
public import CK.Profile.MovingFamily
public import CK.Certificate.ClockBatch.Domains

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
open Set
open scoped BigOperators
namespace CK.Certificate.ClockGeometry.Band3
noncomputable section

def rhoLower : ℝ := (487/500)
def rhoUpper : ℝ := (39/40)
def M : ℝ := (772609873/1000000000)
def constantEnergy : ℝ := (23011179967/40975000000)
def affineIntercept : ℝ := (42023679967/79000000000)
def affineSlope : ℝ := (1521/6320)

def a0 : ℝ := (2/5)

theorem a0_nonneg : 0 ≤ a0 := by
  norm_num [a0]
  all_goals nlinarith only []

theorem a0_parameter : CK.Certificate.ClockBatch.C16.parameters 0 = a0 := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C16.v000 := by
    have h := CK.Certificate.ClockBatch.C16.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C16.v001 = a0
  dsimp only [CK.Certificate.ClockBatch.C16.v000, CK.Certificate.ClockBatch.C16.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a0_nonneg).2
  norm_num [a0]
  all_goals nlinarith only []

theorem a0_bounds : ((2/5):ℝ) ≤ a0 ∧ a0 ≤ ((2/5):ℝ) := by
  have h := CK.Certificate.ClockBatch.C16.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C16.parameters 0) (2/5) (2/5) at h
  rw [a0_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> norm_num [a0]

theorem a0_profile (e : ℝ) : CK.Certificate.ClockBatch.C16.profile e = ((23011179967/6556000000):ℝ)*CK.Profile.profile e a0 := by
  norm_num [CK.Certificate.ClockBatch.C16.profile,CK.Certificate.ClockBatch.C16.weights,Fin.sum_univ_succ,a0_parameter]

def a1 : ℝ := ((1/87195000) * Real.sqrt (1465701909889026))

theorem a1_nonneg : 0 ≤ a1 := by
  have hs0 : (Real.sqrt (1465701909889026:ℝ))^2=(1465701909889026:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (1465701909889026:ℝ)
  norm_num [a1]
  all_goals nlinarith only [hs0,hn0]

theorem a1_parameter : CK.Certificate.ClockBatch.C17.parameters 0 = a1 := by
  have hs0 : (Real.sqrt (1465701909889026:ℝ))^2=(1465701909889026:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (1465701909889026:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C17.v000 := by
    have h := CK.Certificate.ClockBatch.C17.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C17.v001 = a1
  dsimp only [CK.Certificate.ClockBatch.C17.v000, CK.Certificate.ClockBatch.C17.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a1_nonneg).2
  norm_num [a1]
  all_goals nlinarith only [hs0,hn0]

theorem a1_bounds : ((439067/1000000):ℝ) ≤ a1 ∧ a1 ≤ ((109767/250000):ℝ) := by
  have h := CK.Certificate.ClockBatch.C17.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C17.parameters 0) (439067452759494109/1000000000000000000) (43906745275949411/100000000000000000) at h
  rw [a1_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> linarith

def r1 : ℝ := 0

theorem a1_cap_parameter : CK.Certificate.ClockBatch.C17.parameters 1 = a1 := by
  have hs0 : (Real.sqrt (1465701909889026:ℝ))^2=(1465701909889026:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (1465701909889026:ℝ)
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C17.v000 := by
    have h := CK.Certificate.ClockBatch.C17.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C17.v001 = a1
  dsimp only [CK.Certificate.ClockBatch.C17.v000, CK.Certificate.ClockBatch.C17.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a1_bounds.1,a1_bounds.2])).2
  norm_num [a1]
  all_goals nlinarith only [hs0,hn0]

theorem a1_profile (e : ℝ) : CK.Certificate.ClockBatch.C17.profile e =
    CK.Profile.profile e a1+(2:ℝ)*CK.Profile.profile e a1+CK.Profile.profile e (Real.sqrt r1) := by
  norm_num [CK.Certificate.ClockBatch.C17.profile, CK.Certificate.ClockBatch.C17.weights, Fin.sum_univ_succ, a1_parameter, a1_cap_parameter, r1]
  all_goals ring

def a2 : ℝ := (1/2)

theorem a2_nonneg : 0 ≤ a2 := by
  norm_num [a2]
  all_goals nlinarith only []

theorem a2_parameter : CK.Certificate.ClockBatch.C18.parameters 0 = a2 := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C18.v000 := by
    have h := CK.Certificate.ClockBatch.C18.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C18.v001 = a2
  dsimp only [CK.Certificate.ClockBatch.C18.v000, CK.Certificate.ClockBatch.C18.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a2_nonneg).2
  norm_num [a2]
  all_goals nlinarith only []

theorem a2_bounds : ((1/2):ℝ) ≤ a2 ∧ a2 ≤ ((1/2):ℝ) := by
  have h := CK.Certificate.ClockBatch.C18.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C18.parameters 0) (1/2) (1/2) at h
  rw [a2_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> norm_num [a2]

def r2 : ℝ := (7276804967/79000000000)

theorem a2_cap_parameter : CK.Certificate.ClockBatch.C18.parameters 1 = a2 := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C18.v000 := by
    have h := CK.Certificate.ClockBatch.C18.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C18.v001 = a2
  dsimp only [CK.Certificate.ClockBatch.C18.v000, CK.Certificate.ClockBatch.C18.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a2_bounds.1,a2_bounds.2])).2
  norm_num [a2]
  all_goals nlinarith only []

theorem a2_rest_parameter : CK.Certificate.ClockBatch.C18.parameters 2 = Real.sqrt r2 := by
  change CK.Certificate.ClockBatch.C18.v003 = Real.sqrt r2
  dsimp only [CK.Certificate.ClockBatch.C18.v002, CK.Certificate.ClockBatch.C18.v003, r2]
  all_goals congr 1
  all_goals ring

theorem a2_profile (e : ℝ) : CK.Certificate.ClockBatch.C18.profile e =
    CK.Profile.profile e a2+(1:ℝ)*CK.Profile.profile e a2+CK.Profile.profile e (Real.sqrt r2) := by
  norm_num [CK.Certificate.ClockBatch.C18.profile, CK.Certificate.ClockBatch.C18.weights, Fin.sum_univ_succ, a2_parameter, a2_cap_parameter, r2, a2_rest_parameter]
  all_goals ring

def a3 : ℝ := (18499/25000)

theorem a3_nonneg : 0 ≤ a3 := by
  norm_num [a3]
  all_goals nlinarith only []

theorem a3_parameter : CK.Certificate.ClockBatch.C19.parameters 0 = a3 := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C19.v000 := by
    have h := CK.Certificate.ClockBatch.C19.v000_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C19.v001 = a3
  dsimp only [CK.Certificate.ClockBatch.C19.v000, CK.Certificate.ClockBatch.C19.v001] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 a3_nonneg).2
  norm_num [a3]
  all_goals nlinarith only []

theorem a3_bounds : ((18499/25000):ℝ) ≤ a3 ∧ a3 ≤ ((18499/25000):ℝ) := by
  have h := CK.Certificate.ClockBatch.C19.v001_bound
  change RationalBound (CK.Certificate.ClockBatch.C19.parameters 0) (18499/25000) (18499/25000) at h
  rw [a3_parameter] at h
  have hl := h.1
  have hu := h.2
  norm_num at hl hu
  constructor <;> norm_num [a3]

def r3 : ℝ := (191801640231/3950000000000)

theorem a3_cap_parameter : CK.Certificate.ClockBatch.C19.parameters 1 = (1-a3) := by
  have hq0 : 0 ≤ CK.Certificate.ClockBatch.C19.v002 := by
    have h := CK.Certificate.ClockBatch.C19.v002_bound.1
    norm_num at h
    linarith
  change CK.Certificate.ClockBatch.C19.v003 = (1-a3)
  dsimp only [CK.Certificate.ClockBatch.C19.v002, CK.Certificate.ClockBatch.C19.v003] at hq0 ⊢
  apply (Real.sqrt_eq_iff_eq_sq hq0 (by linarith [a3_bounds.1,a3_bounds.2])).2
  norm_num [a3]
  all_goals nlinarith only []

theorem a3_rest_parameter : CK.Certificate.ClockBatch.C19.parameters 2 = Real.sqrt r3 := by
  change CK.Certificate.ClockBatch.C19.v005 = Real.sqrt r3
  dsimp only [CK.Certificate.ClockBatch.C19.v004, CK.Certificate.ClockBatch.C19.v005, r3]
  all_goals congr 1
  all_goals ring

theorem a3_profile (e : ℝ) : CK.Certificate.ClockBatch.C19.profile e =
    CK.Profile.profile e a3+(1:ℝ)*CK.Profile.profile e (1-a3)+CK.Profile.profile e (Real.sqrt r3) := by
  norm_num [CK.Certificate.ClockBatch.C19.profile, CK.Certificate.ClockBatch.C19.weights, Fin.sum_univ_succ, a3_parameter, a3_cap_parameter, r3, a3_rest_parameter]
  all_goals ring

theorem segment0_domain :
    0 < a0 ∧ a0 ≤ a1 ∧ a1 < 1 ∧ ((-4799/6320):ℝ) ≤ 0 ∧
    a1 ≤ (1/2:ℝ) ∧
    (((-4799/6320))*a0^2+((42023679967/79000000000))-(2:ℝ)*a0^2) ∈ Icc (0:ℝ) (a0^2) ∧
    (((-4799/6320))*a1^2+((42023679967/79000000000))-(2:ℝ)*a1^2) ∈ Icc (0:ℝ) (a1^2) ∧
    0 ≤ ((42023679967/79000000000))+((-4799/6320))*a1 := by
  have hl := a0_bounds
  have hu := a1_bounds
  have hs0 : (Real.sqrt (1465701909889026:ℝ))^2=(1465701909889026:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (1465701909889026:ℝ)
  dsimp only [a0,a1] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2,hs0,hn0]

theorem segment0_upper_residual : (((-4799/6320))*a1^2+((42023679967/79000000000))-(2:ℝ)*a1^2) = r1 := by
  have hs0 : (Real.sqrt (1465701909889026:ℝ))^2=(1465701909889026:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a1,r1]
  all_goals nlinarith only [hs0]

theorem segment1_domain :
    0 < a1 ∧ a1 ≤ a2 ∧ a2 < 1 ∧ ((-4799/6320):ℝ) ≤ 0 ∧
    a2 ≤ (1/2:ℝ) ∧
    (((-4799/6320))*a1^2+((42023679967/79000000000))-(1:ℝ)*a1^2) ∈ Icc (0:ℝ) (a1^2) ∧
    (((-4799/6320))*a2^2+((42023679967/79000000000))-(1:ℝ)*a2^2) ∈ Icc (0:ℝ) (a2^2) ∧
    0 ≤ ((42023679967/79000000000))+((-4799/6320))*a2 := by
  have hl := a1_bounds
  have hu := a2_bounds
  have hs0 : (Real.sqrt (1465701909889026:ℝ))^2=(1465701909889026:ℝ) := Real.sq_sqrt (by norm_num)
  have hn0 := Real.sqrt_nonneg (1465701909889026:ℝ)
  dsimp only [a1,a2] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2,hs0,hn0]

theorem segment1_lower_residual : (((-4799/6320))*a1^2+((42023679967/79000000000))-(1:ℝ)*a1^2) = a1^2 := by
  have hs0 : (Real.sqrt (1465701909889026:ℝ))^2=(1465701909889026:ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [a1,r1]
  all_goals nlinarith only [hs0]

theorem segment1_upper_residual : (((-4799/6320))*a2^2+((42023679967/79000000000))-(1:ℝ)*a2^2) = r2 := by
  norm_num [a2,r2]
  all_goals nlinarith only []

theorem segment2_domain :
    0 < a2 ∧ a2 ≤ a3 ∧ a3 < 1 ∧ ((-4799/6320):ℝ) ≤ 0 ∧
    (1/2:ℝ) ≤ a2 ∧
    (((-4799/6320))*a2^2+((42023679967/79000000000))-(1:ℝ)*(1-a2)^2) ∈ Icc (0:ℝ) ((1-a2)^2) ∧
    (((-4799/6320))*a3^2+((42023679967/79000000000))-(1:ℝ)*(1-a3)^2) ∈ Icc (0:ℝ) ((1-a3)^2) ∧
    ((42023679967/79000000000))*((1:ℝ)+1-((-4799/6320)))+((-4799/6320))*((1:ℝ)+1) ≤ 0 := by
  have hl := a2_bounds
  have hu := a3_bounds
  dsimp only [a2,a3] at hl hu ⊢
  repeat' constructor
  all_goals nlinarith only [hl.1,hl.2,hu.1,hu.2]

theorem segment2_lower_residual : (((-4799/6320))*a2^2+((42023679967/79000000000))-(1:ℝ)*(1-a2)^2) = r2 := by
  norm_num [a2,r2]
  all_goals nlinarith only []

theorem segment2_upper_residual : (((-4799/6320))*a3^2+((42023679967/79000000000))-(1:ℝ)*(1-a3)^2) = r3 := by
  norm_num [a3,r3]
  all_goals nlinarith only []

end
end CK.Certificate.ClockGeometry.Band3
