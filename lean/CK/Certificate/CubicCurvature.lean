module

public import CK.Certificate.BernsteinRectangle

/-! Full-rectangle algebraic bounds in the source cubic-endpoint curvature lemma.
The two coordinates range independently over x∈[0,43/500], M∈[3/4,83/100]. -/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace CK.Certificate.CubicCurvature
noncomputable section

def C (M x : ℝ) : ℝ := 3-2*M+(-3+5*M)*x+(1-4*M)*x^2+M*x^3
def N (x : ℝ) : ℝ := 1/2+3*x-3*x^2+x^3
def C1 (M x : ℝ) : ℝ := (-3+5*M)+2*(1-4*M)*x+3*M*x^2
def C2 (M x : ℝ) : ℝ := 2*(1-4*M)+6*M*x
def N1 (x : ℝ) : ℝ := 3-6*x+3*x^2
def N2 (x : ℝ) : ℝ := -6+6*x
def D1 (M x : ℝ) : ℝ := N1 x*C M x-N x*C1 M x
def D2 (M x : ℝ) : ℝ := (N2 x*C M x-N x*C2 M x)*C M x-2*D1 M x*C1 M x

def den_lowerData : List BernsteinTerm2 := [
  (0, 0, 0),
  (4/25, 0, 1),
  (989/10000, 1, 0),
  (1089/2000, 1, 1),
  (70563/390625, 2, 0),
  (18569/31250, 2, 1),
  (1028365081/12500000000, 3, 0),
  (105092521/500000000, 3, 1)
]

theorem den_lower_checked : checkBernstein2 den_lowerData = true := by
  norm_num [checkBernstein2,den_lowerData]

theorem den_lower_identity (u v : ℝ) :
    (C ((83/100:ℝ)-(2/25)*v) ((43/500:ℝ)*u)-(67/50:ℝ)) = evalBernstein2 3 1 den_lowerData u v := by
  norm_num [C,N,C1,C2,N1,N2,D1,D2,evalBernstein2,evalBernsteinTerm2,den_lowerData]
  ring

theorem den_lower_certificate {M x : ℝ} (hM : M ∈ Set.Icc (3/4:ℝ) (83/100))
    (hx : x ∈ Set.Icc (0:ℝ) (43/500)) : 0 ≤ C M x-(67/50:ℝ) := by
  let u : ℝ := x/(43/500)
  let v : ℝ := (83/100-M)/(2/25)
  have hu : u ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [u]
    constructor
    · exact div_nonneg hx.1 (by norm_num)
    · exact (div_le_one (by norm_num)).mpr hx.2
  have hv : v ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [v]
    constructor
    · exact div_nonneg (by linarith [hM.2]) (by norm_num)
    · apply (div_le_one (by norm_num)).mpr
      linarith [hM.1]
  have hxu : (43/500:ℝ)*u=x := by dsimp [u]; ring
  have hMv : (83/100:ℝ)-(2/25)*v=M := by dsimp [v]; ring
  have h := checkBernstein2_sound (du:=3) (dv:=1) den_lower_checked hu hv
  rw [←den_lower_identity] at h
  simp only [hxu,hMv] at h
  exact h

def den_upperData : List BernsteinTerm2 := [
  (13/50, 0, 0),
  (1/10, 0, 1),
  (6811/10000, 1, 0),
  (471/2000, 1, 1),
  (468249/781250, 2, 0),
  (2903/15625, 2, 1),
  (2221634919/12500000000, 3, 0),
  (24907479/500000000, 3, 1)
]

theorem den_upper_checked : checkBernstein2 den_upperData = true := by
  norm_num [checkBernstein2,den_upperData]

theorem den_upper_identity (u v : ℝ) :
    ((8/5:ℝ)-C ((83/100:ℝ)-(2/25)*v) ((43/500:ℝ)*u)) = evalBernstein2 3 1 den_upperData u v := by
  norm_num [C,N,C1,C2,N1,N2,D1,D2,evalBernstein2,evalBernsteinTerm2,den_upperData]
  ring

theorem den_upper_certificate {M x : ℝ} (hM : M ∈ Set.Icc (3/4:ℝ) (83/100))
    (hx : x ∈ Set.Icc (0:ℝ) (43/500)) : 0 ≤ (8/5:ℝ)-C M x := by
  let u : ℝ := x/(43/500)
  let v : ℝ := (83/100-M)/(2/25)
  have hu : u ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [u]
    constructor
    · exact div_nonneg hx.1 (by norm_num)
    · exact (div_le_one (by norm_num)).mpr hx.2
  have hv : v ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [v]
    constructor
    · exact div_nonneg (by linarith [hM.2]) (by norm_num)
    · apply (div_le_one (by norm_num)).mpr
      linarith [hM.1]
  have hxu : (43/500:ℝ)*u=x := by dsimp [u]; ring
  have hMv : (83/100:ℝ)-(2/25)*v=M := by dsimp [v]; ring
  have h := checkBernstein2_sound (du:=3) (dv:=1) den_upper_checked hu hv
  rw [←den_upper_identity] at h
  simp only [hxu,hMv] at h
  exact h

def num_nonnegData : List BernsteinTerm2 := [
  (1/2, 0, 0),
  (879/500, 1, 0),
  (498453/250000, 2, 0),
  (92056007/125000000, 3, 0)
]

theorem num_nonneg_checked : checkBernstein2 num_nonnegData = true := by
  norm_num [checkBernstein2,num_nonnegData]

theorem num_nonneg_identity (u v : ℝ) :
    (N ((43/500:ℝ)*u)) = evalBernstein2 3 0 num_nonnegData u v := by
  norm_num [C,N,C1,C2,N1,N2,D1,D2,evalBernstein2,evalBernsteinTerm2,num_nonnegData]
  ring

theorem num_nonneg_certificate {M x : ℝ} (hM : M ∈ Set.Icc (3/4:ℝ) (83/100))
    (hx : x ∈ Set.Icc (0:ℝ) (43/500)) : 0 ≤ N x := by
  let u : ℝ := x/(43/500)
  let v : ℝ := (83/100-M)/(2/25)
  have hu : u ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [u]
    constructor
    · exact div_nonneg hx.1 (by norm_num)
    · exact (div_le_one (by norm_num)).mpr hx.2
  have hv : v ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [v]
    constructor
    · exact div_nonneg (by linarith [hM.2]) (by norm_num)
    · apply (div_le_one (by norm_num)).mpr
      linarith [hM.1]
  have hxu : (43/500:ℝ)*u=x := by dsimp [u]; ring
  have hMv : (83/100:ℝ)-(2/25)*v=M := by dsimp [v]; ring
  have h := checkBernstein2_sound (du:=3) (dv:=0) num_nonneg_checked hu hv
  rw [←num_nonneg_identity] at h
  simp only [hxu,hMv] at h
  exact h

def num_upperData : List BernsteinTerm2 := [
  (38/125, 0, 0),
  (2/5, 0, 1),
  (35667/50000, 1, 0),
  (9807/10000, 1, 1),
  (16455399/31250000, 2, 0),
  (968391/1250000, 2, 1),
  (7307091743/62500000000, 3, 0),
  (484157423/2500000000, 3, 1)
]

theorem num_upper_checked : checkBernstein2 num_upperData = true := by
  norm_num [checkBernstein2,num_upperData]

theorem num_upper_identity (u v : ℝ) :
    ((3/5:ℝ)*C ((83/100:ℝ)-(2/25)*v) ((43/500:ℝ)*u)-N ((43/500:ℝ)*u)) = evalBernstein2 3 1 num_upperData u v := by
  norm_num [C,N,C1,C2,N1,N2,D1,D2,evalBernstein2,evalBernsteinTerm2,num_upperData]
  ring

theorem num_upper_certificate {M x : ℝ} (hM : M ∈ Set.Icc (3/4:ℝ) (83/100))
    (hx : x ∈ Set.Icc (0:ℝ) (43/500)) : 0 ≤ (3/5:ℝ)*C M x-N x := by
  let u : ℝ := x/(43/500)
  let v : ℝ := (83/100-M)/(2/25)
  have hu : u ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [u]
    constructor
    · exact div_nonneg hx.1 (by norm_num)
    · exact (div_le_one (by norm_num)).mpr hx.2
  have hv : v ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [v]
    constructor
    · exact div_nonneg (by linarith [hM.2]) (by norm_num)
    · apply (div_le_one (by norm_num)).mpr
      linarith [hM.1]
  have hxu : (43/500:ℝ)*u=x := by dsimp [u]; ring
  have hMv : (83/100:ℝ)-(2/25)*v=M := by dsimp [v]; ring
  have h := checkBernstein2_sound (du:=3) (dv:=1) num_upper_checked hu hv
  rw [←num_upper_identity] at h
  simp only [hxu,hMv] at h
  exact h

def slope_upperData : List BernsteinTerm2 := [
  (731/5000, 0, 0),
  (47/100, 0, 1),
  (3/8, 0, 2),
  (237403/125000, 1, 0),
  (60663/12500, 1, 1),
  (3239/1000, 1, 2),
  (1122535597/156250000, 2, 0),
  (21199123/1250000, 2, 1),
  (1304609/125000, 2, 2),
  (1979127751497/156250000000, 3, 0),
  (89705788241/3125000000, 3, 1),
  (4214610521/250000000, 3, 2),
  (228396763591079/19531250000000, 4, 0),
  (20190221489851/781250000000, 4, 1),
  (22999439469/1562500000, 4, 2),
  (53774714961069199/9765625000000000, 5, 0),
  (467239840804069/39062500000000, 5, 1),
  (104162750667171/15625000000000, 5, 2),
  (81861786120607636561/78125000000000000000, 6, 0),
  (3511642596980159201/1562500000000000000, 6, 1),
  (154043165209635441/125000000000000000, 6, 2)
]

theorem slope_upper_checked : checkBernstein2 slope_upperData = true := by
  norm_num [checkBernstein2,slope_upperData]

theorem slope_upper_identity (u v : ℝ) :
    (2*(C ((83/100:ℝ)-(2/25)*v) ((43/500:ℝ)*u))^2-D1 ((83/100:ℝ)-(2/25)*v) ((43/500:ℝ)*u)) = evalBernstein2 6 2 slope_upperData u v := by
  norm_num [C,N,C1,C2,N1,N2,D1,D2,evalBernstein2,evalBernsteinTerm2,slope_upperData]
  ring

theorem slope_upper_certificate {M x : ℝ} (hM : M ∈ Set.Icc (3/4:ℝ) (83/100))
    (hx : x ∈ Set.Icc (0:ℝ) (43/500)) : 0 ≤ 2*(C M x)^2-D1 M x := by
  let u : ℝ := x/(43/500)
  let v : ℝ := (83/100-M)/(2/25)
  have hu : u ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [u]
    constructor
    · exact div_nonneg hx.1 (by norm_num)
    · exact (div_le_one (by norm_num)).mpr hx.2
  have hv : v ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [v]
    constructor
    · exact div_nonneg (by linarith [hM.2]) (by norm_num)
    · apply (div_le_one (by norm_num)).mpr
      linarith [hM.1]
  have hxu : (43/500:ℝ)*u=x := by dsimp [u]; ring
  have hMv : (83/100:ℝ)-(2/25)*v=M := by dsimp [v]; ring
  have h := checkBernstein2_sound (du:=6) (dv:=2) slope_upper_checked hu hv
  rw [←slope_upper_identity] at h
  simp only [hxu,hMv] at h
  exact h

def second_lowerData : List BernsteinTerm2 := [
  (313607/250000, 0, 0),
  (83581/10000, 0, 1),
  (1121/80, 0, 2),
  (111/16, 0, 3),
  (370736843/25000000, 1, 0),
  (441331013/5000000, 1, 1),
  (28404389/200000, 1, 2),
  (550743/8000, 1, 3),
  (9346089277641/125000000000, 2, 0),
  (411408307503/1000000000, 2, 1),
  (128151661179/200000000, 2, 2),
  (2441275737/8000000, 2, 3),
  (26865060275701911/125000000000000, 3, 0),
  (5585362301166581/5000000000000, 3, 1),
  (339060802590501/200000000000, 3, 2),
  (254604863199/320000000, 3, 3),
  (12287403028123298163/31250000000000000, 4, 0),
  (2449148460459542681/1250000000000000, 4, 1),
  (29131852460698821/10000000000000, 4, 2),
  (2701924036698291/2000000000000, 4, 3),
  (15015588206483201399061/31250000000000000000, 5, 0),
  (2901184235258414413359/1250000000000000000, 5, 1),
  (169828429843151255583/50000000000000000, 5, 2),
  (3120606036894264069/2000000000000000, 5, 3),
  (310961880682545402158907/781250000000000000000, 6, 0),
  (58757821391118848724937/31250000000000000000, 6, 1),
  (16998520669167404698469/6250000000000000000, 6, 2),
  (310164071284978290847/250000000000000000, 6, 3),
  (1724697309219794076148319169/7812500000000000000000000, 7, 0),
  (64240174108228468565811959/62500000000000000000000, 7, 1),
  (18444419176334091013776739/12500000000000000000000, 7, 2),
  (335028542467267063327313/500000000000000000000, 7, 3),
  (153025812897277850405372157531/1953125000000000000000000000, 8, 0),
  (28302878993320033589951166321/78125000000000000000000000, 8, 1),
  (1619897690661299244840286929/3125000000000000000000000, 8, 2),
  (29371065017556037433860539/125000000000000000000000, 8, 3),
  (31273667990559742350478350446847/1953125000000000000000000000000, 9, 0),
  (5792700575138108508280714395661/78125000000000000000000000000, 9, 1),
  (332067161428855737473218826781/3125000000000000000000000000, 9, 2),
  (6028927930606127632743133967/125000000000000000000000000, 9, 3),
  (138836867759808116774151675643461/97656250000000000000000000000000, 10, 0),
  (26027705591828959989757031066303/3906250000000000000000000000000, 10, 1),
  (1503587583637302668413622383023/156250000000000000000000000000, 10, 2),
  (27442553553769590918166224181/6250000000000000000000000000, 10, 3)
]

theorem second_lower_checked : checkBernstein2 second_lowerData = true := by
  norm_num [checkBernstein2,second_lowerData]

theorem second_lower_identity (u v : ℝ) :
    (D2 ((83/100:ℝ)-(2/25)*v) ((43/500:ℝ)*u)-(-7+30*((43/500:ℝ)*u))*(C ((83/100:ℝ)-(2/25)*v) ((43/500:ℝ)*u))^3) = evalBernstein2 10 3 second_lowerData u v := by
  norm_num [C,N,C1,C2,N1,N2,D1,D2,evalBernstein2,evalBernsteinTerm2,second_lowerData]
  ring

theorem second_lower_certificate {M x : ℝ} (hM : M ∈ Set.Icc (3/4:ℝ) (83/100))
    (hx : x ∈ Set.Icc (0:ℝ) (43/500)) : 0 ≤ D2 M x-(-7+30*x)*(C M x)^3 := by
  let u : ℝ := x/(43/500)
  let v : ℝ := (83/100-M)/(2/25)
  have hu : u ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [u]
    constructor
    · exact div_nonneg hx.1 (by norm_num)
    · exact (div_le_one (by norm_num)).mpr hx.2
  have hv : v ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [v]
    constructor
    · exact div_nonneg (by linarith [hM.2]) (by norm_num)
    · apply (div_le_one (by norm_num)).mpr
      linarith [hM.1]
  have hxu : (43/500:ℝ)*u=x := by dsimp [u]; ring
  have hMv : (83/100:ℝ)-(2/25)*v=M := by dsimp [v]; ring
  have h := checkBernstein2_sound (du:=10) (dv:=3) second_lower_checked hu hv
  rw [←second_lower_identity] at h
  simp only [hxu,hMv] at h
  exact h

def second_upperData : List BernsteinTerm2 := [
  (155883/10000, 0, 0),
  (6523/200, 0, 1),
  (267/16, 0, 2),
  (221915349/2500000, 1, 0),
  (9285141/50000, 1, 1),
  (379989/4000, 1, 2),
  (526268024241/2500000000, 2, 0),
  (22017412209/50000000, 2, 1),
  (180177213/800000, 2, 2),
  (20789154368683/78125000000, 3, 0),
  (173936752877/312500000, 3, 1),
  (35578652247/125000000, 3, 2),
  (7386665066287833/39062500000000, 4, 0),
  (12359672386977/31250000000, 4, 1),
  (12638752084377/62500000000, 4, 2),
  (5595440080435477431/78125000000000000, 5, 0),
  (9362188647480039/62500000000000, 5, 1),
  (9572149502280039/125000000000000, 5, 2),
  (882407286681004693139/78125000000000000000, 6, 0),
  (36910448865432299283/1562500000000000000, 6, 1),
  (1509326818240128147/125000000000000000, 6, 2)
]

theorem second_upper_checked : checkBernstein2 second_upperData = true := by
  norm_num [checkBernstein2,second_upperData]

theorem second_upper_identity (u v : ℝ) :
    (-D2 ((83/100:ℝ)-(2/25)*v) ((43/500:ℝ)*u)) = evalBernstein2 6 2 second_upperData u v := by
  norm_num [C,N,C1,C2,N1,N2,D1,D2,evalBernstein2,evalBernsteinTerm2,second_upperData]
  ring

theorem second_upper_certificate {M x : ℝ} (hM : M ∈ Set.Icc (3/4:ℝ) (83/100))
    (hx : x ∈ Set.Icc (0:ℝ) (43/500)) : 0 ≤ -D2 M x := by
  let u : ℝ := x/(43/500)
  let v : ℝ := (83/100-M)/(2/25)
  have hu : u ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [u]
    constructor
    · exact div_nonneg hx.1 (by norm_num)
    · exact (div_le_one (by norm_num)).mpr hx.2
  have hv : v ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [v]
    constructor
    · exact div_nonneg (by linarith [hM.2]) (by norm_num)
    · apply (div_le_one (by norm_num)).mpr
      linarith [hM.1]
  have hxu : (43/500:ℝ)*u=x := by dsimp [u]; ring
  have hMv : (83/100:ℝ)-(2/25)*v=M := by dsimp [v]; ring
  have h := checkBernstein2_sound (du:=6) (dv:=2) second_upper_checked hu hv
  rw [←second_upper_identity] at h
  simp only [hxu,hMv] at h
  exact h

def value_slope_lowerData : List BernsteinTerm2 := [
  (134/1875, 0, 0),
  (2/25, 0, 1),
  (0, 0, 2),
  (1308473/2500000, 1, 0),
  (6073/10000, 1, 1),
  (129/4000, 1, 2),
  (4422518393/2500000000, 2, 0),
  (333301003/150000000, 2, 1),
  (1278777/4000000, 2, 2),
  (325918540553/93750000000, 3, 0),
  (7439367953/1562500000, 3, 1),
  (2189689/2000000, 3, 2),
  (784243966373119/187500000000000, 4, 0),
  (7714742013461/1250000000000, 4, 1),
  (2742120770683/1500000000000, 4, 2),
  (177492354612073483/58593750000000000, 5, 0),
  (92555744234571/19531250000000, 5, 1),
  (50887425597567/31250000000000, 5, 2),
  (567838521781350645011/468750000000000000000, 6, 0),
  (18570664433125951411/9375000000000000000, 6, 1),
  (186739561760986737/250000000000000000, 6, 2),
  (24075107927690306001119/117187500000000000000000, 7, 0),
  (814035145795845349679/2343750000000000000000, 7, 1),
  (26107674534815552639/187500000000000000000, 7, 2)
]

theorem value_slope_lower_checked : checkBernstein2 value_slope_lowerData = true := by
  norm_num [checkBernstein2,value_slope_lowerData]

theorem value_slope_lower_identity (u v : ℝ) :
    (N ((43/500:ℝ)*u)*C ((83/100:ℝ)-(2/25)*v) ((43/500:ℝ)*u)-2*((43/500:ℝ)*u)*D1 ((83/100:ℝ)-(2/25)*v) ((43/500:ℝ)*u)-((1/3:ℝ)-2*((43/500:ℝ)*u))*(C ((83/100:ℝ)-(2/25)*v) ((43/500:ℝ)*u))^2) = evalBernstein2 7 2 value_slope_lowerData u v := by
  norm_num [C,N,C1,C2,N1,N2,D1,D2,evalBernstein2,evalBernsteinTerm2,value_slope_lowerData]
  ring

theorem value_slope_lower_certificate {M x : ℝ} (hM : M ∈ Set.Icc (3/4:ℝ) (83/100))
    (hx : x ∈ Set.Icc (0:ℝ) (43/500)) : 0 ≤ N x*C M x-2*x*D1 M x-((1/3:ℝ)-2*x)*(C M x)^2 := by
  let u : ℝ := x/(43/500)
  let v : ℝ := (83/100-M)/(2/25)
  have hu : u ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [u]
    constructor
    · exact div_nonneg hx.1 (by norm_num)
    · exact (div_le_one (by norm_num)).mpr hx.2
  have hv : v ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [v]
    constructor
    · exact div_nonneg (by linarith [hM.2]) (by norm_num)
    · apply (div_le_one (by norm_num)).mpr
      linarith [hM.1]
  have hxu : (43/500:ℝ)*u=x := by dsimp [u]; ring
  have hMv : (83/100:ℝ)-(2/25)*v=M := by dsimp [v]; ring
  have h := checkBernstein2_sound (du:=7) (dv:=2) value_slope_lower_checked hu hv
  rw [←value_slope_lower_identity] at h
  simp only [hxu,hMv] at h
  exact h

theorem bounds {M x : ℝ} (hM : M ∈ Set.Icc (3/4:ℝ) (83/100))
    (hx : x ∈ Set.Icc (0:ℝ) (43/500)) :
    (67/50:ℝ) ≤ C M x ∧ C M x ≤ 8/5 ∧ 0 ≤ N x ∧ N x ≤ (3/5)*C M x ∧
    D1 M x ≤ 2*(C M x)^2 ∧ (-7+30*x)*(C M x)^3 ≤ D2 M x ∧ D2 M x ≤ 0 ∧
    ((1/3:ℝ)-2*x)*(C M x)^2 ≤ N x*C M x-2*x*D1 M x := by
  have h0 := den_lower_certificate hM hx
  have h1 := den_upper_certificate hM hx
  have h2 := num_nonneg_certificate hM hx
  have h3 := num_upper_certificate hM hx
  have h4 := slope_upper_certificate hM hx
  have h5 := second_lower_certificate hM hx
  have h6 := second_upper_certificate hM hx
  have h7 := value_slope_lower_certificate hM hx
  refine ⟨by linarith,by linarith,h2,by linarith,by linarith,by linarith,by linarith,by linarith⟩

end
end CK.Certificate.CubicCurvature
