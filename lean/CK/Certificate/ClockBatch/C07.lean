module
public import CK.Certificate.ClockPanels
public import CK.Certificate.ClockBatch.LogData

@[expose] public section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open MeasureTheory
open scoped BigOperators Interval
namespace CK.Certificate.ClockBatch.C07
noncomputable section

def v000 : ℝ := (4/25 : ℝ)
theorem v000_bound : RationalBound v000 (4/25) (4/25) := by
  change RationalBound ((4/25 : ℝ)) (4/25) (4/25)
  norm_num [RationalBound]

def v001 : ℝ := Real.sqrt v000
theorem v001_bound : RationalBound v001 (2/5) (2/5) := by
  change RationalBound (Real.sqrt v000) (2/5) (2/5)
  exact rationalBound_sqrt v000_bound (by norm_num) (by norm_num) (by norm_num)

def v002 : ℝ := (1/40 : ℝ)
theorem v002_bound : RationalBound v002 (1/40) (1/40) := by
  change RationalBound ((1/40 : ℝ)) (1/40) (1/40)
  norm_num [RationalBound]

def v003 : ℝ := Real.log (40 : ℝ)
theorem v003_bound : RationalBound v003 (36888794541139363/10000000000000000) (1844439727056968153/500000000000000000) := by
  change RationalBound (Real.log (40 : ℝ)) (36888794541139363/10000000000000000) (1844439727056968153/500000000000000000)
  exact LogData.log090_bound

def v004 : ℝ := v002*v003
theorem v004_bound : RationalBound v004 (92221986352848407/1000000000000000000) (11527748294106051/125000000000000000) := by
  change RationalBound (v002*v003) (92221986352848407/1000000000000000000) (11527748294106051/125000000000000000)
  exact rationalBound_mul v002_bound v003_bound (by norm_num) (by norm_num)

def v005 : ℝ := (39/40 : ℝ)
theorem v005_bound : RationalBound v005 (39/40) (39/40) := by
  change RationalBound ((39/40 : ℝ)) (39/40) (39/40)
  norm_num [RationalBound]

def v006 : ℝ := Real.log (40/39 : ℝ)
theorem v006_bound : RationalBound v006 (202542463874319/8000000000000000) (6329451996072469/250000000000000000) := by
  change RationalBound (Real.log (40/39 : ℝ)) (202542463874319/8000000000000000) (6329451996072469/250000000000000000)
  exact LogData.log091_bound

def v007 : ℝ := v005*v006
theorem v007_bound : RationalBound v007 (6171215696170657/250000000000000000) (2468486278468263/100000000000000000) := by
  change RationalBound (v005*v006) (6171215696170657/250000000000000000) (2468486278468263/100000000000000000)
  exact rationalBound_mul v005_bound v006_bound (by norm_num) (by norm_num)

def v008 : ℝ := v004+v007
theorem v008_bound : RationalBound v008 (23381369827506207/200000000000000000) (58453424568765519/500000000000000000) := by
  change RationalBound (v004+v007) (23381369827506207/200000000000000000) (58453424568765519/500000000000000000)
  exact rationalBound_add v004_bound v007_bound (by norm_num) (by norm_num)

def v009 : ℝ := CK.Profile.meanEntropy (19/20 : ℝ)
theorem v009_bound : RationalBound v009 (23381369827506207/200000000000000000) (58453424568765519/500000000000000000) := by
  change RationalBound (CK.Profile.meanEntropy (19/20 : ℝ)) (23381369827506207/200000000000000000) (58453424568765519/500000000000000000)
  have heq : CK.Profile.meanEntropy (19/20 : ℝ) = v008 := by
    rw [CK.Profile.meanEntropy, binEntropy_eq_log_inv]
    norm_num [v002, v003, v004, v005, v006, v007, v008]
  rw [heq]
  exact v008_bound

def v010 : ℝ := (1/2 : ℝ)
theorem v010_bound : RationalBound v010 (1/2) (1/2) := by
  change RationalBound ((1/2 : ℝ)) (1/2) (1/2)
  norm_num [RationalBound]

def v011 : ℝ := Real.log (8713251683883907/293947570857085 : ℝ)
theorem v011_bound : RationalBound v011 (338919890681529141/100000000000000000) (677839781363058283/200000000000000000) := by
  change RationalBound (Real.log (8713251683883907/293947570857085 : ℝ)) (338919890681529141/100000000000000000) (677839781363058283/200000000000000000)
  exact LogData.log093_bound

def v012 : ℝ := v010*v011
theorem v012_bound : RationalBound v012 (338919890681529141/200000000000000000) (423649863351911427/250000000000000000) := by
  change RationalBound (v010*v011) (338919890681529141/200000000000000000) (423649863351911427/250000000000000000)
  exact rationalBound_mul v010_bound v011_bound (by norm_num) (by norm_num)

def v013 : ℝ := Real.artanh (4209652056513411/4503599627370496 : ℝ)
theorem v013_bound : RationalBound v013 (338919890681529141/200000000000000000) (423649863351911427/250000000000000000) := by
  change RationalBound (Real.artanh (4209652056513411/4503599627370496 : ℝ)) (338919890681529141/200000000000000000) (423649863351911427/250000000000000000)
  have heq : Real.artanh (4209652056513411/4503599627370496 : ℝ) = v012 := by
    rw [Real.artanh_eq_half_log (by norm_num : (4209652056513411/4503599627370496 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)]
    norm_num [v010, v011, v012] <;> ring
  rw [heq]
  exact v012_bound

def v014 : ℝ := (293947570857085/9007199254740992 : ℝ)
theorem v014_bound : RationalBound v014 (293947570857085/9007199254740992) (293947570857085/9007199254740992) := by
  change RationalBound ((293947570857085/9007199254740992 : ℝ)) (293947570857085/9007199254740992) (293947570857085/9007199254740992)
  norm_num [RationalBound]

def v015 : ℝ := Real.log (9007199254740992/293947570857085 : ℝ)
theorem v015_bound : RationalBound v015 (1711189016365354737/500000000000000000) (3422378032730709479/1000000000000000000) := by
  change RationalBound (Real.log (9007199254740992/293947570857085 : ℝ)) (1711189016365354737/500000000000000000) (3422378032730709479/1000000000000000000)
  exact LogData.log094_bound

def v016 : ℝ := v014*v015
theorem v016_bound : RationalBound v016 (111688404000425277/1000000000000000000) (55844202000212639/500000000000000000) := by
  change RationalBound (v014*v015) (111688404000425277/1000000000000000000) (55844202000212639/500000000000000000)
  exact rationalBound_mul v014_bound v015_bound (by norm_num) (by norm_num)

def v017 : ℝ := (8713251683883907/9007199254740992 : ℝ)
theorem v017_bound : RationalBound v017 (8713251683883907/9007199254740992) (8713251683883907/9007199254740992) := by
  change RationalBound ((8713251683883907/9007199254740992 : ℝ)) (8713251683883907/9007199254740992) (8713251683883907/9007199254740992)
  norm_num [RationalBound]

def v018 : ℝ := Real.log (9007199254740992/8713251683883907 : ℝ)
theorem v018_bound : RationalBound v018 (33179125915418063/1000000000000000000) (2073695369713629/62500000000000000) := by
  change RationalBound (Real.log (9007199254740992/8713251683883907 : ℝ)) (33179125915418063/1000000000000000000) (2073695369713629/62500000000000000)
  exact LogData.log095_bound

def v019 : ℝ := v017*v018
theorem v019_bound : RationalBound v019 (32096333896482211/1000000000000000000) (32096333896482213/1000000000000000000) := by
  change RationalBound (v017*v018) (32096333896482211/1000000000000000000) (32096333896482213/1000000000000000000)
  exact rationalBound_mul v017_bound v018_bound (by norm_num) (by norm_num)

def v020 : ℝ := v016+v019
theorem v020_bound : RationalBound v020 (4493273059278359/31250000000000000) (143784737896907491/1000000000000000000) := by
  change RationalBound (v016+v019) (4493273059278359/31250000000000000) (143784737896907491/1000000000000000000)
  exact rationalBound_add v016_bound v019_bound (by norm_num) (by norm_num)

def v021 : ℝ := CK.Profile.meanEntropy (4209652056513411/4503599627370496 : ℝ)
theorem v021_bound : RationalBound v021 (4493273059278359/31250000000000000) (143784737896907491/1000000000000000000) := by
  change RationalBound (CK.Profile.meanEntropy (4209652056513411/4503599627370496 : ℝ)) (4493273059278359/31250000000000000) (143784737896907491/1000000000000000000)
  have heq : CK.Profile.meanEntropy (4209652056513411/4503599627370496 : ℝ) = v020 := by
    rw [CK.Profile.meanEntropy, binEntropy_eq_log_inv]
    norm_num [v014, v015, v016, v017, v018, v019, v020]
  rw [heq]
  exact v020_bound

def v022 : ℝ := (2561239166744079944237628431095/20282409603651670423947251286016 : ℝ)
theorem v022_bound : RationalBound v022 (2561239166744079944237628431095/20282409603651670423947251286016) (2561239166744079944237628431095/20282409603651670423947251286016) := by
  change RationalBound ((2561239166744079944237628431095/20282409603651670423947251286016 : ℝ)) (2561239166744079944237628431095/20282409603651670423947251286016) (2561239166744079944237628431095/20282409603651670423947251286016)
  norm_num [RationalBound]

def v023 : ℝ := Real.log (2 : ℝ)
theorem v023_bound : RationalBound v023 (693147180559945309/1000000000000000000) (69314718055994531/100000000000000000) := by
  change RationalBound (Real.log (2 : ℝ)) (693147180559945309/1000000000000000000) (69314718055994531/100000000000000000)
  exact LogData.log000_bound

def v024 : ℝ := Real.log (20282409603651670423947251286016/2561239166744079944237628431095 : ℝ)
theorem v024_bound : RationalBound v024 (2069262797526236919/1000000000000000000) (1034631398763118461/500000000000000000) := by
  change RationalBound (Real.log (20282409603651670423947251286016/2561239166744079944237628431095 : ℝ)) (2069262797526236919/1000000000000000000) (1034631398763118461/500000000000000000)
  exact LogData.log096_bound

def v025 : ℝ := v010*v024
theorem v025_bound : RationalBound v025 (1034631398763118459/1000000000000000000) (1034631398763118461/1000000000000000000) := by
  change RationalBound (v010*v024) (1034631398763118459/1000000000000000000) (1034631398763118461/1000000000000000000)
  exact rationalBound_mul v010_bound v024_bound (by norm_num) (by norm_num)

def v026 : ℝ := v023+v025
theorem v026_bound : RationalBound v026 (215972322415382971/125000000000000000) (1727778579323063771/1000000000000000000) := by
  change RationalBound (v023+v025) (215972322415382971/125000000000000000) (1727778579323063771/1000000000000000000)
  exact rationalBound_add v023_bound v025_bound (by norm_num) (by norm_num)

def v027 : ℝ := v022*v026
theorem v027_bound : RationalBound v027 (218181875590706233/1000000000000000000) (109090937795353117/500000000000000000) := by
  change RationalBound (v022*v026) (218181875590706233/1000000000000000000) (109090937795353117/500000000000000000)
  exact rationalBound_mul v022_bound v026_bound (by norm_num) (by norm_num)

def v028 : ℝ := (17721170436907590479709622854921/20282409603651670423947251286016 : ℝ)
theorem v028_bound : RationalBound v028 (17721170436907590479709622854921/20282409603651670423947251286016) (17721170436907590479709622854921/20282409603651670423947251286016) := by
  change RationalBound ((17721170436907590479709622854921/20282409603651670423947251286016 : ℝ)) (17721170436907590479709622854921/20282409603651670423947251286016) (17721170436907590479709622854921/20282409603651670423947251286016)
  norm_num [RationalBound]

def v029 : ℝ := 1/v027
theorem v029_bound : RationalBound v029 (4583332127348328727/1000000000000000000) (4583332127348328749/1000000000000000000) := by
  change RationalBound (1/v027) (4583332127348328727/1000000000000000000) (4583332127348328749/1000000000000000000)
  exact rationalBound_inv v027_bound (by norm_num) (by norm_num) (by norm_num)

def v030 : ℝ := v028*v029
theorem v030_bound : RationalBound v030 (15642790081269229/3906250000000000) (1001138565201230661/250000000000000000) := by
  change RationalBound (v028*v029) (15642790081269229/3906250000000000) (1001138565201230661/250000000000000000)
  exact rationalBound_mul v028_bound v029_bound (by norm_num) (by norm_num)

def v031 : ℝ := CK.Profile.tangentFactor (4209652056513411/4503599627370496 : ℝ)
theorem v031_bound : RationalBound v031 (15642790081269229/3906250000000000) (1001138565201230661/250000000000000000) := by
  change RationalBound (CK.Profile.tangentFactor (4209652056513411/4503599627370496 : ℝ)) (15642790081269229/3906250000000000) (1001138565201230661/250000000000000000)
  have heq : CK.Profile.tangentFactor (4209652056513411/4503599627370496 : ℝ) = v030 := by
    rw [tangentFactor_positiveLogs]
    norm_num [v010, v022, v023, v024, v025, v026, v027, v028, v029, v030, div_eq_mul_inv] <;> ring
  rw [heq]
  exact v030_bound

def v032 : ℝ := (1909002661/514550000 : ℝ)
theorem v032_bound : RationalBound v032 (1909002661/514550000) (1909002661/514550000) := by
  change RationalBound ((1909002661/514550000 : ℝ)) (1909002661/514550000) (1909002661/514550000)
  norm_num [RationalBound]

def v033 : ℝ := v032*v001
theorem v033_bound : RationalBound v033 (1484017227480322611/1000000000000000000) (371004306870080653/250000000000000000) := by
  change RationalBound (v032*v001) (1484017227480322611/1000000000000000000) (371004306870080653/250000000000000000)
  exact rationalBound_mul v032_bound v001_bound (by norm_num) (by norm_num)

def v034 : ℝ := (4209652056513411/4503599627370496 : ℝ)
theorem v034_bound : RationalBound v034 (4209652056513411/4503599627370496) (4209652056513411/4503599627370496) := by
  change RationalBound ((4209652056513411/4503599627370496 : ℝ)) (4209652056513411/4503599627370496) (4209652056513411/4503599627370496)
  norm_num [RationalBound]

def v035 : ℝ := 1/v034
theorem v035_bound : RationalBound v035 (534913523363798291/500000000000000000) (1069827046727596583/1000000000000000000) := by
  change RationalBound (1/v034) (534913523363798291/500000000000000000) (1069827046727596583/1000000000000000000)
  exact rationalBound_inv v034_bound (by norm_num) (by norm_num) (by norm_num)

def v036 : ℝ := v021*v035
theorem v036_bound : RationalBound v036 (76912400754375037/500000000000000000) (76912400754375039/500000000000000000) := by
  change RationalBound (v021*v035) (76912400754375037/500000000000000000) (76912400754375039/500000000000000000)
  exact rationalBound_mul v021_bound v035_bound (by norm_num) (by norm_num)

def v037 : ℝ := v036*v031
theorem v037_bound : RationalBound v037 (307999882149668299/500000000000000000) (615999764299336619/1000000000000000000) := by
  change RationalBound (v036*v031) (307999882149668299/500000000000000000) (615999764299336619/1000000000000000000)
  exact rationalBound_mul v036_bound v031_bound (by norm_num) (by norm_num)

def v038 : ℝ := v013+v037
theorem v038_bound : RationalBound v038 (2310599217706982303/1000000000000000000) (2310599217706982327/1000000000000000000) := by
  change RationalBound (v013+v037) (2310599217706982303/1000000000000000000) (2310599217706982327/1000000000000000000)
  exact rationalBound_add v013_bound v037_bound (by norm_num) (by norm_num)

def v039 : ℝ := v033*v038
theorem v039_bound : RationalBound v039 (137158761795188729/40000000000000000) (3428969044879718263/1000000000000000000) := by
  change RationalBound (v033*v038) (137158761795188729/40000000000000000) (3428969044879718263/1000000000000000000)
  exact rationalBound_mul v033_bound v038_bound (by norm_num) (by norm_num)

def v040 : ℝ := v032*v031
theorem v040_bound : RationalBound v040 (14857068778535585057/1000000000000000000) (3714267194633896283/250000000000000000) := by
  change RationalBound (v032*v031) (14857068778535585057/1000000000000000000) (3714267194633896283/250000000000000000)
  exact rationalBound_mul v032_bound v031_bound (by norm_num) (by norm_num)

def v041 : ℝ := (1 : ℝ)
theorem v041_bound : RationalBound v041 (1) (1) := by
  change RationalBound ((1 : ℝ)) (1) (1)
  norm_num [RationalBound]

def v042 : ℝ := -v040
theorem v042_bound : RationalBound v042 (-3714267194633896283/250000000000000000) (-14857068778535585057/1000000000000000000) := by
  change RationalBound (-v040) (-3714267194633896283/250000000000000000) (-14857068778535585057/1000000000000000000)
  exact rationalBound_neg v040_bound (by norm_num) (by norm_num)

def v043 : ℝ := v041+v042
theorem v043_bound : RationalBound v043 (-3464267194633896283/250000000000000000) (-13857068778535585057/1000000000000000000) := by
  change RationalBound (v041+v042) (-3464267194633896283/250000000000000000) (-13857068778535585057/1000000000000000000)
  exact rationalBound_add v041_bound v042_bound (by norm_num) (by norm_num)

def weights : Fin 1 → ℝ := ![(1909002661/514550000 : ℝ)]
def parameters : Fin 1 → ℝ := ![v001]
def profile (e : ℝ) : ℝ := ∑ i : Fin 1, weights i*CK.Profile.profile e (parameters i)

theorem weights_nonneg : ∀ i, 0 ≤ weights i := by
  intro i
  fin_cases i <;> norm_num [weights]

theorem parameters_nonneg : ∀ i, 0 ≤ parameters i := by
  intro i
  fin_cases i
  · change 0 ≤ v001
    have h := v001_bound.1
    norm_num at h
    linarith

theorem profile_nonneg {e : ℝ} (he : 0 < e) : 0 ≤ profile e := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (weights_nonneg i) (CK.Profile.profile_nonneg he (parameters_nonneg i))

theorem profile_continuous : ContinuousOn profile (Set.Ioi (0 : ℝ)) :=
  continuousOn_profile_sum weights parameters parameters_nonneg

theorem endpoint_enclosure : CK.Profile.meanEntropy (19/20 : ℝ) / (19/20 : ℝ) < (123059841207/1000000000000 : ℝ) := by
  have h := v009_bound.2
  norm_num [v009] at h
  apply (div_lt_iff₀ (by norm_num : 0 < (19/20 : ℝ))).2
  linarith

def supports0 : Fin 1 → ℝ := ![(4209652056513411/4503599627370496 : ℝ)]
theorem panel0_bound :
    IntervalIntegrable (fun e => 1/(e+profile e)) volume (0 : ℝ) (123059841207/1000000000000 : ℝ) ∧
      (∫ e in (0 : ℝ)..(123059841207/1000000000000 : ℝ), 1/(e+profile e)) ≤ (49633490405778317/1000000000000000000 : ℝ) := by
  have hA : (137158761795188729/40000000000000000 : ℝ) ≤ ∑ i : Fin 1, weights i*parameters i*(Real.artanh (supports0 i)+
      CK.Profile.meanEntropy (supports0 i)/supports0 i*CK.Profile.tangentFactor (supports0 i)) := by
    have h := v039_bound.1
    norm_num [weights, parameters, supports0, Fin.sum_univ_succ, v000, v001, v002, v003, v004, v005, v006, v007, v008, v009, v010, v011, v012, v013, v014, v015, v016, v017, v018, v019, v020, v021, v022, v023, v024, v025, v026, v027, v028, v029, v030, v031, v032, v033, v034, v035, v036, v037, v038, v039, v040, v041, v042, v043] at h ⊢
    nlinarith only [h]
  have hB : (-3464267194633896283/250000000000000000 : ℝ) ≤ 1-∑ i : Fin 1, weights i*CK.Profile.tangentFactor (supports0 i) := by
    have h := v043_bound.1
    norm_num [weights, supports0, Fin.sum_univ_succ, v000, v001, v002, v003, v004, v005, v006, v007, v008, v009, v010, v011, v012, v013, v014, v015, v016, v017, v018, v019, v020, v021, v022, v023, v024, v025, v026, v027, v028, v029, v030, v031, v032, v033, v034, v035, v036, v037, v038, v039, v040, v041, v042, v043] at h ⊢
    nlinarith only [h]
  have hlog : Real.log (((137158761795188729/40000000000000000 : ℝ)+(-3464267194633896283/250000000000000000 : ℝ)*(0 : ℝ))/
      ((137158761795188729/40000000000000000 : ℝ)+(-3464267194633896283/250000000000000000 : ℝ)*(123059841207/1000000000000 : ℝ))) ≤ (-(-3464267194633896283/250000000000000000 : ℝ))*(49633490405778317/1000000000000000000 : ℝ) := by
    have h := LogData.log097_bound.2
    norm_num at h ⊢
    linarith
  simpa only [profile] using profile_panel_integral_bound weights parameters supports0
    weights_nonneg parameters_nonneg (by intro i; fin_cases i <;> norm_num [supports0])
    (a := (0 : ℝ)) (b := (123059841207/1000000000000 : ℝ)) (A := (137158761795188729/40000000000000000 : ℝ)) (B := (-3464267194633896283/250000000000000000 : ℝ)) (U := (49633490405778317/1000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA hB hlog

theorem clock_certified :
    CK.Profile.meanEntropy (19/20 : ℝ) / (19/20 : ℝ) < (123059841207/1000000000000 : ℝ) ∧
    IntervalIntegrable (fun e => 1/(e+profile e)) volume 0 (123059841207/1000000000000 : ℝ) ∧
    (∫ e in (0 : ℝ)..(123059841207/1000000000000 : ℝ), 1/(e+profile e)) + (207475497721527/250000000000000000 : ℝ) < Real.log (1/(19/20 : ℝ)) := by
  have h0 := panel0_bound
  refine ⟨endpoint_enclosure, h0.1, ?_⟩
  have hlog := LogData.log092_bound.1
  have hbound := h0.2
  norm_num at hbound hlog ⊢
  linarith only [hbound, hlog]

theorem clock_improper_limit :
    Filter.Tendsto (fun ε => ∫ e in ε..(123059841207/1000000000000 : ℝ), 1/(e+profile e))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ e in (0 : ℝ)..(123059841207/1000000000000 : ℝ), 1/(e+profile e))) := by
  exact tendsto_integral_from_right (by norm_num) clock_certified.2.1

end
end CK.Certificate.ClockBatch.C07
