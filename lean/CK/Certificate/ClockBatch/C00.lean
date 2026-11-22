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
namespace CK.Certificate.ClockBatch.C00
noncomputable section

def v000 : ℝ := (4/25 : ℝ)
theorem v000_bound : RationalBound v000 (4/25) (4/25) := by
  change RationalBound ((4/25 : ℝ)) (4/25) (4/25)
  norm_num [RationalBound]

def v001 : ℝ := Real.sqrt v000
theorem v001_bound : RationalBound v001 (2/5) (2/5) := by
  change RationalBound (Real.sqrt v000) (2/5) (2/5)
  exact rationalBound_sqrt v000_bound (by norm_num) (by norm_num) (by norm_num)

def v002 : ℝ := (43/1000 : ℝ)
theorem v002_bound : RationalBound v002 (43/1000) (43/1000) := by
  change RationalBound ((43/1000 : ℝ)) (43/1000) (43/1000)
  norm_num [RationalBound]

def v003 : ℝ := Real.log (1000/43 : ℝ)
theorem v003_bound : RationalBound v003 (1573277581644287313/500000000000000000) (3146555163288574631/1000000000000000000) := by
  change RationalBound (Real.log (1000/43 : ℝ)) (1573277581644287313/500000000000000000) (3146555163288574631/1000000000000000000)
  exact LogData.log001_bound

def v004 : ℝ := v002*v003
theorem v004_bound : RationalBound v004 (33825468005352177/250000000000000000) (13530187202140871/100000000000000000) := by
  change RationalBound (v002*v003) (33825468005352177/250000000000000000) (13530187202140871/100000000000000000)
  exact rationalBound_mul v002_bound v003_bound (by norm_num) (by norm_num)

def v005 : ℝ := (957/1000 : ℝ)
theorem v005_bound : RationalBound v005 (957/1000) (957/1000) := by
  change RationalBound ((957/1000 : ℝ)) (957/1000) (957/1000)
  norm_num [RationalBound]

def v006 : ℝ := Real.log (1000/957 : ℝ)
theorem v006_bound : RationalBound v006 (43951887529182789/1000000000000000000) (4395188752918279/100000000000000000) := by
  change RationalBound (Real.log (1000/957 : ℝ)) (43951887529182789/1000000000000000000) (4395188752918279/100000000000000000)
  exact LogData.log002_bound

def v007 : ℝ := v005*v006
theorem v007_bound : RationalBound v007 (42061956365427929/1000000000000000000) (42061956365427931/1000000000000000000) := by
  change RationalBound (v005*v006) (42061956365427929/1000000000000000000) (42061956365427931/1000000000000000000)
  exact rationalBound_mul v005_bound v006_bound (by norm_num) (by norm_num)

def v008 : ℝ := v004+v007
theorem v008_bound : RationalBound v008 (177363828386836637/1000000000000000000) (177363828386836641/1000000000000000000) := by
  change RationalBound (v004+v007) (177363828386836637/1000000000000000000) (177363828386836641/1000000000000000000)
  exact rationalBound_add v004_bound v007_bound (by norm_num) (by norm_num)

def v009 : ℝ := CK.Profile.meanEntropy (457/500 : ℝ)
theorem v009_bound : RationalBound v009 (177363828386836637/1000000000000000000) (177363828386836641/1000000000000000000) := by
  change RationalBound (CK.Profile.meanEntropy (457/500 : ℝ)) (177363828386836637/1000000000000000000) (177363828386836641/1000000000000000000)
  have heq : CK.Profile.meanEntropy (457/500 : ℝ) = v008 := by
    rw [CK.Profile.meanEntropy, binEntropy_eq_log_inv]
    norm_num [v002, v003, v004, v005, v006, v007, v008]
  rw [heq]
  exact v008_bound

def v010 : ℝ := (1/2 : ℝ)
theorem v010_bound : RationalBound v010 (1/2) (1/2) := by
  change RationalBound ((1/2 : ℝ)) (1/2) (1/2)
  norm_num [RationalBound]

def v011 : ℝ := Real.log (1062991783453097/62908123389527 : ℝ)
theorem v011_bound : RationalBound v011 (2827167345674126917/1000000000000000000) (1413583672837063461/500000000000000000) := by
  change RationalBound (Real.log (1062991783453097/62908123389527 : ℝ)) (2827167345674126917/1000000000000000000) (1413583672837063461/500000000000000000)
  exact LogData.log004_bound

def v012 : ℝ := v010*v011
theorem v012_bound : RationalBound v012 (706791836418531729/500000000000000000) (1413583672837063461/1000000000000000000) := by
  change RationalBound (v010*v011) (706791836418531729/500000000000000000) (1413583672837063461/1000000000000000000)
  exact rationalBound_mul v010_bound v011_bound (by norm_num) (by norm_num)

def v013 : ℝ := Real.artanh (500041830031785/562949953421312 : ℝ)
theorem v013_bound : RationalBound v013 (706791836418531729/500000000000000000) (1413583672837063461/1000000000000000000) := by
  change RationalBound (Real.artanh (500041830031785/562949953421312 : ℝ)) (706791836418531729/500000000000000000) (1413583672837063461/1000000000000000000)
  have heq : Real.artanh (500041830031785/562949953421312 : ℝ) = v012 := by
    rw [Real.artanh_eq_half_log (by norm_num : (500041830031785/562949953421312 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)]
    norm_num [v010, v011, v012] <;> ring
  rw [heq]
  exact v012_bound

def v014 : ℝ := (62908123389527/1125899906842624 : ℝ)
theorem v014_bound : RationalBound v014 (62908123389527/1125899906842624) (62908123389527/1125899906842624) := by
  change RationalBound ((62908123389527/1125899906842624 : ℝ)) (62908123389527/1125899906842624) (62908123389527/1125899906842624)
  norm_num [RationalBound]

def v015 : ℝ := Real.log (1125899906842624/62908123389527 : ℝ)
theorem v015_bound : RationalBound v015 (2884662609013933321/1000000000000000000) (1442331304506966663/500000000000000000) := by
  change RationalBound (Real.log (1125899906842624/62908123389527 : ℝ)) (2884662609013933321/1000000000000000000) (1442331304506966663/500000000000000000)
  exact LogData.log005_bound

def v016 : ℝ := v014*v015
theorem v016_bound : RationalBound v016 (32235318653484661/200000000000000000) (80588296633711653/500000000000000000) := by
  change RationalBound (v014*v015) (32235318653484661/200000000000000000) (80588296633711653/500000000000000000)
  exact rationalBound_mul v014_bound v015_bound (by norm_num) (by norm_num)

def v017 : ℝ := (1062991783453097/1125899906842624 : ℝ)
theorem v017_bound : RationalBound v017 (1062991783453097/1125899906842624) (1062991783453097/1125899906842624) := by
  change RationalBound ((1062991783453097/1125899906842624 : ℝ)) (1062991783453097/1125899906842624) (1062991783453097/1125899906842624)
  norm_num [RationalBound]

def v018 : ℝ := Real.log (1125899906842624/1062991783453097 : ℝ)
theorem v018_bound : RationalBound v018 (57495263339806403/1000000000000000000) (14373815834951601/250000000000000000) := by
  change RationalBound (Real.log (1125899906842624/1062991783453097 : ℝ)) (57495263339806403/1000000000000000000) (14373815834951601/250000000000000000)
  exact LogData.log006_bound

def v019 : ℝ := v017*v018
theorem v019_bound : RationalBound v019 (54282793831182973/1000000000000000000) (2171311753247319/40000000000000000) := by
  change RationalBound (v017*v018) (54282793831182973/1000000000000000000) (2171311753247319/40000000000000000)
  exact rationalBound_mul v017_bound v018_bound (by norm_num) (by norm_num)

def v020 : ℝ := v016+v019
theorem v020_bound : RationalBound v020 (107729693549303139/500000000000000000) (215459387098606281/1000000000000000000) := by
  change RationalBound (v016+v019) (107729693549303139/500000000000000000) (215459387098606281/1000000000000000000)
  exact rationalBound_add v016_bound v019_bound (by norm_num) (by norm_num)

def v021 : ℝ := CK.Profile.meanEntropy (500041830031785/562949953421312 : ℝ)
theorem v021_bound : RationalBound v021 (107729693549303139/500000000000000000) (215459387098606281/1000000000000000000) := by
  change RationalBound (CK.Profile.meanEntropy (500041830031785/562949953421312 : ℝ)) (107729693549303139/500000000000000000) (215459387098606281/1000000000000000000)
  have heq : CK.Profile.meanEntropy (500041830031785/562949953421312 : ℝ) = v020 := by
    rw [CK.Profile.meanEntropy, binEntropy_eq_log_inv]
    norm_num [v014, v015, v016, v017, v018, v019, v020]
  rw [heq]
  exact v020_bound

def v022 : ℝ := (66870818275520791240065515119/316912650057057350374175801344 : ℝ)
theorem v022_bound : RationalBound v022 (66870818275520791240065515119/316912650057057350374175801344) (66870818275520791240065515119/316912650057057350374175801344) := by
  change RationalBound ((66870818275520791240065515119/316912650057057350374175801344 : ℝ)) (66870818275520791240065515119/316912650057057350374175801344) (66870818275520791240065515119/316912650057057350374175801344)
  norm_num [RationalBound]

def v023 : ℝ := Real.log (2 : ℝ)
theorem v023_bound : RationalBound v023 (693147180559945309/1000000000000000000) (69314718055994531/100000000000000000) := by
  change RationalBound (Real.log (2 : ℝ)) (693147180559945309/1000000000000000000) (69314718055994531/100000000000000000)
  exact LogData.log000_bound

def v024 : ℝ := Real.log (316912650057057350374175801344/66870818275520791240065515119 : ℝ)
theorem v024_bound : RationalBound v024 (777931755616924553/500000000000000000) (1555863511233849109/1000000000000000000) := by
  change RationalBound (Real.log (316912650057057350374175801344/66870818275520791240065515119 : ℝ)) (777931755616924553/500000000000000000) (1555863511233849109/1000000000000000000)
  exact LogData.log007_bound

def v025 : ℝ := v010*v024
theorem v025_bound : RationalBound v025 (777931755616924553/1000000000000000000) (155586351123384911/200000000000000000) := by
  change RationalBound (v010*v024) (777931755616924553/1000000000000000000) (155586351123384911/200000000000000000)
  exact rationalBound_mul v010_bound v024_bound (by norm_num) (by norm_num)

def v026 : ℝ := v023+v025
theorem v026_bound : RationalBound v026 (735539468088434931/500000000000000000) (294215787235373973/200000000000000000) := by
  change RationalBound (v023+v025) (735539468088434931/500000000000000000) (294215787235373973/200000000000000000)
  exact rationalBound_add v023_bound v025_bound (by norm_num) (by norm_num)

def v027 : ℝ := v022*v026
theorem v027_bound : RationalBound v027 (19400505981758469/62500000000000000) (155204047854067753/500000000000000000) := by
  change RationalBound (v022*v026) (19400505981758469/62500000000000000) (155204047854067753/500000000000000000)
  exact rationalBound_mul v022_bound v026_bound (by norm_num) (by norm_num)

def v028 : ℝ := (250041831781536559134110286225/316912650057057350374175801344 : ℝ)
theorem v028_bound : RationalBound v028 (250041831781536559134110286225/316912650057057350374175801344) (250041831781536559134110286225/316912650057057350374175801344) := by
  change RationalBound ((250041831781536559134110286225/316912650057057350374175801344 : ℝ)) (250041831781536559134110286225/316912650057057350374175801344) (250041831781536559134110286225/316912650057057350374175801344)
  norm_num [RationalBound]

def v029 : ℝ := 1/v027
theorem v029_bound : RationalBound v029 (322156546116716161/100000000000000000) (100673920661473801/31250000000000000) := by
  change RationalBound (1/v027) (322156546116716161/100000000000000000) (100673920661473801/31250000000000000)
  exact rationalBound_inv v027_bound (by norm_num) (by norm_num) (by norm_num)

def v030 : ℝ := v028*v029
theorem v030_bound : RationalBound v030 (317724035696168857/125000000000000000) (1270896142784675437/500000000000000000) := by
  change RationalBound (v028*v029) (317724035696168857/125000000000000000) (1270896142784675437/500000000000000000)
  exact rationalBound_mul v028_bound v029_bound (by norm_num) (by norm_num)

def v031 : ℝ := CK.Profile.tangentFactor (500041830031785/562949953421312 : ℝ)
theorem v031_bound : RationalBound v031 (317724035696168857/125000000000000000) (1270896142784675437/500000000000000000) := by
  change RationalBound (CK.Profile.tangentFactor (500041830031785/562949953421312 : ℝ)) (317724035696168857/125000000000000000) (1270896142784675437/500000000000000000)
  have heq : CK.Profile.tangentFactor (500041830031785/562949953421312 : ℝ) = v030 := by
    rw [tangentFactor_positiveLogs]
    norm_num [v010, v022, v023, v024, v025, v026, v027, v028, v029, v030, div_eq_mul_inv] <;> ring
  rw [heq]
  exact v030_bound

def v032 : ℝ := (353357479/83800000 : ℝ)
theorem v032_bound : RationalBound v032 (353357479/83800000) (353357479/83800000) := by
  change RationalBound ((353357479/83800000 : ℝ)) (353357479/83800000) (353357479/83800000)
  norm_num [RationalBound]

def v033 : ℝ := v032*v001
theorem v033_bound : RationalBound v033 (168667054415274463/100000000000000000) (1686670544152744631/1000000000000000000) := by
  change RationalBound (v032*v001) (168667054415274463/100000000000000000) (1686670544152744631/1000000000000000000)
  exact rationalBound_mul v032_bound v001_bound (by norm_num) (by norm_num)

def v034 : ℝ := (500041830031785/562949953421312 : ℝ)
theorem v034_bound : RationalBound v034 (500041830031785/562949953421312) (500041830031785/562949953421312) := by
  change RationalBound ((500041830031785/562949953421312 : ℝ)) (500041830031785/562949953421312) (500041830031785/562949953421312)
  norm_num [RationalBound]

def v035 : ℝ := 1/v034
theorem v035_bound : RationalBound v035 (1125805721864365357/1000000000000000000) (562902860932182679/500000000000000000) := by
  change RationalBound (1/v034) (1125805721864365357/1000000000000000000) (562902860932182679/500000000000000000)
  exact rationalBound_inv v034_bound (by norm_num) (by norm_num) (by norm_num)

def v036 : ℝ := v021*v035
theorem v036_bound : RationalBound v036 (30320676353125021/125000000000000000) (242565410825000173/1000000000000000000) := by
  change RationalBound (v021*v035) (30320676353125021/125000000000000000) (242565410825000173/1000000000000000000)
  exact rationalBound_mul v021_bound v035_bound (by norm_num) (by norm_num)

def v037 : ℝ := v036*v031
theorem v037_bound : RationalBound v037 (77068861247618217/125000000000000000) (308275444990472877/500000000000000000) := by
  change RationalBound (v036*v031) (77068861247618217/125000000000000000) (308275444990472877/500000000000000000)
  exact rationalBound_mul v036_bound v031_bound (by norm_num) (by norm_num)

def v038 : ℝ := v013+v037
theorem v038_bound : RationalBound v038 (1015067281409004597/500000000000000000) (406026912563601843/200000000000000000) := by
  change RationalBound (v013+v037) (1015067281409004597/500000000000000000) (406026912563601843/200000000000000000)
  exact rationalBound_add v013_bound v037_bound (by norm_num) (by norm_num)

def v039 : ℝ := v033*v038
theorem v039_bound : RationalBound v039 (856042041942886473/250000000000000000) (3424168167771545931/1000000000000000000) := by
  change RationalBound (v033*v038) (856042041942886473/250000000000000000) (3424168167771545931/1000000000000000000)
  exact rationalBound_mul v033_bound v038_bound (by norm_num) (by norm_num)

def v040 : ℝ := v032*v031
theorem v040_bound : RationalBound v040 (107179154435612637/10000000000000000) (10717915443561263777/1000000000000000000) := by
  change RationalBound (v032*v031) (107179154435612637/10000000000000000) (10717915443561263777/1000000000000000000)
  exact rationalBound_mul v032_bound v031_bound (by norm_num) (by norm_num)

def v041 : ℝ := (1 : ℝ)
theorem v041_bound : RationalBound v041 (1) (1) := by
  change RationalBound ((1 : ℝ)) (1) (1)
  norm_num [RationalBound]

def v042 : ℝ := -v040
theorem v042_bound : RationalBound v042 (-10717915443561263777/1000000000000000000) (-107179154435612637/10000000000000000) := by
  change RationalBound (-v040) (-10717915443561263777/1000000000000000000) (-107179154435612637/10000000000000000)
  exact rationalBound_neg v040_bound (by norm_num) (by norm_num)

def v043 : ℝ := v041+v042
theorem v043_bound : RationalBound v043 (-9717915443561263777/1000000000000000000) (-97179154435612637/10000000000000000) := by
  change RationalBound (v041+v042) (-9717915443561263777/1000000000000000000) (-97179154435612637/10000000000000000)
  exact rationalBound_add v041_bound v042_bound (by norm_num) (by norm_num)

def weights : Fin 1 → ℝ := ![(353357479/83800000 : ℝ)]
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

theorem endpoint_enclosure : CK.Profile.meanEntropy (457/500 : ℝ) / (457/500 : ℝ) < (9702616433/50000000000 : ℝ) := by
  have h := v009_bound.2
  norm_num [v009] at h
  apply (div_lt_iff₀ (by norm_num : 0 < (457/500 : ℝ))).2
  linarith

def supports0 : Fin 1 → ℝ := ![(500041830031785/562949953421312 : ℝ)]
theorem panel0_bound :
    IntervalIntegrable (fun e => 1/(e+profile e)) volume (0 : ℝ) (9702616433/50000000000 : ℝ) ∧
      (∫ e in (0 : ℝ)..(9702616433/50000000000 : ℝ), 1/(e+profile e)) ≤ (82335150091380129/1000000000000000000 : ℝ) := by
  have hA : (856042041942886473/250000000000000000 : ℝ) ≤ ∑ i : Fin 1, weights i*parameters i*(Real.artanh (supports0 i)+
      CK.Profile.meanEntropy (supports0 i)/supports0 i*CK.Profile.tangentFactor (supports0 i)) := by
    have h := v039_bound.1
    norm_num [weights, parameters, supports0, Fin.sum_univ_succ, v000, v001, v002, v003, v004, v005, v006, v007, v008, v009, v010, v011, v012, v013, v014, v015, v016, v017, v018, v019, v020, v021, v022, v023, v024, v025, v026, v027, v028, v029, v030, v031, v032, v033, v034, v035, v036, v037, v038, v039, v040, v041, v042, v043] at h ⊢
    nlinarith only [h]
  have hB : (-9717915443561263777/1000000000000000000 : ℝ) ≤ 1-∑ i : Fin 1, weights i*CK.Profile.tangentFactor (supports0 i) := by
    have h := v043_bound.1
    norm_num [weights, supports0, Fin.sum_univ_succ, v000, v001, v002, v003, v004, v005, v006, v007, v008, v009, v010, v011, v012, v013, v014, v015, v016, v017, v018, v019, v020, v021, v022, v023, v024, v025, v026, v027, v028, v029, v030, v031, v032, v033, v034, v035, v036, v037, v038, v039, v040, v041, v042, v043] at h ⊢
    nlinarith only [h]
  have hlog : Real.log (((856042041942886473/250000000000000000 : ℝ)+(-9717915443561263777/1000000000000000000 : ℝ)*(0 : ℝ))/
      ((856042041942886473/250000000000000000 : ℝ)+(-9717915443561263777/1000000000000000000 : ℝ)*(9702616433/50000000000 : ℝ))) ≤ (-(-9717915443561263777/1000000000000000000 : ℝ))*(82335150091380129/1000000000000000000 : ℝ) := by
    have h := LogData.log008_bound.2
    norm_num at h ⊢
    linarith
  simpa only [profile] using profile_panel_integral_bound weights parameters supports0
    weights_nonneg parameters_nonneg (by intro i; fin_cases i <;> norm_num [supports0])
    (a := (0 : ℝ)) (b := (9702616433/50000000000 : ℝ)) (A := (856042041942886473/250000000000000000 : ℝ)) (B := (-9717915443561263777/1000000000000000000 : ℝ)) (U := (82335150091380129/1000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA hB hlog

theorem clock_certified :
    CK.Profile.meanEntropy (457/500 : ℝ) / (457/500 : ℝ) < (9702616433/50000000000 : ℝ) ∧
    IntervalIntegrable (fun e => 1/(e+profile e)) volume 0 (9702616433/50000000000 : ℝ) ∧
    (∫ e in (0 : ℝ)..(9702616433/50000000000 : ℝ), 1/(e+profile e)) + (3794778718303457/1000000000000000000 : ℝ) < Real.log (1/(457/500 : ℝ)) := by
  have h0 := panel0_bound
  refine ⟨endpoint_enclosure, h0.1, ?_⟩
  have hlog := LogData.log003_bound.1
  have hbound := h0.2
  norm_num at hbound hlog ⊢
  linarith only [hbound, hlog]

theorem clock_improper_limit :
    Filter.Tendsto (fun ε => ∫ e in ε..(9702616433/50000000000 : ℝ), 1/(e+profile e))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ e in (0 : ℝ)..(9702616433/50000000000 : ℝ), 1/(e+profile e))) := by
  exact tendsto_integral_from_right (by norm_num) clock_certified.2.1

end
end CK.Certificate.ClockBatch.C00
