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
namespace CK.Certificate.ClockBatch.C12
noncomputable section

def v000 : ℝ := (4/25 : ℝ)
theorem v000_bound : RationalBound v000 (4/25) (4/25) := by
  change RationalBound ((4/25 : ℝ)) (4/25) (4/25)
  norm_num [RationalBound]

def v001 : ℝ := Real.sqrt v000
theorem v001_bound : RationalBound v001 (2/5) (2/5) := by
  change RationalBound (Real.sqrt v000) (2/5) (2/5)
  exact rationalBound_sqrt v000_bound (by norm_num) (by norm_num) (by norm_num)

def v002 : ℝ := (3/200 : ℝ)
theorem v002_bound : RationalBound v002 (3/200) (3/200) := by
  change RationalBound ((3/200 : ℝ)) (3/200) (3/200)
  norm_num [RationalBound]

def v003 : ℝ := Real.log (200/3 : ℝ)
theorem v003_bound : RationalBound v003 (4199705077879926983/1000000000000000000) (419970507787992699/100000000000000000) := by
  change RationalBound (Real.log (200/3 : ℝ)) (4199705077879926983/1000000000000000000) (419970507787992699/100000000000000000)
  exact LogData.log170_bound

def v004 : ℝ := v002*v003
theorem v004_bound : RationalBound v004 (7874447021024863/125000000000000000) (12599115233639781/200000000000000000) := by
  change RationalBound (v002*v003) (7874447021024863/125000000000000000) (12599115233639781/200000000000000000)
  exact rationalBound_mul v002_bound v003_bound (by norm_num) (by norm_num)

def v005 : ℝ := (197/200 : ℝ)
theorem v005_bound : RationalBound v005 (197/200) (197/200) := by
  change RationalBound ((197/200 : ℝ)) (197/200) (197/200)
  norm_num [RationalBound]

def v006 : ℝ := Real.log (200/197 : ℝ)
theorem v006_bound : RationalBound v006 (1511363781004817/100000000000000000) (15113637810048171/1000000000000000000) := by
  change RationalBound (Real.log (200/197 : ℝ)) (1511363781004817/100000000000000000) (15113637810048171/1000000000000000000)
  exact LogData.log171_bound

def v007 : ℝ := v005*v006
theorem v007_bound : RationalBound v007 (14886933242897447/1000000000000000000) (14886933242897449/1000000000000000000) := by
  change RationalBound (v005*v006) (14886933242897447/1000000000000000000) (14886933242897449/1000000000000000000)
  exact rationalBound_mul v005_bound v006_bound (by norm_num) (by norm_num)

def v008 : ℝ := v004+v007
theorem v008_bound : RationalBound v008 (77882509411096351/1000000000000000000) (38941254705548177/500000000000000000) := by
  change RationalBound (v004+v007) (77882509411096351/1000000000000000000) (38941254705548177/500000000000000000)
  exact rationalBound_add v004_bound v007_bound (by norm_num) (by norm_num)

def v009 : ℝ := CK.Profile.meanEntropy (97/100 : ℝ)
theorem v009_bound : RationalBound v009 (77882509411096351/1000000000000000000) (38941254705548177/500000000000000000) := by
  change RationalBound (CK.Profile.meanEntropy (97/100 : ℝ)) (77882509411096351/1000000000000000000) (38941254705548177/500000000000000000)
  have heq : CK.Profile.meanEntropy (97/100 : ℝ) = v008 := by
    rw [CK.Profile.meanEntropy, binEntropy_eq_log_inv]
    norm_num [v002, v003, v004, v005, v006, v007, v008]
  rw [heq]
  exact v008_bound

def v010 : ℝ := (1/2 : ℝ)
theorem v010_bound : RationalBound v010 (1/2) (1/2) := by
  change RationalBound ((1/2 : ℝ)) (1/2) (1/2)
  norm_num [RationalBound]

def v011 : ℝ := Real.log (8830764325399389/176434929341603 : ℝ)
theorem v011_bound : RationalBound v011 (3913044713808299021/1000000000000000000) (3913044713808299027/1000000000000000000) := by
  change RationalBound (Real.log (8830764325399389/176434929341603 : ℝ)) (3913044713808299021/1000000000000000000) (3913044713808299027/1000000000000000000)
  exact LogData.log173_bound

def v012 : ℝ := v010*v011
theorem v012_bound : RationalBound v012 (195652235690414951/100000000000000000) (978261178452074757/500000000000000000) := by
  change RationalBound (v010*v011) (195652235690414951/100000000000000000) (978261178452074757/500000000000000000)
  exact rationalBound_mul v010_bound v011_bound (by norm_num) (by norm_num)

def v013 : ℝ := Real.artanh (4327164698028893/4503599627370496 : ℝ)
theorem v013_bound : RationalBound v013 (195652235690414951/100000000000000000) (978261178452074757/500000000000000000) := by
  change RationalBound (Real.artanh (4327164698028893/4503599627370496 : ℝ)) (195652235690414951/100000000000000000) (978261178452074757/500000000000000000)
  have heq : Real.artanh (4327164698028893/4503599627370496 : ℝ) = v012 := by
    rw [Real.artanh_eq_half_log (by norm_num : (4327164698028893/4503599627370496 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)]
    norm_num [v010, v011, v012] <;> ring
  rw [heq]
  exact v012_bound

def v014 : ℝ := (176434929341603/9007199254740992 : ℝ)
theorem v014_bound : RationalBound v014 (176434929341603/9007199254740992) (176434929341603/9007199254740992) := by
  change RationalBound ((176434929341603/9007199254740992 : ℝ)) (176434929341603/9007199254740992) (176434929341603/9007199254740992)
  norm_num [RationalBound]

def v015 : ℝ := Real.log (9007199254740992/176434929341603 : ℝ)
theorem v015_bound : RationalBound v015 (3932827317637072043/1000000000000000000) (3932827317637072049/1000000000000000000) := by
  change RationalBound (Real.log (9007199254740992/176434929341603 : ℝ)) (3932827317637072043/1000000000000000000) (3932827317637072049/1000000000000000000)
  exact LogData.log174_bound

def v016 : ℝ := v014*v015
theorem v016_bound : RationalBound v016 (77037055612463641/1000000000000000000) (38518527806231821/500000000000000000) := by
  change RationalBound (v014*v015) (77037055612463641/1000000000000000000) (38518527806231821/500000000000000000)
  exact rationalBound_mul v014_bound v015_bound (by norm_num) (by norm_num)

def v017 : ℝ := (8830764325399389/9007199254740992 : ℝ)
theorem v017_bound : RationalBound v017 (8830764325399389/9007199254740992) (8830764325399389/9007199254740992) := by
  change RationalBound ((8830764325399389/9007199254740992 : ℝ)) (8830764325399389/9007199254740992) (8830764325399389/9007199254740992)
  norm_num [RationalBound]

def v018 : ℝ := Real.log (9007199254740992/8830764325399389 : ℝ)
theorem v018_bound : RationalBound v018 (19782603828773021/1000000000000000000) (9891301914386511/500000000000000000) := by
  change RationalBound (Real.log (9007199254740992/8830764325399389 : ℝ)) (19782603828773021/1000000000000000000) (9891301914386511/500000000000000000)
  exact LogData.log175_bound

def v019 : ℝ := v017*v018
theorem v019_bound : RationalBound v019 (19395097989276317/1000000000000000000) (19395097989276319/1000000000000000000) := by
  change RationalBound (v017*v018) (19395097989276317/1000000000000000000) (19395097989276319/1000000000000000000)
  exact rationalBound_mul v017_bound v018_bound (by norm_num) (by norm_num)

def v020 : ℝ := v016+v019
theorem v020_bound : RationalBound v020 (48216076800869979/500000000000000000) (96432153601739961/1000000000000000000) := by
  change RationalBound (v016+v019) (48216076800869979/500000000000000000) (96432153601739961/1000000000000000000)
  exact rationalBound_add v016_bound v019_bound (by norm_num) (by norm_num)

def v021 : ℝ := CK.Profile.meanEntropy (4327164698028893/4503599627370496 : ℝ)
theorem v021_bound : RationalBound v021 (48216076800869979/500000000000000000) (96432153601739961/1000000000000000000) := by
  change RationalBound (CK.Profile.meanEntropy (4327164698028893/4503599627370496 : ℝ)) (48216076800869979/500000000000000000) (96432153601739961/1000000000000000000)
  have heq : CK.Profile.meanEntropy (4327164698028893/4503599627370496 : ℝ) = v020 := by
    rw [CK.Profile.meanEntropy, binEntropy_eq_log_inv]
    norm_num [v014, v015, v016, v017, v018, v019, v020]
  rw [heq]
  exact v020_bound

def v022 : ℝ := (1558055279784189680707788480567/20282409603651670423947251286016 : ℝ)
theorem v022_bound : RationalBound v022 (1558055279784189680707788480567/20282409603651670423947251286016) (1558055279784189680707788480567/20282409603651670423947251286016) := by
  change RationalBound ((1558055279784189680707788480567/20282409603651670423947251286016 : ℝ)) (1558055279784189680707788480567/20282409603651670423947251286016) (1558055279784189680707788480567/20282409603651670423947251286016)
  norm_num [RationalBound]

def v023 : ℝ := Real.log (2 : ℝ)
theorem v023_bound : RationalBound v023 (693147180559945309/1000000000000000000) (69314718055994531/100000000000000000) := by
  change RationalBound (Real.log (2 : ℝ)) (693147180559945309/1000000000000000000) (69314718055994531/100000000000000000)
  exact LogData.log000_bound

def v024 : ℝ := Real.log (20282409603651670423947251286016/1558055279784189680707788480567 : ℝ)
theorem v024_bound : RationalBound v024 (1283157780172977223/500000000000000000) (51326311206919089/20000000000000000) := by
  change RationalBound (Real.log (20282409603651670423947251286016/1558055279784189680707788480567 : ℝ)) (1283157780172977223/500000000000000000) (51326311206919089/20000000000000000)
  exact LogData.log176_bound

def v025 : ℝ := v010*v024
theorem v025_bound : RationalBound v025 (1283157780172977223/1000000000000000000) (51326311206919089/40000000000000000) := by
  change RationalBound (v010*v024) (1283157780172977223/1000000000000000000) (51326311206919089/40000000000000000)
  exact rationalBound_mul v010_bound v024_bound (by norm_num) (by norm_num)

def v026 : ℝ := v023+v025
theorem v026_bound : RationalBound v026 (494076240183230633/250000000000000000) (395260992146584507/200000000000000000) := by
  change RationalBound (v023+v025) (494076240183230633/250000000000000000) (395260992146584507/200000000000000000)
  exact rationalBound_add v023_bound v025_bound (by norm_num) (by norm_num)

def v027 : ℝ := v022*v026
theorem v027_bound : RationalBound v027 (75907952721239639/500000000000000000) (151815905442479279/1000000000000000000) := by
  change RationalBound (v022*v026) (75907952721239639/500000000000000000) (151815905442479279/1000000000000000000)
  exact rationalBound_mul v022_bound v026_bound (by norm_num) (by norm_num)

def v028 : ℝ := (18724354323867480743239462805449/20282409603651670423947251286016 : ℝ)
theorem v028_bound : RationalBound v028 (18724354323867480743239462805449/20282409603651670423947251286016) (18724354323867480743239462805449/20282409603651670423947251286016) := by
  change RationalBound ((18724354323867480743239462805449/20282409603651670423947251286016 : ℝ)) (18724354323867480743239462805449/20282409603651670423947251286016) (18724354323867480743239462805449/20282409603651670423947251286016)
  norm_num [RationalBound]

def v029 : ℝ := 1/v027
theorem v029_bound : RationalBound v029 (3293462556131461079/500000000000000000) (6586925112262922203/1000000000000000000) := by
  change RationalBound (1/v027) (3293462556131461079/500000000000000000) (6586925112262922203/1000000000000000000)
  exact rationalBound_inv v027_bound (by norm_num) (by norm_num) (by norm_num)

def v030 : ℝ := v028*v029
theorem v030_bound : RationalBound v030 (243237213165414003/40000000000000000) (3040465164567675059/500000000000000000) := by
  change RationalBound (v028*v029) (243237213165414003/40000000000000000) (3040465164567675059/500000000000000000)
  exact rationalBound_mul v028_bound v029_bound (by norm_num) (by norm_num)

def v031 : ℝ := CK.Profile.tangentFactor (4327164698028893/4503599627370496 : ℝ)
theorem v031_bound : RationalBound v031 (243237213165414003/40000000000000000) (3040465164567675059/500000000000000000) := by
  change RationalBound (CK.Profile.tangentFactor (4327164698028893/4503599627370496 : ℝ)) (243237213165414003/40000000000000000) (3040465164567675059/500000000000000000)
  have heq : CK.Profile.tangentFactor (4327164698028893/4503599627370496 : ℝ) = v030 := by
    rw [tangentFactor_positiveLogs]
    norm_num [v010, v022, v023, v024, v025, v026, v027, v028, v029, v030, div_eq_mul_inv] <;> ring
  rw [heq]
  exact v030_bound

def v032 : ℝ := (29150089291/8202592000 : ℝ)
theorem v032_bound : RationalBound v032 (29150089291/8202592000) (29150089291/8202592000) := by
  change RationalBound ((29150089291/8202592000 : ℝ)) (29150089291/8202592000) (29150089291/8202592000)
  norm_num [RationalBound]

def v033 : ℝ := v032*v001
theorem v033_bound : RationalBound v033 (710753120257596623/500000000000000000) (1421506240515193247/1000000000000000000) := by
  change RationalBound (v032*v001) (710753120257596623/500000000000000000) (1421506240515193247/1000000000000000000)
  exact rationalBound_mul v032_bound v001_bound (by norm_num) (by norm_num)

def v034 : ℝ := (4327164698028893/4503599627370496 : ℝ)
theorem v034_bound : RationalBound v034 (4327164698028893/4503599627370496) (4327164698028893/4503599627370496) := by
  change RationalBound ((4327164698028893/4503599627370496 : ℝ)) (4327164698028893/4503599627370496) (4327164698028893/4503599627370496)
  norm_num [RationalBound]

def v035 : ℝ := 1/v034
theorem v035_bound : RationalBound v035 (260193448924071027/250000000000000000) (1040773795696284109/1000000000000000000) := by
  change RationalBound (1/v034) (260193448924071027/250000000000000000) (1040773795696284109/1000000000000000000)
  exact rationalBound_inv v034_bound (by norm_num) (by norm_num) (by norm_num)

def v036 : ℝ := v021*v035
theorem v036_bound : RationalBound v036 (10036405853124999/100000000000000000) (50182029265624997/500000000000000000) := by
  change RationalBound (v021*v035) (10036405853124999/100000000000000000) (50182029265624997/500000000000000000)
  exact rationalBound_mul v021_bound v035_bound (by norm_num) (by norm_num)

def v037 : ℝ := v036*v031
theorem v037_bound : RationalBound v037 (610306847477793541/1000000000000000000) (61030684747779357/100000000000000000) := by
  change RationalBound (v036*v031) (610306847477793541/1000000000000000000) (61030684747779357/100000000000000000)
  exact rationalBound_mul v036_bound v031_bound (by norm_num) (by norm_num)

def v038 : ℝ := v013+v037
theorem v038_bound : RationalBound v038 (2566829204381943051/1000000000000000000) (641707301095485771/250000000000000000) := by
  change RationalBound (v013+v037) (2566829204381943051/1000000000000000000) (641707301095485771/250000000000000000)
  exact rationalBound_add v013_bound v037_bound (by norm_num) (by norm_num)

def v039 : ℝ := v033*v038
theorem v039_bound : RationalBound v039 (182438186618279023/50000000000000000) (364876373236558051/100000000000000000) := by
  change RationalBound (v033*v038) (182438186618279023/50000000000000000) (364876373236558051/100000000000000000)
  exact rationalBound_mul v033_bound v038_bound (by norm_num) (by norm_num)

def v040 : ℝ := v032*v031
theorem v040_bound : RationalBound v040 (21610201027510020431/1000000000000000000) (4322040205502004117/200000000000000000) := by
  change RationalBound (v032*v031) (21610201027510020431/1000000000000000000) (4322040205502004117/200000000000000000)
  exact rationalBound_mul v032_bound v031_bound (by norm_num) (by norm_num)

def v041 : ℝ := (1 : ℝ)
theorem v041_bound : RationalBound v041 (1) (1) := by
  change RationalBound ((1 : ℝ)) (1) (1)
  norm_num [RationalBound]

def v042 : ℝ := -v040
theorem v042_bound : RationalBound v042 (-4322040205502004117/200000000000000000) (-21610201027510020431/1000000000000000000) := by
  change RationalBound (-v040) (-4322040205502004117/200000000000000000) (-21610201027510020431/1000000000000000000)
  exact rationalBound_neg v040_bound (by norm_num) (by norm_num)

def v043 : ℝ := v041+v042
theorem v043_bound : RationalBound v043 (-4122040205502004117/200000000000000000) (-20610201027510020431/1000000000000000000) := by
  change RationalBound (v041+v042) (-4122040205502004117/200000000000000000) (-20610201027510020431/1000000000000000000)
  exact rationalBound_add v041_bound v042_bound (by norm_num) (by norm_num)

def weights : Fin 1 → ℝ := ![(29150089291/8202592000 : ℝ)]
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

theorem endpoint_enclosure : CK.Profile.meanEntropy (97/100 : ℝ) / (97/100 : ℝ) < (3211649873/40000000000 : ℝ) := by
  have h := v009_bound.2
  norm_num [v009] at h
  apply (div_lt_iff₀ (by norm_num : 0 < (97/100 : ℝ))).2
  linarith

def supports0 : Fin 1 → ℝ := ![(4327164698028893/4503599627370496 : ℝ)]
theorem panel0_bound :
    IntervalIntegrable (fun e => 1/(e+profile e)) volume (0 : ℝ) (3211649873/40000000000 : ℝ) ∧
      (∫ e in (0 : ℝ)..(3211649873/40000000000 : ℝ), 1/(e+profile e)) ≤ (29319137657813229/1000000000000000000 : ℝ) := by
  have hA : (182438186618279023/50000000000000000 : ℝ) ≤ ∑ i : Fin 1, weights i*parameters i*(Real.artanh (supports0 i)+
      CK.Profile.meanEntropy (supports0 i)/supports0 i*CK.Profile.tangentFactor (supports0 i)) := by
    have h := v039_bound.1
    norm_num [weights, parameters, supports0, Fin.sum_univ_succ, v000, v001, v002, v003, v004, v005, v006, v007, v008, v009, v010, v011, v012, v013, v014, v015, v016, v017, v018, v019, v020, v021, v022, v023, v024, v025, v026, v027, v028, v029, v030, v031, v032, v033, v034, v035, v036, v037, v038, v039, v040, v041, v042, v043] at h ⊢
    nlinarith only [h]
  have hB : (-4122040205502004117/200000000000000000 : ℝ) ≤ 1-∑ i : Fin 1, weights i*CK.Profile.tangentFactor (supports0 i) := by
    have h := v043_bound.1
    norm_num [weights, supports0, Fin.sum_univ_succ, v000, v001, v002, v003, v004, v005, v006, v007, v008, v009, v010, v011, v012, v013, v014, v015, v016, v017, v018, v019, v020, v021, v022, v023, v024, v025, v026, v027, v028, v029, v030, v031, v032, v033, v034, v035, v036, v037, v038, v039, v040, v041, v042, v043] at h ⊢
    nlinarith only [h]
  have hlog : Real.log (((182438186618279023/50000000000000000 : ℝ)+(-4122040205502004117/200000000000000000 : ℝ)*(0 : ℝ))/
      ((182438186618279023/50000000000000000 : ℝ)+(-4122040205502004117/200000000000000000 : ℝ)*(3211649873/40000000000 : ℝ))) ≤ (-(-4122040205502004117/200000000000000000 : ℝ))*(29319137657813229/1000000000000000000 : ℝ) := by
    have h := LogData.log177_bound.2
    norm_num at h ⊢
    linarith
  simpa only [profile] using profile_panel_integral_bound weights parameters supports0
    weights_nonneg parameters_nonneg (by intro i; fin_cases i <;> norm_num [supports0])
    (a := (0 : ℝ)) (b := (3211649873/40000000000 : ℝ)) (A := (182438186618279023/50000000000000000 : ℝ)) (B := (-4122040205502004117/200000000000000000 : ℝ)) (U := (29319137657813229/1000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA hB hlog

theorem clock_certified :
    CK.Profile.meanEntropy (97/100 : ℝ) / (97/100 : ℝ) < (3211649873/40000000000 : ℝ) ∧
    IntervalIntegrable (fun e => 1/(e+profile e)) volume 0 (3211649873/40000000000 : ℝ) ∧
    (∫ e in (0 : ℝ)..(3211649873/40000000000 : ℝ), 1/(e+profile e)) + (285017456723829/500000000000000000 : ℝ) < Real.log (1/(97/100 : ℝ)) := by
  have h0 := panel0_bound
  refine ⟨endpoint_enclosure, h0.1, ?_⟩
  have hlog := LogData.log172_bound.1
  have hbound := h0.2
  norm_num at hbound hlog ⊢
  linarith only [hbound, hlog]

theorem clock_improper_limit :
    Filter.Tendsto (fun ε => ∫ e in ε..(3211649873/40000000000 : ℝ), 1/(e+profile e))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ e in (0 : ℝ)..(3211649873/40000000000 : ℝ), 1/(e+profile e))) := by
  exact tendsto_integral_from_right (by norm_num) clock_certified.2.1

end
end CK.Certificate.ClockBatch.C12
