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
namespace CK.Certificate.ClockBatch.C01
noncomputable section

def v000 : ℝ := (353357479/2095000000 : ℝ)
theorem v000_bound : RationalBound v000 (353357479/2095000000) (353357479/2095000000) := by
  change RationalBound ((353357479/2095000000 : ℝ)) (353357479/2095000000) (353357479/2095000000)
  norm_num [RationalBound]

def v001 : ℝ := Real.sqrt v000
theorem v001_bound : RationalBound v001 (410690947569184269/1000000000000000000) (41069094756918427/100000000000000000) := by
  change RationalBound (Real.sqrt v000) (410690947569184269/1000000000000000000) (41069094756918427/100000000000000000)
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

def v011 : ℝ := Real.log (8519169901257759/488029353483233 : ℝ)
theorem v011_bound : RationalBound v011 (714924657755599167/250000000000000000) (2859698631022396673/1000000000000000000) := by
  change RationalBound (Real.log (8519169901257759/488029353483233 : ℝ)) (714924657755599167/250000000000000000) (2859698631022396673/1000000000000000000)
  exact LogData.log009_bound

def v012 : ℝ := v010*v011
theorem v012_bound : RationalBound v012 (714924657755599167/500000000000000000) (1429849315511198337/1000000000000000000) := by
  change RationalBound (v010*v011) (714924657755599167/500000000000000000) (1429849315511198337/1000000000000000000)
  exact rationalBound_mul v010_bound v011_bound (by norm_num) (by norm_num)

def v013 : ℝ := Real.artanh (4015570273887263/4503599627370496 : ℝ)
theorem v013_bound : RationalBound v013 (714924657755599167/500000000000000000) (1429849315511198337/1000000000000000000) := by
  change RationalBound (Real.artanh (4015570273887263/4503599627370496 : ℝ)) (714924657755599167/500000000000000000) (1429849315511198337/1000000000000000000)
  have heq : Real.artanh (4015570273887263/4503599627370496 : ℝ) = v012 := by
    rw [Real.artanh_eq_half_log (by norm_num : (4015570273887263/4503599627370496 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)]
    norm_num [v010, v011, v012] <;> ring
  rw [heq]
  exact v012_bound

def v014 : ℝ := (488029353483233/9007199254740992 : ℝ)
theorem v014_bound : RationalBound v014 (488029353483233/9007199254740992) (488029353483233/9007199254740992) := by
  change RationalBound ((488029353483233/9007199254740992 : ℝ)) (488029353483233/9007199254740992) (488029353483233/9007199254740992)
  norm_num [RationalBound]

def v015 : ℝ := Real.log (9007199254740992/488029353483233 : ℝ)
theorem v015_bound : RationalBound v015 (2915403899123984141/1000000000000000000) (1457701949561992073/500000000000000000) := by
  change RationalBound (Real.log (9007199254740992/488029353483233 : ℝ)) (2915403899123984141/1000000000000000000) (1457701949561992073/500000000000000000)
  exact LogData.log010_bound

def v016 : ℝ := v014*v015
theorem v016_bound : RationalBound v016 (157962829486987767/1000000000000000000) (157962829486987769/1000000000000000000) := by
  change RationalBound (v014*v015) (157962829486987767/1000000000000000000) (157962829486987769/1000000000000000000)
  exact rationalBound_mul v014_bound v015_bound (by norm_num) (by norm_num)

def v017 : ℝ := (8519169901257759/9007199254740992 : ℝ)
theorem v017_bound : RationalBound v017 (8519169901257759/9007199254740992) (8519169901257759/9007199254740992) := by
  change RationalBound ((8519169901257759/9007199254740992 : ℝ)) (8519169901257759/9007199254740992) (8519169901257759/9007199254740992)
  norm_num [RationalBound]

def v018 : ℝ := Real.log (9007199254740992/8519169901257759 : ℝ)
theorem v018_bound : RationalBound v018 (55705268101587473/1000000000000000000) (27852634050793737/500000000000000000) := by
  change RationalBound (Real.log (9007199254740992/8519169901257759 : ℝ)) (55705268101587473/1000000000000000000) (27852634050793737/500000000000000000)
  exact LogData.log011_bound

def v019 : ℝ := v017*v018
theorem v019_bound : RationalBound v019 (52687037327696411/1000000000000000000) (52687037327696413/1000000000000000000) := by
  change RationalBound (v017*v018) (52687037327696411/1000000000000000000) (52687037327696413/1000000000000000000)
  exact rationalBound_mul v017_bound v018_bound (by norm_num) (by norm_num)

def v020 : ℝ := v016+v019
theorem v020_bound : RationalBound v020 (105324933407342089/500000000000000000) (105324933407342091/500000000000000000) := by
  change RationalBound (v016+v019) (105324933407342089/500000000000000000) (105324933407342091/500000000000000000)
  exact rationalBound_add v016_bound v019_bound (by norm_num) (by norm_num)

def v021 : ℝ := CK.Profile.meanEntropy (4015570273887263/4503599627370496 : ℝ)
theorem v021_bound : RationalBound v021 (105324933407342089/500000000000000000) (105324933407342091/500000000000000000) := by
  change RationalBound (CK.Profile.meanEntropy (4015570273887263/4503599627370496 : ℝ)) (105324933407342089/500000000000000000) (105324933407342091/500000000000000000)
  have heq : CK.Profile.meanEntropy (4015570273887263/4503599627370496 : ℝ) = v020 := by
    rw [CK.Profile.meanEntropy, binEntropy_eq_log_inv]
    norm_num [v014, v015, v016, v017, v018, v019, v020]
  rw [heq]
  exact v020_bound

def v022 : ℝ := (4157604979124642039894417654847/20282409603651670423947251286016 : ℝ)
theorem v022_bound : RationalBound v022 (4157604979124642039894417654847/20282409603651670423947251286016) (4157604979124642039894417654847/20282409603651670423947251286016) := by
  change RationalBound ((4157604979124642039894417654847/20282409603651670423947251286016 : ℝ)) (4157604979124642039894417654847/20282409603651670423947251286016) (4157604979124642039894417654847/20282409603651670423947251286016)
  norm_num [RationalBound]

def v023 : ℝ := Real.log (2 : ℝ)
theorem v023_bound : RationalBound v023 (693147180559945309/1000000000000000000) (69314718055994531/100000000000000000) := by
  change RationalBound (Real.log (2 : ℝ)) (693147180559945309/1000000000000000000) (69314718055994531/100000000000000000)
  exact LogData.log000_bound

def v024 : ℝ := Real.log (20282409603651670423947251286016/4157604979124642039894417654847 : ℝ)
theorem v024_bound : RationalBound v024 (396203701526420249/250000000000000000) (1584814806105680999/1000000000000000000) := by
  change RationalBound (Real.log (20282409603651670423947251286016/4157604979124642039894417654847 : ℝ)) (396203701526420249/250000000000000000) (1584814806105680999/1000000000000000000)
  exact LogData.log012_bound

def v025 : ℝ := v010*v024
theorem v025_bound : RationalBound v025 (396203701526420249/500000000000000000) (1584814806105681/2000000000000000) := by
  change RationalBound (v010*v024) (396203701526420249/500000000000000000) (1584814806105681/2000000000000000)
  exact rationalBound_mul v010_bound v024_bound (by norm_num) (by norm_num)

def v026 : ℝ := v023+v025
theorem v026_bound : RationalBound v026 (1485554583612785807/1000000000000000000) (148555458361278581/100000000000000000) := by
  change RationalBound (v023+v025) (1485554583612785807/1000000000000000000) (148555458361278581/100000000000000000)
  exact rationalBound_add v023_bound v025_bound (by norm_num) (by norm_num)

def v027 : ℝ := v022*v026
theorem v027_bound : RationalBound v027 (2436140184242391/8000000000000000) (76129380757574719/250000000000000000) := by
  change RationalBound (v022*v026) (2436140184242391/8000000000000000) (76129380757574719/250000000000000000)
  exact rationalBound_mul v022_bound v026_bound (by norm_num) (by norm_num)

def v028 : ℝ := (16124804624527028384052833631169/20282409603651670423947251286016 : ℝ)
theorem v028_bound : RationalBound v028 (16124804624527028384052833631169/20282409603651670423947251286016) (16124804624527028384052833631169/20282409603651670423947251286016) := by
  change RationalBound ((16124804624527028384052833631169/20282409603651670423947251286016 : ℝ)) (16124804624527028384052833631169/20282409603651670423947251286016) (16124804624527028384052833631169/20282409603651670423947251286016)
  norm_num [RationalBound]

def v029 : ℝ := 1/v027
theorem v029_bound : RationalBound v029 (1641941636147654511/500000000000000000) (3283883272295309033/1000000000000000000) := by
  change RationalBound (1/v027) (1641941636147654511/500000000000000000) (3283883272295309033/1000000000000000000)
  exact rationalBound_inv v027_bound (by norm_num) (by norm_num) (by norm_num)

def v030 : ℝ := v028*v029
theorem v030_bound : RationalBound v030 (2610733991191106287/1000000000000000000) (2610733991191106297/1000000000000000000) := by
  change RationalBound (v028*v029) (2610733991191106287/1000000000000000000) (2610733991191106297/1000000000000000000)
  exact rationalBound_mul v028_bound v029_bound (by norm_num) (by norm_num)

def v031 : ℝ := CK.Profile.tangentFactor (4015570273887263/4503599627370496 : ℝ)
theorem v031_bound : RationalBound v031 (2610733991191106287/1000000000000000000) (2610733991191106297/1000000000000000000) := by
  change RationalBound (CK.Profile.tangentFactor (4015570273887263/4503599627370496 : ℝ)) (2610733991191106287/1000000000000000000) (2610733991191106297/1000000000000000000)
  have heq : CK.Profile.tangentFactor (4015570273887263/4503599627370496 : ℝ) = v030 := by
    rw [tangentFactor_positiveLogs]
    norm_num [v010, v022, v023, v024, v025, v026, v027, v028, v029, v030, div_eq_mul_inv] <;> ring
  rw [heq]
  exact v030_bound

def v032 : ℝ := (1 : ℝ)
theorem v032_bound : RationalBound v032 (1) (1) := by
  change RationalBound ((1 : ℝ)) (1) (1)
  norm_num [RationalBound]

def v033 : ℝ := v032*v001
theorem v033_bound : RationalBound v033 (410690947569184269/1000000000000000000) (41069094756918427/100000000000000000) := by
  change RationalBound (v032*v001) (410690947569184269/1000000000000000000) (41069094756918427/100000000000000000)
  exact rationalBound_mul v032_bound v001_bound (by norm_num) (by norm_num)

def v034 : ℝ := (4015570273887263/4503599627370496 : ℝ)
theorem v034_bound : RationalBound v034 (4015570273887263/4503599627370496) (4015570273887263/4503599627370496) := by
  change RationalBound ((4015570273887263/4503599627370496 : ℝ)) (4015570273887263/4503599627370496) (4015570273887263/4503599627370496)
  norm_num [RationalBound]

def v035 : ℝ := 1/v034
theorem v035_bound : RationalBound v035 (1121534257950066299/1000000000000000000) (11215342579500663/10000000000000000) := by
  change RationalBound (1/v034) (1121534257950066299/1000000000000000000) (11215342579500663/10000000000000000)
  exact rationalBound_inv v034_bound (by norm_num) (by norm_num) (by norm_num)

def v036 : ℝ := v021*v035
theorem v036_bound : RationalBound v036 (47250208413057423/200000000000000000) (236251042065287121/1000000000000000000) := by
  change RationalBound (v021*v035) (47250208413057423/200000000000000000) (236251042065287121/1000000000000000000)
  exact rationalBound_mul v021_bound v035_bound (by norm_num) (by norm_num)

def v037 : ℝ := v036*v031
theorem v037_bound : RationalBound v037 (616788625974164971/1000000000000000000) (61678862597416499/100000000000000000) := by
  change RationalBound (v036*v031) (616788625974164971/1000000000000000000) (61678862597416499/100000000000000000)
  exact rationalBound_mul v036_bound v031_bound (by norm_num) (by norm_num)

def v038 : ℝ := v013+v037
theorem v038_bound : RationalBound v038 (409327588297072661/200000000000000000) (2046637941485363327/1000000000000000000) := by
  change RationalBound (v013+v037) (409327588297072661/200000000000000000) (2046637941485363327/1000000000000000000)
  exact rationalBound_add v013_bound v037_bound (by norm_num) (by norm_num)

def v039 : ℝ := v033*v038
theorem v039_bound : RationalBound v039 (840535675519668563/1000000000000000000) (33621427020786743/40000000000000000) := by
  change RationalBound (v033*v038) (840535675519668563/1000000000000000000) (33621427020786743/40000000000000000)
  exact rationalBound_mul v033_bound v038_bound (by norm_num) (by norm_num)

def v040 : ℝ := v032*v031
theorem v040_bound : RationalBound v040 (2610733991191106287/1000000000000000000) (2610733991191106297/1000000000000000000) := by
  change RationalBound (v032*v031) (2610733991191106287/1000000000000000000) (2610733991191106297/1000000000000000000)
  exact rationalBound_mul v032_bound v031_bound (by norm_num) (by norm_num)

def v041 : ℝ := (3 : ℝ)
theorem v041_bound : RationalBound v041 (3) (3) := by
  change RationalBound ((3 : ℝ)) (3) (3)
  norm_num [RationalBound]

def v042 : ℝ := v041*v001
theorem v042_bound : RationalBound v042 (1232072842707552807/1000000000000000000) (123207284270755281/100000000000000000) := by
  change RationalBound (v041*v001) (1232072842707552807/1000000000000000000) (123207284270755281/100000000000000000)
  exact rationalBound_mul v041_bound v001_bound (by norm_num) (by norm_num)

def v043 : ℝ := v042*v038
theorem v043_bound : RationalBound v043 (2521607026559005689/1000000000000000000) (2521607026559005723/1000000000000000000) := by
  change RationalBound (v042*v038) (2521607026559005689/1000000000000000000) (2521607026559005723/1000000000000000000)
  exact rationalBound_mul v042_bound v038_bound (by norm_num) (by norm_num)

def v044 : ℝ := v041*v031
theorem v044_bound : RationalBound v044 (7832201973573318861/1000000000000000000) (7832201973573318891/1000000000000000000) := by
  change RationalBound (v041*v031) (7832201973573318861/1000000000000000000) (7832201973573318891/1000000000000000000)
  exact rationalBound_mul v041_bound v031_bound (by norm_num) (by norm_num)

def v045 : ℝ := v039+v043
theorem v045_bound : RationalBound v045 (840535675519668563/250000000000000000) (1681071351039337149/500000000000000000) := by
  change RationalBound (v039+v043) (840535675519668563/250000000000000000) (1681071351039337149/500000000000000000)
  exact rationalBound_add v039_bound v043_bound (by norm_num) (by norm_num)

def v046 : ℝ := v040+v044
theorem v046_bound : RationalBound v046 (2610733991191106287/250000000000000000) (2610733991191106297/250000000000000000) := by
  change RationalBound (v040+v044) (2610733991191106287/250000000000000000) (2610733991191106297/250000000000000000)
  exact rationalBound_add v040_bound v044_bound (by norm_num) (by norm_num)

def v047 : ℝ := -v046
theorem v047_bound : RationalBound v047 (-2610733991191106297/250000000000000000) (-2610733991191106287/250000000000000000) := by
  change RationalBound (-v046) (-2610733991191106297/250000000000000000) (-2610733991191106287/250000000000000000)
  exact rationalBound_neg v046_bound (by norm_num) (by norm_num)

def v048 : ℝ := v032+v047
theorem v048_bound : RationalBound v048 (-2360733991191106297/250000000000000000) (-2360733991191106287/250000000000000000) := by
  change RationalBound (v032+v047) (-2360733991191106297/250000000000000000) (-2360733991191106287/250000000000000000)
  exact rationalBound_add v032_bound v047_bound (by norm_num) (by norm_num)

def weights : Fin 2 → ℝ := ![(1 : ℝ), (3 : ℝ)]
def parameters : Fin 2 → ℝ := ![v001, v001]
def profile (e : ℝ) : ℝ := ∑ i : Fin 2, weights i*CK.Profile.profile e (parameters i)

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

def supports0 : Fin 2 → ℝ := ![(4015570273887263/4503599627370496 : ℝ), (4015570273887263/4503599627370496 : ℝ)]
theorem panel0_bound :
    IntervalIntegrable (fun e => 1/(e+profile e)) volume (0 : ℝ) (9702616433/50000000000 : ℝ) ∧
      (∫ e in (0 : ℝ)..(9702616433/50000000000 : ℝ), 1/(e+profile e)) ≤ (41697541504977293/500000000000000000 : ℝ) := by
  have hA : (840535675519668563/250000000000000000 : ℝ) ≤ ∑ i : Fin 2, weights i*parameters i*(Real.artanh (supports0 i)+
      CK.Profile.meanEntropy (supports0 i)/supports0 i*CK.Profile.tangentFactor (supports0 i)) := by
    have h := v045_bound.1
    norm_num [weights, parameters, supports0, Fin.sum_univ_succ, v000, v001, v002, v003, v004, v005, v006, v007, v008, v009, v010, v011, v012, v013, v014, v015, v016, v017, v018, v019, v020, v021, v022, v023, v024, v025, v026, v027, v028, v029, v030, v031, v032, v033, v034, v035, v036, v037, v038, v039, v040, v041, v042, v043, v044, v045, v046, v047, v048] at h ⊢
    nlinarith only [h]
  have hB : (-2360733991191106297/250000000000000000 : ℝ) ≤ 1-∑ i : Fin 2, weights i*CK.Profile.tangentFactor (supports0 i) := by
    have h := v048_bound.1
    norm_num [weights, supports0, Fin.sum_univ_succ, v000, v001, v002, v003, v004, v005, v006, v007, v008, v009, v010, v011, v012, v013, v014, v015, v016, v017, v018, v019, v020, v021, v022, v023, v024, v025, v026, v027, v028, v029, v030, v031, v032, v033, v034, v035, v036, v037, v038, v039, v040, v041, v042, v043, v044, v045, v046, v047, v048] at h ⊢
    nlinarith only [h]
  have hlog : Real.log (((840535675519668563/250000000000000000 : ℝ)+(-2360733991191106297/250000000000000000 : ℝ)*(0 : ℝ))/
      ((840535675519668563/250000000000000000 : ℝ)+(-2360733991191106297/250000000000000000 : ℝ)*(9702616433/50000000000 : ℝ))) ≤ (-(-2360733991191106297/250000000000000000 : ℝ))*(41697541504977293/500000000000000000 : ℝ) := by
    have h := LogData.log013_bound.2
    norm_num at h ⊢
    linarith
  simpa only [profile] using profile_panel_integral_bound weights parameters supports0
    weights_nonneg parameters_nonneg (by intro i; fin_cases i <;> norm_num [supports0])
    (a := (0 : ℝ)) (b := (9702616433/50000000000 : ℝ)) (A := (840535675519668563/250000000000000000 : ℝ)) (B := (-2360733991191106297/250000000000000000 : ℝ)) (U := (41697541504977293/500000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA hB hlog

theorem clock_certified :
    CK.Profile.meanEntropy (457/500 : ℝ) / (457/500 : ℝ) < (9702616433/50000000000 : ℝ) ∧
    IntervalIntegrable (fun e => 1/(e+profile e)) volume 0 (9702616433/50000000000 : ℝ) ∧
    (∫ e in (0 : ℝ)..(9702616433/50000000000 : ℝ), 1/(e+profile e)) + (816203064754057/250000000000000000 : ℝ) < Real.log (1/(457/500 : ℝ)) := by
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
end CK.Certificate.ClockBatch.C01
