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
namespace CK.Certificate.ClockBatch.C17
noncomputable section

def v000 : ℝ := (42023679967/217987500000 : ℝ)
theorem v000_bound : RationalBound v000 (42023679967/217987500000) (42023679967/217987500000) := by
  change RationalBound ((42023679967/217987500000 : ℝ)) (42023679967/217987500000) (42023679967/217987500000)
  norm_num [RationalBound]

def v001 : ℝ := Real.sqrt v000
theorem v001_bound : RationalBound v001 (439067452759494109/1000000000000000000) (43906745275949411/100000000000000000) := by
  change RationalBound (Real.sqrt v000) (439067452759494109/1000000000000000000) (43906745275949411/100000000000000000)
  exact rationalBound_sqrt v000_bound (by norm_num) (by norm_num) (by norm_num)

def v002 : ℝ := (13/1000 : ℝ)
theorem v002_bound : RationalBound v002 (13/1000) (13/1000) := by
  change RationalBound ((13/1000 : ℝ)) (13/1000) (13/1000)
  norm_num [RationalBound]

def v003 : ℝ := Real.log (1000/13 : ℝ)
theorem v003_bound : RationalBound v003 (4342805921520600313/1000000000000000000) (3392817126187969/781250000000000) := by
  change RationalBound (Real.log (1000/13 : ℝ)) (4342805921520600313/1000000000000000000) (3392817126187969/781250000000000)
  exact LogData.log254_bound

def v004 : ℝ := v002*v003
theorem v004_bound : RationalBound v004 (14114119244941951/250000000000000000) (11291295395953561/200000000000000000) := by
  change RationalBound (v002*v003) (14114119244941951/250000000000000000) (11291295395953561/200000000000000000)
  exact rationalBound_mul v002_bound v003_bound (by norm_num) (by norm_num)

def v005 : ℝ := (987/1000 : ℝ)
theorem v005_bound : RationalBound v005 (987/1000) (987/1000) := by
  change RationalBound ((987/1000 : ℝ)) (987/1000) (987/1000)
  norm_num [RationalBound]

def v006 : ℝ := Real.log (1000/987 : ℝ)
theorem v006_bound : RationalBound v006 (3271309887163867/250000000000000000) (13085239548655469/1000000000000000000) := by
  change RationalBound (Real.log (1000/987 : ℝ)) (3271309887163867/250000000000000000) (13085239548655469/1000000000000000000)
  exact LogData.log255_bound

def v007 : ℝ := v005*v006
theorem v007_bound : RationalBound v007 (6457565717261473/500000000000000000) (3228782858630737/250000000000000000) := by
  change RationalBound (v005*v006) (6457565717261473/500000000000000000) (3228782858630737/250000000000000000)
  exact rationalBound_mul v005_bound v006_bound (by norm_num) (by norm_num)

def v008 : ℝ := v004+v007
theorem v008_bound : RationalBound v008 (277486433657163/4000000000000000) (69371608414290753/1000000000000000000) := by
  change RationalBound (v004+v007) (277486433657163/4000000000000000) (69371608414290753/1000000000000000000)
  exact rationalBound_add v004_bound v007_bound (by norm_num) (by norm_num)

def v009 : ℝ := CK.Profile.meanEntropy (487/500 : ℝ)
theorem v009_bound : RationalBound v009 (277486433657163/4000000000000000) (69371608414290753/1000000000000000000) := by
  change RationalBound (CK.Profile.meanEntropy (487/500 : ℝ)) (277486433657163/4000000000000000) (69371608414290753/1000000000000000000)
  have heq : CK.Profile.meanEntropy (487/500 : ℝ) = v008 := by
    rw [CK.Profile.meanEntropy, binEntropy_eq_log_inv]
    norm_num [v002, v003, v004, v005, v006, v007, v008]
  rw [heq]
  exact v008_bound

def v010 : ℝ := (1/2 : ℝ)
theorem v010_bound : RationalBound v010 (1/2) (1/2) := by
  change RationalBound ((1/2 : ℝ)) (1/2) (1/2)
  norm_num [RationalBound]

def v011 : ℝ := Real.log (4435224041989449/68375585381047 : ℝ)
theorem v011_bound : RationalBound v011 (4172317588226486171/1000000000000000000) (2086158794113243089/500000000000000000) := by
  change RationalBound (Real.log (4435224041989449/68375585381047 : ℝ)) (4172317588226486171/1000000000000000000) (2086158794113243089/500000000000000000)
  exact LogData.log262_bound

def v012 : ℝ := v010*v011
theorem v012_bound : RationalBound v012 (417231758822648617/200000000000000000) (2086158794113243089/1000000000000000000) := by
  change RationalBound (v010*v011) (417231758822648617/200000000000000000) (2086158794113243089/1000000000000000000)
  exact rationalBound_mul v010_bound v011_bound (by norm_num) (by norm_num)

def v013 : ℝ := Real.artanh (2183424228304201/2251799813685248 : ℝ)
theorem v013_bound : RationalBound v013 (417231758822648617/200000000000000000) (2086158794113243089/1000000000000000000) := by
  change RationalBound (Real.artanh (2183424228304201/2251799813685248 : ℝ)) (417231758822648617/200000000000000000) (2086158794113243089/1000000000000000000)
  have heq : Real.artanh (2183424228304201/2251799813685248 : ℝ) = v012 := by
    rw [Real.artanh_eq_half_log (by norm_num : (2183424228304201/2251799813685248 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)]
    norm_num [v010, v011, v012] <;> ring
  rw [heq]
  exact v012_bound

def v014 : ℝ := (68375585381047/4503599627370496 : ℝ)
theorem v014_bound : RationalBound v014 (68375585381047/4503599627370496) (68375585381047/4503599627370496) := by
  change RationalBound ((68375585381047/4503599627370496 : ℝ)) (68375585381047/4503599627370496) (68375585381047/4503599627370496)
  norm_num [RationalBound]

def v015 : ℝ := Real.log (4503599627370496/68375585381047 : ℝ)
theorem v015_bound : RationalBound v015 (418761645115152741/100000000000000000) (4187616451151527417/1000000000000000000) := by
  change RationalBound (Real.log (4503599627370496/68375585381047 : ℝ)) (418761645115152741/100000000000000000) (4187616451151527417/1000000000000000000)
  exact LogData.log263_bound

def v016 : ℝ := v014*v015
theorem v016_bound : RationalBound v016 (31789096488353629/500000000000000000) (63578192976707259/1000000000000000000) := by
  change RationalBound (v014*v015) (31789096488353629/500000000000000000) (63578192976707259/1000000000000000000)
  exact rationalBound_mul v014_bound v015_bound (by norm_num) (by norm_num)

def v017 : ℝ := (4435224041989449/4503599627370496 : ℝ)
theorem v017_bound : RationalBound v017 (4435224041989449/4503599627370496) (4435224041989449/4503599627370496) := by
  change RationalBound ((4435224041989449/4503599627370496 : ℝ)) (4435224041989449/4503599627370496) (4435224041989449/4503599627370496)
  norm_num [RationalBound]

def v018 : ℝ := Real.log (4503599627370496/4435224041989449 : ℝ)
theorem v018_bound : RationalBound v018 (15298862925041239/1000000000000000000) (382471573126031/25000000000000000) := by
  change RationalBound (Real.log (4503599627370496/4435224041989449 : ℝ)) (15298862925041239/1000000000000000000) (382471573126031/25000000000000000)
  exact LogData.log264_bound

def v019 : ℝ := v017*v018
theorem v019_bound : RationalBound v019 (3013317802402501/200000000000000000) (15066589012012507/1000000000000000000) := by
  change RationalBound (v017*v018) (3013317802402501/200000000000000000) (15066589012012507/1000000000000000000)
  exact rationalBound_mul v017_bound v018_bound (by norm_num) (by norm_num)

def v020 : ℝ := v016+v019
theorem v020_bound : RationalBound v020 (78644781988719763/1000000000000000000) (39322390994359883/500000000000000000) := by
  change RationalBound (v016+v019) (78644781988719763/1000000000000000000) (39322390994359883/500000000000000000)
  exact rationalBound_add v016_bound v019_bound (by norm_num) (by norm_num)

def v021 : ℝ := CK.Profile.meanEntropy (2183424228304201/2251799813685248 : ℝ)
theorem v021_bound : RationalBound v021 (78644781988719763/1000000000000000000) (39322390994359883/500000000000000000) := by
  change RationalBound (CK.Profile.meanEntropy (2183424228304201/2251799813685248 : ℝ)) (78644781988719763/1000000000000000000) (39322390994359883/500000000000000000)
  have heq : CK.Profile.meanEntropy (2183424228304201/2251799813685248 : ℝ) = v020 := by
    rw [CK.Profile.meanEntropy, binEntropy_eq_log_inv]
    norm_num [v014, v015, v016, v017, v018, v019, v020]
  rw [heq]
  exact v020_bound

def v022 : ℝ := (303261040167121954730618573103/5070602400912917605986812821504 : ℝ)
theorem v022_bound : RationalBound v022 (303261040167121954730618573103/5070602400912917605986812821504) (303261040167121954730618573103/5070602400912917605986812821504) := by
  change RationalBound ((303261040167121954730618573103/5070602400912917605986812821504 : ℝ)) (303261040167121954730618573103/5070602400912917605986812821504) (303261040167121954730618573103/5070602400912917605986812821504)
  norm_num [RationalBound]

def v023 : ℝ := Real.log (2 : ℝ)
theorem v023_bound : RationalBound v023 (693147180559945309/1000000000000000000) (69314718055994531/100000000000000000) := by
  change RationalBound (Real.log (2 : ℝ)) (693147180559945309/1000000000000000000) (69314718055994531/100000000000000000)
  exact LogData.log000_bound

def v024 : ℝ := Real.log (5070602400912917605986812821504/303261040167121954730618573103 : ℝ)
theorem v024_bound : RationalBound v024 (176038809559792377/62500000000000000) (2816620952956678037/1000000000000000000) := by
  change RationalBound (Real.log (5070602400912917605986812821504/303261040167121954730618573103 : ℝ)) (176038809559792377/62500000000000000) (2816620952956678037/1000000000000000000)
  exact LogData.log265_bound

def v025 : ℝ := v010*v024
theorem v025_bound : RationalBound v025 (176038809559792377/125000000000000000) (1408310476478339019/1000000000000000000) := by
  change RationalBound (v010*v024) (176038809559792377/125000000000000000) (1408310476478339019/1000000000000000000)
  exact rationalBound_mul v010_bound v024_bound (by norm_num) (by norm_num)

def v026 : ℝ := v023+v025
theorem v026_bound : RationalBound v026 (84058306281531373/40000000000000000) (2101457657038284329/1000000000000000000) := by
  change RationalBound (v023+v025) (84058306281531373/40000000000000000) (2101457657038284329/1000000000000000000)
  exact rationalBound_add v023_bound v025_bound (by norm_num) (by norm_num)

def v027 : ℝ := v022*v026
theorem v027_bound : RationalBound v027 (245475269347533/1953125000000000) (62841668952968449/500000000000000000) := by
  change RationalBound (v022*v026) (245475269347533/1953125000000000) (62841668952968449/500000000000000000)
  exact rationalBound_mul v022_bound v026_bound (by norm_num) (by norm_num)

def v028 : ℝ := (4767341360745795651256194248401/5070602400912917605986812821504 : ℝ)
theorem v028_bound : RationalBound v028 (4767341360745795651256194248401/5070602400912917605986812821504) (4767341360745795651256194248401/5070602400912917605986812821504) := by
  change RationalBound ((4767341360745795651256194248401/5070602400912917605986812821504 : ℝ)) (4767341360745795651256194248401/5070602400912917605986812821504) (4767341360745795651256194248401/5070602400912917605986812821504)
  norm_num [RationalBound]

def v029 : ℝ := 1/v027
theorem v029_bound : RationalBound v029 (1989126038227146429/250000000000000000) (1989126038227146461/250000000000000000) := by
  change RationalBound (1/v027) (1989126038227146429/250000000000000000) (1989126038227146461/250000000000000000)
  exact rationalBound_inv v027_bound (by norm_num) (by norm_num) (by norm_num)

def v030 : ℝ := v028*v029
theorem v030_bound : RationalBound v030 (1496128796384334121/200000000000000000) (3740321990960835363/500000000000000000) := by
  change RationalBound (v028*v029) (1496128796384334121/200000000000000000) (3740321990960835363/500000000000000000)
  exact rationalBound_mul v028_bound v029_bound (by norm_num) (by norm_num)

def v031 : ℝ := CK.Profile.tangentFactor (2183424228304201/2251799813685248 : ℝ)
theorem v031_bound : RationalBound v031 (1496128796384334121/200000000000000000) (3740321990960835363/500000000000000000) := by
  change RationalBound (CK.Profile.tangentFactor (2183424228304201/2251799813685248 : ℝ)) (1496128796384334121/200000000000000000) (3740321990960835363/500000000000000000)
  have heq : CK.Profile.tangentFactor (2183424228304201/2251799813685248 : ℝ) = v030 := by
    rw [tangentFactor_positiveLogs]
    norm_num [v010, v022, v023, v024, v025, v026, v027, v028, v029, v030, div_eq_mul_inv] <;> ring
  rw [heq]
  exact v030_bound

def v032 : ℝ := (1 : ℝ)
theorem v032_bound : RationalBound v032 (1) (1) := by
  change RationalBound ((1 : ℝ)) (1) (1)
  norm_num [RationalBound]

def v033 : ℝ := v032*v001
theorem v033_bound : RationalBound v033 (439067452759494109/1000000000000000000) (43906745275949411/100000000000000000) := by
  change RationalBound (v032*v001) (439067452759494109/1000000000000000000) (43906745275949411/100000000000000000)
  exact rationalBound_mul v032_bound v001_bound (by norm_num) (by norm_num)

def v034 : ℝ := (2183424228304201/2251799813685248 : ℝ)
theorem v034_bound : RationalBound v034 (2183424228304201/2251799813685248) (2183424228304201/2251799813685248) := by
  change RationalBound ((2183424228304201/2251799813685248 : ℝ)) (2183424228304201/2251799813685248) (2183424228304201/2251799813685248)
  norm_num [RationalBound]

def v035 : ℝ := 1/v034
theorem v035_bound : RationalBound v035 (51565787914567391/50000000000000000) (1031315758291347821/1000000000000000000) := by
  change RationalBound (1/v034) (51565787914567391/50000000000000000) (1031315758291347821/1000000000000000000)
  exact rationalBound_inv v034_bound (by norm_num) (by norm_num) (by norm_num)

def v036 : ℝ := v021*v035
theorem v036_bound : RationalBound v036 (16221520594470851/200000000000000000) (81107602972354259/1000000000000000000) := by
  change RationalBound (v021*v035) (16221520594470851/200000000000000000) (81107602972354259/1000000000000000000)
  exact rationalBound_mul v021_bound v035_bound (by norm_num) (by norm_num)

def v037 : ℝ := v036*v031
theorem v037_bound : RationalBound v037 (30336855103161703/50000000000000000) (606737102063234101/1000000000000000000) := by
  change RationalBound (v036*v031) (30336855103161703/50000000000000000) (606737102063234101/1000000000000000000)
  exact rationalBound_mul v036_bound v031_bound (by norm_num) (by norm_num)

def v038 : ℝ := v013+v037
theorem v038_bound : RationalBound v038 (538579179235295429/200000000000000000) (269289589617647719/100000000000000000) := by
  change RationalBound (v013+v037) (538579179235295429/200000000000000000) (269289589617647719/100000000000000000)
  exact rationalBound_add v013_bound v037_bound (by norm_num) (by norm_num)

def v039 : ℝ := v033*v038
theorem v039_bound : RationalBound v039 (1182362941680700931/1000000000000000000) (236472588336140191/200000000000000000) := by
  change RationalBound (v033*v038) (1182362941680700931/1000000000000000000) (236472588336140191/200000000000000000)
  exact rationalBound_mul v033_bound v038_bound (by norm_num) (by norm_num)

def v040 : ℝ := v032*v031
theorem v040_bound : RationalBound v040 (1496128796384334121/200000000000000000) (3740321990960835363/500000000000000000) := by
  change RationalBound (v032*v031) (1496128796384334121/200000000000000000) (3740321990960835363/500000000000000000)
  exact rationalBound_mul v032_bound v031_bound (by norm_num) (by norm_num)

def v041 : ℝ := (2 : ℝ)
theorem v041_bound : RationalBound v041 (2) (2) := by
  change RationalBound ((2 : ℝ)) (2) (2)
  norm_num [RationalBound]

def v042 : ℝ := v041*v001
theorem v042_bound : RationalBound v042 (439067452759494109/500000000000000000) (43906745275949411/50000000000000000) := by
  change RationalBound (v041*v001) (439067452759494109/500000000000000000) (43906745275949411/50000000000000000)
  exact rationalBound_mul v041_bound v001_bound (by norm_num) (by norm_num)

def v043 : ℝ := v042*v038
theorem v043_bound : RationalBound v043 (2364725883361401863/1000000000000000000) (2364725883361401909/1000000000000000000) := by
  change RationalBound (v042*v038) (2364725883361401863/1000000000000000000) (2364725883361401909/1000000000000000000)
  exact rationalBound_mul v042_bound v038_bound (by norm_num) (by norm_num)

def v044 : ℝ := v041*v031
theorem v044_bound : RationalBound v044 (1496128796384334121/100000000000000000) (3740321990960835363/250000000000000000) := by
  change RationalBound (v041*v031) (1496128796384334121/100000000000000000) (3740321990960835363/250000000000000000)
  exact rationalBound_mul v041_bound v031_bound (by norm_num) (by norm_num)

def v045 : ℝ := v039+v043
theorem v045_bound : RationalBound v045 (1773544412521051397/500000000000000000) (221693051565131429/62500000000000000) := by
  change RationalBound (v039+v043) (1773544412521051397/500000000000000000) (221693051565131429/62500000000000000)
  exact rationalBound_add v039_bound v043_bound (by norm_num) (by norm_num)

def v046 : ℝ := v040+v044
theorem v046_bound : RationalBound v046 (4488386389153002363/200000000000000000) (11220965972882506089/500000000000000000) := by
  change RationalBound (v040+v044) (4488386389153002363/200000000000000000) (11220965972882506089/500000000000000000)
  exact rationalBound_add v040_bound v044_bound (by norm_num) (by norm_num)

def v047 : ℝ := -v046
theorem v047_bound : RationalBound v047 (-11220965972882506089/500000000000000000) (-4488386389153002363/200000000000000000) := by
  change RationalBound (-v046) (-11220965972882506089/500000000000000000) (-4488386389153002363/200000000000000000)
  exact rationalBound_neg v046_bound (by norm_num) (by norm_num)

def v048 : ℝ := v032+v047
theorem v048_bound : RationalBound v048 (-10720965972882506089/500000000000000000) (-4288386389153002363/200000000000000000) := by
  change RationalBound (v032+v047) (-10720965972882506089/500000000000000000) (-4288386389153002363/200000000000000000)
  exact rationalBound_add v032_bound v047_bound (by norm_num) (by norm_num)

def weights : Fin 2 → ℝ := ![(1 : ℝ), (2 : ℝ)]
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

theorem endpoint_enclosure : CK.Profile.meanEntropy (487/500 : ℝ) / (487/500 : ℝ) < (71223417273/1000000000000 : ℝ) := by
  have h := v009_bound.2
  norm_num [v009] at h
  apply (div_lt_iff₀ (by norm_num : 0 < (487/500 : ℝ))).2
  linarith

def supports0 : Fin 2 → ℝ := ![(2183424228304201/2251799813685248 : ℝ), (2183424228304201/2251799813685248 : ℝ)]
theorem panel0_bound :
    IntervalIntegrable (fun e => 1/(e+profile e)) volume (0 : ℝ) (71223417273/1000000000000 : ℝ) ∧
      (∫ e in (0 : ℝ)..(71223417273/1000000000000 : ℝ), 1/(e+profile e)) ≤ (13130084051771339/500000000000000000 : ℝ) := by
  have hA : (1773544412521051397/500000000000000000 : ℝ) ≤ ∑ i : Fin 2, weights i*parameters i*(Real.artanh (supports0 i)+
      CK.Profile.meanEntropy (supports0 i)/supports0 i*CK.Profile.tangentFactor (supports0 i)) := by
    have h := v045_bound.1
    norm_num [weights, parameters, supports0, Fin.sum_univ_succ, v000, v001, v002, v003, v004, v005, v006, v007, v008, v009, v010, v011, v012, v013, v014, v015, v016, v017, v018, v019, v020, v021, v022, v023, v024, v025, v026, v027, v028, v029, v030, v031, v032, v033, v034, v035, v036, v037, v038, v039, v040, v041, v042, v043, v044, v045, v046, v047, v048] at h ⊢
    nlinarith only [h]
  have hB : (-10720965972882506089/500000000000000000 : ℝ) ≤ 1-∑ i : Fin 2, weights i*CK.Profile.tangentFactor (supports0 i) := by
    have h := v048_bound.1
    norm_num [weights, supports0, Fin.sum_univ_succ, v000, v001, v002, v003, v004, v005, v006, v007, v008, v009, v010, v011, v012, v013, v014, v015, v016, v017, v018, v019, v020, v021, v022, v023, v024, v025, v026, v027, v028, v029, v030, v031, v032, v033, v034, v035, v036, v037, v038, v039, v040, v041, v042, v043, v044, v045, v046, v047, v048] at h ⊢
    nlinarith only [h]
  have hlog : Real.log (((1773544412521051397/500000000000000000 : ℝ)+(-10720965972882506089/500000000000000000 : ℝ)*(0 : ℝ))/
      ((1773544412521051397/500000000000000000 : ℝ)+(-10720965972882506089/500000000000000000 : ℝ)*(71223417273/1000000000000 : ℝ))) ≤ (-(-10720965972882506089/500000000000000000 : ℝ))*(13130084051771339/500000000000000000 : ℝ) := by
    have h := LogData.log266_bound.2
    norm_num at h ⊢
    linarith
  simpa only [profile] using profile_panel_integral_bound weights parameters supports0
    weights_nonneg parameters_nonneg (by intro i; fin_cases i <;> norm_num [supports0])
    (a := (0 : ℝ)) (b := (71223417273/1000000000000 : ℝ)) (A := (1773544412521051397/500000000000000000 : ℝ)) (B := (-10720965972882506089/500000000000000000 : ℝ)) (U := (13130084051771339/500000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA hB hlog

theorem clock_certified :
    CK.Profile.meanEntropy (487/500 : ℝ) / (487/500 : ℝ) < (71223417273/1000000000000 : ℝ) ∧
    IntervalIntegrable (fun e => 1/(e+profile e)) volume 0 (71223417273/1000000000000 : ℝ) ∧
    (∫ e in (0 : ℝ)..(71223417273/1000000000000 : ℝ), 1/(e+profile e)) + (10475904507409/250000000000000000 : ℝ) < Real.log (1/(487/500 : ℝ)) := by
  have h0 := panel0_bound
  refine ⟨endpoint_enclosure, h0.1, ?_⟩
  have hlog := LogData.log256_bound.1
  have hbound := h0.2
  norm_num at hbound hlog ⊢
  linarith only [hbound, hlog]

theorem clock_improper_limit :
    Filter.Tendsto (fun ε => ∫ e in ε..(71223417273/1000000000000 : ℝ), 1/(e+profile e))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ e in (0 : ℝ)..(71223417273/1000000000000 : ℝ), 1/(e+profile e))) := by
  exact tendsto_integral_from_right (by norm_num) clock_certified.2.1

end
end CK.Certificate.ClockBatch.C17
