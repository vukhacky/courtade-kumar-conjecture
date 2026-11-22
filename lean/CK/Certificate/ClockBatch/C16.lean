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
namespace CK.Certificate.ClockBatch.C16
noncomputable section

def v000 : ℝ := (4/25 : ℝ)
theorem v000_bound : RationalBound v000 (4/25) (4/25) := by
  change RationalBound ((4/25 : ℝ)) (4/25) (4/25)
  norm_num [RationalBound]

def v001 : ℝ := Real.sqrt v000
theorem v001_bound : RationalBound v001 (2/5) (2/5) := by
  change RationalBound (Real.sqrt v000) (2/5) (2/5)
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

def v011 : ℝ := Real.log (2213582795757453/38217017927795 : ℝ)
theorem v011_bound : RationalBound v011 (1014771686119216373/250000000000000000) (2029543372238432749/500000000000000000) := by
  change RationalBound (Real.log (2213582795757453/38217017927795 : ℝ)) (1014771686119216373/250000000000000000) (2029543372238432749/500000000000000000)
  exact LogData.log257_bound

def v012 : ℝ := v010*v011
theorem v012_bound : RationalBound v012 (1014771686119216373/500000000000000000) (2029543372238432749/1000000000000000000) := by
  change RationalBound (v010*v011) (1014771686119216373/500000000000000000) (2029543372238432749/1000000000000000000)
  exact rationalBound_mul v010_bound v011_bound (by norm_num) (by norm_num)

def v013 : ℝ := Real.artanh (1087682888914829/1125899906842624 : ℝ)
theorem v013_bound : RationalBound v013 (1014771686119216373/500000000000000000) (2029543372238432749/1000000000000000000) := by
  change RationalBound (Real.artanh (1087682888914829/1125899906842624 : ℝ)) (1014771686119216373/500000000000000000) (2029543372238432749/1000000000000000000)
  have heq : Real.artanh (1087682888914829/1125899906842624 : ℝ) = v012 := by
    rw [Real.artanh_eq_half_log (by norm_num : (1087682888914829/1125899906842624 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)]
    norm_num [v010, v011, v012] <;> ring
  rw [heq]
  exact v012_bound

def v014 : ℝ := (38217017927795/2251799813685248 : ℝ)
theorem v014_bound : RationalBound v014 (38217017927795/2251799813685248) (38217017927795/2251799813685248) := by
  change RationalBound ((38217017927795/2251799813685248 : ℝ)) (38217017927795/2251799813685248) (38217017927795/2251799813685248)
  norm_num [RationalBound]

def v015 : ℝ := Real.log (2251799813685248/38217017927795 : ℝ)
theorem v015_bound : RationalBound v015 (2038102090363885987/500000000000000000) (203810209036388599/50000000000000000) := by
  change RationalBound (Real.log (2251799813685248/38217017927795 : ℝ)) (2038102090363885987/500000000000000000) (203810209036388599/50000000000000000)
  exact LogData.log258_bound

def v016 : ℝ := v014*v015
theorem v016_bound : RationalBound v016 (69180380647282909/1000000000000000000) (6918038064728291/100000000000000000) := by
  change RationalBound (v014*v015) (69180380647282909/1000000000000000000) (6918038064728291/100000000000000000)
  exact rationalBound_mul v014_bound v015_bound (by norm_num) (by norm_num)

def v017 : ℝ := (2213582795757453/2251799813685248 : ℝ)
theorem v017_bound : RationalBound v017 (2213582795757453/2251799813685248) (2213582795757453/2251799813685248) := by
  change RationalBound ((2213582795757453/2251799813685248 : ℝ)) (2213582795757453/2251799813685248) (2213582795757453/2251799813685248)
  norm_num [RationalBound]

def v018 : ℝ := Real.log (2251799813685248/2213582795757453 : ℝ)
theorem v018_bound : RationalBound v018 (8558718125453241/500000000000000000) (17117436250906483/1000000000000000000) := by
  change RationalBound (Real.log (2251799813685248/2213582795757453 : ℝ)) (8558718125453241/500000000000000000) (17117436250906483/1000000000000000000)
  exact LogData.log259_bound

def v019 : ℝ := v017*v018
theorem v019_bound : RationalBound v019 (8413461570207291/500000000000000000) (2103365392551823/125000000000000000) := by
  change RationalBound (v017*v018) (8413461570207291/500000000000000000) (2103365392551823/125000000000000000)
  exact rationalBound_mul v017_bound v018_bound (by norm_num) (by norm_num)

def v020 : ℝ := v016+v019
theorem v020_bound : RationalBound v020 (86007303787697491/1000000000000000000) (43003651893848747/500000000000000000) := by
  change RationalBound (v016+v019) (86007303787697491/1000000000000000000) (43003651893848747/500000000000000000)
  exact rationalBound_add v016_bound v019_bound (by norm_num) (by norm_num)

def v021 : ℝ := CK.Profile.meanEntropy (1087682888914829/1125899906842624 : ℝ)
theorem v021_bound : RationalBound v021 (86007303787697491/1000000000000000000) (43003651893848747/500000000000000000) := by
  change RationalBound (CK.Profile.meanEntropy (1087682888914829/1125899906842624 : ℝ)) (86007303787697491/1000000000000000000) (43003651893848747/500000000000000000)
  have heq : CK.Profile.meanEntropy (1087682888914829/1125899906842624 : ℝ) = v020 := by
    rw [CK.Profile.meanEntropy, binEntropy_eq_log_inv]
    norm_num [v014, v015, v016, v017, v018, v019, v020]
  rw [heq]
  exact v020_bound

def v022 : ℝ := (84596533390121159167487106135/1267650600228229401496703205376 : ℝ)
theorem v022_bound : RationalBound v022 (84596533390121159167487106135/1267650600228229401496703205376) (84596533390121159167487106135/1267650600228229401496703205376) := by
  change RationalBound ((84596533390121159167487106135/1267650600228229401496703205376 : ℝ)) (84596533390121159167487106135/1267650600228229401496703205376) (84596533390121159167487106135/1267650600228229401496703205376)
  norm_num [RationalBound]

def v023 : ℝ := Real.log (2 : ℝ)
theorem v023_bound : RationalBound v023 (693147180559945309/1000000000000000000) (69314718055994531/100000000000000000) := by
  change RationalBound (Real.log (2 : ℝ)) (693147180559945309/1000000000000000000) (69314718055994531/100000000000000000)
  exact LogData.log000_bound

def v024 : ℝ := Real.log (1267650600228229401496703205376/84596533390121159167487106135 : ℝ)
theorem v024_bound : RationalBound v024 (1353513627929393919/500000000000000000) (1353513627929393921/500000000000000000) := by
  change RationalBound (Real.log (1267650600228229401496703205376/84596533390121159167487106135 : ℝ)) (1353513627929393919/500000000000000000) (1353513627929393921/500000000000000000)
  exact LogData.log260_bound

def v025 : ℝ := v010*v024
theorem v025_bound : RationalBound v025 (1353513627929393919/1000000000000000000) (1353513627929393921/1000000000000000000) := by
  change RationalBound (v010*v024) (1353513627929393919/1000000000000000000) (1353513627929393921/1000000000000000000)
  exact rationalBound_mul v010_bound v024_bound (by norm_num) (by norm_num)

def v026 : ℝ := v023+v025
theorem v026_bound : RationalBound v026 (511665202122334807/250000000000000000) (2046660808489339231/1000000000000000000) := by
  change RationalBound (v023+v025) (511665202122334807/250000000000000000) (2046660808489339231/1000000000000000000)
  exact rationalBound_add v023_bound v025_bound (by norm_num) (by norm_num)

def v027 : ℝ := v022*v026
theorem v027_bound : RationalBound v027 (13658370010825407/100000000000000000) (136583700108254071/1000000000000000000) := by
  change RationalBound (v022*v026) (13658370010825407/100000000000000000) (136583700108254071/1000000000000000000)
  exact rationalBound_mul v022_bound v026_bound (by norm_num) (by norm_num)

def v028 : ℝ := (1183054066838108242329216099241/1267650600228229401496703205376 : ℝ)
theorem v028_bound : RationalBound v028 (1183054066838108242329216099241/1267650600228229401496703205376) (1183054066838108242329216099241/1267650600228229401496703205376) := by
  change RationalBound ((1183054066838108242329216099241/1267650600228229401496703205376 : ℝ)) (1183054066838108242329216099241/1267650600228229401496703205376) (1183054066838108242329216099241/1267650600228229401496703205376)
  norm_num [RationalBound]

def v029 : ℝ := 1/v027
theorem v029_bound : RationalBound v029 (457594866374710107/62500000000000000) (7321517861995361767/1000000000000000000) := by
  change RationalBound (1/v027) (457594866374710107/62500000000000000) (7321517861995361767/1000000000000000000)
  exact rationalBound_inv v027_bound (by norm_num) (by norm_num) (by norm_num)

def v030 : ℝ := v028*v029
theorem v030_bound : RationalBound v030 (68329171149384471/10000000000000000) (427057319683652947/62500000000000000) := by
  change RationalBound (v028*v029) (68329171149384471/10000000000000000) (427057319683652947/62500000000000000)
  exact rationalBound_mul v028_bound v029_bound (by norm_num) (by norm_num)

def v031 : ℝ := CK.Profile.tangentFactor (1087682888914829/1125899906842624 : ℝ)
theorem v031_bound : RationalBound v031 (68329171149384471/10000000000000000) (427057319683652947/62500000000000000) := by
  change RationalBound (CK.Profile.tangentFactor (1087682888914829/1125899906842624 : ℝ)) (68329171149384471/10000000000000000) (427057319683652947/62500000000000000)
  have heq : CK.Profile.tangentFactor (1087682888914829/1125899906842624 : ℝ) = v030 := by
    rw [tangentFactor_positiveLogs]
    norm_num [v010, v022, v023, v024, v025, v026, v027, v028, v029, v030, div_eq_mul_inv] <;> ring
  rw [heq]
  exact v030_bound

def v032 : ℝ := (23011179967/6556000000 : ℝ)
theorem v032_bound : RationalBound v032 (23011179967/6556000000) (23011179967/6556000000) := by
  change RationalBound ((23011179967/6556000000 : ℝ)) (23011179967/6556000000) (23011179967/6556000000)
  norm_num [RationalBound]

def v033 : ℝ := v032*v001
theorem v033_bound : RationalBound v033 (175497101639719341/125000000000000000) (1403976813117754729/1000000000000000000) := by
  change RationalBound (v032*v001) (175497101639719341/125000000000000000) (1403976813117754729/1000000000000000000)
  exact rationalBound_mul v032_bound v001_bound (by norm_num) (by norm_num)

def v034 : ℝ := (1087682888914829/1125899906842624 : ℝ)
theorem v034_bound : RationalBound v034 (1087682888914829/1125899906842624) (1087682888914829/1125899906842624) := by
  change RationalBound ((1087682888914829/1125899906842624 : ℝ)) (1087682888914829/1125899906842624) (1087682888914829/1125899906842624)
  norm_num [RationalBound]

def v035 : ℝ := 1/v034
theorem v035_bound : RationalBound v035 (207027235293905149/200000000000000000) (517568088234762873/500000000000000000) := by
  change RationalBound (1/v034) (207027235293905149/200000000000000000) (517568088234762873/500000000000000000)
  exact rationalBound_inv v034_bound (by norm_num) (by norm_num) (by norm_num)

def v036 : ℝ := v021*v035
theorem v036_bound : RationalBound v036 (4451463579562507/50000000000000000) (2782164737226567/31250000000000000) := by
  change RationalBound (v021*v035) (4451463579562507/50000000000000000) (2782164737226567/31250000000000000)
  exact rationalBound_mul v021_bound v035_bound (by norm_num) (by norm_num)

def v037 : ℝ := v036*v031
theorem v037_bound : RationalBound v037 (152082408396589089/250000000000000000) (152082408396589097/250000000000000000) := by
  change RationalBound (v036*v031) (152082408396589089/250000000000000000) (152082408396589097/250000000000000000)
  exact rationalBound_mul v036_bound v031_bound (by norm_num) (by norm_num)

def v038 : ℝ := v013+v037
theorem v038_bound : RationalBound v038 (1318936502912394551/500000000000000000) (2637873005824789137/1000000000000000000) := by
  change RationalBound (v013+v037) (1318936502912394551/500000000000000000) (2637873005824789137/1000000000000000000)
  exact rationalBound_add v013_bound v037_bound (by norm_num) (by norm_num)

def v039 : ℝ := v033*v038
theorem v039_bound : RationalBound v039 (1851756268063619929/500000000000000000) (370351253612723991/100000000000000000) := by
  change RationalBound (v033*v038) (1851756268063619929/500000000000000000) (370351253612723991/100000000000000000)
  exact rationalBound_mul v033_bound v038_bound (by norm_num) (by norm_num)

def v040 : ℝ := v032*v031
theorem v040_bound : RationalBound v040 (191865143906580879/8000000000000000) (23983142988322610059/1000000000000000000) := by
  change RationalBound (v032*v031) (191865143906580879/8000000000000000) (23983142988322610059/1000000000000000000)
  exact rationalBound_mul v032_bound v031_bound (by norm_num) (by norm_num)

def v041 : ℝ := (1 : ℝ)
theorem v041_bound : RationalBound v041 (1) (1) := by
  change RationalBound ((1 : ℝ)) (1) (1)
  norm_num [RationalBound]

def v042 : ℝ := -v040
theorem v042_bound : RationalBound v042 (-23983142988322610059/1000000000000000000) (-191865143906580879/8000000000000000) := by
  change RationalBound (-v040) (-23983142988322610059/1000000000000000000) (-191865143906580879/8000000000000000)
  exact rationalBound_neg v040_bound (by norm_num) (by norm_num)

def v043 : ℝ := v041+v042
theorem v043_bound : RationalBound v043 (-22983142988322610059/1000000000000000000) (-183865143906580879/8000000000000000) := by
  change RationalBound (v041+v042) (-22983142988322610059/1000000000000000000) (-183865143906580879/8000000000000000)
  exact rationalBound_add v041_bound v042_bound (by norm_num) (by norm_num)

def weights : Fin 1 → ℝ := ![(23011179967/6556000000 : ℝ)]
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

theorem endpoint_enclosure : CK.Profile.meanEntropy (487/500 : ℝ) / (487/500 : ℝ) < (71223417273/1000000000000 : ℝ) := by
  have h := v009_bound.2
  norm_num [v009] at h
  apply (div_lt_iff₀ (by norm_num : 0 < (487/500 : ℝ))).2
  linarith

def supports0 : Fin 1 → ℝ := ![(1087682888914829/1125899906842624 : ℝ)]
theorem panel0_bound :
    IntervalIntegrable (fun e => 1/(e+profile e)) volume (0 : ℝ) (71223417273/1000000000000 : ℝ) ∧
      (∫ e in (0 : ℝ)..(71223417273/1000000000000 : ℝ), 1/(e+profile e)) ≤ (25383354771214569/1000000000000000000 : ℝ) := by
  have hA : (1851756268063619929/500000000000000000 : ℝ) ≤ ∑ i : Fin 1, weights i*parameters i*(Real.artanh (supports0 i)+
      CK.Profile.meanEntropy (supports0 i)/supports0 i*CK.Profile.tangentFactor (supports0 i)) := by
    have h := v039_bound.1
    norm_num [weights, parameters, supports0, Fin.sum_univ_succ, v000, v001, v002, v003, v004, v005, v006, v007, v008, v009, v010, v011, v012, v013, v014, v015, v016, v017, v018, v019, v020, v021, v022, v023, v024, v025, v026, v027, v028, v029, v030, v031, v032, v033, v034, v035, v036, v037, v038, v039, v040, v041, v042, v043] at h ⊢
    nlinarith only [h]
  have hB : (-22983142988322610059/1000000000000000000 : ℝ) ≤ 1-∑ i : Fin 1, weights i*CK.Profile.tangentFactor (supports0 i) := by
    have h := v043_bound.1
    norm_num [weights, supports0, Fin.sum_univ_succ, v000, v001, v002, v003, v004, v005, v006, v007, v008, v009, v010, v011, v012, v013, v014, v015, v016, v017, v018, v019, v020, v021, v022, v023, v024, v025, v026, v027, v028, v029, v030, v031, v032, v033, v034, v035, v036, v037, v038, v039, v040, v041, v042, v043] at h ⊢
    nlinarith only [h]
  have hlog : Real.log (((1851756268063619929/500000000000000000 : ℝ)+(-22983142988322610059/1000000000000000000 : ℝ)*(0 : ℝ))/
      ((1851756268063619929/500000000000000000 : ℝ)+(-22983142988322610059/1000000000000000000 : ℝ)*(71223417273/1000000000000 : ℝ))) ≤ (-(-22983142988322610059/1000000000000000000 : ℝ))*(25383354771214569/1000000000000000000 : ℝ) := by
    have h := LogData.log261_bound.2
    norm_num at h ⊢
    linarith
  simpa only [profile] using profile_panel_integral_bound weights parameters supports0
    weights_nonneg parameters_nonneg (by intro i; fin_cases i <;> norm_num [supports0])
    (a := (0 : ℝ)) (b := (71223417273/1000000000000 : ℝ)) (A := (1851756268063619929/500000000000000000 : ℝ)) (B := (-22983142988322610059/1000000000000000000 : ℝ)) (U := (25383354771214569/1000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA hB hlog

theorem clock_certified :
    CK.Profile.meanEntropy (487/500 : ℝ) / (487/500 : ℝ) < (71223417273/1000000000000 : ℝ) ∧
    IntervalIntegrable (fun e => 1/(e+profile e)) volume 0 (71223417273/1000000000000 : ℝ) ∧
    (∫ e in (0 : ℝ)..(71223417273/1000000000000 : ℝ), 1/(e+profile e)) + (480310284193691/1000000000000000000 : ℝ) < Real.log (1/(487/500 : ℝ)) := by
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
end CK.Certificate.ClockBatch.C16
