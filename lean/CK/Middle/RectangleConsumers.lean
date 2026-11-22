module

public import CK.Profile.RectanglePacked
public import CK.Profile.ClockPropagation
public import CK.Middle.ClockConsequences
public import CK.Middle.CubicBands
public import CK.Middle.RectangleCover

/-! Cubic energy and clock bounds on the five source rectangles numbered 14–18. Lean checks all rational endpoint data. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Middle
noncomputable section
open CK.Profile

theorem leaf14_profile_eq : CK.Certificate.ClockBatch.C24.profile = (fun e => CK.Profile.profile e (532301/800000)+(27 : ℝ)*CK.Profile.profile e (1/16)+CK.Profile.profile e (Real.sqrt (328778882521/1056000000000000))) := by
  funext e
  norm_num [CK.Certificate.ClockBatch.C24.profile,CK.Certificate.ClockBatch.C24.weights,CK.Certificate.ClockBatch.C24.parameters,CK.Certificate.ClockBatch.C24.v000,CK.Certificate.ClockBatch.C24.v001,CK.Certificate.ClockBatch.C24.v002,CK.Certificate.ClockBatch.C24.v003,CK.Certificate.ClockBatch.C24.v004,CK.Certificate.ClockBatch.C24.v005,Fin.sum_univ_succ] <;> ring

theorem mutualInformation_le_phi_leaf14 {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i j : Fin n) (hij : i ≠ j)
    (ha : fourier (lift f) {i} ∈ Icc (532301/800000 : ℝ) (228129/320000))
    (hb : fourier (lift f) {j} ∈ Icc (0 : ℝ) (1/16))
    (hsecond : ∀ l : Fin n, l ≠ i → fourier (lift f) {l} ≤ fourier (lift f) {j}) :
    mutualInformation ρ f ≤ phi ρ := by
  by_cases hW : fourierWeight (lift f) 1 ≤ (1305041145985667/2112000000000000 : ℝ)
  · apply mutualInformation_le_phi_cubic_band4 hρ f
    exact cubicWeight_le_of_harris_pair_cell (by linarith [hρ.1]) hρ.2
      (by norm_num : (1 : ℝ) ∈ Ioc 0 1) (by norm_num : (0 : ℝ)≤532301/800000)
      (by norm_num : (0 : ℝ)≤0) f hf i j hij ha.1 hb.1 hW (by norm_num [cubicBeta])
  · have hw : (1305041145985667/2112000000000000 : ℝ) ≤ fourierWeight (lift f) 1 := (lt_of_not_ge hW).le
    have hWpos : 0 < fourierWeight (lift f) 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1305041145985667/2112000000000000) hw
    have henv (e : ℝ) (he : 0 < e) : CK.Certificate.ClockBatch.C24.profile e ≤ singletonProfile f e := by
      rw [leaf14_profile_eq]
      apply rectangle_one_profile_le (k := 27) (r := (328778882521/1056000000000000 : ℝ)) (w := (1305041145985667/2112000000000000 : ℝ)) f i he (by norm_num : (0 : ℝ)≤532301/800000)
        (by norm_num : (0 : ℝ)<1/16)
        (by simpa only [abs_of_nonneg (singleton_nonneg_of_monotone hf i)] using ha)
      · intro l hli
        rw [abs_of_nonneg (singleton_nonneg_of_monotone hf l)]
        exact (hsecond l hli).trans hb.2
      · norm_num
      · norm_num
      · exact hw
    exact mutualInformation_le_phi_of_profile_clock
      (show ρ ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hρ.1],by linarith [hρ.2]⟩)
      f hWpos CK.Certificate.ClockBatch.C24.profile CK.Certificate.ClockBatch.C24.profile_continuous
      (sumProfile_antitone CK.Certificate.ClockBatch.C24.weights CK.Certificate.ClockBatch.C24.parameters CK.Certificate.ClockBatch.C24.weights_nonneg CK.Certificate.ClockBatch.C24.parameters_nonneg)
      (fun e he => sumProfile_pos CK.Certificate.ClockBatch.C24.weights CK.Certificate.ClockBatch.C24.parameters CK.Certificate.ClockBatch.C24.weights_nonneg
        CK.Certificate.ClockBatch.C24.parameters_nonneg CK.Certificate.ClockBatch.C24.positive_term he) henv
      (ClockConsequences.C24_propagated ⟨hρ.1,by linarith [hρ.2]⟩)

theorem leaf15_profile_eq : CK.Certificate.ClockBatch.C25.profile = (fun e => CK.Profile.profile e (228129/320000)+(55 : ℝ)*CK.Profile.profile e (1/32)+CK.Profile.profile e (Real.sqrt (874486208417/1013760000000000))) := by
  funext e
  norm_num [CK.Certificate.ClockBatch.C25.profile,CK.Certificate.ClockBatch.C25.weights,CK.Certificate.ClockBatch.C25.parameters,CK.Certificate.ClockBatch.C25.v000,CK.Certificate.ClockBatch.C25.v001,CK.Certificate.ClockBatch.C25.v002,CK.Certificate.ClockBatch.C25.v003,CK.Certificate.ClockBatch.C25.v004,CK.Certificate.ClockBatch.C25.v005,Fin.sum_univ_succ] <;> ring

theorem mutualInformation_le_phi_leaf15 {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i j : Fin n) (hij : i ≠ j)
    (ha : fourier (lift f) {i} ∈ Icc (228129/320000 : ℝ) (76043/100000))
    (hb : fourier (lift f) {j} ∈ Icc (0 : ℝ) (1/32))
    (hsecond : ∀ l : Fin n, l ≠ i → fourier (lift f) {l} ≤ fourier (lift f) {j}) :
    mutualInformation ρ f ≤ phi ρ := by
  by_cases hW : fourierWeight (lift f) 1 ≤ (642525043188641/1013760000000000 : ℝ)
  · apply mutualInformation_le_phi_cubic_band4 hρ f
    exact cubicWeight_le_of_harris_pair_cell (by linarith [hρ.1]) hρ.2
      (by norm_num : (1 : ℝ) ∈ Ioc 0 1) (by norm_num : (0 : ℝ)≤228129/320000)
      (by norm_num : (0 : ℝ)≤0) f hf i j hij ha.1 hb.1 hW (by norm_num [cubicBeta])
  · have hw : (642525043188641/1013760000000000 : ℝ) ≤ fourierWeight (lift f) 1 := (lt_of_not_ge hW).le
    have hWpos : 0 < fourierWeight (lift f) 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ)<642525043188641/1013760000000000) hw
    have henv (e : ℝ) (he : 0 < e) : CK.Certificate.ClockBatch.C25.profile e ≤ singletonProfile f e := by
      rw [leaf15_profile_eq]
      apply rectangle_one_profile_le (k := 55) (r := (874486208417/1013760000000000 : ℝ)) (w := (642525043188641/1013760000000000 : ℝ)) f i he (by norm_num : (0 : ℝ)≤228129/320000)
        (by norm_num : (0 : ℝ)<1/32)
        (by simpa only [abs_of_nonneg (singleton_nonneg_of_monotone hf i)] using ha)
      · intro l hli
        rw [abs_of_nonneg (singleton_nonneg_of_monotone hf l)]
        exact (hsecond l hli).trans hb.2
      · norm_num
      · norm_num
      · exact hw
    exact mutualInformation_le_phi_of_profile_clock
      (show ρ ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hρ.1],by linarith [hρ.2]⟩)
      f hWpos CK.Certificate.ClockBatch.C25.profile CK.Certificate.ClockBatch.C25.profile_continuous
      (sumProfile_antitone CK.Certificate.ClockBatch.C25.weights CK.Certificate.ClockBatch.C25.parameters CK.Certificate.ClockBatch.C25.weights_nonneg CK.Certificate.ClockBatch.C25.parameters_nonneg)
      (fun e he => sumProfile_pos CK.Certificate.ClockBatch.C25.weights CK.Certificate.ClockBatch.C25.parameters CK.Certificate.ClockBatch.C25.weights_nonneg
        CK.Certificate.ClockBatch.C25.parameters_nonneg CK.Certificate.ClockBatch.C25.positive_term he) henv
      (ClockConsequences.C25_propagated ⟨hρ.1,by linarith [hρ.2]⟩)

theorem leaf16_profile_eq : CK.Certificate.ClockBatch.C26.profile = (fun e => CK.Profile.profile e (228129/320000)+CK.Profile.profile e (1/32)+(22 : ℝ)*CK.Profile.profile e (1/16)+CK.Profile.profile e (Real.sqrt (130017477263/101376000000000))) := by
  funext e
  norm_num [CK.Certificate.ClockBatch.C26.profile,CK.Certificate.ClockBatch.C26.weights,CK.Certificate.ClockBatch.C26.parameters,CK.Certificate.ClockBatch.C26.v000,CK.Certificate.ClockBatch.C26.v001,CK.Certificate.ClockBatch.C26.v002,CK.Certificate.ClockBatch.C26.v003,CK.Certificate.ClockBatch.C26.v004,CK.Certificate.ClockBatch.C26.v005,CK.Certificate.ClockBatch.C26.v006,CK.Certificate.ClockBatch.C26.v007,Fin.sum_univ_succ] <;> ring

theorem mutualInformation_le_phi_leaf16 {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i j : Fin n) (hij : i ≠ j)
    (ha : fourier (lift f) {i} ∈ Icc (228129/320000 : ℝ) (2357333/3200000))
    (hb : fourier (lift f) {j} ∈ Icc (1/32 : ℝ) (1/16))
    (hsecond : ∀ l : Fin n, l ≠ i → fourier (lift f) {l} ≤ fourier (lift f) {j}) :
    mutualInformation ρ f ≤ phi ρ := by
  by_cases hW : fourierWeight (lift f) 1 ≤ (642525043188641/1013760000000000 : ℝ)
  · apply mutualInformation_le_phi_cubic_band4 hρ f
    exact cubicWeight_le_of_harris_pair_cell (by linarith [hρ.1]) hρ.2
      (by norm_num : (1 : ℝ) ∈ Ioc 0 1) (by norm_num : (0 : ℝ)≤228129/320000)
      (by norm_num : (0 : ℝ)≤1/32) f hf i j hij ha.1 hb.1 hW (by norm_num [cubicBeta])
  · have hw : (642525043188641/1013760000000000 : ℝ) ≤ fourierWeight (lift f) 1 := (lt_of_not_ge hW).le
    have hWpos : 0 < fourierWeight (lift f) 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ)<642525043188641/1013760000000000) hw
    have henv (e : ℝ) (he : 0 < e) : CK.Certificate.ClockBatch.C26.profile e ≤ singletonProfile f e := by
      rw [leaf16_profile_eq]
      apply rectangle_two_profile_le (k := 22) (r := (130017477263/101376000000000 : ℝ)) (w := (642525043188641/1013760000000000 : ℝ)) f i j hij he (by norm_num : (0 : ℝ)≤228129/320000)
        (by norm_num : (0 : ℝ)≤1/32) (by norm_num : (0 : ℝ)<1/16)
        (by simpa only [abs_of_nonneg (singleton_nonneg_of_monotone hf i)] using ha)
        (by simpa only [abs_of_nonneg (singleton_nonneg_of_monotone hf j)] using hb)
      · intro l hli hlj
        rw [abs_of_nonneg (singleton_nonneg_of_monotone hf l)]
        exact (hsecond l hli).trans hb.2
      · norm_num
      · norm_num
      · exact hw
    exact mutualInformation_le_phi_of_profile_clock
      (show ρ ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hρ.1],by linarith [hρ.2]⟩)
      f hWpos CK.Certificate.ClockBatch.C26.profile CK.Certificate.ClockBatch.C26.profile_continuous
      (sumProfile_antitone CK.Certificate.ClockBatch.C26.weights CK.Certificate.ClockBatch.C26.parameters CK.Certificate.ClockBatch.C26.weights_nonneg CK.Certificate.ClockBatch.C26.parameters_nonneg)
      (fun e he => sumProfile_pos CK.Certificate.ClockBatch.C26.weights CK.Certificate.ClockBatch.C26.parameters CK.Certificate.ClockBatch.C26.weights_nonneg
        CK.Certificate.ClockBatch.C26.parameters_nonneg CK.Certificate.ClockBatch.C26.positive_term he) henv
      (ClockConsequences.C26_propagated ⟨hρ.1,by linarith [hρ.2]⟩)

theorem leaf17_profile_eq : CK.Certificate.ClockBatch.C27.profile = (fun e => CK.Profile.profile e (2357333/3200000)+CK.Profile.profile e (1/32)+(15 : ℝ)*CK.Profile.profile e (1/16)+CK.Profile.profile e (Real.sqrt (4132962083037518531/2167782064513125000000))) := by
  funext e
  norm_num [CK.Certificate.ClockBatch.C27.profile,CK.Certificate.ClockBatch.C27.weights,CK.Certificate.ClockBatch.C27.parameters,CK.Certificate.ClockBatch.C27.v000,CK.Certificate.ClockBatch.C27.v001,CK.Certificate.ClockBatch.C27.v002,CK.Certificate.ClockBatch.C27.v003,CK.Certificate.ClockBatch.C27.v004,CK.Certificate.ClockBatch.C27.v005,CK.Certificate.ClockBatch.C27.v006,CK.Certificate.ClockBatch.C27.v007,Fin.sum_univ_succ] <;> ring

theorem mutualInformation_le_phi_leaf17 {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i j : Fin n) (hij : i ≠ j)
    (ha : fourier (lift f) {i} ∈ Icc (2357333/3200000 : ℝ) (76043/100000))
    (hb : fourier (lift f) {j} ∈ Icc (1/32 : ℝ) (1/16))
    (hsecond : ∀ l : Fin n, l ≠ i → fourier (lift f) {l} ≤ fourier (lift f) {j}) :
    mutualInformation ρ f ≤ phi ρ := by
  by_cases hW : fourierWeight (lift f) 1 ≤ (35664576633808853453/55495220851536000000 : ℝ)
  · apply mutualInformation_le_phi_cubic_band4 hρ f
    exact cubicWeight_le_of_harris_pair_cell (by linarith [hρ.1]) hρ.2
      (by norm_num : (17473/20000 : ℝ) ∈ Ioc 0 1) (by norm_num : (0 : ℝ)≤2357333/3200000)
      (by norm_num : (0 : ℝ)≤1/32) f hf i j hij ha.1 hb.1 hW (by norm_num [cubicBeta])
  · have hw : (35664576633808853453/55495220851536000000 : ℝ) ≤ fourierWeight (lift f) 1 := (lt_of_not_ge hW).le
    have hWpos : 0 < fourierWeight (lift f) 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ)<35664576633808853453/55495220851536000000) hw
    have henv (e : ℝ) (he : 0 < e) : CK.Certificate.ClockBatch.C27.profile e ≤ singletonProfile f e := by
      rw [leaf17_profile_eq]
      apply rectangle_two_profile_le (k := 15) (r := (4132962083037518531/2167782064513125000000 : ℝ)) (w := (35664576633808853453/55495220851536000000 : ℝ)) f i j hij he (by norm_num : (0 : ℝ)≤2357333/3200000)
        (by norm_num : (0 : ℝ)≤1/32) (by norm_num : (0 : ℝ)<1/16)
        (by simpa only [abs_of_nonneg (singleton_nonneg_of_monotone hf i)] using ha)
        (by simpa only [abs_of_nonneg (singleton_nonneg_of_monotone hf j)] using hb)
      · intro l hli hlj
        rw [abs_of_nonneg (singleton_nonneg_of_monotone hf l)]
        exact (hsecond l hli).trans hb.2
      · norm_num
      · norm_num
      · exact hw
    exact mutualInformation_le_phi_of_profile_clock
      (show ρ ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hρ.1],by linarith [hρ.2]⟩)
      f hWpos CK.Certificate.ClockBatch.C27.profile CK.Certificate.ClockBatch.C27.profile_continuous
      (sumProfile_antitone CK.Certificate.ClockBatch.C27.weights CK.Certificate.ClockBatch.C27.parameters CK.Certificate.ClockBatch.C27.weights_nonneg CK.Certificate.ClockBatch.C27.parameters_nonneg)
      (fun e he => sumProfile_pos CK.Certificate.ClockBatch.C27.weights CK.Certificate.ClockBatch.C27.parameters CK.Certificate.ClockBatch.C27.weights_nonneg
        CK.Certificate.ClockBatch.C27.parameters_nonneg CK.Certificate.ClockBatch.C27.positive_term he) henv
      (ClockConsequences.C27_propagated ⟨hρ.1,by linarith [hρ.2]⟩)

theorem leaf18_profile_eq : CK.Certificate.ClockBatch.C28.profile = (fun e => CK.Profile.profile e (532301/800000)+CK.Profile.profile e (1/16)+(6 : ℝ)*CK.Profile.profile e (1/8)+CK.Profile.profile e (Real.sqrt (328778882521/1056000000000000))) := by
  funext e
  norm_num [CK.Certificate.ClockBatch.C28.profile,CK.Certificate.ClockBatch.C28.weights,CK.Certificate.ClockBatch.C28.parameters,CK.Certificate.ClockBatch.C28.v000,CK.Certificate.ClockBatch.C28.v001,CK.Certificate.ClockBatch.C28.v002,CK.Certificate.ClockBatch.C28.v003,CK.Certificate.ClockBatch.C28.v004,CK.Certificate.ClockBatch.C28.v005,CK.Certificate.ClockBatch.C28.v006,CK.Certificate.ClockBatch.C28.v007,Fin.sum_univ_succ] <;> ring

theorem mutualInformation_le_phi_leaf18 {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i j : Fin n) (hij : i ≠ j)
    (ha : fourier (lift f) {i} ∈ Icc (532301/800000 : ℝ) (228129/320000))
    (hb : fourier (lift f) {j} ∈ Icc (1/16 : ℝ) (1/8))
    (hsecond : ∀ l : Fin n, l ≠ i → fourier (lift f) {l} ≤ fourier (lift f) {j}) :
    mutualInformation ρ f ≤ phi ρ := by
  by_cases hW : fourierWeight (lift f) 1 ≤ (1305041145985667/2112000000000000 : ℝ)
  · apply mutualInformation_le_phi_cubic_band4 hρ f
    exact cubicWeight_le_of_harris_pair_cell (by linarith [hρ.1]) hρ.2
      (by norm_num : (1 : ℝ) ∈ Ioc 0 1) (by norm_num : (0 : ℝ)≤532301/800000)
      (by norm_num : (0 : ℝ)≤1/16) f hf i j hij ha.1 hb.1 hW (by norm_num [cubicBeta])
  · have hw : (1305041145985667/2112000000000000 : ℝ) ≤ fourierWeight (lift f) 1 := (lt_of_not_ge hW).le
    have hWpos : 0 < fourierWeight (lift f) 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1305041145985667/2112000000000000) hw
    have henv (e : ℝ) (he : 0 < e) : CK.Certificate.ClockBatch.C28.profile e ≤ singletonProfile f e := by
      rw [leaf18_profile_eq]
      apply rectangle_two_profile_le (k := 6) (r := (328778882521/1056000000000000 : ℝ)) (w := (1305041145985667/2112000000000000 : ℝ)) f i j hij he (by norm_num : (0 : ℝ)≤532301/800000)
        (by norm_num : (0 : ℝ)≤1/16) (by norm_num : (0 : ℝ)<1/8)
        (by simpa only [abs_of_nonneg (singleton_nonneg_of_monotone hf i)] using ha)
        (by simpa only [abs_of_nonneg (singleton_nonneg_of_monotone hf j)] using hb)
      · intro l hli hlj
        rw [abs_of_nonneg (singleton_nonneg_of_monotone hf l)]
        exact (hsecond l hli).trans hb.2
      · norm_num
      · norm_num
      · exact hw
    exact mutualInformation_le_phi_of_profile_clock
      (show ρ ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hρ.1],by linarith [hρ.2]⟩)
      f hWpos CK.Certificate.ClockBatch.C28.profile CK.Certificate.ClockBatch.C28.profile_continuous
      (sumProfile_antitone CK.Certificate.ClockBatch.C28.weights CK.Certificate.ClockBatch.C28.parameters CK.Certificate.ClockBatch.C28.weights_nonneg CK.Certificate.ClockBatch.C28.parameters_nonneg)
      (fun e he => sumProfile_pos CK.Certificate.ClockBatch.C28.weights CK.Certificate.ClockBatch.C28.parameters CK.Certificate.ClockBatch.C28.weights_nonneg
        CK.Certificate.ClockBatch.C28.parameters_nonneg CK.Certificate.ClockBatch.C28.positive_term he) henv
      (ClockConsequences.C28_propagated ⟨hρ.1,by linarith [hρ.2]⟩)

end
end CK.Middle
