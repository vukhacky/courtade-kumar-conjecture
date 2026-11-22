module

public import CK.Profile.ClockDynamics
public import CK.Profile.Ratio
public import CK.Functional.SignEntropy

/-! The source profile height, defined through the proved unique entropy
profile root. These identities share one entropy-production budget across
all coordinates; zero coefficients are included explicitly. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Set
namespace CK
noncomputable section

def edgeHeight (e q : ℝ) : ℝ := Real.artanh (Profile.profilePoint e q)
def profileHeight (ρ a : ℝ) : ℝ := edgeHeight (signEntropy ρ) (ρ*a)
def profileCoefficient (ρ v : ℝ) : ℝ :=
  signEntropy ρ*Real.tanh v/(ρ*signEntropy (Real.tanh v))

@[simp] theorem edgeHeight_zero (e : ℝ) : edgeHeight e 0 = 0 := by
  simp [edgeHeight,Profile.profilePoint]

@[simp] theorem profileHeight_zero (ρ : ℝ) : profileHeight ρ 0 = 0 := by
  simp [profileHeight]

theorem edgeHeight_pos {e q : ℝ} (he : 0 < e) (hq : 0 < q) : 0 < edgeHeight e q :=
  Real.artanh_pos (Profile.profilePoint_spec he hq).1

theorem edgeHeight_nonneg {e q : ℝ} (he : 0 < e) (hq : 0 ≤ q) : 0 ≤ edgeHeight e q := by
  rcases hq.eq_or_lt with rfl | hq
  · simp
  · exact (edgeHeight_pos he hq).le

theorem edgeHeight_mono_right {e a b : ℝ} (he : 0 < e) (ha : 0 ≤ a) (hab : a ≤ b) :
    edgeHeight e a ≤ edgeHeight e b := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using edgeHeight_nonneg he hab
  have hb : 0 < b := ha.trans_le hab
  have hpa := (Profile.profilePoint_spec he ha).1
  have hpb := (Profile.profilePoint_spec he hb).1
  exact Real.artanh_le_artanh (by linarith [hpa.1]) hpb.2
    (Profile.profilePoint_mono_right he ha hb hab)

theorem edgeHeight_antitone_left {e d q : ℝ} (he : 0 < e) (hed : e ≤ d) (hq : 0 ≤ q) :
    edgeHeight d q ≤ edgeHeight e q := by
  rcases hq.eq_or_lt with rfl | hq
  · simp
  have hd : 0 < d := he.trans_le hed
  have hpe := (Profile.profilePoint_spec he hq).1
  have hpd := (Profile.profilePoint_spec hd hq).1
  exact Real.artanh_le_artanh (by linarith [hpd.1]) hpe.2
    (Profile.profilePoint_antitone hq he hd hed)

theorem profile_eq_mul_edgeHeight (e q : ℝ) : Profile.profile e q=q*edgeHeight e q := rfl

theorem profileHeight_nonneg {ρ a : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (ha : 0 ≤ a) :
    0 ≤ profileHeight ρ a :=
  edgeHeight_nonneg (Profile.meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩) (mul_nonneg hρ.1.le ha)

theorem profileHeight_mono {ρ a b : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (ha : 0 ≤ a) (hab : a ≤ b) : profileHeight ρ a ≤ profileHeight ρ b :=
  edgeHeight_mono_right (Profile.meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩)
    (mul_nonneg hρ.1.le ha) (mul_le_mul_of_nonneg_left hab hρ.1.le)

theorem profileHeight_one {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    profileHeight ρ 1 = Real.artanh ρ := by
  have he : 0 < signEntropy ρ := Profile.meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩
  have h := Profile.profilePoint_unique he hρ.1 hρ (by change signEntropy ρ*ρ=ρ*signEntropy ρ; ring)
  simp only [profileHeight,mul_one,edgeHeight,←h]

theorem profileHeight_le_artanh {ρ a : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) : profileHeight ρ a ≤ Real.artanh ρ := by
  rw [← profileHeight_one hρ]
  exact profileHeight_mono hρ ha.1 ha.2

theorem profile_eq_height (ρ a : ℝ) :
    Profile.profile (signEntropy ρ) (ρ*a)=ρ*a*profileHeight ρ a := rfl

theorem profileHeight_root {ρ a : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    signEntropy ρ*Real.tanh (profileHeight ρ a) =
      ρ*a*signEntropy (Real.tanh (profileHeight ρ a)) := by
  have he : 0 < signEntropy ρ := Profile.meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩
  have h := Profile.profilePoint_spec he (mul_pos hρ.1 ha)
  unfold profileHeight edgeHeight
  rw [Real.tanh_artanh ⟨by linarith [h.1.1],h.1.2⟩]
  exact h.2

theorem profileHeight_ratio_eq {ρ a : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    profileHeight ρ a/a = (ρ/signEntropy ρ)*
      Profile.scaledProfile (Profile.profilePoint (signEntropy ρ) (ρ*a)) := by
  have he : 0 < signEntropy ρ := Profile.meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩
  have h := Profile.profilePoint_spec he (mul_pos hρ.1 ha)
  unfold profileHeight edgeHeight Profile.scaledProfile
  rw [phiSlope_eq_artanh ⟨by linarith [h.1.1],h.1.2⟩]
  field_simp [ha.ne',he.ne',h.1.1.ne']
  nlinarith only [congrArg (fun z : ℝ => z*Real.artanh (Profile.profilePoint (signEntropy ρ) (ρ*a))) h.2]

theorem profileHeight_ratio_antitone {ρ a b : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (ha : 0 < a) (hab : a ≤ b) : profileHeight ρ b/b ≤ profileHeight ρ a/a := by
  have hb : 0 < b := ha.trans_le hab
  have he : 0 < signEntropy ρ := Profile.meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩
  have hpa := (Profile.profilePoint_spec he (mul_pos hρ.1 ha)).1
  have hpb := (Profile.profilePoint_spec he (mul_pos hρ.1 hb)).1
  have hmono := Profile.profilePoint_mono_right he (mul_pos hρ.1 ha) (mul_pos hρ.1 hb)
    (mul_le_mul_of_nonneg_left hab hρ.1.le)
  rw [profileHeight_ratio_eq hρ hb,profileHeight_ratio_eq hρ ha]
  exact mul_le_mul_of_nonneg_left (Profile.scaledProfile_antitone hpa hpb hmono)
    (div_nonneg hρ.1.le he.le)

theorem profileCoefficient_pos {ρ v : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    0 < profileCoefficient ρ v := by
  have ht : 0 < Real.tanh v := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hv) (Real.cosh_pos v)
  exact div_pos (mul_pos (Profile.meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩) ht)
    (mul_pos hρ.1 (Profile.meanEntropy_pos ⟨Real.neg_one_lt_tanh v,Real.tanh_lt_one v⟩))

theorem profileHeight_profileCoefficient {ρ v : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    profileHeight ρ (profileCoefficient ρ v) = v := by
  have ht : Real.tanh v ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨?_,Real.tanh_lt_one v⟩
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hv) (Real.cosh_pos v)
  have he : 0 < signEntropy ρ := Profile.meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩
  have hH : 0 < signEntropy (Real.tanh v) := Profile.meanEntropy_pos ⟨Real.neg_one_lt_tanh v,ht.2⟩
  have hq := mul_pos hρ.1 (profileCoefficient_pos hρ hv)
  have hp := Profile.profilePoint_unique he hq ht (by
    change signEntropy ρ*Real.tanh v=ρ*profileCoefficient ρ v*signEntropy (Real.tanh v)
    unfold profileCoefficient
    field_simp [hρ.1.ne',hH.ne'])
  unfold profileHeight edgeHeight
  rw [←hp,Real.artanh_tanh]

theorem conditionalEntropy_lt_of_positive_gap {n : ℕ} {ρ : ℝ} (f : BooleanFunction n)
    (hgap : 0 < informationGap ρ f) : conditionalEntropy ρ f < signEntropy ρ := by
  have hphi := sq_div_two_le_phi (mean_mem_Icc f)
  have hid : informationGap ρ f = signEntropy ρ-conditionalEntropy ρ f-phi (mean f) := by
    unfold informationGap
    rw [information_eq_signEntropy_sub_posterior,signEntropy_eq_log_two_sub_phi,
      signEntropy_eq_log_two_sub_phi]
    change Real.log 2-phi (mean f)-conditionalEntropy ρ f-phi ρ = _
    ring
  rw [hid] at hgap
  nlinarith only [hgap,hphi,sq_nonneg (mean f)]

/-- The common production budget used by all retained/discarded coordinates. -/
theorem profileHeight_common_budget {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v) (hgap : 0 < informationGap ρ f) :
    (∑ i : Fin n, |fourier (lift f) {i}| *profileHeight ρ |fourier (lift f) {i}|) ≤
      entropyProduction (noise ρ (lift f))/ρ := by
  have hE := Profile.conditionalEntropy_pos hρ f hf
  have hH : 0 < signEntropy ρ := Profile.meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩
  have hEH := conditionalEntropy_lt_of_positive_gap f hgap
  have hprofile := Profile.entropyProduction_noise_ge_profile hρ f hf
  have hsum : (∑ i : Fin n, Profile.profile (signEntropy ρ) (ρ*|fourier (lift f) {i}|)) ≤
      ∑ i : Fin n, Profile.profile (conditionalEntropy ρ f) (ρ*|fourier (lift f) {i}|) := by
    apply Finset.sum_le_sum
    intro i _
    rcases (abs_nonneg (fourier (lift f) {i})).eq_or_lt with heq | hpos
    · rw [←heq,mul_zero,Profile.profile_zero_right,Profile.profile_zero_right]
    · exact Profile.profile_antitone (mul_pos hρ.1 hpos) hE hH hEH.le
  have h := hsum.trans hprofile
  simp only [profile_eq_height] at h
  have hid : (∑ i : Fin n, ρ*|fourier (lift f) {i}| *profileHeight ρ |fourier (lift f) {i}|) =
      ρ*(∑ i : Fin n, |fourier (lift f) {i}| *profileHeight ρ |fourier (lift f) {i}|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid] at h
  apply (le_div_iff₀ hρ.1).mpr
  nlinarith only [h]

theorem profileHeight_strictMono {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    StrictMonoOn (profileHeight ρ) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  rcases ha.eq_or_lt with rfl | ha
  · rw [profileHeight_zero]
    exact edgeHeight_pos (Profile.meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩) (mul_pos hρ.1 hab)
  have hb0 : 0 < b := ha.trans hab
  have he : 0 < signEntropy ρ := Profile.meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩
  have hpa := Profile.profilePoint_spec he (mul_pos hρ.1 ha)
  have hpb := Profile.profilePoint_spec he (mul_pos hρ.1 hb0)
  have hpmono := Profile.profilePoint_mono_right he (mul_pos hρ.1 ha) (mul_pos hρ.1 hb0)
    (mul_le_mul_of_nonneg_left hab.le hρ.1.le)
  have hpne : Profile.profilePoint (signEntropy ρ) (ρ*a) ≠ Profile.profilePoint (signEntropy ρ) (ρ*b) := by
    intro hEq
    rw [hEq] at hpa
    have hh : 0 < Profile.meanEntropy (Profile.profilePoint (signEntropy ρ) (ρ*b)) :=
      Profile.meanEntropy_pos ⟨by linarith [hpb.1.1],hpb.1.2⟩
    have hprod := mul_pos (mul_pos hρ.1 (sub_pos.mpr hab)) hh
    nlinarith only [hpa.2,hpb.2,hprod]
  exact Real.artanh_lt_artanh (by linarith [hpa.1.1]) hpb.1.2 (lt_of_le_of_ne hpmono hpne)

theorem profileHeight_le_iff {ρ a b : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : profileHeight ρ a ≤ profileHeight ρ b ↔ a ≤ b :=
  (profileHeight_strictMono hρ).le_iff_le ha hb

theorem profileCoefficient_le_one {ρ v : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hv : 0 < v) (hvu : v ≤ Real.artanh ρ) : profileCoefficient ρ v ≤ 1 := by
  apply (profileHeight_le_iff hρ (profileCoefficient_pos hρ hv).le (by norm_num)).mp
  rw [profileHeight_profileCoefficient hρ hv,profileHeight_one hρ]
  exact hvu

theorem profileHeight_cutoff_iff {ρ v a : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hv : 0 < v) (ha : 0 ≤ a) : v ≤ profileHeight ρ a ↔ profileCoefficient ρ v ≤ a := by
  have h := profileHeight_le_iff hρ (profileCoefficient_pos hρ hv).le ha
  rw [profileHeight_profileCoefficient hρ hv] at h
  exact h

end
end CK
