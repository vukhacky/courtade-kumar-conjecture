module

public import CK.Analysis.BinaryEntropy
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity

/-! The entropy profile is defined by the unique positive root of its scalar equation. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

def meanEntropy (t : ℝ) : ℝ := Real.binEntropy ((1-t)/2)

@[simp] theorem meanEntropy_zero : meanEntropy 0 = Real.log 2 := by
  simpa only [meanEntropy, sub_zero, one_div] using Real.binEntropy_two_inv

@[simp] theorem meanEntropy_one : meanEntropy 1 = 0 := by simp [meanEntropy]

@[fun_prop] theorem continuous_meanEntropy : Continuous meanEntropy := by
  unfold meanEntropy
  fun_prop

theorem meanEntropy_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 < meanEntropy t := by
  apply Real.binEntropy_pos <;> linarith [ht.1, ht.2]

theorem meanEntropy_nonneg {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    0 ≤ meanEntropy t := by
  apply Real.binEntropy_nonneg <;> linarith [ht.1, ht.2]

theorem strictAntiOn_meanEntropy : StrictAntiOn meanEntropy (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  apply Real.binEntropy_strictMonoOn
  · constructor <;> linarith [hy.1, hy.2]
  · constructor <;> linarith [hx.1, hx.2]
  · linarith

theorem hasDerivAt_meanEntropy {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt meanEntropy (-phiSlope t) t := by
  have h := (hasDerivAt_phi ht).const_sub (Real.log 2)
  have hf : (fun x => Real.log 2 - phi x) = meanEntropy := by
    funext x
    simp [phi, meanEntropy]
  rw [hf] at h
  exact h

theorem exists_unique_profilePoint {e q : ℝ} (he : 0 < e) (hq : 0 < q) :
    ∃! t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧ e*t = q*meanEntropy t := by
  let G : ℝ → ℝ := fun t => e*t - q*meanEntropy t
  have hc : Continuous G := by dsimp [G]; fun_prop
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hleft : G 0 < 0 := by dsimp [G]; simp only [mul_zero, meanEntropy_zero]; nlinarith
  have hright : 0 < G 1 := by simpa [G] using he
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hc.continuousOn (show (0 : ℝ) ∈ Icc (G 0) (G 1) from ⟨hleft.le, hright.le⟩)
  have ht0 : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro h
    have : G 0 = 0 := by simpa [← h] using hzero
    linarith
  have ht1 : t < 1 := by
    apply lt_of_le_of_ne ht.2
    intro h
    have : G 1 = 0 := by simpa [h] using hzero
    linarith
  have heq : e*t = q*meanEntropy t := by dsimp [G] at hzero; linarith
  refine ⟨t, ⟨⟨ht0, ht1⟩, heq⟩, ?_⟩
  intro s hs
  rcases lt_trichotomy s t with hst | hst | hts
  · have hh := strictAntiOn_meanEntropy ⟨hs.1.1.le, hs.1.2.le⟩ ⟨ht0.le, ht1.le⟩ hst
    nlinarith [hs.2]
  · exact hst
  · have hh := strictAntiOn_meanEntropy ⟨ht0.le, ht1.le⟩ ⟨hs.1.1.le, hs.1.2.le⟩ hts
    nlinarith [hs.2]

def profilePoint (e q : ℝ) : ℝ :=
  if h : 0 < e ∧ 0 < q then Classical.choose (exists_unique_profilePoint h.1 h.2) else 0

theorem profilePoint_spec {e q : ℝ} (he : 0 < e) (hq : 0 < q) :
    profilePoint e q ∈ Ioo (0 : ℝ) 1 ∧ e*profilePoint e q = q*meanEntropy (profilePoint e q) := by
  unfold profilePoint
  rw [dite_eq_left ⟨he, hq⟩]
  exact (Classical.choose_spec (exists_unique_profilePoint he hq)).1

theorem profilePoint_unique {e q t : ℝ} (he : 0 < e) (hq : 0 < q)
    (ht : t ∈ Ioo (0 : ℝ) 1) (heq : e*t = q*meanEntropy t) :
    t = profilePoint e q := by
  unfold profilePoint
  rw [dite_eq_left ⟨he, hq⟩]
  exact (Classical.choose_spec (exists_unique_profilePoint he hq)).2 t ⟨ht, heq⟩

def profile (e q : ℝ) : ℝ := q * Real.artanh (profilePoint e q)

@[simp] theorem profile_zero_right (e : ℝ) : profile e 0 = 0 := by simp [profile]

@[simp] theorem profile_zero_left (q : ℝ) : profile 0 q = 0 := by
  simp [profile, profilePoint]

theorem profile_pos {e q : ℝ} (he : 0 < e) (hq : 0 < q) : 0 < profile e q :=
  mul_pos hq (Real.artanh_pos (profilePoint_spec he hq).1)

theorem profilePoint_antitone {q : ℝ} (hq : 0 < q) :
    AntitoneOn (fun e => profilePoint e q) (Ioi (0 : ℝ)) := by
  intro e he d hd hed
  have hs := profilePoint_spec he hq
  have ht := profilePoint_spec hd hq
  by_contra hn
  have hlt : profilePoint e q < profilePoint d q := lt_of_not_ge hn
  have hh := strictAntiOn_meanEntropy ⟨hs.1.1.le, hs.1.2.le⟩
    ⟨ht.1.1.le, ht.1.2.le⟩ hlt
  have hmul := mul_le_mul_of_nonneg_right hed ht.1.1.le
  have hhq := mul_lt_mul_of_pos_left hh hq
  have her := mul_lt_mul_of_pos_left hlt (show 0 < e from he)
  linarith [hs.2, ht.2]

theorem profile_antitone {q : ℝ} (hq : 0 < q) :
    AntitoneOn (fun e => profile e q) (Ioi (0 : ℝ)) := by
  intro e he d hd hed
  have hs := profilePoint_spec he hq
  have ht := profilePoint_spec hd hq
  apply mul_le_mul_of_nonneg_left _ hq.le
  exact Real.artanh_le_artanh (by linarith [ht.1.1]) hs.1.2
    (profilePoint_antitone hq he hd hed)

theorem neg_profilePoint_image {q : ℝ} (hq : 0 < q) :
    (fun e => -profilePoint e q) '' Ioi (0 : ℝ) = Ioo (-1 : ℝ) 0 := by
  ext y
  constructor
  · rintro ⟨e, he, rfl⟩
    have hs := (profilePoint_spec he hq).1
    constructor <;> linarith [hs.1, hs.2]
  · intro hy
    have ht : -y ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hy.1, hy.2]
    let e := q * meanEntropy (-y) / (-y)
    have he : 0 < e := div_pos (mul_pos hq
      (meanEntropy_pos ⟨by linarith [ht.1], ht.2⟩)) ht.1
    have hroot : -y = profilePoint e q := by
      apply profilePoint_unique he hq ht
      dsimp [e]
      exact div_mul_cancel₀ _ (ne_of_gt ht.1)
    refine ⟨e, he, ?_⟩
    change -profilePoint e q = y
    rw [← hroot]
    ring

theorem continuousAt_profilePoint {e q : ℝ} (he : 0 < e) (hq : 0 < q) :
    ContinuousAt (fun d => profilePoint d q) e := by
  have hm : MonotoneOn (fun d => -profilePoint d q) (Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    exact neg_le_neg (profilePoint_antitone hq ha hb hab)
  have hn : ContinuousAt (fun d => -profilePoint d q) e := by
    apply continuousAt_of_monotoneOn_of_image_mem_nhds hm (Ioi_mem_nhds he)
    rw [neg_profilePoint_image hq]
    have hs := (profilePoint_spec he hq).1
    exact Ioo_mem_nhds (by linarith [hs.2]) (by linarith [hs.1])
  have hf : (fun d => profilePoint d q) = -(fun d => -profilePoint d q) := by
    funext d
    exact (neg_neg (profilePoint d q)).symm
  rw [hf]
  exact hn.neg

theorem continuousOn_profile {q : ℝ} (hq : 0 < q) :
    ContinuousOn (fun e => profile e q) (Ioi (0 : ℝ)) := by
  have hc : ContinuousOn (fun e => q * phiSlope (profilePoint e q)) (Ioi (0 : ℝ)) := by
    intro e he
    have hs := (profilePoint_spec he hq).1
    have hp : ContinuousAt (fun d => phiSlope (profilePoint d q)) e :=
      ContinuousAt.comp (f := fun d => profilePoint d q)
        (hasDerivAt_phiSlope ⟨by linarith [hs.1], hs.2⟩).continuousAt
        (continuousAt_profilePoint he hq)
    exact (continuousAt_const.mul hp).continuousWithinAt
  apply hc.congr
  intro e he
  have hs := (profilePoint_spec he hq).1
  change q * Real.artanh (profilePoint e q) = q * phiSlope (profilePoint e q)
  rw [phiSlope_eq_artanh ⟨by linarith [hs.1], hs.2⟩]

end
end CK.Profile
