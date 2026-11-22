module

public import CK.Profile.CGNAlgebra

/-! CGN scalar edge entropy inequality, in the exact sign-valued
normalization used in STOC `lem:edge-entropy-profile`. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

theorem profilePoint_le_of_root_inequality {e q t : ℝ} (he : 0 < e) (hq : 0 < q)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hineq : q*meanEntropy t ≤ e*t) :
    profilePoint e q ≤ t := by
  have hs := profilePoint_spec he hq
  by_contra h
  have hlt := lt_of_not_ge h
  have hH := strictAntiOn_meanEntropy ⟨ht.1.le, ht.2.le⟩ ⟨hs.1.1.le, hs.1.2.le⟩ hlt
  have hqH := mul_lt_mul_of_pos_left hH hq
  have het := mul_lt_mul_of_pos_left hlt he
  linarith only [hineq, hs.2, hqH, het]

theorem profile_le_of_root_inequality {e q t : ℝ} (he : 0 < e) (hq : 0 < q)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hineq : q*meanEntropy t ≤ e*t) :
    profile e q ≤ q*Real.artanh t := by
  have hs := (profilePoint_spec he hq).1
  exact mul_le_mul_of_nonneg_left
    (Real.artanh_le_artanh (by linarith [hs.1]) ht.2
      (profilePoint_le_of_root_inequality he hq ht hineq)) hq.le

theorem edge_odds_ordered {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    profile ((meanEntropy (oddsSign a)+meanEntropy (oddsSign b))/2)
      ((oddsSign a-oddsSign b)/2) ≤
    (oddsSign a-oddsSign b)*(Real.artanh (oddsSign a)-Real.artanh (oddsSign b))/4 := by
  let D := (1+a^2)*(1+b^2)
  let e := (meanEntropy (oddsSign a)+meanEntropy (oddsSign b))/2
  let d := (oddsSign a-oddsSign b)/2
  let t := (a-b)/(a+b)
  have hD : 0 < D := by dsimp [D]; positivity
  have hsum : 0 < a+b := add_pos ha hb
  have hd : d = (a-b)*(a+b)/D := by
    dsimp [d, oddsSign, D]
    field_simp
    ring
  have hdpos : 0 < d := by rw [hd]; exact div_pos (mul_pos (sub_pos.mpr hba) hsum) hD
  have he : 0 < e := div_pos
    (add_pos (meanEntropy_pos (oddsSign_mem ha)) (meanEntropy_pos (oddsSign_mem hb))) (by norm_num)
  have ht : t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr hba) hsum
    · apply (div_lt_iff₀ hsum).2; linarith
  have hnum : (a+b)^2*meanEntropy t ≤ D*e := by
    have h := odds_entropy_comparison ha hb
    change 2*(a+b)^2*meanEntropy t ≤ D*(meanEntropy (oddsSign a)+meanEntropy (oddsSign b)) at h
    dsimp [e]
    linarith only [h]
  have hroot : d*meanEntropy t ≤ e*t := by
    calc
      _ = ((a-b)/(a+b)/D)*((a+b)^2*meanEntropy t) := by
        rw [hd]
        field_simp
      _ ≤ ((a-b)/(a+b)/D)*(D*e) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = e*t := by
        dsimp [t]
        field_simp
  have h := profile_le_of_root_inequality he hdpos ht hroot
  change profile e d ≤ _
  calc
    _ ≤ d*Real.artanh t := h
    _ = _ := by
      dsimp [d, t]
      rw [artanh_pair_ratio ha hb, artanh_oddsSign ha, artanh_oddsSign hb]
      ring

theorem edge_odds {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    profile ((meanEntropy (oddsSign a)+meanEntropy (oddsSign b))/2)
      |(oddsSign a-oddsSign b)/2| ≤
    (oddsSign a-oddsSign b)*(Real.artanh (oddsSign a)-Real.artanh (oddsSign b))/4 := by
  rcases lt_trichotomy b a with hba | hba | hab
  · have hdiff : 0 < (oddsSign a-oddsSign b)/2 := by
      have hd : (oddsSign a-oddsSign b)/2 = (a-b)*(a+b)/((1+a^2)*(1+b^2)) := by
        unfold oddsSign
        field_simp
        ring
      rw [hd]
      exact div_pos (mul_pos (sub_pos.mpr hba) (add_pos ha hb)) (by positivity)
    rw [abs_of_pos hdiff]
    exact edge_odds_ordered ha hb hba
  · subst a
    simp
  · have h := edge_odds_ordered hb ha hab
    have hdiff : 0 < (oddsSign b-oddsSign a)/2 := by
      have hd : (oddsSign b-oddsSign a)/2 = (b-a)*(b+a)/((1+b^2)*(1+a^2)) := by
        unfold oddsSign
        field_simp
        ring
      rw [hd]
      exact div_pos (mul_pos (sub_pos.mpr hab) (add_pos hb ha)) (by positivity)
    have habs : |(oddsSign a-oddsSign b)/2| = (oddsSign b-oddsSign a)/2 := by
      rw [show (oddsSign a-oddsSign b)/2 = -((oddsSign b-oddsSign a)/2) by ring,
        abs_neg, abs_of_pos hdiff]
    rw [habs, add_comm (meanEntropy (oddsSign a)) (meanEntropy (oddsSign b))]
    nlinarith only [h]

/-- The required specialization of CGN Lemma 10. No external inequality
or profile-convexity assumption remains in the theorem type. -/
theorem edge_entropy_profile {x y : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hy : y ∈ Ioo (-1 : ℝ) 1) :
    profile ((meanEntropy x+meanEntropy y)/2) |(x-y)/2| ≤
      (x-y)*(Real.artanh x-Real.artanh y)/4 := by
  have hA : 0 < Real.sqrt ((1+x)/(1-x)) := by
    apply Real.sqrt_pos.2
    exact div_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hB : 0 < Real.sqrt ((1+y)/(1-y)) := by
    apply Real.sqrt_pos.2
    exact div_pos (by linarith [hy.1]) (by linarith [hy.2])
  have h := edge_odds hA hB
  simpa only [oddsSign_sqrt_inverse hx, oddsSign_sqrt_inverse hy] using h

end
end CK.Profile
