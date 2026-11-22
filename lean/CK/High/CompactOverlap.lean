module

public import CK.High.CompactParameters
public import CK.Analysis.Production
public import CK.Certificate.ClockPilotLogs

/-! Exact correlation/height overlap and exclusion of the compact local
neighborhood at a positive Shannon gap. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem compact_start_lt_artanh :
    (45951/20000 : ℝ) < Real.artanh (49/50) := by
  have hr : (43623/100000 : ℝ) ≤ Real.log (99/64) := by
    have h := (Certificate.logCertificate_sound (q := 99/64)
      (lower := 43623/100000) (upper := 1/2) (n := 4)
      (by norm_num [Certificate.logCertificate,Certificate.logSeries,
        Certificate.logRemainder,Finset.sum_range_succ])).1
    norm_num at h ⊢
    exact h
  have h99 : Real.log (99 : ℝ)=6*Real.log 2+Real.log (99/64) := by
    rw [show (99 : ℝ)=2^6*(99/64) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [Real.artanh_eq_half_log (by norm_num : (49/50 : ℝ) ∈ Icc (-1) 1)]
  norm_num
  rw [h99]
  linarith only [hr,Certificate.P03.log_two_bounds.1]

theorem compact_height_overlap {ρ : ℝ}
    (hρ : ρ ∈ Ico (49/50 : ℝ) 1) (hu : Real.artanh ρ ≤ 8) :
    Real.artanh ρ ∈ Icc (45951/20000 : ℝ) 8 := by
  have hm := Real.artanh_le_artanh (by norm_num : (-1 : ℝ) < 49/50) hρ.2 hρ.1
  exact ⟨compact_start_lt_artanh.le.trans hm,hu⟩

theorem positive_gap_compact_singleton {n : ℕ} {u : ℝ}
    (hu : (9/4 : ℝ) ≤ u) (f : BooleanFunction n)
    (hgap : 0 < informationGap (Real.tanh u) f) (i : Fin n) :
    |fourier (lift f) {i}| < compactAlpha u := by
  by_contra hh
  have hc := mutualInformation_le_phi_exponential_coordinate
    (log_nine_lt_nine_fourths.le.trans hu) f i (le_of_not_gt hh)
  have hr := tanh_mem_Ioo_positive (by linarith : 0 < u)
  rw [mutualInformation_eq_information ⟨hr.1.le,hr.2.le⟩] at hc
  exact (not_lt_of_ge (sub_nonpos.mpr hc)) hgap

theorem positive_gap_compact_max {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu : (9/4 : ℝ) ≤ u) (f : BooleanFunction n)
    (hgap : 0 < informationGap (Real.tanh u) f) :
    maxSingletonCoeff hn f < compactAlpha u := by
  obtain ⟨i,hi⟩ := exists_max_singleton hn f
  rw [hi]
  exact positive_gap_compact_singleton hu f hgap i

end
end CK
