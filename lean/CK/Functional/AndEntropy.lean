module

public import CK.Functional.SignEntropy

/-! Scalar entropy inequality for the conjunction of independent bits.
The proof is elementary concavity and includes all degenerate endpoints. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section
open Set

def andEntropyDefect (s t : ℝ) : ℝ :=
  t * Real.binEntropy s + s * Real.binEntropy t - Real.binEntropy (s * t)

def andEntropyDefectSlope (s t : ℝ) : ℝ :=
  Real.binEntropy s + s * (Real.log (1 - t) - Real.log t) -
    s * (Real.log (1 - s * t) - Real.log (s * t))

theorem hasDerivAt_andEntropyDefect {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (andEntropyDefect s) (andEntropyDefectSlope s t) t := by
  have hst : s * t ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos hs.1 ht.1, by nlinarith [hs.2, mul_pos hs.1 (sub_pos.mpr ht.2)]⟩
  convert (((hasDerivAt_id t).mul_const (Real.binEntropy s)).add
    ((Real.hasDerivAt_binEntropy (ne_of_gt ht.1) (ne_of_lt ht.2)).const_mul s)).sub
    ((Real.hasDerivAt_binEntropy (ne_of_gt hst.1) (ne_of_lt hst.2)).comp t
      ((hasDerivAt_id t).const_mul s)) using 1 <;>
    (first | rfl | (dsimp [andEntropyDefect, andEntropyDefectSlope]; ring))

theorem hasDerivAt_andEntropyDefectSlope {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (andEntropyDefectSlope s)
      (-s * (1 - s) / ((1 - t) * (1 - s * t))) t := by
  have hst : s * t ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos hs.1 ht.1, by nlinarith [hs.2, mul_pos hs.1 (sub_pos.mpr ht.2)]⟩
  have d1 := ((hasDerivAt_const t 1).sub (hasDerivAt_id t)).log
    (ne_of_gt (sub_pos.mpr ht.2))
  have d2 := (hasDerivAt_id t).log (ne_of_gt ht.1)
  have d3 := ((hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul s)).log
    (ne_of_gt (sub_pos.mpr hst.2))
  have d4 := ((hasDerivAt_id t).const_mul s).log (ne_of_gt hst.1)
  convert ((hasDerivAt_const t (Real.binEntropy s)).add ((d1.sub d2).const_mul s)).sub
    ((d3.sub d4).const_mul s) using 1
  · rfl
  · dsimp
    field_simp [ne_of_gt ht.1, ne_of_gt hs.1,
      ne_of_gt (sub_pos.mpr ht.2), ne_of_gt (sub_pos.mpr hst.2)]
    ring

theorem andEntropyDefect_concave {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (andEntropyDefect s) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := andEntropyDefectSlope s)
    (f'' := fun t => -s * (1 - s) / ((1 - t) * (1 - s * t)))
  · unfold andEntropyDefect
    fun_prop
  · intro t ht
    exact (hasDerivAt_andEntropyDefect hs (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
  · intro t ht
    exact (hasDerivAt_andEntropyDefectSlope hs (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
  · intro t ht
    simp only [interior_Icc, mem_Ioo] at ht
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.1.le) (sub_nonneg.mpr hs.2.le)
    · apply mul_nonneg (sub_nonneg.mpr ht.2.le)
      nlinarith [hs.2, mul_pos hs.1 (sub_pos.mpr ht.2)]

/-- Entropy of the AND of two independent Bernoulli variables. -/
theorem binEntropy_mul_le {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Real.binEntropy (s * t) ≤ t * Real.binEntropy s + s * Real.binEntropy t := by
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · simp [← h0]
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · simp [h1]
  have h := (andEntropyDefect_concave ⟨h0, h1⟩).2
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (sub_nonneg.mpr ht.2) ht.1 (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul, andEntropyDefect, mul_zero, Real.binEntropy_zero,
    mul_one, Real.binEntropy_one, add_zero, zero_add] at h
  linarith

end
end CK
