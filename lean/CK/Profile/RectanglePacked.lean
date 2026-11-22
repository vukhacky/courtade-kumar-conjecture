module

public import CK.Profile.Retained

/-! Lower profile envelopes from interval bounds on retained coordinates. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

theorem rectangle_one_profile_le {n : ℕ} (f : BooleanFunction n) (i : Fin n)
    {e a A c r w : ℝ} (he : 0 < e) (ha : 0 ≤ a) (hc : 0 < c)
    (hi : |fourier (lift f) {i}| ∈ Icc a A)
    (hcap : ∀ j : Fin n, j ≠ i → |fourier (lift f) {j}| ≤ c)
    (k : ℕ) (hr : r ∈ Icc (0 : ℝ) (c^2))
    (hm : A^2+(k : ℝ)*c^2+r ≤ w) (hw : w ≤ fourierWeight (lift f) 1) :
    profile e a+(k : ℝ)*profile e c+profile e (Real.sqrt r) ≤ singletonProfile f e := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hi.2
  have hs := (sq_le_sq₀ (abs_nonneg (fourier (lift f) {i})) hA).mpr hi.2
  have h := retained_one_profile_le f i he hc rfl hcap k hr
    (by linarith only [hs,hm,hw])
  have hmono := profile_mono_right he ha hi.1
  linarith only [h,hmono]

theorem rectangle_two_profile_le {n : ℕ} (f : BooleanFunction n) (i j : Fin n)
    (hij : i ≠ j) {e a A b B c r w : ℝ} (he : 0 < e)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hi : |fourier (lift f) {i}| ∈ Icc a A) (hj : |fourier (lift f) {j}| ∈ Icc b B)
    (hcap : ∀ l : Fin n, l ≠ i → l ≠ j → |fourier (lift f) {l}| ≤ c)
    (k : ℕ) (hr : r ∈ Icc (0 : ℝ) (c^2))
    (hm : A^2+B^2+(k : ℝ)*c^2+r ≤ w) (hw : w ≤ fourierWeight (lift f) 1) :
    profile e a+profile e b+(k : ℝ)*profile e c+profile e (Real.sqrt r) ≤ singletonProfile f e := by
  classical
  have hA : 0 ≤ A := (abs_nonneg _).trans hi.2
  have hB : 0 ≤ B := (abs_nonneg _).trans hj.2
  have hsA := (sq_le_sq₀ (abs_nonneg (fourier (lift f) {i})) hA).mpr hi.2
  have hsB := (sq_le_sq₀ (abs_nonneg (fourier (lift f) {j})) hB).mpr hj.2
  simp only [sq_abs] at hsA hsB
  have h := retained_packed_profile_le f {i,j} he hc
    (fun l hl => hcap l (by simpa using (fun hli : l=i => hl (by simp [hli])))
      (by simpa using (fun hlj : l=j => hl (by simp [hlj])))) k hr
    (by simp only [Finset.sum_pair hij]; linarith only [hm,hw,hsA,hsB])
  simp only [Finset.sum_pair hij] at h
  have hma := profile_mono_right he ha hi.1
  have hmb := profile_mono_right he hb hj.1
  linarith only [h,hma,hmb]

end
end CK.Profile
