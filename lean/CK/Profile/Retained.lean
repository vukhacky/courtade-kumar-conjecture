module

public import CK.Profile.Packed
public import CK.Fourier.Influences

/-! Packing with retained singleton coordinates and closed residual domains.
The zero-cap case is recorded separately; positive-cap division is never
used to dispose of zero Fourier mass. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Set
namespace CK.Profile
noncomputable section

theorem packed_profile_le_sum_closed {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) {e c r : ℝ} (he : 0 < e) (hc : 0 < c)
    (ha : ∀ i ∈ s, a i ∈ Icc (0 : ℝ) c)
    (k : ℕ) (hr : r ∈ Icc (0 : ℝ) (c^2))
    (hm : (k : ℝ)*c^2+r ≤ ∑ i ∈ s, (a i)^2) :
    (k : ℝ)*profile e c+profile e (Real.sqrt r) ≤ ∑ i ∈ s, profile e (a i) := by
  obtain hlt | heq := hr.2.lt_or_eq
  · exact packed_profile_le_sum s a he hc ha k ⟨hr.1,hlt⟩ hm
  · subst r
    have h := packed_profile_le_sum s a he hc ha (k+1)
      (show (0 : ℝ) ∈ Ico 0 (c^2) from ⟨le_rfl,sq_pos_of_pos hc⟩)
      (by push_cast; nlinarith only [hm])
    simpa only [Nat.cast_add, Nat.cast_one, Real.sqrt_zero, profile_zero_right,
      add_zero, Real.sqrt_sq hc.le, add_mul, one_mul] using h

theorem profile_sum_of_zero_cap {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (e : ℝ)
    (ha : ∀ i ∈ s, a i ∈ Icc (0 : ℝ) 0) :
    (∑ i ∈ s, profile e (a i))=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hai : a i=0 := le_antisymm (ha i hi).2 (ha i hi).1
  simp [hai]

theorem retained_packed_profile_le {n : ℕ} (f : BooleanFunction n)
    (K : Finset (Fin n)) {e c r : ℝ} (he : 0 < e) (hc : 0 < c)
    (hcap : ∀ i : Fin n, i ∉ K → |fourier (lift f) {i}| ≤ c)
    (k : ℕ) (hr : r ∈ Icc (0 : ℝ) (c^2))
    (hm : (k : ℝ)*c^2+r + (∑ i ∈ K, fourier (lift f) {i}^2) ≤
      fourierWeight (lift f) 1) :
    (∑ i ∈ K, profile e |fourier (lift f) {i}|)+
      (k : ℝ)*profile e c+profile e (Real.sqrt r) ≤ singletonProfile f e := by
  classical
  have hs := Finset.sum_sdiff (f := fun i : Fin n => fourier (lift f) {i}^2)
    (Finset.subset_univ K)
  rw [← fourierWeight_one] at hs
  have hp := packed_profile_le_sum_closed (Finset.univ \ K)
    (fun i => |fourier (lift f) {i}|) he hc
    (fun i hi => ⟨abs_nonneg _,hcap i (Finset.mem_sdiff.mp hi).2⟩) k hr
    (by simp only [sq_abs]; linarith only [hm,hs])
  have hsp := Finset.sum_sdiff (f := fun i : Fin n => profile e |fourier (lift f) {i}|)
    (Finset.subset_univ K)
  change _ + _ = singletonProfile f e at hsp
  linarith only [hp,hsp]

theorem retained_one_profile_le {n : ℕ} (f : BooleanFunction n) (i : Fin n)
    {e a c r : ℝ} (he : 0 < e) (hc : 0 < c)
    (hai : |fourier (lift f) {i}|=a)
    (hcap : ∀ j : Fin n, j ≠ i → |fourier (lift f) {j}| ≤ c)
    (k : ℕ) (hr : r ∈ Icc (0 : ℝ) (c^2))
    (hm : a^2+(k : ℝ)*c^2+r ≤ fourierWeight (lift f) 1) :
    profile e a+(k : ℝ)*profile e c+profile e (Real.sqrt r) ≤ singletonProfile f e := by
  have hs : fourier (lift f) {i}^2=a^2 := by rw [← hai,sq_abs]
  have h := retained_packed_profile_le f {i} he hc
    (fun j hj => hcap j (by simpa using hj)) k hr
    (by simpa only [Finset.sum_singleton,hs] using (show (k : ℝ)*c^2+r+a^2 ≤ _ by linarith only [hm]))
  simpa only [Finset.sum_singleton,hai] using h

/-- Ordering and the Boolean pair bound produce the source moving cap. -/
theorem singleton_tail_le_min {n : ℕ} (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i : Fin n)
    (hmax : ∀ j, fourier (lift f) {j} ≤ fourier (lift f) {i})
    (j : Fin n) (hji : j ≠ i) :
    |fourier (lift f) {j}| ≤ min (fourier (lift f) {i}) (1-fourier (lift f) {i}) := by
  rw [abs_of_nonneg (singleton_nonneg_of_monotone hf j)]
  exact le_min (hmax j) (by linarith [singleton_pair_le_one f j i hji])

end
end CK.Profile
