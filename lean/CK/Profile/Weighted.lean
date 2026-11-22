module

public import CK.Profile.Convex

/-! Finite weighted profile sums and their certified affine lower bounds. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK.Profile
noncomputable section

def weightedProfile (L : List (ℝ × ℝ)) (e : ℝ) : ℝ :=
  (L.map (fun z => z.1*profile e z.2)).sum

theorem continuousOn_profile_of_nonneg {q : ℝ} (hq : 0 ≤ q) :
    ContinuousOn (fun e => profile e q) (Set.Ioi (0 : ℝ)) := by
  obtain rfl | hq := hq.eq_or_lt
  · simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioi 0))
  · exact continuousOn_profile hq

theorem weightedProfile_nonneg (L : List (ℝ × ℝ)) {e : ℝ} (he : 0 < e)
    (hL : ∀ z ∈ L, 0 ≤ z.1 ∧ 0 ≤ z.2) : 0 ≤ weightedProfile L e := by
  induction L with
  | nil => simp [weightedProfile]
  | cons z L ih =>
    have hz := hL z (by simp)
    have ht : ∀ t ∈ L, 0 ≤ t.1 ∧ 0 ≤ t.2 := fun t ht => hL t (by simp [ht])
    change 0 ≤ z.1*profile e z.2+weightedProfile L e
    exact add_nonneg (mul_nonneg hz.1 (profile_nonneg he hz.2)) (ih ht)

theorem continuousOn_weightedProfile (L : List (ℝ × ℝ))
    (hL : ∀ z ∈ L, 0 ≤ z.2) : ContinuousOn (weightedProfile L) (Set.Ioi (0 : ℝ)) := by
  induction L with
  | nil =>
    change ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioi 0)
    exact continuousOn_const
  | cons z L ih =>
    exact (continuousOn_const.mul (continuousOn_profile_of_nonneg (hL z (by simp)))).add
      (ih (fun t ht => hL t (by simp [ht])))

theorem weighted_tangent_sum {ι : Type*} [Fintype ι] {e : ℝ} (he : 0 < e)
    (w q t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, 0 ≤ q i)
    (ht : ∀ i, t i ∈ Set.Ioo (0 : ℝ) 1) :
    (∑ i, w i*(q i*Real.artanh (t i) +
      (q i*meanEntropy (t i)/t i-e)*tangentFactor (t i))) ≤
      ∑ i, w i*profile e (q i) := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (profile_tangent_nonneg he (hq i) (ht i)) (hw i)

/-- A source-level affine denominator lower bound, valid for every positive
entropy argument; certificate modules may lower its coefficients rationally. -/
theorem affine_lower_bound_profile_sum {ι : Type*} [Fintype ι] {e : ℝ} (he : 0 < e)
    (w q t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, 0 ≤ q i)
    (ht : ∀ i, t i ∈ Set.Ioo (0 : ℝ) 1) :
    (∑ i, w i*q i*(Real.artanh (t i) +
      meanEntropy (t i)/t i*tangentFactor (t i))) +
        (1-∑ i, w i*tangentFactor (t i))*e ≤ e+∑ i, w i*profile e (q i) := by
  have h := weighted_tangent_sum he w q t hw hq ht
  have hid :
      (∑ i, w i*q i*(Real.artanh (t i) + meanEntropy (t i)/t i*tangentFactor (t i))) +
        (1-∑ i, w i*tangentFactor (t i))*e = e +
      ∑ i, w i*(q i*Real.artanh (t i) + (q i*meanEntropy (t i)/t i-e)*tangentFactor (t i)) := by
    simp only [sub_mul, one_mul, Finset.sum_mul]
    rw [show (∑ i, w i*q i*(Real.artanh (t i) + meanEntropy (t i)/t i*tangentFactor (t i))) +
        (e-∑ i, w i*tangentFactor (t i)*e) =
        e + ((∑ i, w i*q i*(Real.artanh (t i) + meanEntropy (t i)/t i*tangentFactor (t i))) -
          ∑ i, w i*tangentFactor (t i)*e) by ring]
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid]
  simpa only [add_comm] using add_le_add_left h e

end
end CK.Profile
