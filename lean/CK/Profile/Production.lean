module

public import CK.Profile.Edge
public import CK.Analysis.Production
public import Mathlib.Algebra.BigOperators.Pi

/-! Averaging CGN edge inequalities by the proved joint convexity gives
the singleton-profile lower bound for actual cube entropy production. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK.Profile
noncomputable section

def edgeEntropy {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  (meanEntropy (g x)+meanEntropy (g (flipCoordinate i x)))/2

def orientedEdge {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  sign (x i)*coordinatePartial i g x

theorem edgeEntropy_pos {n : ℕ} (i : Fin n) (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Ioo (-1 : ℝ) 1) (x : Cube n) : 0 < edgeEntropy i g x :=
  div_pos (add_pos (meanEntropy_pos (hg x))
    (meanEntropy_pos (hg (flipCoordinate i x)))) (by norm_num)

theorem avg_edgeEntropy {n : ℕ} (i : Fin n) (g : Cube n → ℝ) :
    avg (edgeEntropy i g) = avg (fun x => meanEntropy (g x)) := by
  have hfun : edgeEntropy i g = fun x => (1/2 : ℝ)*
      (meanEntropy (g x)+meanEntropy (g (flipCoordinate i x))) := by
    funext x
    unfold edgeEntropy
    ring
  rw [hfun, avg_smul, avg_add, avg_flipCoordinate i (fun x => meanEntropy (g x))]
  ring

theorem avg_orientedEdge {n : ℕ} (i : Fin n) (g : Cube n → ℝ) :
    avg (orientedEdge i g) = fourier g {i} := by
  calc
    _ = fourier (coordinatePartial i g) {i} := by
      unfold orientedEdge fourier walsh
      simp only [Finset.prod_singleton]
      congr 1
      funext x
      ring
    _ = fourier g {i} := by rw [fourier_coordinatePartial]; simp

theorem abs_orientedEdge {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) :
    |orientedEdge i g x| = |(g x-g (flipCoordinate i x))/2| := by
  unfold orientedEdge coordinatePartial
  cases h : x i <;> simp [sign, h]

theorem avg_profile_edge_le {n : ℕ} (i : Fin n) (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Ioo (-1 : ℝ) 1) :
    profile (avg (fun x => meanEntropy (g x))) |fourier g {i}| ≤
      avg (fun x => profile (edgeEntropy i g x) |orientedEdge i g x|) := by
  let w : Cube n → ℝ := fun _ => (Fintype.card (Cube n) : ℝ)⁻¹
  let p : Cube n → ℝ × ℝ := fun x => (edgeEntropy i g x, orientedEdge i g x)
  have hw : ∀ x, 0 ≤ w x := by intro x; dsimp [w]; positivity
  have hsum : ∑ x, w x = 1 := by simp [w]
  have hj := convexOn_profile_signed.map_sum_le (t := Finset.univ) (w := w) (p := p)
    (fun x _ => hw x) hsum (fun x _ => edgeEntropy_pos i g hg x)
  have hp : ∑ x, w x • p x = (avg (edgeEntropy i g), avg (orientedEdge i g)) := by
    ext
    · simp [Prod.fst_sum, p, w, avg, Finset.mul_sum]
    · simp [Prod.snd_sum, p, w, avg, Finset.mul_sum]
  rw [hp] at hj
  simp only [smul_eq_mul] at hj
  rw [avg_edgeEntropy, avg_orientedEdge] at hj
  simpa only [p, w, avg, Finset.mul_sum] using hj

theorem entropyProduction_ge_profile {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∑ i : Fin n, profile (avg (fun x => meanEntropy (g x))) |fourier g {i}|) ≤
      entropyProduction g := by
  rw [entropyProduction_eq_edges]
  apply Finset.sum_le_sum
  intro i _
  apply (avg_profile_edge_le i g hg).trans
  apply avg_mono
  intro x
  rw [phiSlope_eq_artanh (hg x), phiSlope_eq_artanh (hg (flipCoordinate i x)),
    abs_orientedEdge]
  exact edge_entropy_profile (hg x) (hg (flipCoordinate i x))

/-- STOC `prop:profile-production`, including nonbalanced Boolean functions. -/
theorem entropyProduction_noise_ge_profile {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (f : BooleanFunction n)
    (hf : ∃ u v, f u ≠ f v) :
    (∑ i : Fin n, profile (conditionalEntropy ρ f) (ρ*|fourier (lift f) {i}|)) ≤
      entropyProduction (noise ρ (lift f)) := by
  have h := entropyProduction_ge_profile (noise ρ (lift f))
    (noise_lift_mem_Ioo ⟨by linarith [hρ.1], hρ.2⟩ f hf)
  simp only [fourier_noise, Finset.card_singleton, pow_one, abs_mul, abs_of_pos hρ.1] at h
  exact h

end
end CK.Profile
