module

public import CK.Middle.RectangleConsumers
public import CK.Middle.MomentTransport
public import CK.Middle.OrderedCoordinates

/-! Coverage above the largest singleton cutoff 2/3 in the final middle-correlation band, via a moment half-plane and five rectangles. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Middle
noncomputable section

theorem mutualInformation_le_phi_last_large_coordinate {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i j : Fin n) (hij : i ≠ j)
    (ha : fourier (lift f) {i} ∈ Icc (2/3 : ℝ) (76043/100000))
    (hsecond : ∀ l : Fin n, l ≠ i → fourier (lift f) {l} ≤ fourier (lift f) {j}) :
    mutualInformation ρ f ≤ phi ρ := by
  rcases last_band_rectangle_cover ha (singleton_nonneg_of_monotone hf j) with
    h | h | h | h | h | h
  · exact (mutualInformation_lt_phi_moment_band_pair hρ f hf i j hij ha h).le
  · exact mutualInformation_le_phi_leaf14 hρ f hf i j hij h.1 h.2 hsecond
  · exact mutualInformation_le_phi_leaf15 hρ f hf i j hij h.1 h.2 hsecond
  · exact mutualInformation_le_phi_leaf16 hρ f hf i j hij h.1 h.2 hsecond
  · exact mutualInformation_le_phi_leaf17 hρ f hf i j hij h.1 h.2 hsecond
  · exact mutualInformation_le_phi_leaf18 hρ f hf i j hij h.1 h.2 hsecond

end
end CK.Middle
