module

public import CK.High.Refund

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

/-- Jensen over every edge parallel to one coordinate; both orientations
are included, and the signed average is the exact singleton coefficient. -/
theorem edgeRefund_le_average {n : ℕ} (i : Fin n) (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Ioo (-1 : ℝ) 1) :
    edgeRefund (avg (fun x => signEntropy (g x))) |fourier g {i}| ≤
      avg (fun x => edgeRefund (Profile.edgeEntropy i g x) |Profile.orientedEdge i g x|) := by
  let w : Cube n → ℝ := fun _ => (Fintype.card (Cube n) : ℝ)⁻¹
  let p : Cube n → ℝ × ℝ := fun x => (Profile.edgeEntropy i g x,Profile.orientedEdge i g x)
  have hw : ∀ x, 0 ≤ w x := fun x => by dsimp [w]; positivity
  have hsum : ∑ x, w x = 1 := by simp [w]
  have hj := convexOn_edgeRefund_signed.map_sum_le (t := Finset.univ) (w := w) (p := p)
    (fun x _ => hw x) hsum (fun x _ => Profile.edgeEntropy_pos i g hg x)
  have hp : ∑ x, w x • p x = (avg (Profile.edgeEntropy i g),avg (Profile.orientedEdge i g)) := by
    ext
    · simp [Prod.fst_sum,p,w,avg,Finset.mul_sum]
    · simp [Prod.snd_sum,p,w,avg,Finset.mul_sum]
  rw [hp] at hj
  simp only [smul_eq_mul] at hj
  rw [Profile.avg_edgeEntropy,Profile.avg_orientedEdge] at hj
  simpa only [p,w,avg,Finset.mul_sum,Profile.meanEntropy,signEntropy] using hj

end
end CK
