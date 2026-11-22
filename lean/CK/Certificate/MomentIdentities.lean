module

public import CK.Basic.Cube
public import CK.Certificate.MomentPolygon
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Exact uniform two-cube moments underlying the source polynomial.
These identities identify the certified polynomial with the mathematical
moment expression; they do not assume an entropy-gap lower bound. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK.Certificate
noncomputable section

theorem avg_cube_two (g : Cube 2 → ℝ) :
    avg g = (g ![false, false] + g ![false, true] +
      g ![true, false] + g ![true, true]) / 4 := by
  have hs : (∑ x : Cube 2, g x) = ∑ p : Bool × Bool, g ![p.1, p.2] := by
    apply Fintype.sum_equiv (finTwoArrowEquiv Bool) g (fun p => g ![p.1, p.2])
    intro x
    congr 1
    funext i
    fin_cases i <;> rfl
  unfold avg
  rw [hs, card_cube]
  norm_num [Fintype.sum_prod_type]
  ring

def twoCoreSignal (ρ a b c : ℝ) (x : Cube 2) : ℝ :=
  ρ * a * sign (x 0) + ρ * b * sign (x 1) + ρ^2 * c * sign (x 0) * sign (x 1)

theorem avg_twoCoreSignal (ρ a b c : ℝ) : avg (twoCoreSignal ρ a b c) = 0 := by
  rw [avg_cube_two]
  norm_num [twoCoreSignal]
  ring

theorem avg_twoCoreSignal_sq (ρ a b c : ℝ) :
    avg (fun x => twoCoreSignal ρ a b c x ^ 2) =
      ρ^2 * (a^2 + b^2) + ρ^4 * c^2 := by
  rw [avg_cube_two]
  norm_num [twoCoreSignal]
  ring

theorem avg_twoCoreSignal_cube (ρ a b c : ℝ) :
    avg (fun x => twoCoreSignal ρ a b c x ^ 3) = 6 * ρ^4 * a * b * c := by
  rw [avg_cube_two]
  norm_num [twoCoreSignal]
  ring

theorem avg_twoCoreSignal_fourth (ρ a b c : ℝ) :
    avg (fun x => twoCoreSignal ρ a b c x ^ 4) =
      ρ^4 * (a^4 + b^4 + 6 * a^2 * b^2) +
        6 * ρ^6 * c^2 * (a^2 + b^2) + ρ^8 * c^4 := by
  rw [avg_cube_two]
  norm_num [twoCoreSignal]
  ring

theorem localMomentQ_eq_moments (ρ a b : ℝ) :
    localMomentQ ρ a b =
      (17/12 : ℝ) * (ρ^2 * (a+b) - 1) - ρ^2*b/5 + 9/13 -
        avg (fun x => twoCoreSignal ρ a b b x ^ 2) / 2 -
        avg (fun x => twoCoreSignal ρ a b b x ^ 4) / 5 - 1/198 := by
  rw [avg_twoCoreSignal_sq, avg_twoCoreSignal_fourth]
  rfl

/-- The finite-cube moment expression in source equation
`eq:local-moment-polynomial` has a uniform positive margin on its full domain. -/
theorem source_moment_expression_lower_bound {ρ a b : ℝ}
    (hρ : ρ ∈ Set.Icc (39/40 : ℝ) (49/50))
    (ha : a ∈ Set.Icc (2/3 : ℝ) (76043/100000))
    (hab : a + b ≤ 1) (hl : (64/25 : ℝ) ≤ 3*a + 7*b) :
    (1/1000 : ℝ) ≤
      (17/12 : ℝ) * (ρ^2 * (a+b) - 1) - ρ^2*b/5 + 9/13 -
        avg (fun x => twoCoreSignal ρ a b b x ^ 2) / 2 -
        avg (fun x => twoCoreSignal ρ a b b x ^ 4) / 5 - 1/198 := by
  rw [← localMomentQ_eq_moments]
  exact localMomentQ_lower_bound hρ ha hab hl

end
end CK.Certificate
