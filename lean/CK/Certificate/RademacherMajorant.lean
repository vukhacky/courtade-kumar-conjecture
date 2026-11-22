module

public import Mathlib.Tactic

/-! Exact even polynomial majorant for the specialized small-coefficient
Rademacher estimate. The moment identity is a separate finite-probability
theorem; this module proves the global scalar majorant and its full moment
region bound, with no numerical sampling. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate
noncomputable section

def rademacherMajorant (t : ℝ) : ℝ :=
  208225896585/794794754447 +
    (953811216322069/906066020069580 : ℝ)*t^2 -
    (1922625114815459/5662912625434875 : ℝ)*t^4 +
    (61055789396287/906066020069580 : ℝ)*t^6 -
    (91372599570/15101100334493 : ℝ)*t^8 +
    (2949466500/15101100334493 : ℝ)*t^10

theorem rademacherMajorant_factorization (t : ℝ) :
    rademacherMajorant t - t =
      (t-3/5)^2*(t-19/10)^2*(t-10/3)^2 * 15 *
        (196631100*t^4+2294029500*t^3+10255747579*t^2+
          21351952610*t+18265429525)/15101100334493 := by
  unfold rademacherMajorant
  ring

theorem le_rademacherMajorant_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    t ≤ rademacherMajorant t := by
  have h : 0 ≤ rademacherMajorant t-t := by
    rw [rademacherMajorant_factorization]
    positivity
  linarith only [h]

theorem rademacherMajorant_abs (t : ℝ) : rademacherMajorant |t| = rademacherMajorant t := by
  unfold rademacherMajorant
  simp only [sq_abs, show |t|^4=t^4 by rw [show |t|^4=(|t|^2)^2 by ring, sq_abs]; ring,
    show |t|^6=t^6 by rw [show |t|^6=(|t|^2)^3 by ring, sq_abs]; ring,
    show |t|^8=t^8 by rw [show |t|^8=(|t|^2)^4 by ring, sq_abs]; ring,
    show |t|^10=t^10 by rw [show |t|^10=(|t|^2)^5 by ring, sq_abs]; ring]

theorem abs_le_rademacherMajorant (t : ℝ) : |t| ≤ rademacherMajorant t := by
  simpa only [rademacherMajorant_abs] using le_rademacherMajorant_of_nonneg (abs_nonneg t)

def rademacherMomentMajorant (p4 p6 p8 p10 : ℝ) : ℝ :=
  208225896585/794794754447 + 953811216322069/906066020069580 -
    (1922625114815459/5662912625434875 : ℝ)*(3-2*p4) +
    (61055789396287/906066020069580 : ℝ)*(15-30*p4+16*p6) -
    (91372599570/15101100334493 : ℝ)*(105-420*p4+448*p6+140*p4^2-272*p8) +
    (2949466500/15101100334493 : ℝ)*
      (945-6300*p4+10080*p6+6300*p4^2-12240*p8-6720*p4*p6+7936*p10)

/-- A closed inequality on the full moment region supplied by normalized
Rademacher sums with every coefficient of magnitude at most 2/5. -/
theorem rademacherMomentMajorant_lt {p4 p6 p8 p10 : ℝ}
    (hp4 : p4 ∈ Set.Icc (0 : ℝ) (4/25))
    (hp6 : p6 ∈ Set.Icc (0 : ℝ) ((4/25)*p4)) (hp8 : 0 ≤ p8)
    (hp10 : p10 ∈ Set.Icc (0 : ℝ) ((4/25)^3*p4)) :
    rademacherMomentMajorant p4 p6 p8 p10 < 7/8 := by
  have h44 : p4^2 ≤ (4/25 : ℝ)*p4 := by
    have h := mul_le_mul_of_nonneg_right hp4.2 hp4.1
    nlinarith only [h]
  have h46 : 0 ≤ p4*p6 := mul_nonneg hp4.1 hp6.1
  unfold rademacherMomentMajorant
  nlinarith only [hp4.1, hp4.2, hp6.1, hp6.2, hp8, hp10.1, hp10.2, h44, h46]

theorem rademacherMomentMajorant_le {p4 p6 p8 p10 : ℝ}
    (hp4 : p4 ∈ Set.Icc (0 : ℝ) (4/25))
    (hp6 : p6 ∈ Set.Icc (0 : ℝ) ((4/25)*p4)) (hp8 : 0 ≤ p8)
    (hp10 : p10 ∈ Set.Icc (0 : ℝ) ((4/25)^3*p4)) :
    rademacherMomentMajorant p4 p6 p8 p10 ≤ 7/8 :=
  (rademacherMomentMajorant_lt hp4 hp6 hp8 hp10).le

end
end CK.Certificate
