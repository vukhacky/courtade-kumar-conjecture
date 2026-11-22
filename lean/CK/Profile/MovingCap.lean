module

public import CK.Profile.Packed

/-! Concavity for an entropy profile with a varying cap, via a two-point Jensen argument on the cap and residual domain. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

theorem concave_weighted_pair_endpoints_le {b : ℝ → ℝ}
    (hb : ConcaveOn ℝ (Ici (0 : ℝ)) b) {k a d x y : ℝ}
    (hk : 0 ≤ k) (ha : 0 ≤ a) (hax : a ≤ x) (hxd : x ≤ d)
    (hay : a ≤ y) (hyd : y ≤ d) (hs : k*x+y=k*d+a) :
    k*b d+b a ≤ k*b x+b y := by
  have had : a ≤ d := hax.trans hxd
  obtain heq | hlt := had.eq_or_lt
  · have hx : x=a := by linarith
    have hy : y=a := by linarith
    simp [hx, hy, ← heq]
  have hden : 0 < d-a := sub_pos.mpr hlt
  have hx₁ : 0 ≤ (d-x)/(d-a) := div_nonneg (sub_nonneg.mpr hxd) hden.le
  have hx₂ : 0 ≤ (x-a)/(d-a) := div_nonneg (sub_nonneg.mpr hax) hden.le
  have hy₁ : 0 ≤ (d-y)/(d-a) := div_nonneg (sub_nonneg.mpr hyd) hden.le
  have hy₂ : 0 ≤ (y-a)/(d-a) := div_nonneg (sub_nonneg.mpr hay) hden.le
  have hxsum : (d-x)/(d-a)+(x-a)/(d-a)=1 := by field_simp; ring
  have hysum : (d-y)/(d-a)+(y-a)/(d-a)=1 := by field_simp; ring
  have hxarg : ((d-x)/(d-a))*a+((x-a)/(d-a))*d=x := by field_simp; ring
  have hyarg : ((d-y)/(d-a))*a+((y-a)/(d-a))*d=y := by field_simp; ring
  have hxj := hb.2 ha (ha.trans had) hx₁ hx₂ hxsum
  have hyj := hb.2 ha (ha.trans had) hy₁ hy₂ hysum
  simp only [smul_eq_mul, hxarg, hyarg] at hxj hyj
  have hxk := mul_le_mul_of_nonneg_left hxj hk
  have hcoefA : k*((d-x)/(d-a))+(d-y)/(d-a)=1 := by
    field_simp
    nlinarith only [hs]
  have hcoefD : k*((x-a)/(d-a))+(y-a)/(d-a)=k := by
    field_simp
    nlinarith only [hs]
  have hA := congrArg (fun z : ℝ => z*b a) hcoefA
  have hD := congrArg (fun z : ℝ => z*b d) hcoefD
  nlinarith only [hxk, hyj, hA, hD]

def packedCost (b : ℝ → ℝ) (k c w : ℝ) : ℝ := k*b c+b (w-k*c)

theorem packedCost_antitone_cap {b : ℝ → ℝ}
    (hb : ConcaveOn ℝ (Ici (0 : ℝ)) b) {k c d w : ℝ} (hk : 0 ≤ k)
    (hcd : c ≤ d) (hremD : 0 ≤ w-k*d) (hremC : w-k*c ≤ c) :
    packedCost b k d w ≤ packedCost b k c w := by
  have hkd := mul_le_mul_of_nonneg_left hcd hk
  exact concave_weighted_pair_endpoints_le hb
    (a := w-k*d) (d := d) (x := c) (y := w-k*c) hk hremD
    (by linarith only [hkd, hremC]) hcd (by linarith only [hkd])
    (by linarith only [hremC, hcd]) (by ring)

/-- Source moving-cap concavity, proved for every nonnegative real k.
The integer packing multiplicities used by CK are a special case. -/
theorem concaveOn_moving_packedCost {I : Set ℝ} {b C : ℝ → ℝ} {k A B : ℝ}
    (hb : ConcaveOn ℝ (Ici (0 : ℝ)) b) (hC : ConvexOn ℝ I C) (hk : 0 ≤ k)
    (hrem : ∀ x ∈ I, A*x+B-k*C x ∈ Icc (0 : ℝ) (C x)) :
    ConcaveOn ℝ I (fun x => packedCost b k (C x) (A*x+B)) := by
  refine ⟨hC.1, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  have hz := hC.1 hx hy hα hβ hαβ
  have hxrem := hrem x hx
  have hyrem := hrem y hy
  have hzrem := hrem _ hz
  have hCx : 0 ≤ C x := hxrem.1.trans hxrem.2
  have hCy : 0 ≤ C y := hyrem.1.trans hyrem.2
  have hc := hC.2 hx hy hα hβ hαβ
  simp only [smul_eq_mul] at hc hzrem ⊢
  have hw : A*(α*x+β*y)+B=α*(A*x+B)+β*(A*y+B) := by
    nlinarith only [congrArg (fun z : ℝ => z*B) hαβ]
  have hrbar : 0 ≤ A*(α*x+β*y)+B-k*(α*C x+β*C y) := by
    rw [hw]
    have h₁ := mul_nonneg hα hxrem.1
    have h₂ := mul_nonneg hβ hyrem.1
    nlinarith only [h₁, h₂]
  have hanti := packedCost_antitone_cap hb hk hc hrbar hzrem.2
  have hJc := hb.2 hCx hCy hα hβ hαβ
  have hJr := hb.2 hxrem.1 hyrem.1 hα hβ hαβ
  simp only [smul_eq_mul] at hJc hJr
  have hkJ := mul_le_mul_of_nonneg_left hJc hk
  have harg : α*(A*x+B-k*C x)+β*(A*y+B-k*C y)=
      A*(α*x+β*y)+B-k*(α*C x+β*C y) := by rw [hw]; ring
  rw [harg] at hJr
  dsimp only [packedCost] at hanti ⊢
  linarith only [hanti, hkJ, hJr]

end
end CK.Profile
