module

public import CK.Profile.MovingCap
public import CK.Profile.ClockConvexity
public import CK.Profile.Retained
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! Moving-cap envelopes in the squared largest-coefficient parameter, with explicit domain hypotheses. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

def highCap (x : ℝ) : ℝ := (1-Real.sqrt x)^2

theorem highCap_convex : ConvexOn ℝ (Ici (0 : ℝ)) highCap := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy α β hα hβ hsum
  have hz : 0 ≤ α*x+β*y := add_nonneg (mul_nonneg hα hx) (mul_nonneg hβ hy)
  have h := Real.strictConcaveOn_sqrt.concaveOn.2 hx hy hα hβ hsum
  simp only [smul_eq_mul] at h ⊢
  have hsqx := Real.sq_sqrt hx
  have hsqy := Real.sq_sqrt hy
  have hsqz := Real.sq_sqrt hz
  dsimp only [highCap]
  nlinarith only [h,hsqx,hsqy,hsqz,hsum,
    congrArg (fun z : ℝ => z*α) hsqx, congrArg (fun z : ℝ => z*β) hsqy]

def movingProfile (k : ℕ) (A B : ℝ) (C : ℝ → ℝ) (x e : ℝ) : ℝ :=
  profile e (Real.sqrt x)+(k : ℝ)*profile e (Real.sqrt (C x))+
    profile e (Real.sqrt (A*x+B-(k : ℝ)*C x))

theorem movingProfile_continuous (k : ℕ) (A B : ℝ) (C : ℝ → ℝ) (x : ℝ) :
    ContinuousOn (movingProfile k A B C x) (Ioi (0 : ℝ)) := by
  exact ((continuousOn_profile_of_nonneg (Real.sqrt_nonneg x)).add
    (continuousOn_const.mul (continuousOn_profile_of_nonneg (Real.sqrt_nonneg (C x))))).add
    (continuousOn_profile_of_nonneg (Real.sqrt_nonneg _))

theorem movingProfile_antitone (k : ℕ) (A B : ℝ) (C : ℝ → ℝ) (x : ℝ) :
    AntitoneOn (movingProfile k A B C x) (Ioi (0 : ℝ)) := by
  have h (q : ℝ) (hq : 0 ≤ q) : AntitoneOn (fun e => profile e q) (Ioi (0 : ℝ)) := by
    obtain rfl | hq := hq.eq_or_lt
    · intro e he d hd hed; simp
    · exact profile_antitone hq
  intro e he d hd hed
  have h₁ := h (Real.sqrt x) (Real.sqrt_nonneg _) he hd hed
  have h₂ := mul_le_mul_of_nonneg_left
    (h (Real.sqrt (C x)) (Real.sqrt_nonneg _) he hd hed) (Nat.cast_nonneg k)
  have h₃ := h (Real.sqrt (A*x+B-(k : ℝ)*C x)) (Real.sqrt_nonneg _) he hd hed
  dsimp only [movingProfile]
  linarith only [h₁,h₂,h₃]

theorem movingProfile_pos (k : ℕ) (A B : ℝ) (C : ℝ → ℝ) {x e : ℝ}
    (hx : 0 < x) (he : 0 < e) : 0 < movingProfile k A B C x e := by
  have h₁ := profile_pos he (Real.sqrt_pos.mpr hx)
  have h₂ := mul_nonneg (Nat.cast_nonneg k) (profile_nonneg he (Real.sqrt_nonneg (C x)))
  have h₃ := profile_nonneg he (Real.sqrt_nonneg (A*x+B-(k : ℝ)*C x))
  dsimp only [movingProfile]
  linarith only [h₁,h₂,h₃]

theorem movingProfile_concave {I : Set ℝ} (hI : Convex ℝ I)
    (hIpos : ∀ x ∈ I, 0 ≤ x) (k : ℕ) (A B : ℝ) (C : ℝ → ℝ)
    (hC : ConvexOn ℝ I C)
    (hr : ∀ x ∈ I, A*x+B-(k : ℝ)*C x ∈ Icc (0 : ℝ) (C x))
    {e : ℝ} (he : 0 < e) : ConcaveOn ℝ I (fun x => movingProfile k A B C x e) := by
  have hb := concaveOn_profile_sqrt he
  have hfirst : ConcaveOn ℝ I (fun x => profile e (Real.sqrt x)) := by
    refine ⟨hI, ?_⟩
    intro x hx y hy α β hα hβ hsum
    exact hb.2 (hIpos x hx) (hIpos y hy) hα hβ hsum
  have htail := concaveOn_moving_packedCost hb hC (Nat.cast_nonneg k) hr
  refine ⟨hI, ?_⟩
  intro x hx y hy α β hα hβ hsum
  have h₁ := hfirst.2 hx hy hα hβ hsum
  have h₂ := htail.2 hx hy hα hβ hsum
  simp only [smul_eq_mul,packedCost,movingProfile] at h₁ h₂ ⊢
  linarith only [h₁,h₂]

theorem movingProfile_clock_convex {I : Set ℝ} (hI : Convex ℝ I)
    (hIpos : ∀ x ∈ I, 0 < x) (k : ℕ) (A B : ℝ) (C : ℝ → ℝ)
    (hC : ConvexOn ℝ I C)
    (hr : ∀ x ∈ I, A*x+B-(k : ℝ)*C x ∈ Icc (0 : ℝ) (C x))
    {Y : ℝ} (hY : 0 ≤ Y) :
    ConvexOn ℝ I (fun x => clock (movingProfile k A B C x) Y) := by
  exact convexOn_clock_family hI (movingProfile k A B C)
    (fun e he => movingProfile_concave hI (fun x hx => (hIpos x hx).le) k A B C hC hr he)
    (fun x _ => movingProfile_continuous k A B C x)
    (fun x _ => movingProfile_antitone k A B C x)
    (fun x hx e he => movingProfile_pos k A B C (hIpos x hx) he) hY

theorem small_chord_le_packed {e c r w : ℝ} (he : 0 < e) (hc : 0 < c)
    (k : ℕ) (hr : r ∈ Icc (0 : ℝ) (c^2))
    (hw : w*c^2 ≤ ((k : ℝ)+1)*c^2+r) :
    w*profile e c ≤ profile e c+(k : ℝ)*profile e c+profile e (Real.sqrt r) := by
  have hsq := Real.sq_sqrt hr.1
  have hq : Real.sqrt r ≤ c := (sq_le_sq₀ (Real.sqrt_nonneg r) hc.le).mp (by linarith only [hsq,hr.2])
  have hch := profile_ge_squared_chord he hc (Real.sqrt_nonneg r) hq
  rw [hsq] at hch
  have hw' : w ≤ (k : ℝ)+1+r/c^2 := by
    have hd : 0 < c^2 := sq_pos_of_pos hc
    have heq : (k : ℝ)+1+r/c^2=(((k : ℝ)+1)*c^2+r)/c^2 := by field_simp
    rw [heq]
    exact (le_div_iff₀ hd).mpr hw
  have hm := mul_le_mul_of_nonneg_right hw' (profile_pos he hc).le
  nlinarith only [hm,hch]

end
end CK.Profile
