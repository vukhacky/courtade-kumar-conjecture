module

public import CK.Profile.Packing

/-! Finite packing of capped squares. The redistribution is a proved
finite induction; no dimension bound or numerical sampling is used. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Set
namespace CK.Profile
noncomputable section

theorem concave_pair_endpoints_le {b : ℝ → ℝ}
    (hb : ConcaveOn ℝ (Ici (0 : ℝ)) b) {a d x y : ℝ}
    (ha : 0 ≤ a) (hax : a ≤ x) (hxd : x ≤ d) (hay : a ≤ y) (hyd : y ≤ d)
    (hs : x+y=a+d) : b a+b d ≤ b x+b y := by
  have had : a ≤ d := hax.trans hxd
  obtain heq | hlt := had.eq_or_lt
  · have hx : x=a := by linarith
    have hy : y=a := by linarith
    simp [hx, hy, ← heq]
  have hden : 0 < d-a := sub_pos.mpr hlt
  have hw₁ : 0 ≤ (d-x)/(d-a) := div_nonneg (sub_nonneg.mpr hxd) hden.le
  have hw₂ : 0 ≤ (x-a)/(d-a) := div_nonneg (sub_nonneg.mpr hax) hden.le
  have hsum : (d-x)/(d-a)+(x-a)/(d-a)=1 := by field_simp; ring
  have hxarg : ((d-x)/(d-a))*a+((x-a)/(d-a))*d=x := by
    field_simp
    ring
  have hyarg : ((x-a)/(d-a))*a+((d-x)/(d-a))*d=y := by
    field_simp
    nlinarith only [congrArg (fun z : ℝ => z*(d-a)) hs]
  have hxj := hb.2 ha (ha.trans had) hw₁ hw₂ hsum
  have hyj := hb.2 ha (ha.trans had) hw₂ hw₁ (by linarith only [hsum])
  simp only [smul_eq_mul, hxarg, hyarg] at hxj hyj
  have hwba := congrArg (fun z : ℝ => z*b a) hsum
  have hwbd := congrArg (fun z : ℝ => z*b d) hsum
  nlinarith only [hxj, hyj, hwba, hwbd]

theorem exists_packed_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → ℝ)
    {b : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hb : ConcaveOn ℝ (Ici (0 : ℝ)) b) (hb0 : b 0=0)
    (hu : ∀ i ∈ s, u i ∈ Icc (0 : ℝ) c) :
    ∃ k : ℕ, ∃ r : ℝ, r ∈ Ico (0 : ℝ) c ∧
      (∑ i ∈ s, u i)=(k : ℝ)*c+r ∧
      (k : ℝ)*b c+b r ≤ ∑ i ∈ s, b (u i) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, 0, ⟨le_rfl, hc⟩, ?_, ?_⟩ <;> simp [hb0]
  | @insert i s hi ih =>
    obtain ⟨k, r, hr, hsum, hcost⟩ := ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
    have hui := hu i (Finset.mem_insert_self i s)
    by_cases hlt : u i+r < c
    · have hpair := concave_pair_endpoints_le hb
        (a := 0) (d := u i+r) (x := u i) (y := r)
        le_rfl hui.1 (by linarith [hr.1]) hr.1 (by linarith [hui.1]) (by ring)
      rw [hb0, zero_add] at hpair
      refine ⟨k, u i+r, ⟨add_nonneg hui.1 hr.1, hlt⟩, ?_, ?_⟩
      · rw [Finset.sum_insert hi, hsum]
        ring
      · rw [Finset.sum_insert hi]
        linarith only [hcost, hpair]
    · have hge : c ≤ u i+r := le_of_not_gt hlt
      have hpair := concave_pair_endpoints_le hb
        (a := u i+r-c) (d := c) (x := u i) (y := r)
        (by linarith only [hge]) (by linarith [hr.2]) hui.2
        (by linarith only [hui.2]) hr.2.le (by ring)
      refine ⟨k+1, u i+r-c, ⟨by linarith only [hge], by linarith only [hui.2, hr.2]⟩, ?_, ?_⟩
      · rw [Finset.sum_insert hi, hsum]
        push_cast
        ring
      · rw [Finset.sum_insert hi]
        push_cast
        nlinarith only [hcost, hpair]

theorem packed_cost_mono_mass {b : ℝ → ℝ} {c r s : ℝ} {k l : ℕ}
    (hc : 0 < c) (hb : MonotoneOn b (Ici (0 : ℝ))) (hb0 : b 0=0)
    (hr : r ∈ Ico (0 : ℝ) c) (hs : s ∈ Ico (0 : ℝ) c)
    (hm : (k : ℝ)*c+r ≤ (l : ℝ)*c+s) :
    (k : ℝ)*b c+b r ≤ (l : ℝ)*b c+b s := by
  have hbc : 0 ≤ b c := by simpa only [hb0] using hb (show (0 : ℝ) ∈ Ici 0 from le_rfl) hc.le hc.le
  have hbs : 0 ≤ b s := by simpa only [hb0] using hb (show (0 : ℝ) ∈ Ici 0 from le_rfl) hs.1 hs.1
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · have hcast : (k : ℝ)+1 ≤ l := by exact_mod_cast hkl
    have hbr := hb hr.1 hc.le hr.2.le
    have h := mul_le_mul_of_nonneg_right hcast hbc
    nlinarith only [hbr, h, hbs]
  · subst l
    have hrs : r ≤ s := by linarith only [hm]
    linarith only [hb hr.1 hs.1 hrs]
  · have hcast : (l : ℝ)+1 ≤ k := by exact_mod_cast hlk
    have h := mul_le_mul_of_nonneg_right hcast hc.le
    exfalso
    nlinarith only [h, hm, hr.1, hs.2]

/-- The sharp finite capped-mass lower bound used in source `jp:profile`. -/
theorem packed_sum_lower_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → ℝ)
    {b : ℝ → ℝ} {c r : ℝ} (hc : 0 < c)
    (hb : ConcaveOn ℝ (Ici (0 : ℝ)) b) (hmono : MonotoneOn b (Ici (0 : ℝ)))
    (hb0 : b 0=0) (hu : ∀ i ∈ s, u i ∈ Icc (0 : ℝ) c)
    (k : ℕ) (hr : r ∈ Ico (0 : ℝ) c)
    (hm : (k : ℝ)*c+r ≤ ∑ i ∈ s, u i) :
    (k : ℝ)*b c+b r ≤ ∑ i ∈ s, b (u i) := by
  obtain ⟨l, v, hv, heq, hcost⟩ := exists_packed_sum s u hc hb hb0 hu
  exact (packed_cost_mono_mass hc hmono hb0 hr hv (by simpa only [heq] using hm)).trans hcost

theorem packed_profile_le_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) {e c r : ℝ} (he : 0 < e) (hc : 0 < c)
    (ha : ∀ i ∈ s, a i ∈ Icc (0 : ℝ) c)
    (k : ℕ) (hr : r ∈ Ico (0 : ℝ) (c^2))
    (hm : (k : ℝ)*c^2+r ≤ ∑ i ∈ s, (a i)^2) :
    (k : ℝ)*profile e c+profile e (Real.sqrt r) ≤ ∑ i ∈ s, profile e (a i) := by
  have hmono : MonotoneOn (fun x => profile e (Real.sqrt x)) (Ici (0 : ℝ)) := by
    intro x hx y hy hxy
    exact profile_mono_right he (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hxy)
  have h := packed_sum_lower_bound s (fun i => (a i)^2) (sq_pos_of_pos hc)
    (concaveOn_profile_sqrt he) hmono (by simp)
    (fun i hi => ⟨sq_nonneg _, (sq_le_sq₀ (ha i hi).1 hc.le).2 (ha i hi).2⟩)
    k hr hm
  have heq : (∑ i ∈ s, profile e (Real.sqrt ((a i)^2))) = ∑ i ∈ s, profile e (a i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.sqrt_sq (ha i hi).1]
  simpa only [Real.sqrt_sq hc.le, heq] using h

end
end CK.Profile
