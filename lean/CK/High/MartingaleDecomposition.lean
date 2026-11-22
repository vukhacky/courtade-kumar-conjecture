module

public import CK.High.InfluenceVariance
public import CK.Functional.LogSobolev

/-! Ordered finite Doob increments outside an arbitrary retained set.
Every increment is an actual coordinate projection followed by a partial
difference; the Fourier partition proves the exact two energy identities. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def projectionResidual {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) : Cube n → ℝ :=
  fun x => g x-coordinateProjection K g x

def martingaleWindow {n : ℕ} (K : Finset (Fin n)) (i : Fin n) : Finset (Fin n) :=
  K ∪ Finset.Iic i

def martingaleSelect {n : ℕ} (K : Finset (Fin n)) (i : Fin n) (S : Finset (Fin n)) : Prop :=
  i ∉ K ∧ i∈S ∧ S ⊆ martingaleWindow K i

instance {n : ℕ} (K : Finset (Fin n)) (i : Fin n) (S : Finset (Fin n)) :
    Decidable (martingaleSelect K i S) := by
  unfold martingaleSelect
  infer_instance

noncomputable def martingalePiece {n : ℕ} (K : Finset (Fin n)) (i : Fin n)
    (g : Cube n → ℝ) : Cube n → ℝ :=
  if i∈K then fun _ => 0 else coordinatePartial i (coordinateProjection (martingaleWindow K i) g)

theorem fourier_projectionResidual {n : ℕ} (K : Finset (Fin n))
    (g : Cube n → ℝ) (S : Finset (Fin n)) :
    fourier (projectionResidual K g) S = if S⊆K then 0 else fourier g S := by
  unfold projectionResidual
  rw [fourier_sub,fourier_coordinateProjection]
  split_ifs <;> ring

theorem avg_projectionResidual {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) :
    avg (projectionResidual K g)=0 := by
  unfold projectionResidual
  rw [avg_sub,avg_coordinateProjection,sub_self]

theorem fourier_martingalePiece {n : ℕ} (K : Finset (Fin n)) (i : Fin n)
    (g : Cube n → ℝ) (S : Finset (Fin n)) :
    fourier (martingalePiece K i g) S = if martingaleSelect K i S then fourier g S else 0 := by
  classical
  unfold martingalePiece martingaleSelect
  by_cases hi : i∈K
  · simp [hi,fourier_const]
  · rw [ite_eq_right hi,fourier_coordinatePartial,fourier_coordinateProjection]
    by_cases hiS : i∈S <;> by_cases hS : S⊆martingaleWindow K i <;> simp [hi,hiS,hS]

/-- Each Fourier mode outside `K` belongs to exactly the increment
indexed by its largest coordinate outside `K`. -/
theorem martingale_select_sum {n : ℕ} (K S : Finset (Fin n)) (c : ℝ) :
    (∑ i : Fin n, if martingaleSelect K i S then c else 0) = if S⊆K then 0 else c := by
  classical
  by_cases hSK : S⊆K
  · rw [ite_eq_left hSK]
    apply Finset.sum_eq_zero
    intro i _
    have hi : ¬martingaleSelect K i S := by
      intro h
      exact h.1 (hSK h.2.1)
    rw [ite_eq_right hi]
  · rw [ite_eq_right hSK]
    have hT : (S\K).Nonempty := Finset.sdiff_nonempty.mpr hSK
    let i := (S\K).max' hT
    have hiT : i∈S\K := Finset.max'_mem _ _
    have hiS : i∈S := (Finset.mem_sdiff.mp hiT).1
    have hiK : i∉K := (Finset.mem_sdiff.mp hiT).2
    have hselect : martingaleSelect K i S := by
      refine ⟨hiK,hiS,?_⟩
      intro j hj
      by_cases hjK : j∈K
      · exact Finset.mem_union_left _ hjK
      · apply Finset.mem_union_right
        rw [Finset.mem_Iic]
        exact Finset.le_max' (S\K) j (Finset.mem_sdiff.mpr ⟨hj,hjK⟩)
    have huniq (j : Fin n) (hj : martingaleSelect K j S) : j=i := by
      apply le_antisymm
      · exact Finset.le_max' (S\K) j (Finset.mem_sdiff.mpr ⟨hj.2.1,hj.1⟩)
      · have his := hj.2.2 hiS
        change i∈K ∪ Finset.Iic j at his
        rcases Finset.mem_union.mp his with h | h
        · exact (hiK h).elim
        · exact Finset.mem_Iic.mp h
    calc
      _ = if martingaleSelect K i S then c else 0 := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          rw [ite_eq_right (fun h => hji (huniq j h))]
        · intro h
          exact (h (Finset.mem_univ i)).elim
      _ = c := ite_eq_left hselect

theorem martingale_square_energy {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) :
    (∑ i : Fin n, avg (fun x => martingalePiece K i g x^2)) =
      avg (fun x => projectionResidual K g x^2) := by
  classical
  simp only [parseval,fourier_martingalePiece,fourier_projectionResidual,
    ite_pow,zero_pow (by decide : 2 ≠ 0)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  exact martingale_select_sum K S (fourier g S^2)

theorem martingale_dirichlet_energy {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) :
    (∑ i : Fin n, dirichlet (martingalePiece K i g)) = dirichlet (projectionResidual K g) := by
  classical
  simp only [dirichlet_eq_fourier,fourier_martingalePiece,fourier_projectionResidual,
    ite_pow,zero_pow (by decide : 2 ≠ 0),mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  exact martingale_select_sum K S ((S.card : ℝ)*fourier g S^2)

theorem martingalePiece_l1_le {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) (i : Fin n) :
    avg (fun x => |martingalePiece K i g x|) ≤ if i∈K then 0 else coordinateL1 g i := by
  classical
  unfold martingalePiece
  by_cases hi : i∈K
  · simp [hi]
  · rw [ite_eq_right hi,ite_eq_right hi]
    exact coordinateL1_projection_le (martingaleWindow K i) g i

theorem coordinatePartial_flip {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) :
    coordinatePartial i g (flipCoordinate i x) = -coordinatePartial i g x := by
  rw [coordinatePartial,flipCoordinate_involutive i x,coordinatePartial]
  ring

theorem martingalePiece_flip {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ)
    (i : Fin n) (x : Cube n) :
    martingalePiece K i g (flipCoordinate i x) = -martingalePiece K i g x := by
  unfold martingalePiece
  split_ifs
  · simp
  · exact coordinatePartial_flip i _ x

theorem twoPointEntropy_self (a : ℝ) : twoPointEntropy a a=0 := by
  unfold twoPointEntropy
  rw [show (a+a)/2=a by ring]
  ring

theorem square_coordinateEntropy_of_odd {n : ℕ} (i : Fin n) (g : Cube n → ℝ)
    (hg : ∀ x, g (flipCoordinate i x) = -g x) (x : Cube n) :
    coordinateEntropy (fun y => g y^2) i x=0 := by
  have he : flipCoordinate i (Function.update x i false) = Function.update x i true := by
    simp [flipCoordinate]
  have h := hg (Function.update x i false)
  rw [he] at h
  change twoPointEntropy (g (Function.update x i false)^2) (g (Function.update x i true)^2)=0
  rw [h,neg_sq,twoPointEntropy_self]

/-- Log-Sobolev after removing a sign coordinate.  Tensorization shows
that this coordinate contributes zero entropy but contributes all the
square mass to Dirichlet energy. -/
theorem entropyFunctional_square_odd_le {n : ℕ} (i : Fin n) (g : Cube n → ℝ)
    (hg : ∀ x, g (flipCoordinate i x) = -g x) :
    entropyFunctional (fun x => g x^2) ≤ 2*(dirichlet g-avg (fun x => g x^2)) := by
  classical
  have hpartial (x : Cube n) : coordinatePartial i g x=g x := by
    unfold coordinatePartial
    rw [hg]
    ring
  have hbound (j : Fin n) (x : Cube n) : coordinateEntropy (fun y => g y^2) j x ≤
      2*coordinatePartial j g x^2 - if j=i then 2*g x^2 else 0 := by
    by_cases hj : j=i
    · subst j
      rw [square_coordinateEntropy_of_odd i g hg x,hpartial,ite_eq_left rfl,sub_self]
    · rw [ite_eq_right hj,sub_zero,two_mul_partial_sq_eq_update]
      exact twoPointEntropy_sq_le _ _
  calc
    _ ≤ ∑ j : Fin n, avg (coordinateEntropy (fun x => g x^2) j) :=
      entropyFunctional_tensorization n (fun x => g x^2) (fun x => sq_nonneg (g x))
    _ ≤ ∑ j : Fin n, avg (fun x => 2*coordinatePartial j g x^2 - if j=i then 2*g x^2 else 0) :=
      Finset.sum_le_sum (fun j _ => avg_mono (hbound j))
    _ = 2*(dirichlet g-avg (fun x => g x^2)) := by
      simp only [avg_sub,avg_smul,Finset.sum_sub_distrib,← Finset.mul_sum,← dirichlet_eq_sum_partials]
      have he : (∑ j : Fin n, avg (fun x => if j=i then 2*g x^2 else 0)) = 2*avg (fun x => g x^2) := by
        have hj (j : Fin n) : avg (fun x => if j=i then 2*g x^2 else 0) =
            if j=i then 2*avg (fun x => g x^2) else 0 := by
          by_cases hji : j=i <;> simp [hji,avg_smul]
        simp_rw [hj]
        simp
      rw [he]
      ring

end
end CK
