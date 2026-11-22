module

public import Mathlib.Tactic

/-! A computable Horner-to-Bernstein positivity checker. The transformation
updates Pascal rows along with the coefficient vector, avoiding expansion of
large powers by ring normalization. Its soundness is proved for every rational
input polynomial and every real argument in the full unit interval. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate.Dense
noncomputable section

def eval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c::cs, x => (c : ℝ)+x*eval cs x

def add : List ℚ → List ℚ → List ℚ
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => (x+y)::add xs ys

def scale (c : ℚ) (xs : List ℚ) : List ℚ := xs.map (c*·)

def basisEval : ℕ → List ℚ → ℝ → ℝ
  | _, [], _ => 0
  | n, c::cs, x => (c : ℝ)*(1-x)^n+x*basisEval (n-1) cs x

def pascalRow : ℕ → List ℚ
  | 0 => [1]
  | n+1 => let r := pascalRow n; add r (0::r)

/-- The first component is the next Pascal row. Sharing it avoids repeated
binomial computations when a high-degree certificate is reduced in the kernel. -/
def bernsteinState : List ℚ → List ℚ × List ℚ
  | [] => ([1], [])
  | c::cs => let s := bernsteinState cs
             (add s.1 (0::s.1), add (scale c s.1) (0::s.2))

def toBernstein (cs : List ℚ) : List ℚ := (bernsteinState cs).2

def checkNonneg (cs : List ℚ) : Bool := (toBernstein cs).all (fun c => decide (0 ≤ c))

theorem eval_add (xs ys : List ℚ) (x : ℝ) : eval (add xs ys) x = eval xs x+eval ys x := by
  induction xs generalizing ys with
  | nil => simp [add,eval]
  | cons a xs ih =>
    cases ys with
    | nil => simp [add,eval]
    | cons b ys => simp only [add,eval,Rat.cast_add,ih]; ring

theorem eval_scale (c : ℚ) (xs : List ℚ) (x : ℝ) : eval (scale c xs) x = (c : ℝ)*eval xs x := by
  induction xs with
  | nil => simp [scale,eval]
  | cons a xs ih => simp only [scale,List.map_cons,eval,Rat.cast_mul] at *; rw [ih]; ring

theorem length_add (xs ys : List ℚ) : (add xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [add]
  | cons a xs ih =>
    cases ys with
    | nil => simp [add]
    | cons b ys => simp [add,ih,Nat.succ_max_succ]

theorem basisEval_add (n : ℕ) (xs ys : List ℚ) (x : ℝ) :
    basisEval n (add xs ys) x = basisEval n xs x+basisEval n ys x := by
  induction xs generalizing ys n with
  | nil => simp [add,basisEval]
  | cons a xs ih =>
    cases ys with
    | nil => simp [add,basisEval]
    | cons b ys => simp only [add,basisEval,Rat.cast_add,ih]; ring

theorem basisEval_scale (n : ℕ) (c : ℚ) (xs : List ℚ) (x : ℝ) :
    basisEval n (scale c xs) x = (c : ℝ)*basisEval n xs x := by
  induction xs generalizing n with
  | nil => simp [scale,basisEval]
  | cons a xs ih =>
    simp only [scale,List.map_cons,basisEval,Rat.cast_mul] at *
    rw [ih]
    ring

theorem pascalRow_length (n : ℕ) : (pascalRow n).length = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pascalRow,length_add,ih]

theorem basisEval_succ_degree (n : ℕ) (xs : List ℚ) (x : ℝ)
    (hlen : xs.length ≤ n+1) :
    basisEval (n+1) xs x = (1-x)*basisEval n xs x := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [basisEval]
    | cons a xs =>
      have hx : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst xs
      simp [basisEval]
      ring
  | succ n ih =>
    cases xs with
    | nil => simp [basisEval]
    | cons a xs =>
      have hx : xs.length ≤ n+1 := by simpa using hlen
      simp only [basisEval,Nat.add_sub_cancel]
      rw [ih xs hx]
      rw [pow_succ (1-x) (n+1)]
      ring

theorem basisEval_pascalRow (n : ℕ) (x : ℝ) : basisEval n (pascalRow n) x = 1 := by
  induction n with
  | zero => simp [pascalRow,basisEval]
  | succ n ih =>
    rw [pascalRow,basisEval_add,basisEval_succ_degree n (pascalRow n) x (by rw [pascalRow_length])]
    simp only [basisEval,Rat.cast_zero,zero_mul,zero_add,Nat.add_sub_cancel,ih]
    ring

theorem bernsteinState_fst (cs : List ℚ) : (bernsteinState cs).1 = pascalRow cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [bernsteinState,List.length_cons,pascalRow,ih]

theorem toBernstein_cons (c : ℚ) (cs : List ℚ) :
    toBernstein (c::cs) = add (scale c (pascalRow cs.length)) (0::toBernstein cs) := by
  simp only [toBernstein,bernsteinState,bernsteinState_fst]

theorem toBernstein_sound (cs : List ℚ) (x : ℝ) :
    basisEval (cs.length-1) (toBernstein cs) x = eval cs x := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [toBernstein_cons]
    simp only [List.length_cons,Nat.add_sub_cancel,basisEval_add,basisEval_scale,
      basisEval_pascalRow,basisEval,Rat.cast_zero,zero_mul,zero_add,mul_one,ih,eval]

theorem basisEval_nonneg (n : ℕ) (cs : List ℚ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hc : ∀ c ∈ cs, 0 ≤ c) : 0 ≤ basisEval n cs x := by
  induction cs generalizing n with
  | nil => simp [basisEval]
  | cons c cs ih =>
    have h0 : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc c (by simp)
    have ht := ih (n-1) (fun d hd => hc d (by simp [hd]))
    change 0 ≤ (c : ℝ)*(1-x)^n+x*basisEval (n-1) cs x
    exact add_nonneg (mul_nonneg h0 (pow_nonneg (sub_nonneg.mpr hx.2) n)) (mul_nonneg hx.1 ht)

/-- Soundness of the finite exact rational check on the entire unit interval. -/
theorem checkNonneg_sound {cs : List ℚ} (h : checkNonneg cs = true)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ eval cs x := by
  have hc : ∀ c ∈ toBernstein cs, 0 ≤ c := by
    intro c hc
    exact of_decide_eq_true ((List.all_eq_true.mp h) c hc)
  have hp := basisEval_nonneg (cs.length-1) (toBernstein cs) hx hc
  rwa [toBernstein_sound] at hp

end
end CK.Certificate.Dense
