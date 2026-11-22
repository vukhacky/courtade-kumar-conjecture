module
public import CK.Certificate.PointCertificates

/-! The five real-valued scalar margins checked in the compact correlation range. -/
@[expose] public section
set_option autoImplicit false
namespace CK.Certificate.Compact
noncomputable section

def P : ℝ := Real.pi^2/4
def L : ℝ := Real.log 2
def CS : ℝ := (Real.pi/2-1)^2/(L-1/2)
def q (u : ℝ) : ℝ := Real.exp (-2*u)
def rho (u : ℝ) : ℝ := (1-q u)/(1+q u)
def raw (u : ℝ) : ℝ := Real.log (1+q u)/(q u)+2*u/(1+q u)
def F (u : ℝ) : ℝ := q u*raw u/rho u
def z (u : ℝ) : ℝ := Real.log u+u/25-2/5
def t (u : ℝ) : ℝ := 49*u/100+7/5
def first (u : ℝ) : ℝ := Real.exp (-1/5-51*u/50)/2
def extra (u : ℝ) : ℝ := Real.exp (1/4-31*u/20)
def G (u : ℝ) : ℝ := first u+extra u
def R (u : ℝ) : ℝ := Real.exp (53*u/100-9/20)/2
def w (u : ℝ) : ℝ := Real.exp (-9*u/20-1/4)/(1+R u)
def d (u : ℝ) : ℝ := 4*q u/(1+q u)^2
def psi (u : ℝ) : ℝ := raw u-4*L/(1+q u)^2

def cap (u : ℝ) : ℝ := 1-2*Real.exp (-u)
def top (u : ℝ) : ℝ := u+(2*u+1)*Real.log (cap u)/(4*u+1)
def upperSource (u : ℝ) : ℝ :=
  Real.exp (-2*(u-top u))*(2*u+1)/(2*top u+1)

def master (u : ℝ) : ℝ :=
  let a := Real.exp (-9*u/20-1/4)
  let D := 1+R u+t u*a
  (P*t u*(rho u)^2*(1+R u)-extra u*D*(1+R u)*CS*psi u-rho u*u*D)*
    (1+t u*a)*z u*F (z u)-P*first u*(1+R u)^2*rho u*raw u*u

inductive PointKind where | low | middle | top deriving DecidableEq, Repr
inductive Branch where | logarithmic | quadratic deriving DecidableEq, Repr

def pointHeight (u : ℝ) : PointKind → ℝ
  | .low => z u | .middle => 2*u/3 | .top => top u

def sourceDiff (u : ℝ) : PointKind → ℝ
  | .middle => u/3 | _ => 24*u/25-Real.log u+2/5

def sourceA (u : ℝ) (kind : PointKind) : ℝ :=
  let v := pointHeight u kind
  match kind with
  | .top => upperSource u
  | _ => Real.exp (-2*sourceDiff u kind)*(raw u*rho v/(raw v*rho u))

def sourceLog (u : ℝ) (kind : PointKind) : ℝ :=
  let v := pointHeight u kind
  Real.log 4+2*sourceDiff u kind+Real.log (raw v)+Real.log (rho u)-
    Real.log (raw u)-Real.log (rho v)

def endpointMargin (u : ℝ) (branch : Branch) (kind : PointKind) : ℝ :=
  let v := pointHeight u kind
  let anchor := match branch with | .logarithmic => z u | .quadratic => top u
  let sh := (Real.exp anchor-Real.exp (-anchor))/2
  let theta := Real.arctan sh
  let eq := Real.exp (-2*anchor)
  let chord := theta^2*(1+eq)/(1-eq)
  let constant := 1-(1-theta/sh)^2
  let arcnum := match kind with | .middle => constant*(v-anchor)+chord | _ => chord
  let a := sourceA u kind
  let base := P*t u*(rho u)^2-(G u+t u*q u)*CS*psi u
  let firstterm := v*(1+w u)*(1+2*w u)*base-
    u*rho u*(1+t u*w u)*(1+w u)*(1+2*w u)*arcnum
  let aterm := u*P*(rho u)^2*(1+t u*w u+(t u-2)*d u*(1+w u))*a
  let ktermmult := u*P*(t u-2)*(rho u)^4*(1+w u)
  match branch with
  | .logarithmic => (firstterm-aterm)*sourceLog u kind-ktermmult*2*(1-a/4)
  | .quadratic => firstterm-aterm-ktermmult*(1+a)/2

def lowerLogMargin (u : ℝ) : ℝ := endpointMargin u .logarithmic .low
def middleLogMargin (u : ℝ) : ℝ := endpointMargin u .logarithmic .middle
def middleQuadMargin (u : ℝ) : ℝ := endpointMargin u .quadratic .middle
def upperQuadMargin (u : ℝ) : ℝ := endpointMargin u .quadratic .top

end
end CK.Certificate.Compact
