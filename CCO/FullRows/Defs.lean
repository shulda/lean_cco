import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Prod

/-! Source-free full-row coordinates. Multiplication denotes the additive
elementary two-group in the source. A packet is the WHOLE pair `(i,f)`;
distinct rows over the same structural index remain distinct packets. -/
universe u v w
namespace CCO.FullRows

abbrev Row (I : Type u) (K : Type v) := I → K
abbrev Packet (I : Type u) (K : Type v) := I × Row I K
abbrev Vertex (I : Type u) (K : Type v) := Packet I K × K
abbrev Matrix (I : Type u) (K : Type v) := I → I → K

@[ext] structure Structural (I : Type u) (K : Type v) where
  sigma : I ≃ I
  offset : I → K

variable {I : Type u} {K : Type v}

/-- Only DISTINCT UNRECORDED structural pairs impose a correction equation. -/
def Legal (R : I → I → Prop) (C : Matrix I K) : Prop :=
  ∀ i j, i ≠ j → ¬R i j → C i j = C j i

section Group
variable [CommGroup K]

def translate (g : K) (x : Vertex I K) : Vertex I K := (x.1, g * x.2)
def projection (x : Vertex I K) : I × K := (x.1.1,x.2)
def baseMap (s : Structural I K) (x : I × K) : I × K :=
  (s.sigma x.1,x.2 * s.offset x.1)

def rowImage (s : Structural I K) (C : Matrix I K) (i : I)
    (f : Row I K) : Row I K :=
  fun j => f (s.sigma.symm j) * (C i (s.sigma.symm j) * s.offset i)

@[simp] theorem rowImage_apply_sigma (s : Structural I K) (C : Matrix I K)
    (i j : I) (f : Row I K) :
    rowImage s C i f (s.sigma j) = f j * (C i j * s.offset i) := by
  simp [rowImage]

def packetMap (s : Structural I K) (C : Matrix I K) (p : Packet I K) : Packet I K :=
  (s.sigma p.1,rowImage s C p.1 p.2)

def lift (s : Structural I K) (C : Matrix I K) (x : Vertex I K) : Vertex I K :=
  (packetMap s C x.1,x.2 * s.offset x.1.1)

def chi (x : Vertex I K) (j : I) : K := x.2 * x.1.2 j
def parameter (x y : Vertex I K) : K := chi x y.1.1 * chi y x.1.1

/-- Prescriptions use FULL rows; unused values of `r` impose no conditions. -/
def forced (s : Structural I K) (r : I → Row I K → Row I K)
    (i : I) (f : Row I K) (j : I) : K := r i f (s.sigma j) * f j * s.offset i

def Realizes (s : Structural I K) (T : I → Finset (Row I K))
    (r : I → Row I K → Row I K) (C : Matrix I K) : Prop :=
  ∀ i f, f ∈ T i → rowImage s C i f = r i f

def RC1 (s : Structural I K) (T : I → Finset (Row I K))
    (r : I → Row I K → Row I K) : Prop :=
  ∀ i f, f ∈ T i → ∀ f', f' ∈ T i → forced s r i f = forced s r i f'

def RC2 (s : Structural I K) (R : I → I → Prop)
    (T : I → Finset (Row I K)) (r : I → Row I K → Row I K) : Prop :=
  ∀ i j, i ≠ j → ¬R i j → ∀ f, f ∈ T i → ∀ f', f' ∈ T j →
    forced s r i f j = forced s r j f' i

end Group
end CCO.FullRows
