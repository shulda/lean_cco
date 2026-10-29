import Mathlib.Algebra.Group.Action.Basic
import CCO.OwnerTransversal.CountableColourLanguage
import CCO.OwnerTransversal.PacketBackAndForth

/-! The literal packet language contains EVERY unary translation,
owner name and fine-colour name.  For a finite group, its actual generated
substructures are precisely finite unions of packets. -/

open scoped FirstOrder
open FirstOrder FirstOrder.Language

universe u v w z z'
namespace CCO.OwnerTransversal.PacketLanguage
open CountableColour

inductive Function (K : Type u) : ℕ → Type u
  | translate : K → Function K 1

def language (K : Type u) (B : Type v) (C : Type w) : FirstOrder.Language.{u,max v w} where
  Functions := Function K
  Relations := Symbol B C

variable {K : Type u} [Group K] {B : Type v} {C : Type w}
variable {X : Type z} {Y : Type z'} [MulAction K X] [MulAction K Y]

@[instance_reducible]
def ofTable (T : Table B C X) : (language K B C).Structure X where
  funMap f x := match f with | .translate g => g • x 0
  RelMap r x := match r with
    | .owner b => T.owner (x 0) = b
    | .colour c => T.colour (x 0) (x 1) = c

/-- Genuine packet-language embeddings retain the complete literal
owner/colour tables and commute with every named translation. -/
theorem embedding_preserves (T : Table B C X) (U : Table B C Y)
    (f : @FirstOrder.Language.Embedding (language K B C) X Y (ofTable T) (ofTable U)) :
    (∀ x, U.owner (f x) = T.owner x) ∧
      (∀ x y, U.colour (f x) (f y) = T.colour x y) ∧
      (∀ g : K, ∀ x, f (g • x) = g • f x) := by
  let := ofTable (K := K) T
  let := ofTable (K := K) U
  refine ⟨?_,?_,?_⟩
  · intro x
    exact (f.map_rel (Symbol.owner (T.owner x)) (fun _ => x)).mpr rfl
  · intro x y
    exact (f.map_rel (Symbol.colour (T.colour x y)) (![x,y])).mpr rfl
  · intro g x
    exact f.map_fun (Function.translate g) (fun _ => x)

/-- Owner/colour preservation and translation commutation suffice for
an actual embedding of all symbols, including loops and same-packet pairs. -/
def embedding (T : Table B C X) (U : Table B C Y) (f : X ↪ Y)
    (ho : ∀ x, U.owner (f x) = T.owner x)
    (hc : ∀ x y, U.colour (f x) (f y) = T.colour x y)
    (ht : ∀ g : K, ∀ x, f (g • x) = g • f x) :
    @FirstOrder.Language.Embedding (language K B C) X Y (ofTable T) (ofTable U) := by
  letI := ofTable (K := K) T
  letI := ofTable (K := K) U
  exact {
    toFun := f
    inj' := f.injective
    map_fun' := by
      intro n F x
      cases F with
      | translate g => exact ht g (x 0)
    map_rel' := by
      intro n r x
      cases r with
      | owner b => exact (congrArg (· = b) (ho (x 0))).to_iff
      | colour c => exact (congrArg (· = c) (hc (x 0) (x 1))).to_iff }

def equiv (T : Table B C X) (U : Table B C Y) (f : X ≃ Y)
    (ho : ∀ x, U.owner (f x) = T.owner x)
    (hc : ∀ x y, U.colour (f x) (f y) = T.colour x y)
    (ht : ∀ g : K, ∀ x, f (g • x) = g • f x) :
    @FirstOrder.Language.Equiv (language K B C) X Y (ofTable T) (ofTable U) := by
  letI := ofTable (K := K) T
  letI := ofTable (K := K) U
  exact {
    toEquiv := f
    map_fun' := by
      intro n F x
      cases F with
      | translate g => exact ht g (x 0)
    map_rel' := by
      intro n r x
      cases r with
      | owner b => exact (congrArg (· = b) (ho (x 0))).to_iff
      | colour c => exact (congrArg (· = c) (hc (x 0) (x 1))).to_iff }

/-- Full substructures are closed under every named translation. -/
theorem translate_mem (T : Table B C X)
    (A : @FirstOrder.Language.Substructure (language K B C) X (ofTable T))
    (g : K) (x : X) (hx : x ∈ A) : g • x ∈ A := by
  let := ofTable (K := K) T
  exact A.fun_mem (Function.translate g) (fun _ => x) (fun _ => hx)

/-- Restrict the group action to any full named-function substructure. -/
@[instance_reducible]
def subaction (T : Table B C X)
    (A : @FirstOrder.Language.Substructure (language K B C) X (ofTable T)) : MulAction K A where
  smul g x := ⟨g • x.val,translate_mem T A g x.val x.property⟩
  one_smul x := Subtype.ext (one_smul K x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

@[simp] theorem coe_smul (T : Table B C X)
    (A : @FirstOrder.Language.Substructure (language K B C) X (ofTable T)) (g : K) (x : A) :
    letI := subaction T A
    ((g • x : A) : X) = g • (x : X) := rfl

def restrictTable (T : Table B C X)
    (A : @FirstOrder.Language.Substructure (language K B C) X (ofTable T)) : Table B C A where
  owner x := T.owner x.val
  colour x y := T.colour x.val y.val

/-- The actual group-orbit closure is a full substructure of the named
function language. No freeness or faithfulness is used. -/
def orbitClosure (T : Table B C X) (s : Set X) :
    @FirstOrder.Language.Substructure (language K B C) X (ofTable T) := by
  letI := ofTable (K := K) T
  exact {
    carrier := {x | ∃ g : K, ∃ a ∈ s, g • a = x}
    fun_mem := by
      intro n F x hx
      cases F with
      | translate g =>
        obtain ⟨k,a,ha,hka⟩ := hx 0
        exact ⟨g*k,a,ha,(mul_smul g k a).trans (congrArg (fun y => g • y) hka)⟩ }

/-- Closing under all t_g adds exactly whole orbits. -/
theorem closure_eq_orbit (T : Table B C X) (s : Set X) :
    letI := ofTable (K := K) T
    Substructure.closure (language K B C) s = orbitClosure T s := by
  letI := ofTable (K := K) T
  apply le_antisymm
  · apply Substructure.closure_le.mpr
    intro x hx
    exact ⟨1,x,hx,one_smul K x⟩
  · intro x hx
    obtain ⟨g,a,ha,rfl⟩ := hx
    exact (Substructure.closure (language K B C) s).fun_mem
      (Function.translate g) (fun _ => a) (fun _ => Substructure.subset_closure ha)

/-- Finite groups give finite closures of every finite real set. -/
theorem finite_closure [Finite K] (T : Table B C X) (s : Set X) (hs : s.Finite) :
    letI := ofTable (K := K) T
    Finite (Substructure.closure (language K B C) s) := by
  letI := ofTable (K := K) T
  rw [closure_eq_orbit T s]
  let : Finite ↥s := hs.to_subtype
  let f : K × ↥s → orbitClosure T s := fun p =>
    ⟨p.1 • p.2.val,p.1,p.2.val,p.2.property,rfl⟩
  apply Finite.of_surjective f
  rintro ⟨x,g,a,ha,rfl⟩
  exact ⟨(g,⟨a,ha⟩),rfl⟩

/-- The local-finiteness input for generic full-packet back-and-forth is
proved from the finite group, not supplied as an opaque source provider. -/
theorem locallyFinite [Finite K] (T : Table B C X) :
    @PacketBackAndForth.LocallyFinite (language K B C) X (ofTable T) := by
  letI := ofTable (K := K) T
  intro A hA
  obtain ⟨s,hs,rfl⟩ := Substructure.fg_def.mp hA
  exact finite_closure T s hs

end CCO.OwnerTransversal.PacketLanguage
