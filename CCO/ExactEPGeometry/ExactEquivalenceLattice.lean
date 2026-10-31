import CCO.RigidGroupoid.Geometry.Basic
import CCO.ParityHasse.Original.OrbitalAlgebra

/-!
# B062 E1: actual finite FULL-exact invariant-equivalence sublattice

The source's exact-equivalence lattice is not the whole finite invariant
equivalence lattice. This construction singles out only genuine represented
equality-inclusive RAW exact equivalences. Finite orbital support gives
finiteness; original HOM+CCO exact convolution makes joins exact, and
identity-inclusive nonempty meets remain exact.

All lattice operations are actual relations on a named ORIGINAL sort,
not formal quotients or an assumed external algebra. No SAP is imposed.
A following source instance must construct and analyse the current-sort
restriction homomorphism (E1).
-/

universe u v w t

namespace CCO.ExactEPGeometry

open CCO.ParityHasse.Original
open CCO.RigidGroupoid.Geometry

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The genuine full-RAW-exact members of the finite ORIGINAL
invariant-equivalence lattice. In particular this is NOT the whole
`ColourEq` lattice unless exactness is independently established. -/
abbrev ExactEq (i : ι) : Type _ :=
  {E : ColourEq S i // FullExact S (fun x y => E x y)}

namespace ExactEq

variable {S} {i : ι}

/-- The represented relation of a true exact equivalence. -/
instance : CoeFun (ExactEq S i) (fun _ => X i → X i → Prop) :=
  ⟨fun E => E.val⟩

instance : PartialOrder (ExactEq S i) := inferInstance

instance : Finite (ExactEq S i) := inferInstance

/-- Original Top is an actual inhabited RAW exact empty presentation. -/
def top : ExactEq S i :=
  ⟨(⊤ : ColourEq S i), fullExact_top S i i⟩

/-- Original Bottom is actual logical identity, not a diversity colour. -/
def bot : ExactEq S i :=
  ⟨(⊥ : ColourEq S i), fullExact_identity S i⟩

instance : OrderTop (ExactEq S i) where
  top := top
  le_top := by
    intro E
    change E.val ≤ (⊤ : ColourEq S i)
    exact le_top

instance : OrderBot (ExactEq S i) where
  bot := bot
  bot_le := by
    intro E
    change (⊥ : ColourEq S i) ≤ E.val
    exact bot_le

/-- Meet stays FULL exact by original RAW intersection with a witnessed
diagonal, independently of quotient SAP. -/
def inf (E F : ExactEq S i) : ExactEq S i := by
  let x : X i := Classical.choice (S.nonemptySort i)
  have hNE : TRel.Nonempty
      (fun a b : X i => E.val a b ∧ F.val a b) :=
    ⟨x,x,E.val.val.refl x,F.val.val.refl x⟩
  exact ⟨E.val ⊓ F.val,fullExact_meet S E.property F.property hNE⟩

instance : SemilatticeInf (ExactEq S i) where
  inf := inf
  inf_le_left := by
    intro E F
    change E.val ⊓ F.val ≤ E.val
    exact inf_le_left
  inf_le_right := by
    intro E F
    change E.val ⊓ F.val ≤ F.val
    exact inf_le_right
  le_inf := by
    intro E F K hE hF
    change E.val ≤ F.val ⊓ K.val
    exact le_inf hE hF

/-- Equality of actual pair relations suffices to identify original
exact-equivalence objects, including their proof-irrelevant exactness. -/
@[ext] theorem ext {E F : ExactEq S i}
    (h : ∀ x y : X i, E x y ↔ F x y) : E = F :=
  Subtype.ext (ColourEq.ext h)

/-- In the ONE named original symmetric sort, the join of two exact
equivalences is their represented product. Its RAW exactness follows from
the accepted HOM+CCO calculus, NOT from quotient SAP. -/
def sup {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (E F : ExactEq S i) : ExactEq S i := by
  letI := ColourEq.lattice S H (i := i)
  let J := ColourEq.join S H E.val F.val
  have hComp : FullExact S
      (TRel.comp (fun x y : X i => E x y) (fun x y => F x y)) :=
    (exactCalculus_of_homogeneous_CCO S H cco).comp E.property F.property
  have hRelation :
      (fun x y : X i => J x y) =
      TRel.comp (fun x y : X i => E x y) (fun x y => F x y) := by
    funext x y
    apply propext
    exact sup_relation_iff S H E.val F.val x y
  refine ⟨J,?_⟩
  rw [hRelation]
  exact hComp

/-- A finite genuine FULL-exact equivalence lattice for one actual
source sort. The inherited order is inclusion, its meet is intersection,
and its join is actual represented relational product. -/
@[instance_reducible] def lattice
    {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    Lattice (ExactEq S i) where
  __ := (inferInstance : SemilatticeInf (ExactEq S i))
  sup := sup H cco
  le_sup_left := by
    intro E F
    letI := ColourEq.lattice S H (i := i)
    change E.val ≤ ColourEq.join S H E.val F.val
    exact le_sup_left
  le_sup_right := by
    intro E F
    letI := ColourEq.lattice S H (i := i)
    change F.val ≤ ColourEq.join S H E.val F.val
    exact le_sup_right
  sup_le := by
    intro E F K hE hF
    letI := ColourEq.lattice S H (i := i)
    change ColourEq.join S H E.val F.val ≤ K.val
    exact sup_le hE hF

end ExactEq
end CCO.ExactEPGeometry
