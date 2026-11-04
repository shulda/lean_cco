import CCO.CloneTupleGeometry.TypedSourceMap
import CCO.TerminalPowers.FullSource
import CCO.APCharacter.SourceAge.UnarySourceHomogeneity

/-!
# B060 N02: genuine homogeneous full-automorphism transport

An actual complete typed source isomorphism transports the full
automorphism group action backwards by point conjugation. The exact
optional pair-colour identity makes the conjugated permutations
literal full automorphisms of the source. The finite-diagram
homogeneity of the target then transports to full-source
homogeneity of the source, retaining the same complete sort and
atom names. This proof does NOT assume an action quotient section.

The true B047 marked successor is already homogeneous by B047.
Its new explicit B060 source isomorphism therefore supplies
homogeneity of the pure clone of its actual owner-child source.
Descending this homogeneity to the OWNER source is a further step.
-/

universe u v w t
namespace CCO.CloneTupleGeometry.TypedAtomicSourceEquiv

open TerminalPowers
variable {ι : Type u} {X Y : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,v,w} ι Y}

/-- A true whole-source automorphism conjugated along the complete
typed point bijections is still a true full automorphism. -/
noncomputable def pullbackFullAut (E : TypedAtomicSourceEquiv S T)
    (g : FullAut T) : FullAut S := by
  refine ⟨fun i => ((E.point i).trans (g.val i)).trans (E.point i).symm, ?_⟩
  intro i j x y
  change S.colour
      ((E.point i).symm (g.val i (E.point i x)))
      ((E.point j).symm (g.val j (E.point j y))) =
    S.colour x y
  have hT := E.colour
    ((E.point i).symm (g.val i (E.point i x)))
    ((E.point j).symm (g.val j (E.point j y)))
  have hT' :
      T.colour (g.val i (E.point i x)) (g.val j (E.point j y)) =
        (S.colour
          ((E.point i).symm (g.val i (E.point i x)))
          ((E.point j).symm (g.val j (E.point j y)))).map (E.atom i j) := by
    simpa only [Equiv.apply_symm_apply] using hT
  apply Option.map_injective (E.atom i j).injective
  calc
    (S.colour
      ((E.point i).symm (g.val i (E.point i x)))
      ((E.point j).symm (g.val j (E.point j y)))).map (E.atom i j) =
        T.colour (g.val i (E.point i x)) (g.val j (E.point j y)) :=
          hT'.symm
    _ = T.colour (E.point i x) (E.point j y) := g.property i j _ _
    _ = (S.colour x y).map (E.atom i j) := E.colour x y

/-- The pointwise conjugation law is an ACTUAL equality of whole
Sigma-points, not a presupposed quotient compatibility. -/
theorem sigmaPoint_pullbackFullAut (E : TypedAtomicSourceEquiv S T)
    (g : FullAut T) (p : Sigma X) :
    sigmaPoint E (pullbackFullAut E g • p) =
      g • sigmaPoint E p := by
  rcases p with ⟨i,x⟩
  change (⟨i,E.point i ((E.point i).symm (g.val i (E.point i x)))⟩ : Sigma Y) =
    ⟨i,g.val i (E.point i x)⟩
  rw [Equiv.apply_symm_apply]

/-- Finite complete-diagram homogeneity transports across a genuine
sort-preserving typed atomic source equivalence. The target may have
ANY known actual homogeneous action; its full automorphism action is
then used, rather than postulating a section of that action. -/
theorem homogeneous_pullback
    (E : TypedAtomicSourceEquiv S T)
    {G : Type t} [Group G] [∀ i : ι, MulAction G (Y i)]
    (H : HomogeneousSource T G) :
    HomogeneousSource S (FullAut S) := by
  have Hfull : HomogeneousSource T (FullAut T) :=
    full_homogeneous T H
  refine ⟨?_,?_,?_⟩
  · intro g p
    rfl
  · rintro g ⟨i,x⟩ ⟨j,y⟩
    exact congrArg
      (fun z : Option (S.Atom i j) =>
        (⟨i,j,z⟩ : Σ i, Σ j, Option (S.Atom i j)))
      (fullAut_colour S g i j x y)
  · intro V _ f h hc
    obtain ⟨g,hg⟩ := Hfull.extends_finite_diagram
      (fun a => sigmaPoint E (f a))
      (fun a => sigmaPoint E (h a))
      (finite_diagram_map E f h hc)
    refine ⟨pullbackFullAut E g,?_⟩
    intro a
    apply (sigmaPoint E).injective
    exact (sigmaPoint_pullbackFullAut E g (f a)).trans (hg a)

end CCO.CloneTupleGeometry.TypedAtomicSourceEquiv

namespace CCO.CloneTupleGeometry

open APCharacter
open APCharacter.SourceAge
open RigidGroupoid.Geometry
open TerminalPowers
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (C : ExactCalculus (CloneSAP.source S))
variable {r : ι} {A : Kernel (CloneSAP.source S) r}
variable (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

-- The one concrete dependent FullAut group has a large reducible index family.
-- This only adjusts elaboration of its existing inferred instance, not the theorem.
set_option synthInstance.maxHeartbeats 250000

include ap in
/-- Actual B047 marked-limit homogeneity transported along the
whole B060 source equivalence yields genuine homogeneity of the
pure clone of its ACTUAL owner-child source. No new premise
concerning an abstract terminal or owner group is added. -/
theorem actual_marked_owner_clone_homogeneous
    (I : CloneMarkedIdentification S H C P cco) :
    HomogeneousSource
      (CloneSAP.source (owner_child_source S H ap C P cco I))
      (FullAut (CloneSAP.source (owner_child_source S H ap C P cco I))) := by
  exact TypedAtomicSourceEquiv.homogeneous_pullback
    (actual_marked_owner_clone_source_equiv S H ap C P cco I)
    (UnarySource.homogeneous I)

end
end CCO.CloneTupleGeometry
