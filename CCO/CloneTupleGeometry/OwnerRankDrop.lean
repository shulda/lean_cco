import CCO.CloneTupleGeometry.MarkedChildSourceEquiv
import CCO.APCharacter.SourceAge.CharacterRank

/-! The rank of the genuine marked successor equals the rank of the
canonical pure clone of its actual owner quotient. The equality uses the
proved complete occurring-atom bijections, not a hypothetical palette. -/

universe u v w t
namespace CCO.CloneTupleGeometry
open APCharacter APCharacter.SourceAge RigidGroupoid.Geometry
noncomputable section
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (C : ExactCalculus (CloneSAP.source S))
variable {r : ι} {A : Kernel (CloneSAP.source S) r}
variable (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

include ap in
/-- Every complete same-child atom palette has exactly the cardinality
of the actual B047 marked palette, including its real clone atom. -/
theorem owner_clone_atom_card (I : CloneMarkedIdentification S H C P cco)
    (c : Rank.Child (UnarySource.β I)) :
    Nat.card ((CloneSAP.source (owner_child_source S H ap C P cco I)).Atom c c) =
      Nat.card ((UnarySource.source I).Atom c c) :=
  Nat.card_congr (actualMarkedCloneAtomEquiv S H ap C P cco I c c)

include ap in
/-- The actual source character step strictly decreases the SAME finite
potential after canonicalising the successor as owner times N. -/
theorem owner_clone_actual_rank_drop (I : CloneMarkedIdentification S H C P cco) :
    letI := S.finiteSort
    Rank.potential (fun c : Rank.Child (UnarySource.β I) =>
      Nat.card ((CloneSAP.source (owner_child_source S H ap C P cco I)).Atom c c)) <
      Rank.potential (fun i => Nat.card ((CloneSAP.source S).Atom i i)) := by
  letI := S.finiteSort
  have he : (fun c : Rank.Child (UnarySource.β I) =>
      Nat.card ((CloneSAP.source (owner_child_source S H ap C P cco I)).Atom c c)) =
      (fun c => Nat.card ((UnarySource.source I).Atom c c)) :=
    funext (owner_clone_atom_card S H ap C P cco I)
  rw [he]
  exact CharacterRank.actual_rank_drop P (CloneSAP.CCO.cco_forward S cco) I

end
end CCO.CloneTupleGeometry
