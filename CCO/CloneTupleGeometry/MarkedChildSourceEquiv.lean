import CCO.CloneTupleGeometry.MarkedChildFullColour

/-!
# B060 N02: the genuine complete marked child source is a pure clone

A typed atomic source equivalence has bijections on every named sort,
bijections on the COMPLETE actual occurring atom palettes on all
ordered sort pairs, and equality of the FULL optional pair colours
under those bijections. Logical equality `none` is preserved.

For the genuine B047 maximal-character marked successor of the B045
pure clone source we explicitly construct such an equivalence to
the pure clone of its actual owner child source. This is not an
unverified assumption about a hypothetical unary expansion:
the points, atoms and colour equation were all proved in preceding
B060 modules from the real marked Fraisse source and its actual
old-reduct identification.

The finite terminal iteration, owner homogeneity/AP/CCO transport,
and all four B060 main source exports remain separate obligations.
-/

universe u v w t
namespace CCO.CloneTupleGeometry

/-- A complete sort-preserving isomorphism of actual typed atomic
sources: all optional pair colours, not just the diversity palette,
are transported exactly. No new axiom or quotient action is involved. -/
structure TypedAtomicSourceEquiv
    {ι : Type u} {X Y : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X)
    (T : AtomicSource.{u,v,w} ι Y) where
  point : ∀ i, X i ≃ Y i
  atom : ∀ i j, S.Atom i j ≃ T.Atom i j
  colour : ∀ {i j} (x : X i) (y : X j),
    T.colour (point i x) (point j y) =
      (S.colour x y).map (atom i j)

namespace TypedAtomicSourceEquiv

variable {ι : Type u} {X Y : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,v,w} ι Y}

/-- The FULL colour-preserving equivalence automatically commutes
with actual converse on atomic names, because every named atom is
really realized by a pair of source points. -/
theorem preserves_conv (E : TypedAtomicSourceEquiv S T)
    {i j : ι} (a : S.Atom i j) :
    E.atom j i (S.conv a) = T.conv (E.atom i j a) := by
  obtain ⟨x,y,hxy⟩ := S.realized a
  have hTxy :
      T.colour (E.point i x) (E.point j y) =
        some (E.atom i j a) := by
    simpa only [hxy,Option.map_some] using E.colour x y
  have hSyx : S.colour y x = some (S.conv a) :=
    (S.colour_swap x y a).mp hxy
  have hTyx :
      T.colour (E.point j y) (E.point i x) =
        some (E.atom j i (S.conv a)) := by
    simpa only [hSyx,Option.map_some] using E.colour y x
  have hTconv :
      T.colour (E.point j y) (E.point i x) =
        some (T.conv (E.atom i j a)) :=
    (T.colour_swap (E.point i x) (E.point j y) (E.atom i j a)).mp hTxy
  exact Option.some.inj (hTyx.symm.trans hTconv)

end TypedAtomicSourceEquiv

open APCharacter
open APCharacter.SourceAge
open RigidGroupoid.Geometry
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
/-- A COMPLETE typed atomic-source equivalence between the actual
B047 marked successor and the pure B045 clone over its genuine
owner child source. The forward direction is pure-owner-clone to
marked child, so the full literal option-valued colour theorem
applies directly. Every point bijection and every atom bijection
comes from concrete preceding B060 source lemmas. -/
noncomputable def actual_marked_owner_clone_source_equiv
    (I : CloneMarkedIdentification S H C P cco) :
    TypedAtomicSourceEquiv
      (CloneSAP.source (owner_child_source S H ap C P cco I))
      (UnarySource.source
        (completion := P.completion_property
          (CloneSAP.CCO.cco_forward S cco)) I) where
  point c := (marked_child_equiv S H ap C P cco I c).symm
  atom c d := actualMarkedCloneAtomEquiv S H ap C P cco I c d
  colour := by
    intro c d x y
    have hc := marked_full_colour_transport S H ap C P cco I
      ((marked_child_equiv S H ap C P cco I c).symm x)
      ((marked_child_equiv S H ap C P cco I d).symm y)
    simpa only [Equiv.apply_symm_apply] using hc

end
end CCO.CloneTupleGeometry
