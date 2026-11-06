import CCO.ExactEPGeometry.OriginalPhaseMarkedToActual

/-! B062 C96: the entire actual finite old marked chart lifts into
the actual next CurrentSource. The concrete child tag, corrected bit,
all old binary orbitals and genuine equality are preserved. This does
not identify the new quotient orbital palette or full next age. -/

universe u v w t z
namespace CCO.ExactEPGeometry
open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry
open OwnerTransversal.CountableColour
noncomputable section

/-- Any real marked-limit finite embedding with complete OLD source
names gives an embedding into the TRUE SingleStep successor with
exact child owner/bit names and projected OLD pair colours.
The construction uses only the constructed old-reduct equivalence. -/
theorem originalPhaseFineMarkedChart_nextEmbedding
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    {V : Type z}
    (old : V → Sigma B.Point) (bits : V → ZMod 2)
    (f : V ↪ phase.MarkedLimit B.cco)
    (hOwner : ∀ v,
      (phase.markedCoding B.cco).table.owner (f v) =
        Age.ownerEquiv B.source ((old v).1,bits v))
    (hColour : ∀ v w,
      (phase.markedCoding B.cco).table.colour (f v) (f w) =
        Age.colourEquiv B.source
          (taggedColour B.source (old v) (old w))) :
    ∃ next : V ↪ Sigma (SingleStep.successor B phase).Point,
      (∀ v, UnarySource.childLabel (SingleStep.identification B phase)
        (next v).1 = ((old v).1,bits v)) ∧
      (∀ v w, taggedColour B.source
        ((SingleStep.projection B phase).project (next v))
        ((SingleStep.projection B phase).project (next w)) =
        taggedColour B.source (old v) (old w)) := by
  let I := SingleStep.identification B phase
  let next : V ↪ Sigma (SingleStep.successor B phase).Point := {
    toFun := fun v => originalPhaseMarkedToActual B Kroot phase (f v)
    inj' := (originalPhaseMarkedToActual B Kroot phase).injective.comp
      f.injective
  }
  have hImage (v : V) :
      (UnarySource.newEquiv I) (next v) = f v := by
    change (UnarySource.newEquiv I)
      ((UnarySource.newEquiv I).symm (f v)) = f v
    exact (UnarySource.newEquiv I).apply_symm_apply (f v)
  refine ⟨next,?_,?_⟩
  · intro v
    have h := UnarySource.new_owner I (next v)
    change (phase.markedCoding B.cco).table.owner
      ((UnarySource.newEquiv I) (next v)) =
      Age.ownerEquiv B.source (UnarySource.childLabel I (next v).1)
      at h
    rw [hImage v] at h
    exact (Age.ownerEquiv B.source).injective
      (h.symm.trans (hOwner v))
  · intro v w
    have h := originalPhaseMarkedToActual_colours
      B Kroot phase (f v) (f w)
    change (phase.markedCoding B.cco).table.colour (f v) (f w) =
      Age.colourEquiv B.source
        (taggedColour B.source
          ((SingleStep.projection B phase).project (next v))
          ((SingleStep.projection B phase).project (next w))) at h
    exact (Age.colourEquiv B.source).injective
      (h.symm.trans (hColour v w))

end
end CCO.ExactEPGeometry
