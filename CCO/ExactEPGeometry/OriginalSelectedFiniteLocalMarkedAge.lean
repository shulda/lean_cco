import CCO.ExactEPGeometry.OriginalSelectedFiniteMarkedOldChart

/-!
# B062 C95: genuine finite marked-age witness from LOCAL old mask legality

An arbitrary global marking of the old source is NOT required to obtain
a finite object of the actual AP-only marked age. For a finite family
of distinct, already-realized selected E-quotient points, take the
genuine old representatives from C90 and their complete real old
atomic table. If the prescribed bits satisfy the actual original
SourcePhase mask on every chosen OLD pair, this is already an ACTUAL
finite marked old-age object. The existing AP-only Fraisse-limit
construction embeds it into the genuine output, preserving every
old atomic name, every owner and every bit. The indexed points are
Fin n; arbitrary finite vertex types are covered by finite relabeling.

It remains NONTRIVIAL to obtain this old pair-mask legality from
arbitrary selected quotient orbitals and their prescribed corrected
bits; this is exactly the missing C88/C93–C95 source correspondence.
No arbitrary choice of fine old colours is justified, no quotient
SAP or automorphism section is assumed, and no global seed is falsely
declared homogeneous.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open OwnerTransversal.CountableColour

noncomputable section

/-- C95: actual finite E-quotient points, a fixed genuine fine old
representative for each, and LOCAL actual original marked-mask
legality give a genuine induced embedding into the homogeneous
marked output, with ALL old orbital/unary/phase names retained.
No original global-marking premise is needed. -/
theorem originalSelectedFiniteLocalMarkedAge_names
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    {n : ℕ}
    (points : Fin n ↪ Sigma
      (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).Point)
    (bits : Fin n → ZMod 2)
    (hValid : ∀ i : Fin n,
      phase.masks.validBit
        (originalSelectedTaggedRepresentative
          A B P transport base hOne E (points i)).1 (bits i))
    (hPair : ∀ i j : Fin n,
      phase.masks.allowed
        (B.source.colour
          (originalSelectedTaggedRepresentative
            A B P transport base hOne E (points i)).2
          (originalSelectedTaggedRepresentative
            A B P transport base hOne E (points j)).2)
        (bits i) (bits j)) :
    let old : Fin n → Sigma B.Point :=
      fun i => originalSelectedTaggedRepresentative
        A B P transport base hOne E (points i)
    ∃ f : Fin n ↪ phase.MarkedLimit B.cco,
      (∀ i, (phase.markedCoding B.cco).table.owner (f i) =
        APCharacter.Age.ownerEquiv B.source ((old i).1,bits i)) ∧
      ∀ i j, (phase.markedCoding B.cco).table.colour (f i) (f j) =
        APCharacter.Age.colourEquiv B.source
          (taggedColour B.source (old i) (old j)) := by
  let old : Fin n → Sigma B.Point :=
    fun i => originalSelectedTaggedRepresentative
      A B P transport base hOne E (points i)
  have hInjective : Function.Injective old :=
    (originalSelectedTaggedRepresentative_injective
      A B P transport base hOne E).comp points.injective
  have hLegal : APCharacter.Age.Legal B.source phase.masks old bits := by
    constructor
    · intro i
      exact hValid i
    · intro i j
      exact hPair i j
  exact APCharacter.Age.embed_realized B.source B.homogeneous
    (phase.completion_property B.cco) old bits hInjective hLegal

end
end CCO.ExactEPGeometry
