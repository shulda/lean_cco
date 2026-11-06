import CCO.ExactEPGeometry.OriginalSelectedFiniteOldChart
import CCO.APCharacter.MarkedSource

/-!
# B062 C95: actual finite OLD marked charts and the genuine marked limit

C90 supplies injective representatives of ANY finite family of ACTUALLY
realized selected E-quotient points, with their entire real fine old
atomic-colour table. Given a character-compatible old global marking
on the true current B source, its restriction to these representatives
is a genuinely REALIZED finite chart in the original marked age.
The existing AP-only marked-age source construction then embeds that
whole chart, preserving both unary bit names and all pair orbital names,
into ONE genuine homogeneous marked output.

A global selected-quotient marking by itself is NOT an old-source
global marking; the corrected-character pullback required to produce
the input marking is still an explicit separate C93–C94 obligation.
No arbitrary seed is asserted homogeneous, no quotient SAP or group
action section is introduced, and no arbitrary unmarked quotient
diagram is assumed realizable.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- On the true source's genuine finite marked age, the complete old
atomic table of distinct real selected E-quotient vertices admits
an actual phase-labeled realization whenever the original source has
a compatible global marking. The bit for each quotient vertex here
is the value on its actual chosen old representative. -/
noncomputable def originalSelectedFiniteMarkedOldChart
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    {V : Type z} [Finite V]
    (points : V ↪ Sigma
      (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).Point)
    (oldMark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking oldMark) :
    APCharacter.Age.Chart B.source phase.masks := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let equiv : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let old : Fin (Fintype.card V) → Sigma B.Point :=
    fun i => originalSelectedTaggedRepresentative
      A B P transport base hOne E (points (equiv i))
  let bits : Fin (Fintype.card V) → ZMod 2 := fun i => oldMark (old i)
  have hInjective : Function.Injective old :=
    (originalSelectedFiniteRepresentative_injective
      A B P transport base hOne E points).comp equiv.injective
  have hLegal : APCharacter.Age.Legal B.source phase.masks old bits := by
    constructor
    · intro i
      exact hMark.1 (old i)
    · intro i j
      exact hMark.2 (old i) (old j)
  exact APCharacter.Age.chartOf B.source
    (APCharacter.Age.table B.source old bits)
    ⟨old,bits,hInjective,hLegal,rfl⟩

/-- C95's genuine marked-output bridge for an already REALIZED finite
quotient prefix diagram together with an ACTUAL original full
character-compatible marking. The chart embeds into the true
homogeneous AP-only marked limit with its entire name table intact;
an arbitrary global seed is not mistaken for that limit. -/
theorem originalSelectedFiniteMarkedOldChart_names
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    {V : Type z} [Finite V]
    (points : V ↪ Sigma
      (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).Point)
    (oldMark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking oldMark) :
    let C := originalSelectedFiniteMarkedOldChart
      A B P transport base hOne E Kroot phase points oldMark hMark
    ∃ f : Fin C.size ↪ phase.MarkedLimit B.cco,
      (∀ i, (phase.markedCoding B.cco).table.owner (f i) =
        C.table.owner i) ∧
      ∀ i j, (phase.markedCoding B.cco).table.colour (f i) (f j) =
        C.table.colour i j := by
  let C := originalSelectedFiniteMarkedOldChart
    A B P transport base hOne E Kroot phase points oldMark hMark
  exact APCharacter.Age.chart_names B.source B.homogeneous
    (phase.completion_property B.cco) C

end
end CCO.ExactEPGeometry
