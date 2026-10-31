import CCO.ExactEPGeometry.ProjectedWords
import CCO.APCharacter.Towers.ProjectionComposition

/-!
# B062 C28: exact RAW trace transport along genuine unary reducts

This is the composition kernel needed for a finite safe character tower.
The structure does NOT assert that an arbitrary unary reduct preserves RAW
exactness. It explicitly stores BOTH proven source-to-child and child-to-source
exactness obligations, with equality of actual represented pair relations.

Every old-to-new application requires a real nonempty trace on the specified
new endpoints. The opposite direction obtains its nonempty old witness from
the actual current exact domain. The empty presentation remains Top, and
identity is still the genuine zero-length RAW word.

The canonical AP-character source discharges both obligations separately.
-/

universe u v w

namespace CCO.ExactEPGeometry

open APCharacter.Towers

/-- Two-way represented exactness of a particular actual unary reduct.
Neither direction is an axiom: canonical character steps will CONSTRUCT it
from the one-step C23–C27 real marked trace theorems. -/
structure ExactTraceTransport
    {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
    (S : AtomicSource.{u,v,w} ι X)
    (T : AtomicSource.{u,v,w} κ Y)
    (P : UnaryReduct S T) : Prop where
  old_to_new :
    ∀ {i j : κ}
      (D : RawExact.NonemptyExact S (P.parent i) (P.parent j)),
      (∃ x : Y i, ∃ z : Y j,
        RawExact.evaluate S D.words (P.point i x) (P.point j z)) →
      ∃ E : RawExact.NonemptyExact T i j,
        ∀ x : Y i, ∀ z : Y j,
          RawExact.evaluate T E.words x z ↔
            RawExact.evaluate S D.words (P.point i x) (P.point j z)
  new_to_old :
    ∀ {i j : κ} (E : RawExact.NonemptyExact T i j),
      ∃ D : RawExact.NonemptyExact S (P.parent i) (P.parent j),
        ∀ x : Y i, ∀ z : Y j,
          RawExact.evaluate T E.words x z ↔
            RawExact.evaluate S D.words (P.point i x) (P.point j z)

namespace ExactTraceTransport

variable {ι κ ν : Type u}
variable {X : ι → Type v} {Y : κ → Type v} {Z : ν → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,v,w} κ Y}
variable {U : AtomicSource.{u,v,w} ν Z}

/-- The zero-stage tower has exact transport without adding any constraints. -/
theorem identity (S : AtomicSource.{u,v,w} ι X) :
    ExactTraceTransport S S (UnaryReduct.identity S) := by
  constructor
  · intro i j D _
    exact ⟨D,fun _ _ => Iff.rfl⟩
  · intro i j E
    exact ⟨E,fun _ _ => Iff.rfl⟩

/-- Actual exactness transports compose through ONE specifically named
middle unary source, retaining the full fixed-typed relation (not only a
palette or support inclusion). Every witness is mapped through the real
global point maps of the two reducts. -/
theorem compose
    (P : UnaryReduct S T) (Q : UnaryReduct T U)
    (hP : ExactTraceTransport S T P)
    (hQ : ExactTraceTransport T U Q) :
    ExactTraceTransport S U (P.compose Q) := by
  constructor
  · intro i j D hFinal
    obtain ⟨x,z,hxz⟩ := hFinal
    have hMiddle :
        ∃ y : Y (Q.parent i), ∃ y' : Y (Q.parent j),
          RawExact.evaluate S D.words
            (P.point (Q.parent i) y) (P.point (Q.parent j) y') :=
      ⟨Q.point i x,Q.point j z,hxz⟩
    obtain ⟨M,hM⟩ := hP.old_to_new D hMiddle
    have hTarget :
        ∃ y : Z i, ∃ y' : Z j,
          RawExact.evaluate T M.words (Q.point i y) (Q.point j y') :=
      ⟨x,z,(hM (Q.point i x) (Q.point j z)).mpr hxz⟩
    obtain ⟨E,hE⟩ := hQ.old_to_new M hTarget
    refine ⟨E,?_⟩
    intro y y'
    exact (hE y y').trans (hM (Q.point i y) (Q.point j y'))
  · intro i j E
    obtain ⟨M,hM⟩ := hQ.new_to_old E
    obtain ⟨D,hD⟩ := hP.new_to_old M
    refine ⟨D,?_⟩
    intro x z
    exact (hM x z).trans (hD (Q.point i x) (Q.point j z))

end ExactTraceTransport

end CCO.ExactEPGeometry
