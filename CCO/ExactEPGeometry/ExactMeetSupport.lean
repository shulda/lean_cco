import CCO.ExactEPGeometry.CanonicalStepMeet
import CCO.ExactEPGeometry.ExactTraceTransport
import Mathlib.Data.Fintype.Basic

/-!
# B062 C47–C48: guarded exact finite-meet supports along real reducts

A transport certificate alone does NOT imply exact-family primality.
This independent property states precisely the source nonempty-old-
intersection guard and the real current support witnesses.

For composition, each old factor is lifted by the PROVED actual
two-way exact-trace theorem on the intermediate source. The previous
prefix's meet-primality first produces a NONEMPTY intermediate common
intersection, which is then passed to the next prefix. In particular
no empty original atomic meet is declared preserved.

The actual AP-character step constructs this property from C47 using
ALL current source-specific marked-age providers, not an axiomatic
primality field of a freely chosen unary reduct.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Preservation of nonempty OLD exact finite meets by REAL pair
supports on each pair of CURRENT named sorts. The family is indexed
by an actual finite type, allowing a canonical witness for each member
at intermediate stages. The old intersection must contain a real
pair before any child-label restrictions are imposed. -/
structure ExactMeetSupport
    {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
    (S : AtomicSource.{u,v,w} ι X)
    (T : AtomicSource.{u,v,w} κ Y)
    (P : UnaryReduct S T) : Prop where
  meets :
    ∀ {F : Type} [Fintype F] {i j : κ}
      (D : F → RawExact.NonemptyExact S (P.parent i) (P.parent j)),
      (∃ a : X (P.parent i), ∃ b : X (P.parent j),
        ∀ f : F, RawExact.evaluate S (D f).words a b) →
      (∀ f : F, ∃ x : Y i, ∃ y : Y j,
        RawExact.evaluate S (D f).words (P.point i x) (P.point j y)) →
      ∃ x : Y i, ∃ y : Y j,
        ∀ f : F,
          RawExact.evaluate S (D f).words (P.point i x) (P.point j y)

namespace ExactMeetSupport

variable {ι κ ν : Type u}
variable {X : ι → Type v} {Y : κ → Type v} {Z : ν → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,v,w} κ Y}
variable {U : AtomicSource.{u,v,w} ν Z}

/-- Zero stages: the same REAL old intersection witness is already a
current witness under the true identity reduct. -/
theorem identity (S : AtomicSource.{u,v,w} ι X) :
    ExactMeetSupport S S (UnaryReduct.identity S) := by
  constructor
  intro F inst i j D hOld _
  obtain ⟨x,y,hxy⟩ := hOld
  exact ⟨x,y,hxy⟩

/-- The genuinely AP-only canonical SourcePhase discharges guarded
finite-family support directly from C47. A finite enumeration of the
family is used only to feed the actual marked-age primality theorem;
it introduces neither infinite supports nor dummy exact factors. -/
theorem canonical_step
    (B : CurrentSource.{u,v,w,t})
    {i : B.Sorts} {K : Kernel B.source i}
    (P : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) K) :
    ExactMeetSupport B.source (SingleStep.successor B P).source
      (SingleStep.projection B P) := by
  constructor
  intro F inst c d D hOld hEach
  classical
  let L : List (RawExact.NonemptyExact B.source c.1 d.1) :=
    (Finset.univ : Finset F).toList.map D
  have hOldL : TRel.Nonempty (rawExactFamily B.source L) := by
    obtain ⟨a,b,hAll⟩ := hOld
    refine ⟨a,b,?_⟩
    intro E hE
    change E ∈ ((Finset.univ : Finset F).toList.map D) at hE
    obtain ⟨f,_,hEq⟩ := List.mem_map.mp hE
    subst E
    exact hAll f
  have hEachL :
      ∀ E ∈ L, ∃ x : (SingleStep.successor B P).Point c,
        ∃ y : (SingleStep.successor B P).Point d,
        RawExact.evaluate B.source E.words
          ((SingleStep.projection B P).point c x)
          ((SingleStep.projection B P).point d y) := by
    intro E hE
    change E ∈ ((Finset.univ : Finset F).toList.map D) at hE
    obtain ⟨f,_,hEq⟩ := List.mem_map.mp hE
    subst E
    exact hEach f
  obtain ⟨x,y,hAll⟩ :=
    canonical_step_exactFamily_support B P L hOldL hEachL
  refine ⟨x,y,?_⟩
  intro f
  apply hAll (D f)
  change D f ∈ ((Finset.univ : Finset F).toList.map D)
  exact List.mem_map.mpr ⟨f, by simp, rfl⟩

/-- Main C48 induction step. From an old original family with a
nonempty global intersection, REAL final support of each member
gives support in the intermediate parent sorts. Existing guarded
primality produces a nonempty intermediate common intersection.
Each original factor is represented by an actual nonempty RAW exact
intermediate factor using the proved source-to-current trace theorem,
and THEN the next guarded-primality instance yields a final witness.

Both input maps are literal UnaryReducts, so no independent choice of
quotient points, section of groups, SAP or arbitrary exact descent. -/
theorem compose
    (P : UnaryReduct S T) (Q : UnaryReduct T U)
    (hTrace : ExactTraceTransport S T P)
    (hP : ExactMeetSupport S T P)
    (hQ : ExactMeetSupport T U Q) :
    ExactMeetSupport S U (P.compose Q) := by
  classical
  constructor
  intro F inst i j D hOld hEach
  have hMiddleEach :
      ∀ f : F, ∃ x : Y (Q.parent i), ∃ y : Y (Q.parent j),
        RawExact.evaluate S (D f).words
          (P.point (Q.parent i) x) (P.point (Q.parent j) y) := by
    intro f
    obtain ⟨x,y,hxy⟩ := hEach f
    exact ⟨Q.point i x,Q.point j y,hxy⟩
  have hMiddleAll := hP.meets D hOld hMiddleEach
  let lifted (f : F) := hTrace.old_to_new (D f) (hMiddleEach f)
  let M (f : F) : RawExact.NonemptyExact T (Q.parent i) (Q.parent j) :=
    Classical.choose (lifted f)
  have hM (f : F) (x : Y (Q.parent i)) (y : Y (Q.parent j)) :
      RawExact.evaluate T (M f).words x y ↔
        RawExact.evaluate S (D f).words
          (P.point (Q.parent i) x) (P.point (Q.parent j) y) :=
    Classical.choose_spec (lifted f) x y
  have hOldM :
      ∃ x : Y (Q.parent i), ∃ y : Y (Q.parent j),
        ∀ f : F, RawExact.evaluate T (M f).words x y := by
    obtain ⟨x,y,hxy⟩ := hMiddleAll
    exact ⟨x,y,fun f => (hM f x y).mpr (hxy f)⟩
  have hEachM :
      ∀ f : F, ∃ x : Z i, ∃ y : Z j,
        RawExact.evaluate T (M f).words (Q.point i x) (Q.point j y) := by
    intro f
    obtain ⟨x,y,hxy⟩ := hEach f
    exact ⟨x,y,(hM f (Q.point i x) (Q.point j y)).mpr hxy⟩
  obtain ⟨x,y,hFinal⟩ := hQ.meets M hOldM hEachM
  exact ⟨x,y,fun f =>
    (hM f (Q.point i x) (Q.point j y)).mp (hFinal f)⟩

end ExactMeetSupport
end
end CCO.ExactEPGeometry
