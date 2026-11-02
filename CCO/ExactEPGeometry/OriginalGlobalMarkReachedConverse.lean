import CCO.ExactEPGeometry.OriginalRetainedAnyMarkCorrection
import CCO.RigidGroupoid.Geometry.PointAction

/-!
# B062 C93–C96: every real old global mask is a full reached-groupoid mark

The accepted AP-only SourcePhase provider constructs original global
mask assignments from free connected-groupoid point markings.
Here the converse is proved on the SAME actual source: every global
bit function satisfying the genuine original SourcePhase masks is
constant on every FULL old K-class, including distinct original
points, and descends to a bona fide full-groupoid marking.

Every Arrow action equation uses an actual real pair in the WHOLE
exact Arrow, with the true source character. The logical diagonal
is never substituted for the whole gate identity. This supplies
the original-marked-age to groupoid-marking bridge required by the
C96 converse, not the more difficult selected quotient-age
identification or arbitrary locally-legal prefix realization.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- The WHOLE current reached exact gate K_b, not just old logical
equality, has a constant bit in every globally legal original
SourcePhase marking. -/
theorem originalGlobalMarkReachedGateConstant
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (mark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking mark)
    (b : Reached B.source Kroot) (x y : B.Point b.val)
    (hK : (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b).rel x y) :
    mark ⟨b.val,x⟩ = mark ⟨b.val,y⟩ := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let K := Reached.kernel B.homogeneous C b
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous C (A := Kroot)
  have hLegal : phase.allows (B.source.colour x y)
      (mark ⟨b.val,x⟩) (mark ⟨b.val,y⟩) :=
    hMark.2 (⟨b.val,x⟩ : Sigma B.Point)
      (⟨b.val,y⟩ : Sigma B.Point)
  have hRead := (phase.rigid_mask_iff b b (Arrow.id K)
    x y hK (mark ⟨b.val,x⟩) (mark ⟨b.val,y⟩)).mp hLegal
  have hBit : mark ⟨b.val,y⟩ =
      mark ⟨b.val,x⟩ + phase.character.value (Arrow.id K) :=
    hRead.2.2
  rw [phase.character.map_id b,add_zero] at hBit
  exact hBit.symm

/-- The bit of an actual original global marking on the literal
K_b-quotient class. This is the WHOLE current reached gate quotient,
not the finer old E-quotient. -/
noncomputable def originalGlobalMarkReachedClassBit
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (mark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking mark)
    (b : Reached B.source Kroot) :
    (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b).Class → ZMod 2 :=
  Quotient.lift
    (fun x : B.Point b.val => mark ⟨b.val,x⟩)
    (fun x y hxy =>
      originalGlobalMarkReachedGateConstant B Kroot
        phase mark hMark b x y hxy)

/-- The true quotient class function reads the actual bit of each
original point, regardless of the representative of its K-class. -/
theorem originalGlobalMarkReachedClassBit_mk
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (mark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking mark)
    (b : Reached B.source Kroot) (x : B.Point b.val) :
    originalGlobalMarkReachedClassBit B Kroot phase mark hMark b
      ((Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) b).project x) =
      mark ⟨b.val,x⟩ := rfl

/-- Every ACTUAL old globally admissible SourcePhase marking induces
a full genuine marking of the REAL reached K-class groupoid.
Conversely the accepted `SourcePhase.original_global_marking`
provides the other direction. All arrows, including identities,
are tested; there is no chosen-generator assumption. -/
theorem originalGlobalMarkInducesReachedCharacter
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (mark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking mark) :
    let C := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    letI := Reached.groupoid B.homogeneous C (A := Kroot)
    let F := Reached.pointFunctor B.homogeneous C Kroot
    ∃ groupMark : Abstract.Point F → ZMod 2,
      Abstract.IsMarking F phase.character groupMark ∧
      ∀ (b : Reached B.source Kroot) (x : B.Point b.val),
        groupMark ⟨b,(Reached.kernel B.homogeneous C b).project x⟩ =
          mark ⟨b.val,x⟩ := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous C (A := Kroot)
  let F := Reached.pointFunctor B.homogeneous C Kroot
  let groupMark : Abstract.Point F → ZMod 2 :=
    fun p => originalGlobalMarkReachedClassBit B Kroot
      phase mark hMark p.1 p.2
  refine ⟨groupMark,?_,?_⟩
  · intro a b R q
    induction q using Quotient.inductionOn with
    | _ x =>
      let K := Reached.kernel B.homogeneous C a
      let L := Reached.kernel B.homogeneous C b
      let y := R.pointImage B.homogeneous x
      have hR : R.rel x y := R.pointImage_spec B.homogeneous x
      have hLegal : phase.allows (B.source.colour x y)
          (mark ⟨a.val,x⟩) (mark ⟨b.val,y⟩) :=
        hMark.2 (⟨a.val,x⟩ : Sigma B.Point)
          (⟨b.val,y⟩ : Sigma B.Point)
      have hChar : mark ⟨b.val,y⟩ =
          mark ⟨a.val,x⟩ + phase.character.value R :=
        ((phase.rigid_mask_iff a b R x y hR
          (mark ⟨a.val,x⟩) (mark ⟨b.val,y⟩)).mp hLegal).2.2
      change groupMark ⟨b,R.quotientMap B.homogeneous (K.project x)⟩ =
        groupMark ⟨a,K.project x⟩ + phase.character.value R
      rw [R.quotientMap_project B.homogeneous x]
      change originalGlobalMarkReachedClassBit B Kroot
          phase mark hMark b (L.project y) =
        originalGlobalMarkReachedClassBit B Kroot
          phase mark hMark a (K.project x) + phase.character.value R
      rw [originalGlobalMarkReachedClassBit_mk,
        originalGlobalMarkReachedClassBit_mk]
      exact hChar
  · intro b x
    exact originalGlobalMarkReachedClassBit_mk
      B Kroot phase mark hMark b x

end
end CCO.ExactEPGeometry
