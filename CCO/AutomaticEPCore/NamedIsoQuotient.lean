import CCO.AutomaticEPCore.NamedIsoReduct
import CCO.ExactEPGeometry.OriginalCodedQuotientSafeHistory

/-! A complete named-source isomorphism transports the actual selected
original-E quotient, including its occupancy owners, whole orbital palette
and literal fixed original saturated predicate code. The point map is the
canonical global-E-class map of the actual inverse unary reduct. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.RigidGroupoid.Geometry
noncomputable section

variable (A B C : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
variable (E : ExactEq A.source base) (I : NamedCurrentSourceIso B C)

/-- The inverse named-source isomorphism preserves and reflects actual
original-E occupancy support, using its surjective displayed fibres. -/
theorem namedIso_original_occupancy_iff (i j : C.Sorts) :
    (originalExactOccupancySetoid A C (P.compose (namedIsoReduct I)) base hOne E).r i j ↔
    (originalExactOccupancySetoid A B P base hOne E).r
      ((namedIsoReduct I).parent i) ((namedIsoReduct I).parent j) := by
  change (∃ x : C.Point i, ∃ y : C.Point j, _) ↔
    ∃ x : B.Point ((namedIsoReduct I).parent i),
      ∃ y : B.Point ((namedIsoReduct I).parent j), _
  constructor
  · rintro ⟨x,y,h⟩
    exact ⟨(namedIsoReduct I).point i x,(namedIsoReduct I).point j y,h⟩
  · rintro ⟨x,y,h⟩
    obtain ⟨a,rfl⟩ := (namedIsoReduct_point_bijective I i).2 x
    obtain ⟨b,rfl⟩ := (namedIsoReduct_point_bijective I j).2 y
    exact ⟨a,b,h⟩

/-- The actual quotient of current sort names by original-E occupancy. -/
def namedIsoOriginalOccupancyEquiv :
    OriginalOccupancy A C (P.compose (namedIsoReduct I)) base hOne E ≃
      OriginalOccupancy A B P base hOne E := by
  let S := originalExactOccupancySetoid A C (P.compose (namedIsoReduct I)) base hOne E
  let T := originalExactOccupancySetoid A B P base hOne E
  let f := (namedIsoReduct I).parent
  have hSurj : Function.Surjective f := I.sorts.symm.surjective
  exact quotientClassEquiv_of_classwiseSurjective S T f
    (namedIso_original_occupancy_iff A B C P base hOne E I)
    (fun i => by
      obtain ⟨j,hj⟩ := hSurj i
      exact ⟨j,hj ▸ T.refl i⟩)

theorem namedIsoOriginalOccupancyEquiv_mk (i : C.Sorts) :
    namedIsoOriginalOccupancyEquiv A B C P base hOne E I (Quotient.mk'' i) =
      (Quotient.mk'' ((namedIsoReduct I).parent i) :
        OriginalOccupancy A B P base hOne E) := rfl

/-- The WHOLE selected quotient point carrier is transported through its
literal global original-E classes, independently of representative choices. -/
def namedIsoOriginalSelectedPointEquiv :
    Sigma (originalExactSelectedQuotientCurrentSource A C
      (P.compose (namedIsoReduct I))
      (ExactTraceTransport.compose P (namedIsoReduct I) transport
        (namedIsoReduct_transport I)) base hOne E).Point ≃
    Sigma (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).Point :=
  (originalSelectedGlobalEClassEquiv A C (P.compose (namedIsoReduct I))
    (ExactTraceTransport.compose P (namedIsoReduct I) transport
      (namedIsoReduct_transport I)) base hOne E).trans
    ((originalGlobalEclassEquivAlongReduct A B C P (namedIsoReduct I) base hOne E).trans
      (originalSelectedGlobalEClassEquiv A B P transport base hOne E).symm)

theorem namedIsoOriginalSelectedPointEquiv_globalE
    (q : Sigma (originalExactSelectedQuotientCurrentSource A C
      (P.compose (namedIsoReduct I))
      (ExactTraceTransport.compose P (namedIsoReduct I) transport
        (namedIsoReduct_transport I)) base hOne E).Point) :
    let R := namedIsoReduct I
    let hC := ExactTraceTransport.compose P R transport (namedIsoReduct_transport I)
    let repC := originalSelectedTaggedRepresentative A C (P.compose R) hC base hOne E
    let repB := originalSelectedTaggedRepresentative A B P transport base hOne E
    (currentOriginalExactSetoid A B P base hOne E).r
      (repB (namedIsoOriginalSelectedPointEquiv A B C P transport base hOne E I q))
      (R.project (repC q)) := by
  let R := namedIsoReduct I
  let hC := ExactTraceTransport.compose P R transport (namedIsoReduct_transport I)
  let eB := originalSelectedGlobalEClassEquiv A B P transport base hOne E
  let eC := originalSelectedGlobalEClassEquiv A C (P.compose R) hC base hOne E
  let eR := originalGlobalEclassEquivAlongReduct A B C P R base hOne E
  have h : eB (namedIsoOriginalSelectedPointEquiv A B C P transport base hOne E I q) =
      eR (eC q) := eB.apply_symm_apply _
  exact Quotient.exact h

theorem namedIsoOriginalSelectedPointEquiv_owner
    (q : Sigma (originalExactSelectedQuotientCurrentSource A C
      (P.compose (namedIsoReduct I))
      (ExactTraceTransport.compose P (namedIsoReduct I) transport
        (namedIsoReduct_transport I)) base hOne E).Point) :
    (namedIsoOriginalSelectedPointEquiv A B C P transport base hOne E I q).1 =
      namedIsoOriginalOccupancyEquiv A B C P base hOne E I q.1 := by
  let R := namedIsoReduct I
  let hC := ExactTraceTransport.compose P R transport (namedIsoReduct_transport I)
  let f := namedIsoOriginalSelectedPointEquiv A B C P transport base hOne E I
  let e := namedIsoOriginalOccupancyEquiv A B C P base hOne E I
  let repC := originalSelectedTaggedRepresentative A C (P.compose R) hC base hOne E
  let repB := originalSelectedTaggedRepresentative A B P transport base hOne E
  have hE := namedIsoOriginalSelectedPointEquiv_globalE A B C P transport base hOne E I q
  have hSupport : (originalExactOccupancySetoid A B P base hOne E).r
      (repB (f q)).1 (R.project (repC q)).1 :=
    ⟨(repB (f q)).2,(R.project (repC q)).2,hE⟩
  have hB := originalOccupancyRepresentative_class A B P base hOne E (f q).1
  have hCclass := originalOccupancyRepresentative_class A C (P.compose R) base hOne E q.1
  have hMap : (Quotient.mk'' (R.project (repC q)).1 :
      OriginalOccupancy A B P base hOne E) =
      e (Quotient.mk'' (repC q).1) := rfl
  exact hB.symm.trans ((Quotient.sound hSupport).trans
    (hMap.trans (congrArg e hCclass)))

/-- At equal selected owners the actual full current atom block is
exactly the fixed original E-saturated block of its projected seed pair. -/
private theorem selected_block_original
    (tp : ExactTraceProduct A.source B.source P)
    (q s q' s' : Sigma
      (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).Point)
    (hq : q'.1 = q.1) (hs : s'.1 = s.1) :
    let rep := originalSelectedTaggedRepresentative A B P transport base hOne E
    originalCurrentExactSaturatedColour A B P base hOne E
      (taggedColour B.source (rep q) (rep s)) (rep q') (rep s') ↔
    originalCurrentExactSaturatedColour A A (UnaryReduct.identity A.source) base hOne E
      (taggedColour A.source (P.project (rep q)) (P.project (rep s)))
      (P.project (rep q')) (P.project (rep s')) := by
  rcases q with ⟨c,q⟩
  rcases s with ⟨d,s⟩
  rcases q' with ⟨c',q'⟩
  rcases s' with ⟨d',s'⟩
  dsimp only at hq hs
  subst c'
  subst d'
  exact originalCurrentAtomicSaturation_iff_original A B P tp base hOne E
    (Quotient.out q) (Quotient.out q') (Quotient.out s) (Quotient.out s')

theorem namedIsoOriginalSelectedPointEquiv_palette
    (tp : ExactTraceProduct A.source B.source P)
    (q s q' s' : Sigma (originalExactSelectedQuotientCurrentSource A C
      (P.compose (namedIsoReduct I))
      (ExactTraceTransport.compose P (namedIsoReduct I) transport
        (namedIsoReduct_transport I)) base hOne E).Point) :
    let R := namedIsoReduct I
    let hC := ExactTraceTransport.compose P R transport (namedIsoReduct_transport I)
    let QC := originalExactSelectedQuotientCurrentSource A C (P.compose R) hC base hOne E
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hOne E
    let f := namedIsoOriginalSelectedPointEquiv A B C P transport base hOne E I
    taggedColour QC.source q s = taggedColour QC.source q' s' ↔
      taggedColour QB.source (f q) (f s) = taggedColour QB.source (f q') (f s') := by
  let R := namedIsoReduct I
  let hC := ExactTraceTransport.compose P R transport (namedIsoReduct_transport I)
  let tpC := ExactTraceProduct.compose P R transport tp
    (namedIsoReduct_transport I) (namedIsoReduct_product I)
  let f := namedIsoOriginalSelectedPointEquiv A B C P transport base hOne E I
  let e := namedIsoOriginalOccupancyEquiv A B C P base hOne E I
  let repC := originalSelectedTaggedRepresentative A C (P.compose R) hC base hOne E
  let repB := originalSelectedTaggedRepresentative A B P transport base hOne E
  let T := currentOriginalExactSetoid A A (UnaryReduct.identity A.source) base hOne E
  have hg (p : Sigma (originalExactSelectedQuotientCurrentSource
      A C (P.compose R) hC base hOne E).Point) :
      T.r (P.project (repB (f p))) ((P.compose R).project (repC p)) :=
    namedIsoOriginalSelectedPointEquiv_globalE A B C P transport base hOne E I p
  have own (p : Sigma (originalExactSelectedQuotientCurrentSource
      A C (P.compose R) hC base hOne E).Point) : (f p).1 = e p.1 :=
    namedIsoOriginalSelectedPointEquiv_owner A B C P transport base hOne E I p
  have owner_iff (p p' : Sigma (originalExactSelectedQuotientCurrentSource
      A C (P.compose R) hC base hOne E).Point) :
      p.1 = p'.1 ↔ (f p).1 = (f p').1 := by
    rw [own p,own p']
    exact e.injective.eq_iff.symm
  have block (hq : q.1 = q'.1) (hs : s.1 = s'.1) :
      originalCurrentExactSaturatedColour A C (P.compose R) base hOne E
        (taggedColour C.source (repC q') (repC s')) (repC q) (repC s) ↔
      originalCurrentExactSaturatedColour A B P base hOne E
        (taggedColour B.source (repB (f q')) (repB (f s'))) (repB (f q)) (repB (f s)) := by
    have hNew := selected_block_original A C (P.compose R) hC base hOne E tpC
      q' s' q s hq hs
    have hOld := selected_block_original A B P transport base hOne E tp
      (f q') (f s') (f q) (f s) ((owner_iff q q').mp hq) ((owner_iff s s').mp hs)
    have hSeed := originalCurrentExactAtomicBlock_seed_congr A A
      (UnaryReduct.identity A.source) base hOne E
      ((P.compose R).project (repC q')) ((P.compose R).project (repC s'))
      (P.project (repB (f q'))) (P.project (repB (f s')))
      ((P.compose R).project (repC q)) ((P.compose R).project (repC s))
      (T.symm (hg q')) (T.symm (hg s'))
    have hEndpoints := setoidSaturation_congr T
      (fun a b => taggedColour A.source a b =
        taggedColour A.source (P.project (repB (f q'))) (P.project (repB (f s'))))
      (hg q) (hg s)
    exact hNew.trans (hSeed.trans (hEndpoints.symm.trans hOld.symm))
  have hNew := originalExactSelectedTaggedColour_iff_globalBlock
    A C (P.compose R) hC base hOne E q' s' q s
  have hOld := originalExactSelectedTaggedColour_iff_globalBlock
    A B P transport base hOne E (f q') (f s') (f q) (f s)
  constructor
  · intro h
    obtain ⟨hq,hs,hBlock⟩ := hNew.mp h
    exact hOld.mpr ⟨(owner_iff q q').mp hq,(owner_iff s s').mp hs,(block hq hs).mp hBlock⟩
  · intro h
    obtain ⟨hq,hs,hBlock⟩ := hOld.mp h
    have hq' := (owner_iff q q').mpr hq
    have hs' := (owner_iff s s').mpr hs
    exact hNew.mpr ⟨hq',hs',(block hq' hs').mpr hBlock⟩

/-- Every original predicate coordinate is retained by VALUE. -/
theorem namedIsoOriginalSelectedPointEquiv_rootCode
    (q s : Sigma (originalExactSelectedQuotientCurrentSource A C
      (P.compose (namedIsoReduct I))
      (ExactTraceTransport.compose P (namedIsoReduct I) transport
        (namedIsoReduct_transport I)) base hOne E).Point) :
    originalQuotientRootCode A B P transport base hOne E
      (namedIsoOriginalSelectedPointEquiv A B C P transport base hOne E I q)
      (namedIsoOriginalSelectedPointEquiv A B C P transport base hOne E I s) =
    originalQuotientRootCode A C (P.compose (namedIsoReduct I))
      (ExactTraceTransport.compose P (namedIsoReduct I) transport
        (namedIsoReduct_transport I)) base hOne E q s := by
  let R := namedIsoReduct I
  let hC := ExactTraceTransport.compose P R transport (namedIsoReduct_transport I)
  let f := namedIsoOriginalSelectedPointEquiv A B C P transport base hOne E I
  let repC := originalSelectedTaggedRepresentative A C (P.compose R) hC base hOne E
  let repB := originalSelectedTaggedRepresentative A B P transport base hOne E
  let T := currentOriginalExactSetoid A A (UnaryReduct.identity A.source) base hOne E
  have hq : T.r (P.project (repB (f q))) ((P.compose R).project (repC q)) :=
    namedIsoOriginalSelectedPointEquiv_globalE A B C P transport base hOne E I q
  have hs : T.r (P.project (repB (f s))) ((P.compose R).project (repC s)) :=
    namedIsoOriginalSelectedPointEquiv_globalE A B C P transport base hOne E I s
  funext a
  exact propext (setoidSaturation_congr T (fun p r => taggedColour A.source p r = a) hq hs)

/-- Actual whole selected quotient compatibility for a named-source
renaming in the outer coded safe tower; no quotient-source provider is assumed. -/
def namedIsoOriginalCodedQuotientIso
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    (s : CertifiedGateTower.ExactPrefix A) {B : CurrentSource.{u,v,w,t}}
    (I : NamedCurrentSourceIso s.current B) :
    CodedCurrentSourceIso
      (originalCodedQuotient A base hOne E (namedIsoExactPrefix s I))
      (originalCodedQuotient A base hOne E s) where
  sorts := namedIsoOriginalOccupancyEquiv A s.current B s.reduct base hOne E I
  points := namedIsoOriginalSelectedPointEquiv A s.current B s.reduct s.transport base hOne E I
  owner := namedIsoOriginalSelectedPointEquiv_owner A s.current B s.reduct s.transport base hOne E I
  palette := namedIsoOriginalSelectedPointEquiv_palette A s.current B s.reduct s.transport
    base hOne E I s.product
  code_eq := namedIsoOriginalSelectedPointEquiv_rootCode A s.current B s.reduct s.transport
    base hOne E I

end
end CCO.AutomaticEPCore
