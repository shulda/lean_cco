import CCO.AclOwners.ClosedPreimages
import CCO.ExactCRT.AbstractFibreProduct

/-! Actual complementary rectangles and their absolute real closure.
The common finite owner is permitted to be nonclosed and nonharmless. -/
universe v w t
namespace CCO.AclOwners
open ParityHasse.Original FinitePackets.Normalization RawExact RealClosure.Bounds
open ExactCRT
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (C K : ColourEq S ())

def rectangleSet (D : Finset (Quotient C.val)) (P : Finset (Quotient K.val)) : Set M :=
  {x | (Quotient.mk'' x : Quotient C.val) ∈ D ∧
    (Quotient.mk'' x : Quotient K.val) ∈ P}

def rectangleTuples (D : Finset (Quotient C.val)) (P : Finset (Quotient K.val)) :=
  {p : Abstract.FibreProduct C.val K.val // p.val.1 ∈ D ∧ p.val.2 ∈ P}

/-- The ambient bijection is a genuine two-factor CRT construction. -/
noncomputable def realFibreProductEquiv (hCK : C.val ⊓ K.val = ⊥) :
    M ≃ Abstract.FibreProduct C.val K.val := by
  let f : M → Abstract.FibreProduct C.val K.val :=
    fun x => Abstract.fibreCoordinates C.val K.val (Quotient.mk _ x)
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have hp := congrArg Subtype.val h
    have hxy : (C.val ⊓ K.val) x y :=
      ⟨Quotient.exact (congrArg Prod.fst hp),Quotient.exact (congrArg Prod.snd hp)⟩
    rw [hCK] at hxy
    exact hxy
  · intro p
    have comm : Abstract.Permutes C.val K.val :=
      invariant_relations_commute S H C.property K.property
    obtain ⟨q,hq⟩ := Abstract.fibreCoordinates_surjective C.val K.val comm p
    induction q using Quotient.inductionOn with | _ x => exact ⟨x,hq⟩

@[simp] theorem realFibreProductEquiv_coordinates (hCK : C.val ⊓ K.val = ⊥) (x : M) :
    (realFibreProductEquiv S H C K hCK x).val =
      (Quotient.mk'' x,Quotient.mk'' x) := rfl

/-- No formally compatible tuple of either finite target is omitted. -/
noncomputable def realRectangleEquiv (hCK : C.val ⊓ K.val = ⊥)
    (D : Finset (Quotient C.val)) (P : Finset (Quotient K.val)) :
    rectangleSet S C K D P ≃ rectangleTuples S C K D P :=
  (realFibreProductEquiv S H C K hCK).subtypeEquiv (fun _ => Iff.rfl)

theorem rectangleSet_finite (hCK : C.val ⊓ K.val = ⊥)
    (D : Finset (Quotient C.val)) (P : Finset (Quotient K.val)) :
    (rectangleSet S C K D P).Finite := by
  let f : rectangleSet S C K D P → ↥D × ↥P := fun x =>
    (⟨Quotient.mk'' x.val,x.property.1⟩,⟨Quotient.mk'' x.val,x.property.2⟩)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hC : C x.val y.val := Quotient.exact (congrArg (fun p : ↥D × ↥P => p.1.val) h)
    have hK : K x.val y.val := Quotient.exact (congrArg (fun p : ↥D × ↥P => p.2.val) h)
    have hh : (C.val ⊓ K.val) x.val y.val := ⟨hC,hK⟩
    rw [hCK] at hh
    exact hh
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

include H in
/-- The source owner hypotheses supply nonemptiness without assuming that
owner is closed. Only the displayed finite onto images are used. -/
theorem rectangle_nonempty_of_owner (hCK : C.val ⊓ K.val = ⊥)
    (D : Finset (Quotient C.val)) (P : Finset (Quotient K.val))
    (B : Finset (Quotient (C.val ⊔ K.val))) (hB : B.Nonempty)
    (ontoD : ∀ b ∈ B, ∃ d ∈ D, Abstract.quotientMap (show C.val ≤ C.val ⊔ K.val from le_sup_left) d = b)
    (ontoP : ∀ b ∈ B, ∃ p ∈ P, Abstract.quotientMap (show K.val ≤ C.val ⊔ K.val from le_sup_right) p = b) :
    (rectangleSet S C K D P).Nonempty := by
  obtain ⟨b,hb⟩ := hB
  obtain ⟨d,hd,hdb⟩ := ontoD b hb
  obtain ⟨p,hp,hpb⟩ := ontoP b hb
  let tuple : Abstract.FibreProduct C.val K.val := ⟨(d,p),hdb.trans hpb.symm⟩
  let x := (realFibreProductEquiv S H C K hCK).symm tuple
  have hx := congrArg Subtype.val ((realFibreProductEquiv S H C K hCK).apply_symm_apply tuple)
  have hxd : (Quotient.mk'' x : Quotient C.val) = d := congrArg Prod.fst hx
  have hxp : (Quotient.mk'' x : Quotient K.val) = p := congrArg Prod.snd hx
  exact ⟨x,hxd.symm ▸ hd,hxp.symm ▸ hp⟩

/-- C26: both factors are absolutely closed in their actual quotient
sources; the common owner is not an argument to the closure proof. -/
theorem rectangle_absolute_closure [Countable M] [DecidableEq M]
    (cco : SemanticCCO.{0,v,0,w} S) (hCK : C.val ⊓ K.val = ⊥)
    (BC BK : NonemptyExact S () ())
    (hC : evaluate S BC.words = C.val.r) (hK : evaluate S BK.words = K.val.r)
    (D : Finset (Quotient C.val)) (P : Finset (Quotient K.val))
    (hne : (rectangleSet S C K D P).Nonempty) :
    letI := originalQuotientAction S H C
    letI := originalQuotientAction S H K
    (Acl G D = (D : Set (Quotient C.val))) →
    (Acl G P = (P : Set (Quotient K.val))) →
    ∃ W : Finset M, W.Nonempty ∧ (∀ x, x ∈ W ↔ x ∈ rectangleSet S C K D P) ∧
      Acl G W = (W : Set M) := by
  classical
  letI := originalQuotientAction S H C
  letI := originalQuotientAction S H K
  intro hD hP
  let J : Bool → ColourEq S () | false => C | true => K
  let E : ∀ _ : Bool, NonemptyExact S () () | false => BC | true => BK
  let F : ∀ i, Finset (Quotient (J i).val) | false => D | true => P
  have hE : ∀ i, evaluate S (E i).words = (J i).val.r := by
    intro i; cases i
    · exact hC
    · exact hK
  have hfin := rectangleSet_finite S C K hCK D P
  let W := hfin.toFinset
  have hW (x : M) : x ∈ W ↔ x ∈ rectangleSet S C K D P := hfin.mem_toFinset
  have hW' (x : M) : x ∈ W ↔ ∀ i, (Quotient.mk'' x : Quotient (J i).val) ∈ F i := by
    rw [hW]
    constructor
    · intro hx i; cases i
      · exact hx.1
      · exact hx.2
    · intro hx; exact ⟨hx false,hx true⟩
  have closed := exact_fullPreimage_closed S H cco J E hE F W hW' (by
    intro i; cases i
    · exact hD
    · exact hP)
  refine ⟨W,?_,hW,closed⟩
  obtain ⟨x,hx⟩ := hne
  exact ⟨x,(hW x).mpr hx⟩

include H in
/-- C27 remains an independent equality-inclusive mixed-orbital identity,
without an owner-closure premise and without being needed by C25. -/
theorem rectangle_mixed_orbit (a : Option (S.Atom () ())) :
    RawSymmetric.compose (RawSymmetric.compose C.val.r (S.rawAtomRel a)) K.val.r =
      RawSymmetric.compose (RawSymmetric.compose (C.val ⊔ K.val).r (S.rawAtomRel a))
        (C.val ⊔ K.val).r := by
  have comm : Abstract.Permutes C.val K.val :=
    invariant_relations_commute S H C.property K.property
  rw [Abstract.join_eq_comp C.val K.val comm]
  exact (actual_mixed_join_of_homogeneous S H C.val.r K.val.r
    ⟨C.val.refl,fun _ _ h => C.val.symm h,fun _ _ _ h k => C.val.trans h k⟩
    ⟨K.val.refl,fun _ _ h => K.val.symm h,fun _ _ _ h k => K.val.trans h k⟩
    (colourInvariant_groupInvariant S H C.property)
    (colourInvariant_groupInvariant S H K.property) a).1
end CCO.AclOwners
