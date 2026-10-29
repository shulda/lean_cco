import CCO.OwnerTransversal.TypedLifting
import CCO.RawExact.QuotientAgeAP

/-! The actual named-owner source in its literal OLD fine colours.
Owner labels specify distinct actual E-classes; repeated formal vertices
with one label are still distinct real points when joined by diversity. -/
universe v w t
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (E : ColourEq S ()) {B : Type} [Fintype B] (q : B → Quotient E.val)

abbrev OwnerCarrier (b : B) := {x : M // (Quotient.mk'' x : Quotient E.val) = q b}
abbrev OwnerAtom (b c : B) := {a : S.Atom () () //
  ∃ (x : OwnerCarrier S E q b) (y : OwnerCarrier S E q c), S.atomRel a x.val y.val}

noncomputable def ownerColour {b c : B} (x : OwnerCarrier S E q b) (y : OwnerCarrier S E q c) :
    Option (OwnerAtom S E q b c) :=
  match hc : S.colour (i := ()) (j := ()) x.val y.val with
  | none => none
  | some a => some ⟨a,x,y,hc⟩

theorem ownerColour_map {b c : B} (x : OwnerCarrier S E q b) (y : OwnerCarrier S E q c) :
    (ownerColour S E q x y).map Subtype.val = S.colour (i := ()) (j := ()) x.val y.val := by
  unfold ownerColour
  split <;> rename_i h <;> exact h.symm

theorem ownerColour_some_iff {b c : B} (x : OwnerCarrier S E q b) (y : OwnerCarrier S E q c)
    (a : OwnerAtom S E q b c) :
    ownerColour S E q x y = some a ↔ S.colour (i := ()) (j := ()) x.val y.val = some a.val := by
  constructor
  · intro h
    rw [← ownerColour_map S E q x y,h]
    rfl
  · intro h
    unfold ownerColour
    split
    next hc => rw [hc] at h; cases h
    next b hc =>
      apply congrArg some
      apply Subtype.ext
      exact Option.some.inj (hc.symm.trans h)

theorem ownerColour_none_iff {b c : B} (x : OwnerCarrier S E q b) (y : OwnerCarrier S E q c) :
    ownerColour S E q x y = none ↔ x.val = y.val := by
  constructor
  · intro h
    have hh : S.colour (i := ()) (j := ()) x.val y.val = none := by
      rw [← ownerColour_map S E q x y,h]
      rfl
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using (S.colour_none_iff _ _).mp hh
  · intro h
    have hh : S.colour (i := ()) (j := ()) x.val y.val = none :=
      (S.colour_none_iff _ _).mpr (congrArg (Sigma.mk ()) h)
    apply Option.map_eq_none_iff.mp
    rw [ownerColour_map,hh]

noncomputable def ownerConverse {b c : B} (a : OwnerAtom S E q b c) : OwnerAtom S E q c b :=
  ⟨a.val,by
    obtain ⟨x,y,hxy⟩ := a.property
    exact ⟨y,x,(colour_symmetric S y.val x.val).trans hxy⟩⟩

noncomputable def typedOwnerSource (hq : Function.Injective q) :
    AtomicSource.{0,v,w} B (OwnerCarrier S E q) where
  Atom := OwnerAtom S E q
  finiteSort := inferInstance
  finiteAtom := fun b c => by
    letI := S.finiteAtom () ()
    exact Fintype.ofFinite _
  nonemptySort := fun b => ⟨⟨(q b).out,Quotient.out_eq _⟩⟩
  conv := ownerConverse S E q
  conv_invol := fun _ => Subtype.ext rfl
  symmetricLoop := fun _ => Subtype.ext rfl
  colour := ownerColour S E q
  colour_none_iff := by
    intro b c x y
    rw [ownerColour_none_iff]
    constructor
    · intro hxy
      have hbc : b = c := hq (x.property.symm.trans ((congrArg Quotient.mk'' hxy).trans y.property))
      subst c
      exact congrArg (Sigma.mk b) (Subtype.ext hxy)
    · intro hxy
      cases hxy
      rfl
  colour_swap := by
    intro b c x y a
    rw [ownerColour_some_iff,ownerColour_some_iff]
    exact Iff.of_eq (congrArg (fun t => t = some a.val) (colour_symmetric S x.val y.val))
  realized := by
    intro b c a
    obtain ⟨x,y,hxy⟩ := a.property
    exact ⟨x,y,(ownerColour_some_iff S E q x y a).mpr hxy⟩

theorem typedOwner_colour_iff (hq : Function.Injective q) {b c : B}
    (x x' : OwnerCarrier S E q b) (y y' : OwnerCarrier S E q c) :
    (typedOwnerSource S E q hq).colour x y = (typedOwnerSource S E q hq).colour x' y' ↔
      S.colour (i := ()) (j := ()) x.val y.val = S.colour x'.val y'.val := by
  constructor
  · intro hh
    simpa only [typedOwnerSource,ownerColour_map] using congrArg (Option.map Subtype.val) hh
  · intro hh
    apply Option.map_injective Subtype.val_injective
    exact (ownerColour_map S E q x y).trans (hh.trans (ownerColour_map S E q x' y').symm)

end CCO.OwnerTransversal
