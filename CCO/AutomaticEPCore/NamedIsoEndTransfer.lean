import CCO.AutomaticEPCore.CodedTowerReceiving
import CCO.ExactEPGeometry.ActualPrefixSupport
import CCO.ExactEPGeometry.RelativeIndexQuotientTransport

/-! Whole-source endpoint receiving preserves the FULL invariant
equivalence lattice and its actual relative classes. Code support tables
are carried to the specified endpoint names with the same code values,
using real point witnesses rather than a cardinality comparison. -/

universe u v w t z z'
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ParityHasse.Original
noncomputable section

variable {A B : CurrentSource.{u,v,w,t}}

/-- The actual whole named-source map restricted to one displayed fibre. -/
def namedIsoFibreEquiv (I : NamedCurrentSourceIso A B) (i : A.Sorts) :
    A.Point i ≃ B.Point (I.sorts i) :=
  namedPointEquiv I.sorts I.points I.owner i

theorem namedIsoFibreEquiv_tagged (I : NamedCurrentSourceIso A B)
    (i : A.Sorts) (x : A.Point i) :
    (⟨I.sorts i,namedIsoFibreEquiv I i x⟩ : Sigma B.Point) = I.points ⟨i,x⟩ :=
  namedPointEquiv_tagged I.sorts I.points I.owner i x

/-- Same-sort complete optional colour partitions agree under the actual
fibre map, including the logical diagonal. -/
theorem namedIsoFibreEquiv_colour_iff (I : NamedCurrentSourceIso A B)
    (i : A.Sorts) (x y x' y' : A.Point i) :
    A.source.colour x y = A.source.colour x' y' ↔
      B.source.colour (namedIsoFibreEquiv I i x) (namedIsoFibreEquiv I i y) =
        B.source.colour (namedIsoFibreEquiv I i x') (namedIsoFibreEquiv I i y') := by
  have h := I.palette ⟨i,x⟩ ⟨i,y⟩ ⟨i,x'⟩ ⟨i,y'⟩
  rw [← namedIsoFibreEquiv_tagged I i x,← namedIsoFibreEquiv_tagged I i y,
    ← namedIsoFibreEquiv_tagged I i x',← namedIsoFibreEquiv_tagged I i y'] at h
  simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using h

/-- An order isomorphism of ALL actual colour-invariant equivalences.
Neither side is restricted to the full RAW-exact sublattice. -/
def namedIsoColourOrderIso (I : NamedCurrentSourceIso A B) (i : A.Sorts) :
    ColourEq A.source i ≃o ColourEq B.source (I.sorts i) where
  toFun E := ⟨Setoid.comap (namedIsoFibreEquiv I i).symm E.val,by
    intro x y x' y' hc
    apply E.property
    apply (namedIsoFibreEquiv_colour_iff I i _ _ _ _).mpr
    simpa only [Equiv.apply_symm_apply] using hc⟩
  invFun E := ⟨Setoid.comap (namedIsoFibreEquiv I i) E.val,by
    intro x y x' y' hc
    exact E.property _ _ _ _ ((namedIsoFibreEquiv_colour_iff I i x y x' y').mp hc)⟩
  left_inv E := by
    apply ColourEq.ext
    intro x y
    change E.val ((namedIsoFibreEquiv I i).symm (namedIsoFibreEquiv I i x))
      ((namedIsoFibreEquiv I i).symm (namedIsoFibreEquiv I i y)) ↔ E.val x y
    simp only [Equiv.symm_apply_apply]
  right_inv E := by
    apply ColourEq.ext
    intro x y
    change E.val (namedIsoFibreEquiv I i ((namedIsoFibreEquiv I i).symm x))
      (namedIsoFibreEquiv I i ((namedIsoFibreEquiv I i).symm y)) ↔ E.val x y
    simp only [Equiv.apply_symm_apply]
  map_rel_iff' := by
    intro E F
    change (∀ ⦃x y : B.Point (I.sorts i)⦄,
      E.val ((namedIsoFibreEquiv I i).symm x) ((namedIsoFibreEquiv I i).symm y) →
      F.val ((namedIsoFibreEquiv I i).symm x) ((namedIsoFibreEquiv I i).symm y)) ↔
      (∀ ⦃x y : A.Point i⦄, E.val x y → F.val x y)
    constructor
    · intro h x y hxy
      have hh := @h (namedIsoFibreEquiv I i x) (namedIsoFibreEquiv I i y)
      have hh' : E x y → F x y := by
        simpa only [Equiv.symm_apply_apply] using hh
      exact hh' hxy
    · intro h x y hxy
      exact @h _ _ hxy

theorem namedIsoColourOrderIso_rel (I : NamedCurrentSourceIso A B)
    (i : A.Sorts) (E : ColourEq A.source i) (x y : A.Point i) :
    namedIsoColourOrderIso I i E (namedIsoFibreEquiv I i x)
      (namedIsoFibreEquiv I i y) ↔ E x y := by
  change E.val ((namedIsoFibreEquiv I i).symm (namedIsoFibreEquiv I i x))
    ((namedIsoFibreEquiv I i).symm (namedIsoFibreEquiv I i y)) ↔ E.val x y
  simp only [Equiv.symm_apply_apply]

/-- The actual relative-class quotient sets, for arbitrary full invariant
equivalences, are bijective under the same displayed fibre map. -/
def namedIsoRelativeClassEquiv (I : NamedCurrentSourceIso A B)
    (i : A.Sorts) (E F : ColourEq A.source i) (a : A.Point i) :
    RelativeClass E.val F.val a ≃
      RelativeClass (namedIsoColourOrderIso I i E).val
        (namedIsoColourOrderIso I i F).val (namedIsoFibreEquiv I i a) :=
  relativeClassEquiv_of_surjective_pullback
    (namedIsoFibreEquiv I i) (namedIsoFibreEquiv I i).surjective E.val F.val
    (namedIsoColourOrderIso I i E).val (namedIsoColourOrderIso I i F).val
    (fun x y => (namedIsoColourOrderIso_rel I i E x y).symm)
    (fun x y => (namedIsoColourOrderIso_rel I i F x y).symm) a

theorem namedIso_relative_index (I : NamedCurrentSourceIso A B)
    (i : A.Sorts) (E F : ColourEq A.source i) (a : A.Point i) :
    relativeIndex E.val F.val a =
      relativeIndex (namedIsoColourOrderIso I i E).val
        (namedIsoColourOrderIso I i F).val (namedIsoFibreEquiv I i a) :=
  Nat.card_congr (namedIsoRelativeClassEquiv I i E F a)

private theorem namedIso_terminal_backward (I : NamedCurrentSourceIso A B)
    (terminal : B.Terminal) : A.Terminal := by
  rintro ⟨i,E,F,a,hEF,hFinite⟩
  let f := namedIsoColourOrderIso I i
  let : Finite (RelativeClass E.val F.val a) := hFinite
  have hFinB : Finite (RelativeClass (f E).val (f F).val (namedIsoFibreEquiv I i a)) :=
    Finite.of_equiv _ (namedIsoRelativeClassEquiv I i E F a)
  exact terminal ⟨I.sorts i,f E,f F,namedIsoFibreEquiv I i a,f.strictMono hEF,hFinB⟩

/-- Terminality transfers for the FULL invariant-equivalence lattice,
including non-exact equivalences and proper intervals ending at Top. -/
theorem namedIso_terminal_iff (I : NamedCurrentSourceIso A B) :
    A.Terminal ↔ B.Terminal :=
  ⟨namedIso_terminal_backward I.symm,namedIso_terminal_backward I⟩

variable {Code : Type z}

/-- A literal fixed-code binary predicate on the actual realized named
sorts. All quantifiers range over real source points. -/
def codedPredicateSupport (X : CodedCurrentSource.{u,v,w,t} Code)
    (R : Code → Prop) (s t : X.current.Sorts) : Prop :=
  ∃ x : X.current.Point s, ∃ y : X.current.Point t, R (X.code ⟨s,x⟩ ⟨t,y⟩)

/-- The entire actual table is finite because the current source has its
finite complete realized unary palette; no external label list is used. -/
def codedPredicateTable (X : CodedCurrentSource.{u,v,w,t} Code)
    (R : Code → Prop) : Set (X.current.Sorts × X.current.Sorts) :=
  {st | codedPredicateSupport X R st.1 st.2}

theorem codedPredicateTable_finite (X : CodedCurrentSource.{u,v,w,t} Code)
    (R : Code → Prop) : (codedPredicateTable X R).Finite := by
  let := X.current.source.finiteSort
  exact Set.toFinite _

variable {X Y : CodedCurrentSource.{u,v,w,t} Code}

/-- The fibre map preserves the literal code value on every actual pair. -/
theorem codedIsoFibre_code (I : CodedCurrentSourceIso X Y)
    (s t : X.current.Sorts) (x : X.current.Point s) (y : X.current.Point t) :
    Y.code ⟨I.sorts s,namedIsoFibreEquiv I.toNamedCurrentSourceIso s x⟩
      ⟨I.sorts t,namedIsoFibreEquiv I.toNamedCurrentSourceIso t y⟩ =
      X.code ⟨s,x⟩ ⟨t,y⟩ := by
  rw [namedIsoFibreEquiv_tagged,namedIsoFibreEquiv_tagged]
  exact I.code_eq _ _

/-- Exact support at the specified image names, with real point witnesses
in BOTH directions and the SAME fixed code predicate. -/
theorem codedPredicateSupport_iso_iff (I : CodedCurrentSourceIso X Y)
    (R : Code → Prop) (s t : X.current.Sorts) :
    codedPredicateSupport X R s t ↔
      codedPredicateSupport Y R (I.sorts s) (I.sorts t) := by
  constructor
  · rintro ⟨x,y,hxy⟩
    refine ⟨namedIsoFibreEquiv I.toNamedCurrentSourceIso s x,
      namedIsoFibreEquiv I.toNamedCurrentSourceIso t y,?_⟩
    rw [codedIsoFibre_code]
    exact hxy
  · rintro ⟨x,y,hxy⟩
    let a := (namedIsoFibreEquiv I.toNamedCurrentSourceIso s).symm x
    let b := (namedIsoFibreEquiv I.toNamedCurrentSourceIso t).symm y
    refine ⟨a,b,?_⟩
    have h := codedIsoFibre_code I s t a b
    dsimp only [a,b] at h
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at h
    exact h ▸ hxy

/-- Read back a fixed-code support witness at the actual prescribed target
names, without choosing unrelated points or merely comparing table sizes. -/
theorem codedPredicateSupport_target_iff (I : CodedCurrentSourceIso X Y)
    (R : Code → Prop) (s t : Y.current.Sorts) :
    codedPredicateSupport Y R s t ↔
      codedPredicateSupport X R (I.sorts.symm s) (I.sorts.symm t) := by
  simpa only [Equiv.apply_symm_apply] using
    (codedPredicateSupport_iso_iff I R (I.sorts.symm s) (I.sorts.symm t)).symm

/-- Equality of the complete finite tables under the actual sort
equivalence, rather than equality of their cardinalities. -/
theorem codedPredicateTable_iso (I : CodedCurrentSourceIso X Y)
    (R : Code → Prop) :
    codedPredicateTable X R =
      (fun st : X.current.Sorts × X.current.Sorts => (I.sorts st.1,I.sorts st.2)) ⁻¹'
        codedPredicateTable Y R := by
  apply Set.ext
  rintro ⟨s,t⟩
  exact codedPredicateSupport_iso_iff I R s t

/-- The exact SAME code value occurs at the corresponding real names. -/
theorem codedValueSupport_iso_iff (I : CodedCurrentSourceIso X Y)
    (c : Code) (s t : X.current.Sorts) :
    codedPredicateSupport X (fun value => value = c) s t ↔
      codedPredicateSupport Y (fun value => value = c) (I.sorts s) (I.sorts t) :=
  codedPredicateSupport_iso_iff I (fun value => value = c) s t

/-- The support table on a received exact prefix is LITERALLY the support
of its fixed original binary relation through the same actual reduct. -/
theorem codedExactPrefix_predicate_support
    {A : CurrentSource.{u,v,w,t}}
    (rootCode : Sigma A.Point → Sigma A.Point → Code)
    (next : CertifiedGateTower.ExactPrefix A) (R : Code → Prop)
    (s t : next.current.Sorts) :
    codedPredicateSupport (codedExactPrefix rootCode next) R s t ↔
      prefixSupport next.reduct (fun p q => R (rootCode p q)) s t := Iff.rfl

/-- Actual original binary support at received names is carried to the
precise literal endpoint source with the SAME original predicate value. -/
theorem codedExactPrefix_support_iso_iff
    {A : CurrentSource.{u,v,w,t}}
    (rootCode : Sigma A.Point → Sigma A.Point → Code)
    (next : CertifiedGateTower.ExactPrefix A)
    {Y : CodedCurrentSource.{u,v,w,t} Code}
    (I : CodedCurrentSourceIso (codedExactPrefix rootCode next) Y)
    (R : Code → Prop) (s t : next.current.Sorts) :
    prefixSupport next.reduct (fun p q => R (rootCode p q)) s t ↔
      codedPredicateSupport Y R (I.sorts s) (I.sorts t) :=
  codedPredicateSupport_iso_iff I R s t

/-- Inverse endpoint readback retains the prescribed target occupancy
names and constructs genuine old-point witnesses in those exact fibres. -/
theorem codedExactPrefix_support_target_iff
    {A : CurrentSource.{u,v,w,t}}
    (rootCode : Sigma A.Point → Sigma A.Point → Code)
    (next : CertifiedGateTower.ExactPrefix A)
    {Y : CodedCurrentSource.{u,v,w,t} Code}
    (I : CodedCurrentSourceIso (codedExactPrefix rootCode next) Y)
    (R : Code → Prop) (s t : Y.current.Sorts) :
    codedPredicateSupport Y R s t ↔
      prefixSupport next.reduct (fun p q => R (rootCode p q))
        (I.sorts.symm s) (I.sorts.symm t) :=
  codedPredicateSupport_target_iff I R s t

/-- Fixed original predicate coordinates keep their own literal names.
This applies to the original E-saturated quotient family without any
renaming of atoms, predicates or endpoint occupancy names. -/
theorem codedCoordinateSupport_iso_iff {Index : Type z'}
    {X Y : CodedCurrentSource.{u,v,w,t} (Index → Prop)}
    (I : CodedCurrentSourceIso X Y) (a : Index) (s t : X.current.Sorts) :
    codedPredicateSupport X (fun code => code a) s t ↔
      codedPredicateSupport Y (fun code => code a) (I.sorts s) (I.sorts t) :=
  codedPredicateSupport_iso_iff I (fun code => code a) s t

end
end CCO.AutomaticEPCore
