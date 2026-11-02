import CCO.TransitionClosure.OriginalMenuSaturation
import CCO.TerminalLattice.QuotientLift

/-!
# B049 source07 OWI-S: actual ORIGINAL J-bisaturated quotient state

The first-hit interpolation proof constructs S = J° * P * J° for
one positive same-sort ORIGINAL word profile P. This is not just a
formal quotient relation: below is the literal quotient-state
relation, with TRUE quotient diagonal allowed and full OLD
diversity pullback at every pair of DIFFERENT old representatives.

Old RAW J ; P ; J permits logical identity in its J exteriors;
its STRONG diversity output has already been proved from the
ORIGINAL SAP source, for arbitrary P, in OriginalMenuSaturation.
Here we identify the precise full quotient relation without
assuming quotient SAP, quotient CCO, a section, or finite quotient.

The source's additional first-hit hypotheses J⋖K, meet-irreducibility
and positive J/K words are NOT needed for this purely algebraic bridge.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- The ACTUAL original quotient relation represented by any real
OLD fine menu P, formed by existentially choosing real representatives
of the two quotient classes linked by P. Crucially this relation may
contain the true quotient diagonal. -/
def originalJMenuQuotientState {i : ι}
    (J : ColourEq S i) (P : S.Menu i i) :
    Quotient J.val → Quotient J.val → Prop :=
  fun q r =>
    ∃ u v : X i,
      Quotient.mk J.val u = q ∧
      Quotient.mk J.val v = r ∧
      S.menuRel P u v

/-- Full source-OLD diversity pullback of the actual quotient
P-state equals the diversity part of equality-inclusive RAW
J ; P ; J, literally for every pair of old real endpoints.
Every quotient-diagonal pair is retained if it has two different
old representatives; NO synthetic real equality edge is added. -/
theorem originalJMenuQuotientState_full_pullback
    {i : ι} (J : ColourEq S i) (P : S.Menu i i) :
    quotientDiversity J.val (originalJMenuQuotientState S J P) =
      fun x y => x ≠ y ∧ originalRawJMenuSandwich S J P x y := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hxy,u,v,hu,hv,hP⟩
    have hJxu : J x u :=
      J.val.symm (Quotient.exact hu)
    have hJvy : J v y :=
      Quotient.exact hv
    exact ⟨hxy,u,v,hJxu,hP,hJvy⟩
  · rintro ⟨hxy,u,v,hJxu,hP,hJvy⟩
    exact ⟨hxy,u,v,Quotient.sound (J.val.symm hJxu),
      Quotient.sound hJvy,hP⟩

/-- Source07 OWI-S foundational REAL equality:
at a genuine nontrivial original invariant J, its positive
J-diversity envelope J° * P * J° equals EXACTLY the full
OLD diversity-colour pullback of the above actual quotient P-state.

This is equality of FINE ORIGINAL ATOM MENUS. It does NOT assume
a positive presentation for P, a fictitious STRONG unit, an
index-two exclusion, MI, FULL cover, CCO or hidden quotient SAP.
The exact source first-hit proof subsequently instantiates P with
a genuinely positive OLD typed word profile.
-/
theorem originalJMenuQuotientState_palette
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (P : S.Menu i i) :
    S.product (originalEquivDiversityPalette S J)
      (S.product P (originalEquivDiversityPalette S J)) =
      S.diversityGuard
        (quotientDiversity J.val (originalJMenuQuotientState S J P)) := by
  have hRaw :=
    original_raw_J_menu_J_guard_eq_strong S H sap J hJ P
  rw [originalJMenuQuotientState_full_pullback] 
  rw [← hRaw]
  ext c
  constructor
  · rintro ⟨x,y,hRawXY,hColour⟩
    have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ :=
      S.atomRel_ne hColour
    have hNe : x ≠ y := by
      intro hEq
      exact hTag (congrArg (Sigma.mk i) hEq)
    exact ⟨x,y,⟨hNe,hRawXY⟩,hColour⟩
  · rintro ⟨x,y,⟨_,hRawXY⟩,hColour⟩
    exact ⟨x,y,hRawXY,hColour⟩

end CCO.TransitionClosure
