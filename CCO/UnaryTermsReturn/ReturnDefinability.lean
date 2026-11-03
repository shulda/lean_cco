import CCO.UnaryTermsReturn.NamedReturnLoop
import CCO.QuotientTransport.Definability

/-!
# B052 C28–C33/C37: genuine original first-order definability gates

B040's generic group-invariant quotient-return theory requires
only a transitive G-action and nonempty invariant RAW factors;
for an ARBITRARY acting subgroup, invariance does not imply
parameter-free first-order definability.

The stronger source10 *original named language* conclusion uses
the SAME original homogeneous full-G action as the actual finite
pair-orbital structure. The existing B040 source-formula provider
constructs a finite disjunction of REAL named atomic optional
pair colours for every old-G invariant relation. Consequently
every finite RAW prefix and its literal Rᵒᵖ;J;R transported FULL
kernel have an ACTUAL typed first-order formula, with original
sorts and true diagonal retained. We prove the link explicitly;
no new definability oracle, source change or general hidden
homogeneity claim is introduced.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original
open CCO.QuotientTransport
open CCO.QuotientTransport.Definability

/-- Each genuinely nonempty original-G invariant typed RAW letter
is parameter-free definable in the finite original named
atomic language, with its literal source and target tags.
This depends on FULL original pair homogeneity; it is not
claimed for an unrelated arbitrary subgroup. -/
theorem original_return_letter_has_original_formula
    (H : HomogeneousSource S G)
    {i j : ι} (P : Letter G X i j) :
    TypedHasFormula (L := namedLanguage S) P.relation :=
  source_invariant_has_formula S H P.relation P.invariant

/-- The complete nonempty typed RAW prefix word has a
FIRST-ORDER existential formula built from the actual old
atomic named symbols and genuine equality for nil. No
new equality-labelled STRONG diversity atom is introduced. -/
theorem original_return_prefix_has_original_formula
    (H : HomogeneousSource S G)
    {a i : ι} (p : Word G X a i) :
    TypedHasFormula (L := namedLanguage S) p.eval :=
  source_typedWord_has_formula S H
    (fun {_ _} (P : Letter G X _ _) => P.relation)
    (fun _ _ (P : Letter G X _ _) => P.invariant) p

/-- The TRUE FULL transported invariant kernel of one B040
return prefix is first-order definable when the base J is
an actual original named FULL equivalence. The exact
relation is Rᵒᵖ;J;R, derived from Return.prefixTransport,
rather than an independent hypothetical name for the
generic intermediate quotient. -/
theorem original_return_prefix_kernel_has_original_formula
    (H : HomogeneousSource S G)
    {a i : ι} (J : ColourEq S a)
    (p : Word G X a i) (s : Word G X i a)
    (h : Return.Bound (originalColourEqAsInvEq S H J) p s) :
    TypedHasFormula (L := namedLanguage S)
      (fun y z : X i =>
        (Return.prefixTransport
          (originalColourEqAsInvEq S H J)
          (originalReturnSortTransitivity S H)
          p s h).target y z) := by
  let E : InvEq G (X a) := originalColourEqAsInvEq S H J
  let T := Return.prefixTransport E
    (originalReturnSortTransitivity S H) p s h
  have hJ : TypedHasFormula (L := namedLanguage S) E.val.r :=
    source_invariant_has_formula S H E.val.r E.property
  have hp : TypedHasFormula (L := namedLanguage S) p.eval :=
    original_return_prefix_has_original_formula S H p
  have hRel : TypedHasFormula (L := namedLanguage S)
      (TRel.comp (TRel.converse p.eval)
        (TRel.comp E.val.r p.eval)) :=
    typed_transport_has_formula hp hJ
  have hExact :
      (TRel.comp (TRel.converse p.eval)
        (TRel.comp E.val.r p.eval)) =
          (fun y z : X i => T.target y z) := by
    funext y z
    apply propext
    constructor
    · rintro ⟨x,hxy,x',hxx',hx'z⟩
      exact (T.target_iff y z).mpr ⟨x,x',hxy,hxx',hx'z⟩
    · intro ht
      obtain ⟨x,x',hxy,hxx',hx'z⟩ := (T.target_iff y z).mp ht
      exact ⟨x,hxy,x',hxx',hx'z⟩
  rw [hExact] at hRel
  exact hRel

end CCO.UnaryTermsReturn
