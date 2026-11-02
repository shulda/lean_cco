import CCO.TerminalProfiles.OriginalQuotientMenuReturn
import CCO.TerminalProfiles.OriginalTwoSheetIndex
import CCO.TerminalProfiles.OriginalQuotientDiagonalInvolution
import CCO.RealClosure.Bounds.TerminalNR2
import CCO.PositiveWords

/-!
# B051 TNR: source09 no-return under a LOCAL original cut exclusion

At any ORIGINAL same-sort FULL invariant J, let P and Q be nonempty
old diversity fine-atom menus. If P*Q is contained in J°, the literal
original-G quotient menu relations R_P,R_Q have RAW product in the
genuine quotient diagonal, are symmetric/serial and invariant.
Consequently one shared ORIGINAL equivariant involution f represents
both relations. A nontrivial f makes an ACTUAL ORIGINAL full
colour-invariant higher equivalence K with exactly two J-classes per
K-class. Only the source's LOCAL no-two-interval hypothesis above J
eliminates it; no global NR2 is needed for this algebraic theorem.

The source-positive-word instance supplies menu nonemptiness from
original SAP and applies the local theorem to arbitrary positive typed
same-sort word profiles, whose interiors can use ANY original sorts.
A separate terminal FULL NR2 wrapper discharges the local condition
without assuming it as a new independent terminal premise.

No CCO, hidden/quotient SAP, arbitrary quotient automorphism action,
synthetic STRONG identity letter, conditional provider or axiom.
-/

universe u v w t

namespace CCO.TerminalProfiles

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.ParityHasse.Original
open CCO.TerminalLattice
open CCO.TransitionClosure

/-- SOURCE09 C06–C12 actual old menu no-return, with only
the locally forbidden index-two interval J<K. These P,Q menus
are nonempty ACTUAL ORIGINAL atom menus; the following original
positive-word wrapper supplies those facts from old SAP. -/
theorem original_no_return_menus_of_local_no_two
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i)
    (hNoTwo : ∀ K : ColourEq S i, J < K →
      ¬ CCO.Selectors.RelativeIndexTwo J.val K.val)
    (P Q : S.Menu i i)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hProduct : S.product P Q ⊆
      originalEquivDiversityPalette S J) :
    P ⊆ originalEquivDiversityPalette S J ∧
      Q ⊆ originalEquivDiversityPalette S J := by
  classical
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  let R : Quotient J.val → Quotient J.val → Prop :=
    originalJMenuQuotientState S J P
  let T : Quotient J.val → Quotient J.val → Prop :=
    originalJMenuQuotientState S J Q
  obtain ⟨f,hRiff,hTiff,hInv,hEquiv⟩ :=
    symmetric_serial_diagonal_comp_equivariant_involution
      R T
      (original_quotient_menu_symmetric S J P)
      (original_quotient_menu_symmetric S J Q)
      (original_quotient_menu_serial S H J P hP)
      (original_quotient_menu_serial S H J Q hQ)
      (original_quotient_menu_comp_subset_diagonal S H J P Q hProduct)
      (original_quotient_menu_invariant S H J P)
  have hId : ∀ q : Quotient J.val, f q = q :=
    original_equivariant_quotient_involution_identity
      S H J hNoTwo f hInv hEquiv
  constructor
  · intro a ha
    obtain ⟨x,y,hxy⟩ := S.realized a
    have hR : R (Quotient.mk J.val x) (Quotient.mk J.val y) :=
      ⟨x,y,rfl,rfl,a,ha,hxy⟩
    have hQuot : Quotient.mk J.val x = Quotient.mk J.val y := by
      calc
        Quotient.mk J.val x = f (Quotient.mk J.val x) := (hId _).symm
        _ = Quotient.mk J.val y := (hRiff _ _).mp hR
    exact ⟨x,y,Quotient.exact hQuot,hxy⟩
  · intro a ha
    obtain ⟨x,y,hxy⟩ := S.realized a
    have hT : T (Quotient.mk J.val x) (Quotient.mk J.val y) :=
      ⟨x,y,rfl,rfl,a,ha,hxy⟩
    have hQuot : Quotient.mk J.val x = Quotient.mk J.val y := by
      calc
        Quotient.mk J.val x = f (Quotient.mk J.val x) := (hId _).symm
        _ = Quotient.mk J.val y := (hTiff _ _).mp hT
    exact ⟨x,y,Quotient.exact hQuot,hxy⟩

/-- SOURCE09 selected typed TNR for two genuinely POSITIVE OLD typed
words, using ONLY the local original J-cut no-index-two exclusion,
with no terminal NR2 at unrelated intervals. The explicit J>Id
is the actual source-side equivalence precondition. -/
theorem original_no_return_positive_words_of_local_no_two
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (_hJ : (⊥ : ColourEq S i) < J)
    (hNoTwo : ∀ K : ColourEq S i, J < K →
      ¬ CCO.Selectors.RelativeIndexTwo J.val K.val)
    (wP wQ : PositiveWord S i i)
    (hProduct : S.product (PositiveWord.profile S wP)
      (PositiveWord.profile S wQ) ⊆
        originalEquivDiversityPalette S J) :
    PositiveWord.profile S wP ⊆ originalEquivDiversityPalette S J ∧
      PositiveWord.profile S wQ ⊆ originalEquivDiversityPalette S J := by
  exact original_no_return_menus_of_local_no_two
    S H J hNoTwo
    (PositiveWord.profile S wP) (PositiveWord.profile S wQ)
    (PositiveWord.profile_nonempty_of_SAP S H sap wP)
    (PositiveWord.profile_nonempty_of_SAP S H sap wQ)
    hProduct

/-- SOURCE09 terminal original FULL NR2 is ONE sufficient source
instance of the local no-two hypothesis. The no-return proof does
not insert global terminality into its local involution argument. -/
theorem original_terminal_no_return_positive_words
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : CCO.Selectors.OriginalNR2 S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (wP wQ : PositiveWord S i i)
    (hProduct : S.product (PositiveWord.profile S wP)
      (PositiveWord.profile S wQ) ⊆
        originalEquivDiversityPalette S J) :
    PositiveWord.profile S wP ⊆ originalEquivDiversityPalette S J ∧
      PositiveWord.profile S wQ ⊆ originalEquivDiversityPalette S J := by
  have hNoTwo : ∀ K : ColourEq S i, J < K →
      ¬ CCO.Selectors.RelativeIndexTwo J.val K.val := by
    intro K _ hTwo
    exact nr2 i J.val K.val J.property K.property hTwo
  exact original_no_return_positive_words_of_local_no_two
    S H sap J hJ hNoTwo wP wQ hProduct

end CCO.TerminalProfiles
