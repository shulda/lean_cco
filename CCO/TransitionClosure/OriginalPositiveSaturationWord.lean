import CCO.TransitionClosure.OriginalFirstHitBase
import CCO.TerminalLattice.CompleteOrbitalWord

/-!
# B049 source07 C11: one actual positive original OLD J-saturation word

The original first-hit argument starts with a genuine positive typed
same-sort endpoint word P and one positive ORIGINAL J-diversity
presentation. Its saturated old fine menu is
  S = J° star P star J°.
The private word is literally obtained by concatenating the three
positive OLD typed word factors; intermediate named sorts may vary.

The exact old SAP positive profile composition theorem makes this
ONE genuine positive word have full J-diversity saturation as its
endpoint STRONG profile. The old nonzero-J RAW/STRONG sandwich
theorem and literal quotient relation give S = Φ(̅S), including
the TRUE quotient diagonal as diversity between distinct OLD points.

This is source C11 support, not an assumed first-hit consequence,
an invented positive STRONG identity, quotient SAP/CCO or an
abstract conditional quotient semigroup provider.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- The actual OLD positive typed atomic word J°;P;J°
with ALL its original interior letters and named sorts retained. -/
def originalJPositiveSaturationWord
    {i : ι} (wJ wP : PositiveWord S i i) :
    PositiveWord S i i :=
  PositiveWord.append S wJ (PositiveWord.append S wP wJ)

/-- The endpoint STRONG profile of this ONE real old word
is EXACTLY the labelled source's three-factor original
J-diversity saturation. No CCO, quotient/hidden SAP,
abstract product axiom or identity letter is used. -/
theorem originalJPositiveSaturationWord_profile
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (wJ wP : PositiveWord S i i) :
    PositiveWord.profile S (originalJPositiveSaturationWord S wJ wP) =
      S.product (PositiveWord.profile S wJ)
        (S.product (PositiveWord.profile S wP)
          (PositiveWord.profile S wJ)) := by
  change PositiveWord.profile S
      (PositiveWord.append S wJ (PositiveWord.append S wP wJ)) = _
  rw [PositiveWord.profile_append_of_SAP S H sap wJ
        (PositiveWord.append S wP wJ),
      PositiveWord.profile_append_of_SAP S H sap wP wJ]

/-- Concrete source07 C11 receiving bridge: if wJ truly presents
the original J° diversity palette, its concatenation around ANY
old positive same-sort word wP has STRONG profile equal to the
genuine full old-diversity pullback of a LITERAL quotient J-state.

This requires original SAP, J>Id, and a real positive wJ.
No FULL cover, MI, quotient SAP, CCO, Set-Pasch or terminality
is needed for the identity itself. -/
theorem originalJPositiveSaturationWord_quotient_profile
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (wJ wP : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J) :
    PositiveWord.profile S (originalJPositiveSaturationWord S wJ wP) =
      S.diversityGuard
        (quotientDiversity J.val
          (originalJMenuQuotientState S J
            (PositiveWord.profile S wP))) := by
  rw [originalJPositiveSaturationWord_profile S H sap wJ wP]
  simp only [hwJ]
  exact originalJMenuQuotientState_palette S H sap J hJ
    (PositiveWord.profile S wP)

end CCO.TransitionClosure
