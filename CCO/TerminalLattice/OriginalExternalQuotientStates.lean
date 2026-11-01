import CCO.TerminalLattice.OriginalQuotientOWLIntersection
import CCO.TerminalLattice.OriginalQuotientPositiveHelly
import CCO.TerminalLattice.OriginalExternalWords

/-!
# B050 source09 OWL: finite family of EXACT complete external old-G orbitals

The quotient of an original real sort by J may be infinite, but the
set of ALL ORIGINAL-G-invariant binary quotient relations is finite.
We use its concrete previously proved finite type and take the
subtype consisting of precisely those COMPLETE original-G pair
orbitals represented by real pairs in K outside J.

This identifies external labels with complete quotient ORBITS,
rather than a separate or potentially enlarged quotient automorphism
group. Distinct external states are disjoint, every such state is
genuinely serial, and source C23 gives each state an ORIGINAL positive
typed old atomic word with its ENTIRE diversity pullback as profile.

The subtype stores only real source evidence, not an extra
source-exactness or reset assumption. It includes the non-index-two
case and index-two case without conflating the true quotient diagonal
with the old identity relation.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- The actual COMPLETE external quotient pair-orbit states in K/J
under the ORIGINAL ambient G-action, with explicit old-real-pair
representatives. Their carrier is finite even when K/J is infinite. -/
def OriginalExternalQuotientState
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) :=
  {R : OriginalInvariantQuotientState S H J //
    ∃ a b : X i, K a b ∧ ¬ J a b ∧
      R.val = originalQuotientOrbital S (G := G) J a b}

/-- Source OWL finite external family: subtype of an ALREADY PROVED
finite complete old-G invariant quotient state type. No new finiteness
axiom, no assumption the J quotient carrier itself is finite. -/
noncomputable instance originalExternalQuotientState_finite
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) :
    Finite (OriginalExternalQuotientState S H J K) := by
  letI : Finite (OriginalInvariantQuotientState S H J) :=
    originalInvariantQuotientState_finite S H J
  infer_instance

/-- One ACTUAL old-real K-external pair gives one member of the exact
finite complete quotient-orbital family. This is not a proper fine
suborbit or a quotient-reduct orbit. -/
def originalExternalQuotientState_of_pair
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i)
    (a b : X i) (hKab : K a b) (hNotJab : ¬ J a b) :
    OriginalExternalQuotientState S H J K :=
  ⟨⟨originalQuotientOrbital S (G := G) J a b,
     originalQuotientOrbital_invariant S H J a b⟩,
    ⟨a,b,hKab,hNotJab,rfl⟩⟩

/-- Every chosen external complete quotient orbital has an actual
root pair, hence is a genuinely NONEMPTY original invariant binary
relation and is serial by original sort-transitivity. -/
theorem originalExternalQuotientState_serial
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i)
    (R : OriginalExternalQuotientState S H J K) :
    ∀ q : Quotient J.val, ∃ r : Quotient J.val, R.val.val q r := by
  obtain ⟨a,b,_,_,hEq⟩ := R.property
  have hNonempty : ∃ q r : Quotient J.val, R.val.val q r := by
    refine ⟨Quotient.mk J.val a,Quotient.mk J.val b,?_⟩
    rw [hEq]
    exact originalQuotientOrbital_root S (G := G) J a b
  exact originalInvariantQuotientState_serial S H J R.val hNonempty

/-- SOURCE C23 instantiated at an arbitrary member of the finite
complete external quotient-orbit family: its ENTIRE quotient
diversity pullback is the STRONG endpoint profile of ONE positive
ORIGINAL typed word. Positivity of J° is the only word input;
positivity of K°, CCO, NR2, quotient SAP, B049 and index≠2
are NOT assumed. The word may traverse other old named sorts. -/
theorem originalExternalQuotientState_positive
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J K : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (R : OriginalExternalQuotientState S H J K) :
    OriginalPositiveQuotientState S J R.val.val := by
  obtain ⟨a,b,_,hNotJ,hEq⟩ := R.property
  have hNe : a ≠ b := by
    intro hh
    subst b
    exact hNotJ (J.val.refl a)
  have hTag : (⟨i,a⟩ : Sigma X) ≠ ⟨i,b⟩ := by
    intro hh
    have hab : a = b := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hh
    exact hNe hab
  obtain ⟨c,hCol⟩ := S.some_colour_of_ne a b hTag
  obtain ⟨word,hWord⟩ :=
    originalQuotientOrbital_positive_word
      S H sap J hJ wJ hwJ c a b hCol
  refine ⟨word, ?_⟩
  calc
    S.menuRel (PositiveWord.profile S word) =
        S.menuRel
          (originalQuotientOrbitalPalette S (G := G) J a b) := by
      rw [hWord]
    _ = quotientDiversity J.val
          (originalQuotientOrbital S (G := G) J a b) :=
      originalQuotientOrbitalPalette_semantics S H J a b
    _ = quotientDiversity J.val R.val.val := by rw [hEq]

/-- Two complete external old-G pair orbitals that meet at even
ONE actual quotient pair coincide as elements of the finite state
type. Distinct subtype states are therefore truly disjoint,
including any possible quotient-diagonal overlap (which in fact
cannot occur for external states). -/
theorem originalExternalQuotientState_eq_of_overlap
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i)
    (R T : OriginalExternalQuotientState S H J K)
    (q r : Quotient J.val)
    (hR : R.val.val q r) (hT : T.val.val q r) :
    R = T := by
  obtain ⟨a,b,_,_,hREq⟩ := R.property
  obtain ⟨c,d,_,_,hTEq⟩ := T.property
  have hOrbEq := originalQuotientOrbital_eq_of_overlap
    S H J a b c d q r (by rwa [← hREq]) (by rwa [← hTEq])
  apply Subtype.ext
  apply Subtype.ext
  exact hREq.trans (hOrbEq.trans hTEq.symm)

end CCO.TerminalLattice
