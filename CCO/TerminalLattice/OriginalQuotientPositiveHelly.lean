import CCO.TerminalLattice.OriginalStrongWordHelly
import CCO.TerminalLattice.FibreSAP
import CCO.TerminalLattice.StrongPaletteBridge
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Basic

/-!
# B050 source09 OWL: positive quotient states retain the actual old STRONG Helly

The source finite-escape procedure uses ORIGINAL-G-invariant quotient states,
which may include the TRUE J-quotient diagonal and need not be complete
orbitals. We encode old positivity by an ACTUAL positive original typed
atomic word whose STRONG endpoint menu is exactly the diversity pullback
of the entire quotient relation (including its quotient diagonal).

Positive old-word concatenation and the genuinely proved original SAP
quotient STRONG semigroup show this class is closed under quotient
composition. For an arbitrary finite indexed family of such quotient
states, nonempty pairwise intersections force a nonempty common
quotient intersection: choose different original representatives of
each pair of J-classes via original SAP, use their genuine old fine
atomic colour, invoke the already proved OLD positive STRONG word
Helly, and then return to the quotient.

No quotient-reduct action, quotient-level SAP/CCO, assumed Helly
provider, complete-orbital restriction, or discarded diagonal state.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- ONE genuine positive ORIGINAL typed word gives the ENTIRE quotient
relation state via its true OLD STRONG endpoint menu. Distinct OLD
real endpoints may project to the SAME quotient J-class, so
the quotient diagonal is deliberately retained. -/
def OriginalPositiveQuotientState {i : ι} (J : ColourEq S i)
    (R : Quotient J.val → Quotient J.val → Prop) : Prop :=
  ∃ word : PositiveWord S i i,
    S.menuRel (PositiveWord.profile S word) =
      quotientDiversity J.val R

/-- Source09 OWL state closure: positive old typed words representing
TWO arbitrary quotient states concatenate to represent their TRUE
quotient relational product. The old three-distinct-vertex STRONG
composition agrees with the quotient product by source-derived SAP
freshness. In particular this includes possible quotient diagonal
returns and does not silently replace them by OLD identity. -/
theorem original_positive_quotient_state_comp
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (R T : Quotient J.val → Quotient J.val → Prop)
    (hR : OriginalPositiveQuotientState S J R)
    (hT : OriginalPositiveQuotientState S J T) :
    OriginalPositiveQuotientState S J (RawSymmetric.compose R T) := by
  obtain ⟨wordR,hWordR⟩ := hR
  obtain ⟨wordT,hWordT⟩ := hT
  refine ⟨PositiveWord.append S wordR wordT, ?_⟩
  calc
    S.menuRel (PositiveWord.profile S (PositiveWord.append S wordR wordT)) =
        S.menuRel (S.product
          (PositiveWord.profile S wordR) (PositiveWord.profile S wordT)) := by
            rw [PositiveWord.profile_append_of_SAP S H sap]
    _ = strongCompose
          (S.menuRel (PositiveWord.profile S wordR))
          (S.menuRel (PositiveWord.profile S wordT)) :=
      menuRel_product_eq_strongCompose S H _ _
    _ = strongCompose (quotientDiversity J.val R)
          (quotientDiversity J.val T) := by rw [hWordR,hWordT]
    _ = quotientDiversity J.val (RawSymmetric.compose R T) :=
      original_quotient_semigroup S H sap J hJ R T

/-- SOURCE OWL finite escape: arbitrary FINITE states, all
representable by genuine original positive word profiles, have
a nonempty COMMON quotient pair whenever each two states
intersect. This explicitly permits a quotient-diagonal common
pair or quotient-diagonal portions of the input states.

The proof lifts each pairwise quotient witness to DISTINCT real
old points by actual original SAP, so the strong word profiles
share a real fine diversity colour. The old WordHelly theorem
then gives a single fine colour valid for every word; its actual
realization projects to the common quotient pair.
-/
theorem original_positive_quotient_states_finite_helly
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    {n : Nat}
    (states : Fin n → Quotient J.val → Quotient J.val → Prop)
    (words : Fin n → PositiveWord S i i)
    (hWords : ∀ k : Fin n,
      S.menuRel (PositiveWord.profile S (words k)) =
        quotientDiversity J.val (states k))
    (hPair : ∀ k l : Fin n,
      ∃ q r : Quotient J.val, states k q r ∧ states l q r) :
    ∃ q r : Quotient J.val, ∀ k : Fin n, states k q r := by
  classical
  have hOldPair :
      ∀ p ∈ List.ofFn words, ∀ q ∈ List.ofFn words,
        (PositiveWord.profile S p ∩
          PositiveWord.profile S q).Nonempty := by
    intro p hp q hq
    obtain ⟨k,rfl⟩ := (List.mem_ofFn' words p).mp hp
    obtain ⟨l,rfl⟩ := (List.mem_ofFn' words q).mp hq
    obtain ⟨u,v,hku,hlv⟩ := hPair k l
    induction u using Quotient.inductionOn with
    | _ x =>
      obtain ⟨y,hyNot,hyClass⟩ :=
        (freshFibre_of_original_SAP S H sap J hJ)
          v ({x} : Finset (X i))
      have hxy : x ≠ y := by
        intro heq
        apply hyNot
        simp [← heq]
      have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
        intro heq
        have hh : x = y := by
          simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using heq
        exact hxy hh
      obtain ⟨c,hCol⟩ := S.some_colour_of_ne x y hTag
      have hFine (a : Fin n)
          (hqa : states a (Quotient.mk J.val x) v) :
          c ∈ PositiveWord.profile S (words a) := by
        have hRel : quotientDiversity J.val (states a) x y := by
          refine ⟨hxy, ?_⟩
          simpa only [hyClass] using hqa
        have hMenu :
            S.menuRel (PositiveWord.profile S (words a)) x y := by
          rw [hWords a]
          exact hRel
        obtain ⟨d,hd,hDcol⟩ := hMenu
        have hdc : d = c := Option.some.inj (hDcol.symm.trans hCol)
        simpa only [hdc] using hd
      exact ⟨c, hFine k hku, hFine l hlv⟩
  obtain ⟨c,hcAll⟩ :=
    original_positive_profiles_helly_of_SAP_CCO
      S H sap cco (List.ofFn words) hOldPair
  obtain ⟨x,y,hCol⟩ := S.realized c
  refine ⟨Quotient.mk J.val x, Quotient.mk J.val y, ?_⟩
  intro k
  have hc : c ∈ PositiveWord.profile S (words k) :=
    hcAll (words k) ((List.mem_ofFn' words (words k)).mpr ⟨k,rfl⟩)
  have hMenu : S.menuRel (PositiveWord.profile S (words k)) x y :=
    ⟨c,hc,hCol⟩
  rw [hWords k] at hMenu
  exact hMenu.2

end CCO.TerminalLattice
