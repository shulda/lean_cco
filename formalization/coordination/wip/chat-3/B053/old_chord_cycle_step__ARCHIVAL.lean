import CCO.TypedOrbitFrames.OldTupleSAP
import CCO.TypedOrbitFrames.ChordSplitSideReading

/-!
# B053 C04: old-SAP one-step realization of the original n-cycle

Two genuine shorter cycle realizations provide finite old-valued
tuples on the two proper subcycle arcs, INCLUDING the actual
specified diversity chord (as their opposite closing edges).
Their two chord readings have the SAME actual old typed atom.
Original old SAP and original two-point homogeneity amalgamate
their ACTUAL finite induced images, not their abstract cycle
indices, into one genuine finite original member. Both chord
endpoints agree there and ALL original old pair colours in each
shorter realization are preserved.

The proved finite-index arc cover and edge cover then assemble
one total map on the original n positions which preserves EVERY
old specified cyclic side with its EXACT typed atomic colour.

This is the complete well-founded INDUCTIVE STEP for a normalized
proper chord at 0,k, with no hidden SAP/CCO. It does not assume
a homomorphism of the long cycle as a premise. The remaining
source11 C04 obligations are to construct the exact shorter
cycle data from an arbitrary long original SimpleCycle, rotate
an arbitrary nonconsecutive chord to 0,k, and combine with
the genuine chordless base cases. Until then it is NOT the full
C04 cycle-realizability theorem or the CCO application.
-/

namespace CCO.TypedOrbitFrames

universe u v w t
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- One true original-age strong-amalgamation step taking TWO
realizations of shorter specified cycles, with their literal
oppositely directed closing chord, into a single realization
of ALL old sides of the longer cycle. No source realisation
of the longer cycle or homomorphism of an arbitrary partial
terminal hidden diagram is assumed. -/
theorem original_normalized_chord_old_sap_cycle_step
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {n k : Nat} (cut : OriginalChordCut n k)
    (left : Fin (k + 1) → Sigma X)
    (right : Fin (n - k + 1) → Sigma X)
    (readSide : Fin n → (Σ i : ι, Σ j : ι, Option (S.Atom i j)))
    {i j : ι} (a : S.Atom i j)
    (x x' : X i) (y y' : X j)
    (hxy : S.colour x y = some a)
    (hx'y' : S.colour x' y' = some a)
    (hLeftK : left ⟨k, by omega⟩ = (⟨i,x⟩ : Sigma X))
    (hLeft0 : left ⟨0, by omega⟩ = (⟨j,y⟩ : Sigma X))
    (hRightK : right ⟨0, by omega⟩ = (⟨i,x'⟩ : Sigma X))
    (hRight0 : right ⟨n - k, by omega⟩ = (⟨j,y'⟩ : Sigma X))
    (hLeftSide : ∀ a b : Fin (k + 1), a.val + 1 = b.val →
      taggedColour S (left a) (left b) =
        readSide (originalChordLeftIndex cut a))
    (hRightSide : ∀ a b : Fin (n - k + 1), a.val + 1 = b.val →
      taggedColour S (right a) (right b) =
        readSide (originalChordRightIndex cut a)) :
    ∃ (M : FiniteInduced (X := X))
      (whole : Fin n → Sigma X),
      (∀ i, whole i ∈ M.vertices) ∧
      (∀ i : Fin n,
        taggedColour S (whole i)
          (whole (CCO.cyclicNext (by omega : 0 < n) i)) =
            readSide i) := by
  obtain ⟨M,fl,gr,hMemL,hMemR,hColL,hColR,hK,h0⟩ :=
    original_old_tuples_same_chord_sap
      S H sap left right a x x' y y' hxy hx'y'
      ⟨k, by omega⟩ ⟨0, by omega⟩
      ⟨0, by omega⟩ ⟨n - k, by omega⟩
      hLeftK hLeft0 hRightK hRight0
  refine ⟨M, originalChordGlue cut fl gr, ?_, ?_⟩
  · intro v
    rcases original_chord_arc_cover cut v with
      ⟨b,hb⟩ | ⟨b,hb⟩
    · rw [← hb, original_chord_glue_left]
      exact hMemL b
    · rw [← hb, original_chord_glue_right cut fl gr hK h0]
      exact hMemR b
  · apply original_chord_glue_preserves_all_old_cycle_sides
      S cut fl gr readSide hK h0
    · intro b c hbc
      calc
        taggedColour S (fl b) (fl c) =
            taggedColour S (left b) (left c) := hColL b c
        _ = readSide (originalChordLeftIndex cut b) :=
          hLeftSide b c hbc
    · intro b c hbc
      calc
        taggedColour S (gr b) (gr c) =
            taggedColour S (right b) (right c) := hColR b c
        _ = readSide (originalChordRightIndex cut b) :=
          hRightSide b c hbc

end CCO.TypedOrbitFrames
