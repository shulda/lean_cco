import CCO.Atomic
import CCO.QuotientTransport.Core

/-!
# B052 source10 C16: concrete two-sorted common-block old diagnostic

This builds an ACTUAL infinite original source with two real named
sorts, countably infinitely many common block labels, and infinitely
many different real points of EACH sort inside EVERY block.
Every fine typed pair colour records same-block/different-block;
only the literal same-sort real diagonal is the optional 'none'.
There is NO fabricated fine equality atom.

The cross-sort same-block RAW relation R has literal
R;Rᵒᵖ = E_A and Rᵒᵖ;R = E_B. Its true original block
quotient maps in the two directions are inverses.

The further source10 C16 obligations to prove the genuine
original age SAP and semantic CCO of this concrete full old
structure, and the resulting HN non-completion comparison, are
SEPARATE. They are not assumed or silently inferred from these
explicit old orbital and quotient calculations.
-/

namespace CCO.UnaryTermsReturn

/-- Literal independent real sort tag and block/clone coordinates.
The same Nat block label appears on BOTH named real sorts. -/
abbrev CommonBlockReal (_i : Bool) := ℕ × ℕ

/-- True ORIGINAL pair colouring: logical real equality is
none only at the same sort and the same actual real point.
Other pairs have colour true iff their block labels agree. -/
def commonBlockOldColour (i j : Bool)
    (x : CommonBlockReal i) (y : CommonBlockReal j) :
    Option Bool :=
  if (⟨i,x⟩ : Sigma CommonBlockReal) = ⟨j,y⟩ then none
  else some (decide (x.1 = y.1))

/-- Genuine two-real-sort binary atomic model, with true
same-sort diagonal and the four possible old typed diversity
block and non-block cases. Its carriers are INFINITE. -/
def commonBlockOriginalAtomicSource :
    AtomicSource Bool CommonBlockReal where
  Atom := fun _ _ => Bool
  finiteSort := inferInstance
  finiteAtom := fun _ _ => inferInstance
  nonemptySort := fun _ => ⟨(0,0)⟩
  conv := fun a => a
  conv_invol := by intro i j a; rfl
  symmetricLoop := by intro i a; rfl
  colour := fun {i j} x y => commonBlockOldColour i j x y
  colour_none_iff := by
    intro i j x y
    classical
    by_cases h : (⟨i,x⟩ : Sigma CommonBlockReal) = ⟨j,y⟩
    · simp [commonBlockOldColour,h]
    · simp [commonBlockOldColour,h]
  colour_swap := by
    intro i j x y a
    classical
    change commonBlockOldColour i j x y = some a ↔
      commonBlockOldColour j i y x = some a
    by_cases h : (⟨i,x⟩ : Sigma CommonBlockReal) = ⟨j,y⟩
    · have hr : (⟨j,y⟩ : Sigma CommonBlockReal) = ⟨i,x⟩ :=
        h.symm
      simp only [commonBlockOldColour, if_pos h, if_pos hr]
    · have hr : (⟨j,y⟩ : Sigma CommonBlockReal) ≠ ⟨i,x⟩ :=
        fun hz => h hz.symm
      simp only [commonBlockOldColour, if_neg h, if_neg hr,
        Option.some.injEq]
      have hs : decide (x.1 = y.1) = decide (y.1 = x.1) := by
        by_cases hxy : x.1 = y.1
        · simp [hxy, hxy.symm]
        · have hyx : y.1 ≠ x.1 := fun e => hxy e.symm
          simp [hxy, hyx]
      rw [hs]
  realized := by
    intro i j a
    cases a with
    | false =>
        refine ⟨(0,0),(1,0),?_⟩
        simp [commonBlockOldColour]
    | true =>
        by_cases hij : i = j
        · subst j
          refine ⟨(0,0),(0,1),?_⟩
          simp [commonBlockOldColour]
        · refine ⟨(0,0),(0,0),?_⟩
          simp [commonBlockOldColour,hij]

/-- Actual original same-block equivalence on a FIXED named
real sort, with its literal equality-containing relation. -/
def commonBlockOldSetoid (i : Bool) : Setoid (CommonBlockReal i) where
  r := fun x y => x.1 = y.1
  iseqv := ⟨fun _ => rfl,fun h => h.symm,fun h k => h.trans k⟩

/-- Actual mixed original A→B same-block typed RAW relation.
Its factor is nonempty, and has no tagged original real diagonal,
because source and target have DISTINCT sort tags. -/
def commonBlockMixedRaw :
    QuotientTransport.Rel (CommonBlockReal false) (CommonBlockReal true) :=
  fun x y => x.1 = y.1

/-- SOURCE10 mixed-block diagnostic: the literal equality-inclusive
R;Rᵒᵖ is the ACTUAL A same-block setoid. This uses a concrete
old B witness from the same block, rather than a quotient chart. -/
theorem commonBlockMixedReturnA
    (x y : CommonBlockReal false) :
    QuotientTransport.compose commonBlockMixedRaw
      (QuotientTransport.converse commonBlockMixedRaw) x y ↔
        (commonBlockOldSetoid false).r x y := by
  constructor
  · rintro ⟨z,hxz,hyz⟩
    exact hxz.trans hyz.symm
  · intro hxy
    exact ⟨(x.1,0),rfl,hxy.symm⟩

/-- Symmetric source10 mixed-block diagnostic on the B real
sort: Rᵒᵖ;R is exactly E_B, with a genuine A witness. -/
theorem commonBlockMixedReturnB
    (x y : CommonBlockReal true) :
    QuotientTransport.compose
      (QuotientTransport.converse commonBlockMixedRaw)
      commonBlockMixedRaw x y ↔
        (commonBlockOldSetoid true).r x y := by
  constructor
  · rintro ⟨z,hxz,hyz⟩
    exact hxz.symm.trans hyz
  · intro hxy
    exact ⟨(x.1,0),rfl,hxy⟩

/-- The literal actual original mixed quotient map A/E_A→B/E_B:
the underlying common block label determines the target class.
The quotient carriers have the same concrete block setoid while
their ORIGINAL named real sort tags remain distinct. -/
def commonBlockForward :
    Quotient (commonBlockOldSetoid false) →
      Quotient (commonBlockOldSetoid true) :=
  fun q => q

def commonBlockBackward :
    Quotient (commonBlockOldSetoid true) →
      Quotient (commonBlockOldSetoid false) :=
  fun q => q

/-- Every actual old cross-sort mixed RAW edge computes
the true target block quotient class, not a chosen section. -/
theorem commonBlockForward_edge
    (x : CommonBlockReal false)
    (y : CommonBlockReal true)
    (hxy : commonBlockMixedRaw x y) :
    commonBlockForward (Quotient.mk _ x) =
      Quotient.mk (commonBlockOldSetoid true) y :=
  Quotient.sound hxy

theorem commonBlockBackward_edge
    (x : CommonBlockReal true)
    (y : CommonBlockReal false)
    (hxy : commonBlockMixedRaw y x) :
    commonBlockBackward (Quotient.mk _ x) =
      Quotient.mk (commonBlockOldSetoid false) y :=
  Quotient.sound hxy.symm

/-- The genuine common-block named mixed transitions have
literal inverse return holonomy on original quotient classes,
despite traversing TWO different named real sorts. -/
theorem commonBlockMixedNamedReturnA
    (q : Quotient (commonBlockOldSetoid false)) :
    commonBlockBackward (commonBlockForward q) = q := rfl

theorem commonBlockMixedNamedReturnB
    (q : Quotient (commonBlockOldSetoid true)) :
    commonBlockForward (commonBlockBackward q) = q := rfl

end CCO.UnaryTermsReturn
