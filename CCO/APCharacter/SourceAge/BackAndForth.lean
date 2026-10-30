import CCO.OwnerTransversal.CountableColourLanguage
import CCO.OwnerTransversal.PacketBackAndForth
import Mathlib.Data.Fintype.EquivFin

/-! Actual countable back-and-forth for literal complete owner/colour tables.
Both finite extension properties are structural SUPPORT: applications must
prove them from the actual source/age. No isomorphism or whole homogeneity
oracle is supplied. Finite and empty carriers and distinct universes work. -/
open scoped FirstOrder
open FirstOrder FirstOrder.Language
universe u v w z
namespace CCO.APCharacter.SourceAge
open CCO.OwnerTransversal.CountableColour

variable {B : Type u} {C : Type v} {Y : Type w} {Z : Type z}

/-- Every finite owner/colour embedding extends over every finite larger
actual source tuple. The two displayed tuples are injective; n=0 is allowed. -/
def FiniteExtension (T : Table B C Y) (U : Table B C Z) : Prop :=
  ∀ (n m : ℕ) (j : Fin n ↪ Fin m) (p : Fin m ↪ Y) (q : Fin n ↪ Z),
    (∀ x, U.owner (q x) = T.owner (p (j x))) ∧
      (∀ x y, U.colour (q x) (q y) = T.colour (p (j x)) (p (j y))) →
    ∃ r : Fin m ↪ Z, (∀ x, U.owner (r x) = T.owner (p x)) ∧
      (∀ x y, U.colour (r x) (r y) = T.colour (p x) (p y)) ∧
      ∀ x, r (j x) = q x

/-- Restriction is a literal induced table, including its diagonal colours. -/
def restrict (T : Table B C Y) (A : Set Y) : Table B C A where
  owner x := T.owner x.val
  colour x y := T.colour x.val y.val

/-- Fin enumerations convert the explicit table extension into actual
first-order finite-full-substructure extension; no new existence is assumed. -/
theorem finiteExtension_firstOrder (T : Table B C Y) (U : Table B C Z)
    (h : FiniteExtension T U) :
    letI := T.toStructure
    letI := U.toStructure
    OwnerTransversal.PacketBackAndForth.FiniteExtension (language B C) Y Z := by
  classical
  letI := T.toStructure
  letI := U.toStructure
  intro A D _ _ hAD f
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype D := Fintype.ofFinite D
  let a := Fintype.equivFin A
  let b := Fintype.equivFin D
  let inc : A ↪ D := ⟨fun x => ⟨x.val,hAD x.property⟩,by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun d : D => d.val) he⟩
  let j : Fin (Fintype.card A) ↪ Fin (Fintype.card D) :=
    a.symm.toEmbedding.trans (inc.trans b.toEmbedding)
  let p : Fin (Fintype.card D) ↪ Y := b.symm.toEmbedding.trans D.subtype.toEmbedding
  let q : Fin (Fintype.card A) ↪ Z := a.symm.toEmbedding.trans f.toEmbedding
  have hp (x : Fin (Fintype.card A)) : p (j x) = (a.symm x).val := by
    change (b.symm (b (inc (a.symm x)))).val = (a.symm x).val
    rw [b.symm_apply_apply]
    rfl
  have hfo (x : A) : U.owner (f x) = T.owner x.val :=
    (f.map_rel (Symbol.owner (T.owner x.val)) (fun _ => x)).mpr rfl
  have hfc (x y : A) : U.colour (f x) (f y) = T.colour x.val y.val :=
    (f.map_rel (Symbol.colour (T.colour x.val y.val)) (![x,y])).mpr rfl
  obtain ⟨r,ho,hc,hr⟩ := h _ _ j p q ⟨by
    intro x
    rw [hp]
    exact hfo (a.symm x),by
    intro x y
    rw [hp,hp]
    exact hfc (a.symm x) (a.symm y)⟩
  let rr : D ↪ Z := b.toEmbedding.trans r
  have hro (x : D) : U.owner (rr x) = T.owner x.val := by
    change U.owner (r (b x)) = T.owner x.val
    have he := ho (b x)
    change U.owner (r (b x)) = T.owner (b.symm (b x)).val at he
    simpa only [b.symm_apply_apply] using he
  have hrc (x y : D) : U.colour (rr x) (rr y) = T.colour x.val y.val := by
    change U.colour (r (b x)) (r (b y)) = T.colour x.val y.val
    have he := hc (b x) (b y)
    change U.colour (r (b x)) (r (b y)) = T.colour (b.symm (b x)).val (b.symm (b y)).val at he
    simpa only [b.symm_apply_apply] using he
  let g : D ↪[language B C] Z := {
    toFun := rr
    inj' := rr.injective
    map_fun' F := Empty.elim F
    map_rel' := by
      intro n R xs
      cases R with
      | owner b =>
        change (U.owner (rr (xs 0)) = b) ↔ T.owner (xs 0).val = b
        rw [hro]
      | colour c =>
        change (U.colour (rr (xs 0)) (rr (xs 1)) = c) ↔ T.colour (xs 0).val (xs 1).val = c
        rw [hrc] }
  refine ⟨g,?_⟩
  ext x
  have he := hr (a x)
  have hj : j (a x) = b (inc x) := by
    change b (inc (a.symm (a x))) = b (inc x)
    rw [a.symm_apply_apply]
  rw [hj] at he
  change r (b (inc x)) = f (a.symm (a x)) at he
  change r (b (inc x)) = f x
  simpa only [a.symm_apply_apply] using he

/-- The concrete finite table extension properties imply the actual
first-order back-and-forth extension pair in the indicated direction. -/
theorem isExtensionPair_of_finiteExtension (T : Table B C Y) (U : Table B C Z)
    (h : FiniteExtension T U) :
    letI := T.toStructure
    letI := U.toStructure
    (language B C).IsExtensionPair Y Z := by
  letI := T.toStructure
  letI := U.toStructure
  apply OwnerTransversal.PacketBackAndForth.isExtensionPair_of_finiteExtension
  · intro A hA
    exact hA.finite
  · exact finiteExtension_firstOrder T U h

/-- Genuine global bijection from finite extensions in BOTH directions.
All owner names and all ordered colours, including equality/diagonals,
are preserved literally. Neither infinity nor inhabitance is assumed. -/
theorem equiv_of_finiteExtension [Countable Y] [Countable Z]
    (T : Table B C Y) (U : Table B C Z)
    (forth : FiniteExtension T U) (back : FiniteExtension U T) :
    ∃ e : Y ≃ Z, (∀ x, U.owner (e x) = T.owner x) ∧
      ∀ x y, U.colour (e x) (e y) = T.colour x y := by
  letI := T.toStructure
  letI := U.toStructure
  letI : IsEmpty ((language B C).Relations 0) := ⟨fun r => nomatch r⟩
  let p : (language B C).FGEquiv Y Z := default
  obtain ⟨e,_⟩ := equiv_between_cg
    (Structure.cg_of_countable (L := language B C) (M := Y))
    (Structure.cg_of_countable (L := language B C) (M := Z)) p
    (isExtensionPair_of_finiteExtension T U forth)
    (isExtensionPair_of_finiteExtension U T back)
  have hp := Table.embedding_preserves T U e.toEmbedding
  exact ⟨e.toEquiv,hp.1,hp.2⟩

end CCO.APCharacter.SourceAge
