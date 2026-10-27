import CCO.BasePaths
import CCO.Finite

/-!
# The base-path consumer under *factorwise* induced embeddings

The left and right factors have independent induced embeddings: NO
colour preservation is assumed for the cross-root pair. Both embeddings
send the displayed base vertices to the SAME designated target base,
and the base index map is onto that entire target base. Additional
vertices outside that target base are permitted. These are precisely
the conditions under which source-literal two-step STRONG menus agree.
-/

universe u v w z t

namespace CCO.AtomicSource

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource ι X)
variable {i j : ι}

/-- If the two *actual* incident atomic pair colours agree, including
their sort tags, then the resulting typed two-step constraints agree.
Logical equality never enters because both inputs are diversity atoms. -/
theorem twoStep_eq_of_tagged_atoms
    {k l : ι}
    (a : S.Atom i k) (b : S.Atom k j)
    (a' : S.Atom i l) (b' : S.Atom l j)
    (hLeft : (⟨i, ⟨k, some a⟩⟩ :
        Σ p : ι, Σ q : ι, Option (S.Atom p q)) =
        ⟨i, ⟨l, some a'⟩⟩)
    (hRight : (⟨k, ⟨j, some b⟩⟩ :
        Σ p : ι, Σ q : ι, Option (S.Atom p q)) =
        ⟨l, ⟨j, some b'⟩⟩) :
    (⟨k, (a, b)⟩ : S.TwoStep i j) = ⟨l, (a', b')⟩ := by
  have hkl : k = l :=
    congrArg (fun p : Σ m : ι, Σ n : ι, Option (S.Atom m n) => p.2.1) hLeft
  cases hkl
  have ha : a = a' := by
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and,
      Option.some.injEq] using hLeft
  have hb : b = b' := by
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and,
      Option.some.injEq] using hRight
  cases ha
  cases hb
  rfl

/-- Factorwise finite induced embeddings preserving the *whole* base.
The source/target factor structures may also contain many additional
vertices. The two factors are NOT assumed to be a single induced
embedding, so the cross-root colour need not be preserved. -/
structure FactorSpanEmbedding
    {C : Type z} {D : Type t}
    (A : S.ActualSpan (i := i) (j := j) C)
    (B : S.ActualSpan (i := i) (j := j) D)
    (LeftSrc RightSrc LeftDst RightDst : FiniteInduced (X := X)) where
  leftEmbedding : InducedEmbedding S LeftSrc LeftDst
  rightEmbedding : InducedEmbedding S RightSrc RightDst
  baseMap : C → D
  baseOnto : Function.Surjective baseMap
  leftRootIn : (⟨i, A.left⟩ : Sigma X) ∈ LeftSrc.vertices
  rightRootIn : (⟨j, A.right⟩ : Sigma X) ∈ RightSrc.vertices
  leftBaseIn : ∀ c, (⟨A.baseSort c, A.point c⟩ : Sigma X) ∈ LeftSrc.vertices
  rightBaseIn : ∀ c, (⟨A.baseSort c, A.point c⟩ : Sigma X) ∈ RightSrc.vertices
  leftRootImage :
    (leftEmbedding.toEmbedding ⟨⟨i, A.left⟩, leftRootIn⟩).val =
      (⟨i, B.left⟩ : Sigma X)
  rightRootImage :
    (rightEmbedding.toEmbedding ⟨⟨j, A.right⟩, rightRootIn⟩).val =
      (⟨j, B.right⟩ : Sigma X)
  leftBaseImage : ∀ c,
    (leftEmbedding.toEmbedding
      ⟨⟨A.baseSort c, A.point c⟩, leftBaseIn c⟩).val =
      (⟨B.baseSort (baseMap c), B.point (baseMap c)⟩ : Sigma X)
  rightBaseImage : ∀ c,
    (rightEmbedding.toEmbedding
      ⟨⟨A.baseSort c, A.point c⟩, rightBaseIn c⟩).val =
      (⟨B.baseSort (baseMap c), B.point (baseMap c)⟩ : Sigma X)

namespace FactorSpanEmbedding

variable {S} {C : Type z} {D : Type t}
variable {A : S.ActualSpan (i := i) (j := j) C}
variable {B : S.ActualSpan (i := i) (j := j) D}
variable {LeftSrc RightSrc LeftDst RightDst : FiniteInduced (X := X)}
variable (F : S.FactorSpanEmbedding A B LeftSrc RightSrc LeftDst RightDst)

theorem preservesOldEdges (c : C) :
    A.edges c = B.edges (F.baseMap c) := by
  have hLeft := F.leftEmbedding.preserves_colours
    (⟨⟨i, A.left⟩, F.leftRootIn⟩ : ↥LeftSrc.vertices)
    (⟨⟨A.baseSort c, A.point c⟩, F.leftBaseIn c⟩ : ↥LeftSrc.vertices)
  have hRight := F.rightEmbedding.preserves_colours
    (⟨⟨A.baseSort c, A.point c⟩, F.rightBaseIn c⟩ : ↥RightSrc.vertices)
    (⟨⟨j, A.right⟩, F.rightRootIn⟩ : ↥RightSrc.vertices)
  rw [F.leftRootImage, F.leftBaseImage c] at hLeft
  rw [F.rightBaseImage c, F.rightRootImage] at hRight
  have hLeftAtoms :
      (⟨i, ⟨A.baseSort c, some (A.leftAtom c)⟩⟩ :
        Σ p : ι, Σ q : ι, Option (S.Atom p q)) =
      ⟨i, ⟨B.baseSort (F.baseMap c), some (B.leftAtom (F.baseMap c))⟩⟩ := by
    simpa only [taggedColour, A.leftColour c,
      B.leftColour (F.baseMap c)] using hLeft
  have hRightAtoms :
      (⟨A.baseSort c, ⟨j, some (A.rightAtom c)⟩⟩ :
        Σ p : ι, Σ q : ι, Option (S.Atom p q)) =
      ⟨B.baseSort (F.baseMap c),
        ⟨j, some (B.rightAtom (F.baseMap c))⟩⟩ := by
    simpa only [taggedColour, A.rightColour c,
      B.rightColour (F.baseMap c)] using hRight
  exact S.twoStep_eq_of_tagged_atoms (A.leftAtom c) (A.rightAtom c)
    (B.leftAtom (F.baseMap c)) (B.rightAtom (F.baseMap c))
    hLeftAtoms hRightAtoms

/-- Natural base-path domain equality under induced embeddings of BOTH
factors, provided their common-base map is onto the exact target base.
No assertion about the cross-root atom or about SIR is made. -/
theorem menu_preserved :
    A.menu = B.menu := by
  exact S.menu_preserved A B
    { baseMap := F.baseMap
      baseOnto := F.baseOnto
      preservesOldEdges := F.preservesOldEdges }

end FactorSpanEmbedding
end CCO.AtomicSource
