import CCO.APCharacter.Masks
import CCO.OwnerTransversal.CountableColourLanguage
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma

/-! Literal unary/binary codes for the actual marked finite age. Finite
alphabet codes live in Type, even when the original named sorts or atom
names live in higher universes. No realized old diagram is replaced by an
arbitrary complete colour assignment. -/
universe u v w z
namespace CCO.APCharacter.Age
open OwnerTransversal.CountableColour
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
noncomputable section

abbrev Colour := Σ i, Σ j, Option (S.Atom i j)
abbrev OwnerCode (_S : AtomicSource.{u,v,w} ι X) := Fin (Nat.card (ι × Bit))
abbrev ColourCode := Fin (Nat.card (Colour S))
def ownerEquiv : (ι × Bit) ≃ OwnerCode S := by
  letI := S.finiteSort
  letI := S.finiteAtom
  exact Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm)
def colourEquiv : Colour S ≃ ColourCode S := by
  letI := S.finiteSort
  letI := S.finiteAtom
  exact Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm)
abbrev Language := language (OwnerCode S) (ColourCode S)
abbrev Table (Y : Type z) := OwnerTransversal.CountableColour.Table (OwnerCode S) (ColourCode S) Y

def table {Y : Type z} (point : Y → Sigma X) (bits : Y → Bit) : Table S Y where
  owner x := ownerEquiv S ((point x).1,bits x)
  colour x y := colourEquiv S (taggedColour S (point x) (point y))

def Legal {Y : Type z} (M : MaskData S) (point : Y → Sigma X) (bits : Y → Bit) : Prop :=
  (∀ x, M.validBit (point x).1 (bits x)) ∧
    ∀ x y, M.allowed (S.colour (point x).2 (point y).2) (bits x) (bits y)

/-- Membership retains an ACTUAL injective old realization. In particular
triangle-consistent or locally legal arbitrary colour tables do not suffice. -/
def Realized {Y : Type z} (M : MaskData S) (T : Table S Y) : Prop :=
  ∃ (point : Y → Sigma X) (bits : Y → Bit), Function.Injective point ∧
    Legal S M point bits ∧ T = table S point bits

structure Chart (M : MaskData S) where
  size : ℕ
  table : Table S (Fin size)
  realized : Realized S M table

instance chartCountable (M : MaskData S) : Countable (Chart S M) := by
  let f : Chart S M → Σ n : ℕ, Table S (Fin n) := fun C => ⟨C.size,C.table⟩
  have hf : Function.Injective f := by
    rintro ⟨n,T,h⟩ ⟨m,U,k⟩ e
    cases e
    rfl
  exact hf.countable

@[instance_reducible] def Chart.structure {M : MaskData S} (C : Chart S M) :
    (Language S).Structure (Fin C.size) := C.table.toStructure

/-- Reindexing an actual marked diagram preserves its literal structure. -/
def reindex {Y : Type z} {Z : Type*} (T : Table S Y) (f : Z → Y) : Table S Z where
  owner z := T.owner (f z)
  colour z z' := T.colour (f z) (f z')

theorem realized_reindex {Y : Type z} {Z : Type*} {M : MaskData S}
    {T : Table S Y} (h : Realized S M T) (f : Z ↪ Y) :
    Realized S M (reindex S T f) := by
  obtain ⟨p,b,hp,hlegal,rfl⟩ := h
  exact ⟨p ∘ f,b ∘ f,hp.comp f.injective,
    ⟨fun x => hlegal.1 (f x),fun x y => hlegal.2 (f x) (f y)⟩,rfl⟩

/-- Every actual finite marked object has a canonical finite chart copy. -/
def chartOf {Y : Type} [Finite Y] {M : MaskData S} (T : Table S Y)
    (h : Realized S M T) : Chart S M := by
  letI := Fintype.ofFinite Y
  exact ⟨Fintype.card Y,reindex S T (Fintype.equivFin Y).symm,
    realized_reindex S h (Fintype.equivFin Y).symm.toEmbedding⟩

def chartOfEquiv {Y : Type} [Finite Y] {M : MaskData S} (T : Table S Y)
    (h : Realized S M T) :
    @FirstOrder.Language.Equiv (Language S) Y (Fin (chartOf S T h).size)
      T.toStructure (chartOf S T h).structure := by
  letI := Fintype.ofFinite Y
  exact T.equiv (chartOf S T h).table (Fintype.equivFin Y)
    (fun x => by
      change T.owner ((Fintype.equivFin Y).symm ((Fintype.equivFin Y) x)) = _
      simp)
    (fun x y => by
      change T.colour ((Fintype.equivFin Y).symm ((Fintype.equivFin Y) x))
        ((Fintype.equivFin Y).symm ((Fintype.equivFin Y) y)) = _
      simp)

end
end CCO.APCharacter.Age
