import CCO.FullPhaseLift.Canonical.FirstOrder
import CCO.APCharacter.Masks

/-! A genuine finite unary expansion of the ONE normalized old full
signature. Every old arity and tuple, including nullaries, is retained. -/
universe v w
namespace CCO.FullPhaseLift.Marked
open Canonical

/-- One new unary predicate; old symbols keep their arities literally. -/
abbrev addBit (L : Signature) : Signature where
  size := L.size+1
  arity := Fin.cases 1 L.arity

abbrev bitBool (b : APCharacter.Bit) : Bool := decide (b = 1)

theorem bitBool_injective : Function.Injective bitBool := by decide

abbrev boolBit (b : Bool) : APCharacter.Bit := if b then 1 else 0

@[simp] theorem boolBit_bitBool (b : APCharacter.Bit) : boolBit (bitBool b) = b := by
  revert b
  decide

@[simp] theorem bitBool_boolBit (b : Bool) : bitBool (boolBit b) = b := by
  cases b <;> decide

/-- The new bit predicate records only one unary truth value, while ALL
old tuple truths are the original table entries. -/
def table {L : Signature} {V : Type v} (T : BoolTable L V)
    (bits : V → APCharacter.Bit) : BoolTable (addBit L) V :=
  Fin.cases (fun xs => bitBool (bits (xs (0 : Fin 1)))) (fun r xs => T r xs)

@[simp] theorem table_old {L : Signature} {V : Type v} (T : BoolTable L V)
    (bits : V → APCharacter.Bit) (r : Fin L.size) (xs : Fin (L.arity r) → V) :
    table T bits r.succ xs = T r xs := rfl

@[simp] theorem table_bit {L : Signature} {V : Type v} (T : BoolTable L V)
    (bits : V → APCharacter.Bit) (x : V) :
    table T bits 0 (fun _ => x) = bitBool (bits x) := rfl

def oldTable {L : Signature} {V : Type v} (T : BoolTable (addBit L) V) : BoolTable L V :=
  fun r xs => T r.succ xs

def bits {L : Signature} {V : Type v} (T : BoolTable (addBit L) V) (x : V) : APCharacter.Bit :=
  boolBit (T 0 (fun _ => x))

@[simp] theorem oldTable_table {L : Signature} {V : Type v} (T : BoolTable L V)
    (b : V → APCharacter.Bit) : oldTable (table T b) = T := rfl

@[simp] theorem bits_table {L : Signature} {V : Type v} (T : BoolTable L V)
    (b : V → APCharacter.Bit) : bits (table T b) = b := by
  funext x
  exact boolBit_bitBool _

/-- Every complete expanded table is exactly its old table and its unary
bits. In particular no extra relation is introduced by decoding a limit. -/
@[simp] theorem table_oldTable_bits {L : Signature} {V : Type v}
    (T : BoolTable (addBit L) V) : table (oldTable T) (bits T) = T := by
  funext r
  refine Fin.cases ?_ (fun _ => rfl) r
  funext xs
  change bitBool (boolBit (T 0 (fun _ => xs (0 : Fin 1)))) = T 0 xs
  rw [bitBool_boolBit]
  congr 1
  funext j
  exact congrArg xs (Subsingleton.elim (0 : Fin 1) (show Fin 1 from j))

/-- Forgetting one unary bit keeps the SAME point map and every old tuple. -/
def oldEmbedding {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W}
    {a : V → APCharacter.Bit} {b : W → APCharacter.Bit}
    (f : Embedding (table A a) (table B b)) : Embedding A B :=
  embeddingOf f.point f.injective (fun r xs => embedding_read f r.succ xs)

theorem embedding_bits {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W}
    {a : V → APCharacter.Bit} {b : W → APCharacter.Bit}
    (f : Embedding (table A a) (table B b)) (x : V) : b (f.point x) = a x := by
  apply bitBool_injective
  exact embedding_read f 0 (fun _ => x)

/-- An old FULL embedding lifts precisely when it retains the endpoint
bits; no binary replacement of any higher old relation occurs. -/
def embedding {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W}
    {a : V → APCharacter.Bit} {b : W → APCharacter.Bit}
    (f : Embedding A B) (hb : ∀ x, b (f.point x) = a x) :
    Embedding (table A a) (table B b) := by
  refine embeddingOf f.point f.injective ?_
  intro r
  refine Fin.cases ?_ (fun s => ?_) r
  · intro xs
    change bitBool (b (f.point (xs (0 : Fin 1)))) = bitBool (a (xs (0 : Fin 1)))
    rw [hb]
  · intro xs
    exact embedding_read f s xs

@[simp] theorem oldEmbedding_embedding {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W}
    {a : V → APCharacter.Bit} {b : W → APCharacter.Bit}
    (f : Embedding A B) (hb : ∀ x, b (f.point x) = a x) :
    oldEmbedding (embedding f hb) = f := by
  cases f
  rfl

end CCO.FullPhaseLift.Marked
