import CCO.OwnerTransversal.CountableAge

/-! A literal finite owner/colour signature for the generic countable-age
construction.  Unary and binary names are retained individually. -/

open scoped FirstOrder
open FirstOrder FirstOrder.Language

universe u v z z'
namespace CCO.OwnerTransversal.CountableColour

inductive Symbol (B : Type u) (C : Type v) : ℕ → Type (max u v)
  | owner : B → Symbol B C 1
  | colour : C → Symbol B C 2

def language (B : Type u) (C : Type v) : FirstOrder.Language.{0,max u v} where
  Functions _ := Empty
  Relations := Symbol B C

instance (B : Type u) (C : Type v) : (language B C).IsRelational := by
  intro n
  change IsEmpty Empty
  infer_instance

/-- Complete tables; equality and repeated owner labels are allowed. -/
structure Table (B : Type u) (C : Type v) (X : Type z) where
  owner : X → B
  colour : X → X → C

namespace Table
variable {B : Type u} {C : Type v} {X : Type z} {Y : Type z'}

@[instance_reducible]
def toStructure (T : Table B C X) : (language B C).Structure X where
  funMap f := Empty.elim f
  RelMap r x := match r with
    | .owner b => T.owner (x 0) = b
    | .colour c => T.colour (x 0) (x 1) = c

/-- Actual embeddings of the relational encoding preserve both literal tables. -/
theorem embedding_preserves (T : Table B C X) (U : Table B C Y)
    (f : @FirstOrder.Language.Embedding (language B C) X Y T.toStructure U.toStructure) :
    (∀ x, U.owner (f x) = T.owner x) ∧
      (∀ x y, U.colour (f x) (f y) = T.colour x y) := by
  let := T.toStructure
  let := U.toStructure
  constructor
  · intro x
    exact (f.map_rel (Symbol.owner (T.owner x)) (fun _ => x)).mpr rfl
  · intro x y
    exact (f.map_rel (Symbol.colour (T.colour x y)) (![x,y])).mpr rfl

/-- Conversely an injective owner/colour preserving map is a genuine
embedding of all the actual unary/binary relation symbols. -/
def embedding (T : Table B C X) (U : Table B C Y) (f : X ↪ Y)
    (ho : ∀ x, U.owner (f x) = T.owner x)
    (hc : ∀ x y, U.colour (f x) (f y) = T.colour x y) :
    @FirstOrder.Language.Embedding (language B C) X Y T.toStructure U.toStructure := by
  letI := T.toStructure
  letI := U.toStructure
  exact {
    toFun := f
    inj' := f.injective
    map_fun' F := Empty.elim F
    map_rel' := by
      intro n r x
      cases r with
      | owner b => exact (congrArg (· = b) (ho (x 0))).to_iff
      | colour c => exact (congrArg (· = c) (hc (x 0) (x 1))).to_iff }


@[simp] theorem embedding_apply (T : Table B C X) (U : Table B C Y) (f : X ↪ Y)
    (ho : ∀ x, U.owner (f x) = T.owner x)
    (hc : ∀ x y, U.colour (f x) (f y) = T.colour x y) (x : X) :
    T.embedding U f ho hc x = f x := rfl

end Table
end CCO.OwnerTransversal.CountableColour
