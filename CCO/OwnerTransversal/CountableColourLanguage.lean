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

instance {B : Type u} {C : Type v} {X : Type z}
    [Finite B] [Finite C] [Finite X] : Finite (Table B C X) :=
  Finite.of_injective (fun T : Table B C X => (T.owner,T.colour))
    (by intro a b h; cases a; cases b; cases h; rfl)

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


def equiv (T : Table B C X) (U : Table B C Y) (f : X ≃ Y)
    (ho : ∀ x, U.owner (f x) = T.owner x)
    (hc : ∀ x y, U.colour (f x) (f y) = T.colour x y) :
    @FirstOrder.Language.Equiv (language B C) X Y T.toStructure U.toStructure := by
  letI := T.toStructure
  letI := U.toStructure
  exact {
    toEquiv := f
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

/-- A genuine structure carrying exactly one literal owner and colour
name on every vertex and ordered pair. -/
structure Coding {B : Type u} {C : Type v} (X : Type z)
    [(language B C).Structure X] : Prop where
  owner_unique : ∀ x : X, ∃! b : B, Structure.RelMap (L := language B C) (Symbol.owner b) (fun _ => x)
  colour_unique : ∀ x y : X, ∃! c : C, Structure.RelMap (L := language B C) (Symbol.colour c) (![x,y])

namespace Coding
variable {B : Type u} {C : Type v} {X : Type z} {Y : Type z'}
variable [(language B C).Structure X] [(language B C).Structure Y]

theorem ofEmbedding (k : Coding (B := B) (C := C) Y) (f : X ↪[language B C] Y) :
    Coding (B := B) (C := C) X := by
  constructor
  · intro x
    obtain ⟨b,hb,hu⟩ := k.owner_unique (f x)
    exact ⟨b,(f.map_rel _ (fun _ => x)).mp hb,
      fun c hc => hu c ((f.map_rel _ (fun _ => x)).mpr hc)⟩
  · intro x y
    have hv : f ∘ ![x,y] = ![f x,f y] := by
      funext a
      refine Fin.cases rfl (fun b => ?_) a
      have hb : b = 0 := Subsingleton.elim _ _
      cases hb
      rfl
    obtain ⟨c,hc,hu⟩ := k.colour_unique (f x) (f y)
    rw [← hv] at hc hu
    exact ⟨c,(f.map_rel _ (![x,y])).mp hc,
      fun d hd => hu d ((f.map_rel _ (![x,y])).mpr hd)⟩

noncomputable def table (h : Coding (B := B) (C := C) X) : Table B C X where
  owner x := (h.owner_unique x).choose
  colour x y := (h.colour_unique x y).choose

theorem owner_rel (h : Coding (B := B) (C := C) X) (x : X) (b : B) :
    Structure.RelMap (L := language B C) (Symbol.owner b) (fun _ => x) ↔ h.table.owner x = b := by
  constructor
  · intro hb
    exact ((h.owner_unique x).choose_spec.2 b hb).symm
  · intro hb
    exact hb ▸ (h.owner_unique x).choose_spec.1

theorem colour_rel (h : Coding (B := B) (C := C) X) (x y : X) (c : C) :
    Structure.RelMap (L := language B C) (Symbol.colour c) (![x,y]) ↔ h.table.colour x y = c := by
  constructor
  · intro hc
    exact ((h.colour_unique x y).choose_spec.2 c hc).symm
  · intro hc
    exact hc ▸ (h.colour_unique x y).choose_spec.1

/-- The extracted complete tables encode the original structure exactly. -/
theorem structure_eq (h : Coding (B := B) (C := C) X) :
    h.table.toStructure = (inferInstance : (language B C).Structure X) := by
  apply FirstOrder.Language.Structure.ext
  · funext n F
    exact Empty.elim F
  · funext n r x
    apply propext
    cases r with
    | owner b =>
      have hv : x = (fun _ => x 0) := by
        funext a
        have ha : a = 0 := Subsingleton.elim _ _
        cases ha
        rfl
      change h.table.owner (x 0) = b ↔ _
      conv_rhs => rw [hv]
      exact (h.owner_rel (x 0) b).symm
    | colour c =>
      have hv : x = ![x 0,x 1] := by
        funext a
        refine Fin.cases rfl (fun b => ?_) a
        have hb : b = 0 := Subsingleton.elim _ _
        cases hb
        rfl
      change h.table.colour (x 0) (x 1) = c ↔ _
      conv_rhs => rw [hv]
      exact (h.colour_rel (x 0) (x 1) c).symm

theorem embedding_preserves (h : Coding (B := B) (C := C) X)
    (k : Coding (B := B) (C := C) Y) (f : X ↪[language B C] Y) :
    (∀ x, k.table.owner (f x) = h.table.owner x) ∧
      (∀ x y, k.table.colour (f x) (f y) = h.table.colour x y) := by
  constructor
  · intro x
    apply (k.owner_rel (f x) _).mp
    exact (f.map_rel _ (fun _ => x)).mpr ((h.owner_rel x _).mpr rfl)
  · intro x y
    apply (k.colour_rel (f x) (f y) _).mp
    have hv : f ∘ ![x,y] = ![f x,f y] := by
      funext a
      refine Fin.cases rfl (fun b => ?_) a
      have hb : b = 0 := Subsingleton.elim _ _
      cases hb
      rfl
    rw [← hv]
    exact (f.map_rel _ (![x,y])).mpr ((h.colour_rel x y _).mpr rfl)

end Coding

namespace Table
variable {B : Type u} {C : Type v} {X : Type z}

theorem coding (T : Table B C X) : @Coding B C X T.toStructure := by
  let := T.toStructure
  exact {
    owner_unique x := ⟨T.owner x,rfl,fun _ h => h.symm⟩
    colour_unique x y := ⟨T.colour x y,rfl,fun _ h => h.symm⟩ }

end Table
end CCO.OwnerTransversal.CountableColour

namespace CCO.OwnerTransversal.CountableAge.Data
open CCO.OwnerTransversal.CountableColour
variable {L : FirstOrder.Language.{u,v}} (D : Data L)

/-- Unique literal relation labels pass from finite stages to their
actual direct limit. This also constructs the limit's complete tables. -/
theorem limit_unique_label {I : Type z} {n : ℕ} (symbol : I → L.Relations n)
    (h : ∀ i : D.Chart, ∀ x : Fin n → D.Carrier i,
      ∃! c : I, Structure.RelMap (symbol c) x)
    (x : Fin n → D.Limit) : ∃! c : I, Structure.RelMap (symbol c) x := by
  obtain ⟨i,y,hy⟩ := DirectLimit.exists_quotient_mk'_sigma_mk'_eq
    (fun i => D.Carrier (D.stage i)) D.chain x
  have hp : x = (D.intoLimit i) ∘ y := hy
  rw [hp]
  obtain ⟨c,hc,hu⟩ := h (D.stage i) y
  exact ⟨c,((D.intoLimit i).map_rel _ y).mpr hc,
    fun d hd => hu d (((D.intoLimit i).map_rel _ y).mp hd)⟩

variable {B : Type u} {C : Type v}

theorem limitCoding (D : Data (language B C))
    (h : ∀ i : D.Chart, Coding (B := B) (C := C) (D.Carrier i)) :
    Coding (B := B) (C := C) D.Limit where
  owner_unique x := D.limit_unique_label Symbol.owner
    (fun i v => by
      have hv : (fun _ : Fin 1 => v 0) = v := by
        funext a
        have ha : a = 0 := Subsingleton.elim _ _
        cases ha
        rfl
      exact hv ▸ (h i).owner_unique (v 0)) (fun _ => x)
  colour_unique x y := D.limit_unique_label Symbol.colour
    (fun i v => by
      have hv : v = ![v 0,v 1] := by
        funext a
        refine Fin.cases rfl (fun b => ?_) a
        have hb : b = 0 := Subsingleton.elim _ _
        cases hb
        rfl
      rw [hv]
      exact (h i).colour_unique (v 0) (v 1)) (![x,y])

end CCO.OwnerTransversal.CountableAge.Data

