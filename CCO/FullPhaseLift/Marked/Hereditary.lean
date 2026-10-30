import CCO.FullPhaseLift.Marked.Class

/-! Heredity is restriction of ALL full tuple data and the same unary
bits. The full marked class is encoded by countably many finite tables. -/
universe u v w m
namespace CCO.FullPhaseLift.Marked
open Canonical APCharacter
noncomputable section
variable {L : Signature} {M : Type m} (U : BoolTable L M)
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (pack : M ≃ Sigma X) (mask : MaskData S)

/-- Actual membership of a full marked table in the legal full class. -/
def Realized {V : Type} (T : BoolTable L V) (b : V → Bit) : Prop :=
  ∃ p : Canonical.Embedding T U, Age.Legal S mask (pack ∘ p.point) b

theorem realized_reindex {V W : Type} {T : BoolTable L V} {b : V → Bit}
    (h : Realized U S pack mask T b) (f : W ↪ V) :
    Realized U S pack mask (pullback T f) (b ∘ f) := by
  obtain ⟨p,hp⟩ := h
  let q : Canonical.Embedding (pullback T f) U :=
    embeddingOf (p.point ∘ f) (p.injective.comp f.injective)
      (fun r xs => embedding_read p r (f ∘ xs))
  exact ⟨q,⟨fun x => hp.1 (f x),fun x y => hp.2 (f x) (f y)⟩⟩

/-- Any actual full marked embedding into a class object gives a legal
full source object. Reflection retains negative higher tuples as well. -/
theorem realized_of_embedding {V : Type} {T : BoolTable L V} {b : V → Bit}
    (C : Chart U S pack mask)
    (f : Canonical.Embedding (table T b) (table C.old.full C.bits)) :
    Realized U S pack mask T b := by
  obtain ⟨p,hp⟩ := C.legal
  let q := p.comp (oldEmbedding f)
  refine ⟨q,?_,?_⟩
  · intro x
    change mask.validBit ((pack ∘ p.point) (f.point x)).1 (b x)
    have h := hp.1 (f.point x)
    simpa only [embedding_bits f x] using h
  · intro x y
    change mask.allowed (S.colour ((pack ∘ p.point) (f.point x)).2
      ((pack ∘ p.point) (f.point y)).2) (b x) (b y)
    have h := hp.2 (f.point x) (f.point y)
    simpa only [embedding_bits f x,embedding_bits f y] using h

/-- A finite FULL table is represented on a finite ordinal, together
with exactly its original bit assignment. -/
def chartOf {V : Type} [Finite V] (T : BoolTable L V) (b : V → Bit)
    (h : Realized U S pack mask T b) : Chart U S pack mask := by
  letI := Fintype.ofFinite V
  let e := (Fintype.equivFin V).symm
  let ht := realized_reindex U S pack mask h e.toEmbedding
  exact ⟨⟨Fintype.card V,pullback T e,⟨ht.choose⟩⟩,b ∘ e,ht⟩

def chartOfIso {V : Type} [Finite V] (T : BoolTable L V) (b : V → Bit)
    (h : Realized U S pack mask T b) :
    Canonical.Iso (table T b)
      (table (chartOf U S pack mask T b h).old.full (chartOf U S pack mask T b h).bits) := by
  letI := Fintype.ofFinite V
  let e := Fintype.equivFin V
  apply isoOf e
  intro r
  refine Fin.cases ?_ (fun s => ?_) r
  · intro xs
    change bitBool (b (e.symm (e (xs (0 : Fin 1))))) = bitBool (b (xs (0 : Fin 1)))
    rw [e.symm_apply_apply]
  · intro xs
    change T s (e.symm ∘ (e ∘ xs)) = T s xs
    congr 1
    funext x
    exact e.symm_apply_apply _

/-- The arbitrary first-order hereditary property required by the
ACTUAL countable-age construction. -/
theorem hereditary (C : Chart U S pack mask) (A : Type)
    [(addBit L).firstOrder.Structure A] [Finite A]
    (f : @FirstOrder.Language.Embedding (addBit L).firstOrder A (Fin C.old.size)
      inferInstance (toFirstOrder (table C.old.full C.bits))) :
    ∃ D : Chart U S pack mask,
      Nonempty (@FirstOrder.Language.Equiv (addBit L).firstOrder A (Fin D.old.size)
        inferInstance (toFirstOrder (table D.old.full D.bits))) := by
  let T := ofFirstOrder (inferInstance : (addBit L).firstOrder.Structure A)
  have hs : toFirstOrder T = (inferInstance : (addBit L).firstOrder.Structure A) :=
    toFirstOrder_ofFirstOrder _
  let f' : FirstOrderEmbedding T (table C.old.full C.bits) :=
    cast (congrArg (fun st => @FirstOrder.Language.Embedding (addBit L).firstOrder
      A (Fin C.old.size) st (toFirstOrder (table C.old.full C.bits))) hs.symm) f
  let ef := embeddingOfFirstOrder f'
  have hT : Realized U S pack mask (oldTable T) (bits T) := by
    apply realized_of_embedding U S pack mask C
    rw [table_oldTable_bits]
    exact ef
  let D := chartOf U S pack mask (oldTable T) (bits T) hT
  have eqv : Canonical.Iso T (table D.old.full D.bits) := by
    rw [← table_oldTable_bits T]
    exact chartOfIso U S pack mask (oldTable T) (bits T) hT
  refine ⟨D,?_⟩
  exact cast (congrArg (fun st => Nonempty (@FirstOrder.Language.Equiv
    (addBit L).firstOrder A (Fin D.old.size) st (toFirstOrder (table D.old.full D.bits)))) hs)
    ⟨isoToFirstOrder eqv⟩

end
end CCO.FullPhaseLift.Marked
