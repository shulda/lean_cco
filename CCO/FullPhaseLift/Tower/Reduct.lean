import CCO.FullPhaseLift.Marked.Signature

/-! Literal full-language reduct maps compose with their SAME carrier
bijections. Every old symbol/tuple, including repetitions and nullaries,
is read through the resulting composite rather than through a binary iso. -/
universe m n o
namespace CCO.FullPhaseLift.Tower
open Canonical

structure SignatureReduct (L K : Signature) where
  symbol : Fin L.size → Fin K.size
  arity : ∀ r, K.arity (symbol r) = L.arity r

namespace SignatureReduct
variable {L K J : Signature}

def forget (P : SignatureReduct L K) {V : Type m} (T : BoolTable K V) : BoolTable L V :=
  fun r xs => T (P.symbol r) (xs ∘ Fin.cast (P.arity r))

def identity (L : Signature) : SignatureReduct L L := ⟨id,fun _ => rfl⟩

def compose (P : SignatureReduct L K) (Q : SignatureReduct K J) : SignatureReduct L J where
  symbol r := Q.symbol (P.symbol r)
  arity r := (Q.arity (P.symbol r)).trans (P.arity r)

theorem compose_forget (P : SignatureReduct L K) (Q : SignatureReduct K J)
    {V : Type m} (T : BoolTable J V) :
    (P.compose Q).forget T = P.forget (Q.forget T) := by
  funext r xs
  change T (Q.symbol (P.symbol r))
      (xs ∘ Fin.cast ((Q.arity (P.symbol r)).trans (P.arity r))) =
    T (Q.symbol (P.symbol r)) ((xs ∘ Fin.cast (P.arity r)) ∘ Fin.cast (Q.arity (P.symbol r)))
  apply congrArg (T (Q.symbol (P.symbol r)))
  funext i
  rfl

theorem forget_pullback (P : SignatureReduct L K) {V : Type m} {W : Type n}
    (T : BoolTable K V) (f : W → V) :
    P.forget (pullback T f) = pullback (P.forget T) f := rfl

/-- The actual single-bit syntactic reduct. All old arities are unchanged. -/
def bit (L : Signature) : SignatureReduct L (Marked.addBit L) :=
  ⟨Fin.succ,fun _ => rfl⟩

@[simp] theorem bit_forget {L : Signature} {V : Type m}
    (T : BoolTable (Marked.addBit L) V) : (bit L).forget T = Marked.oldTable T := rfl

end SignatureReduct

/-- A FULL reduct supplies an actual global bijection preserving EVERY
old relation, not merely a colour map or an arbitrary binary isomorphism. -/
structure FullReduct {L K : Signature} {M : Type m} {N : Type n}
    (U : BoolTable L M) (V : BoolTable K N) where
  signature : SignatureReduct L K
  point : N ≃ M
  read : signature.forget V = pullback U point

namespace FullReduct
variable {L K J : Signature} {M : Type m} {N : Type n} {O : Type o}
variable {U : BoolTable L M} {V : BoolTable K N} {W : BoolTable J O}

def identity (U : BoolTable L M) : FullReduct U U :=
  ⟨SignatureReduct.identity L,Equiv.refl M,rfl⟩

/-- The carrier bijection of the full composite is literally the same
successive reduct map; no fresh comparison isomorphism is chosen. -/
def compose (P : FullReduct U V) (Q : FullReduct V W) : FullReduct U W where
  signature := P.signature.compose Q.signature
  point := Q.point.trans P.point
  read := by
    rw [SignatureReduct.compose_forget,Q.read,SignatureReduct.forget_pullback,P.read]
    rfl

@[simp] theorem compose_point (P : FullReduct U V) (Q : FullReduct V W) (x : O) :
    (P.compose Q).point x = P.point (Q.point x) := rfl

/-- The actual old FULL reduct isomorphism of a constructed marked limit
supplies its one-bit full-language reduct, retaining all higher tuples. -/
def fromOldIso {L : Signature} {M : Type m} {N : Type n}
    (U : BoolTable L M) (V : BoolTable (Marked.addBit L) N)
    (e : Canonical.Iso (Marked.oldTable V) U) : FullReduct U V where
  signature := SignatureReduct.bit L
  point := e.point
  read := by
    funext r xs
    exact (embedding_read e.toEmbedding r xs).symm

/-- Explicit all-arity readout of the SAME full reduct map. -/
theorem tuple_read (P : FullReduct U V) (r : Fin L.size) (xs : Fin (L.arity r) → N) :
    V (P.signature.symbol r) (xs ∘ Fin.cast (P.signature.arity r)) = U r (P.point ∘ xs) :=
  congrFun (congrFun P.read r) xs

end FullReduct
end CCO.FullPhaseLift.Tower
