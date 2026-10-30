import CCO.FullPhaseLift.Canonical.Signature
import Mathlib.ModelTheory.Basic

/-! Exact bridges to Mathlib's first-order Fraisse machinery. No tuples,
including nullaries, are dropped by this change of representation. -/

universe u v w
namespace CCO.FullPhaseLift.Canonical
open scoped FirstOrder

def Signature.firstOrder (L : Signature) : FirstOrder.Language where
  Functions _ := Empty
  Relations := L.language.Rel

instance (L : Signature) : L.firstOrder.IsRelational := fun _ => Empty.instIsEmpty

@[instance_reducible] def toFirstOrder {L : Signature} {V : Type v} (T : BoolTable L V) :
    L.firstOrder.Structure V where
  funMap f := nomatch f
  RelMap := (toRelational T).rel

noncomputable def ofFirstOrder {L : Signature} {V : Type v}
    (A : L.firstOrder.Structure V) : BoolTable L V :=
  ofRelational { rel := A.RelMap }

@[simp] theorem ofFirstOrder_toFirstOrder {L : Signature} {V : Type v}
    (T : BoolTable L V) : ofFirstOrder (toFirstOrder T) = T :=
  ofRelational_toRelational T

@[simp] theorem toFirstOrder_ofFirstOrder {L : Signature} {V : Type v}
    (A : L.firstOrder.Structure V) : toFirstOrder (ofFirstOrder A) = A := by
  apply FirstOrder.Language.Structure.ext
  · funext n f
    exact Empty.elim f
  · exact congrArg RelationalCompletion.Relational.Structure.rel
      (toRelational_ofRelational { rel := A.RelMap })

abbrev FirstOrderEmbedding {L : Signature} {V : Type v} {W : Type w}
    (A : BoolTable L V) (B : BoolTable L W) :=
  @FirstOrder.Language.Embedding L.firstOrder V W (toFirstOrder A) (toFirstOrder B)

abbrev FirstOrderIso {L : Signature} {V : Type v} {W : Type w}
    (A : BoolTable L V) (B : BoolTable L W) :=
  @FirstOrder.Language.Equiv L.firstOrder V W (toFirstOrder A) (toFirstOrder B)

def embeddingToFirstOrder {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Embedding A B) :
    FirstOrderEmbedding A B := by
  letI := toFirstOrder A
  letI := toFirstOrder B
  exact { toFun := e.point
          inj' := e.injective
          map_fun' := fun f => (nomatch f)
          map_rel' := e.rel_iff }

def embeddingOfFirstOrder {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : FirstOrderEmbedding A B) :
    Embedding A B := by
  letI := toFirstOrder A
  letI := toFirstOrder B
  exact { point := e, injective := e.injective, rel_iff := e.map_rel' }

def isoToFirstOrder {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Iso A B) :
    FirstOrderIso A B := by
  letI := toFirstOrder A
  letI := toFirstOrder B
  exact { toEquiv := e.point
          map_fun' := fun f => (nomatch f)
          map_rel' := e.rel_iff }

def isoOfFirstOrder {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : FirstOrderIso A B) :
    Iso A B := by
  letI := toFirstOrder A
  letI := toFirstOrder B
  exact { point := e.toEquiv, rel_iff := e.map_rel' }

@[simp] theorem embeddingOfFirstOrder_toFirstOrder {L : Signature}
    {V : Type v} {W : Type w} {A : BoolTable L V} {B : BoolTable L W}
    (e : Embedding A B) : embeddingOfFirstOrder (embeddingToFirstOrder e) = e := rfl

@[simp] theorem embeddingToFirstOrder_ofFirstOrder {L : Signature}
    {V : Type v} {W : Type w} {A : BoolTable L V} {B : BoolTable L W}
    (e : FirstOrderEmbedding A B) : embeddingToFirstOrder (embeddingOfFirstOrder e) = e := rfl

@[simp] theorem isoOfFirstOrder_toFirstOrder {L : Signature}
    {V : Type v} {W : Type w} {A : BoolTable L V} {B : BoolTable L W}
    (e : Iso A B) : isoOfFirstOrder (isoToFirstOrder e) = e := rfl

@[simp] theorem isoToFirstOrder_ofFirstOrder {L : Signature}
    {V : Type v} {W : Type w} {A : BoolTable L V} {B : BoolTable L W}
    (e : FirstOrderIso A B) : isoToFirstOrder (isoOfFirstOrder e) = e := rfl

end CCO.FullPhaseLift.Canonical
