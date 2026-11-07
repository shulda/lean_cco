import CCO.UnfilteredEP.SingletonRamsey
import Mathlib.Basic.Finite.Sum

/-! B064 C05–C07: finite JEP stores all inverse relabelled targets,
actual singleton objects, and EVERY allowed atom/label pair. -/

universe u v w z p q
namespace CCO.UnfilteredEP.FiniteAge.RamseyProvider
variable {OldSort : Type u} {Atom : Type v} {Label : Type p}
variable {K : FiniteAge.{u,v,w,z} OldSort Atom}
variable {T : FiniteTemplate OldSort Atom Label}
variable (P : K.RamseyProvider.{u,v,w,z,p,q} T)

abbrev AutomorphismIndex := {f : Label → Label // T.Automorphism f}
abbrev PairIndex := {p : Atom × Label × Label // T.rel p.1 p.2.1 p.2.2}

/-- One actual marked old pair, lifted into the Ramsey provider. -/
structure PairWitness (p : PairIndex (T := T)) where
  object : P.Obj
  left : K.Point (P.old object)
  right : K.Point (P.old object)
  distinct : left ≠ right
  colour : K.colour (P.old object) left right = some p.val.1
  left_label : (P.marking object).label left = p.val.2.1
  right_label : (P.marking object).label right = p.val.2.2

theorem pairWitness_exists (lift : P.ReductSurjective) (pairs : K.AllPairsRealized T)
    (p : PairIndex (T := T)) : Nonempty (P.PairWitness p) := by
  obtain ⟨A,m,x,y,hxy,hcol,hx,hy⟩ := pairs p.val.1 p.val.2.1 p.val.2.2 p.property
  obtain ⟨D,e,_⟩ := lift A m
  exact ⟨⟨D,e.old.toFun x,e.old.toFun y,
    fun h => hxy (e.old.injective h),(e.old.colours x y).trans hcol,
    (e.labels x).trans hx,(e.labels y).trans hy⟩⟩

/-- A single provider object containing every finite witness needed by
one target. The embeddings are actual induced old-colour maps. -/
structure CoreWitnesses {A : K.Obj} (a : K.Marking T A) (S : P.Singletons) where
  object : P.Obj
  inverse : ∀ alpha : AutomorphismIndex (T := T),
    K.MarkedEmbedding T
      (a.postcompose (T.automorphismEquiv alpha.property).symm
        (T.automorphism_inverse_endomorphism alpha.property)) (P.marking object)
  singleton : ∀ t, P.Embedding (S.object t) object
  left : PairIndex (T := T) → K.Point (P.old object)
  right : PairIndex (T := T) → K.Point (P.old object)
  distinct : ∀ p, left p ≠ right p
  colour : ∀ p, K.colour (P.old object) (left p) (right p) = some p.val.1
  left_label : ∀ p, (P.marking object).label (left p) = p.val.2.1
  right_label : ∀ p, (P.marking object).label (right p) = p.val.2.2

/-- The finite witness package follows solely from ordinary finite JEP,
realized pairs, and reduct surjectivity. No SAP or EP is used. -/
theorem coreWitnesses_exists [Finite Label] [Finite Atom]
    (S : P.Singletons) (lift : P.ReductSurjective) (jep : P.JEP)
    (pairs : K.AllPairsRealized T) {A : K.Obj} (a : K.Marking T A) :
    Nonempty (P.CoreWitnesses a S) := by
  classical
  let inverseMark (alpha : AutomorphismIndex (T := T)) :=
    a.postcompose (T.automorphismEquiv alpha.property).symm
      (T.automorphism_inverse_endomorphism alpha.property)
  let inverseObject (alpha : AutomorphismIndex (T := T)) : P.Obj :=
    (lift A (inverseMark alpha)).choose
  let inverseMap (alpha : AutomorphismIndex (T := T)) :
      K.MarkedEmbedding T (inverseMark alpha) (P.marking (inverseObject alpha)) :=
    (lift A (inverseMark alpha)).choose_spec.choose
  let pair (p : PairIndex (T := T)) : P.PairWitness p :=
    (P.pairWitness_exists lift pairs p).some
  let objects : AutomorphismIndex (T := T) ⊕ Label ⊕ PairIndex (T := T) → P.Obj :=
    Sum.elim inverseObject (Sum.elim S.object (fun p => (pair p).object))
  obtain ⟨base,_,_⟩ := lift A a
  obtain ⟨D,hD⟩ := P.joint_finite jep base objects
  let intoD (i) : P.Embedding (objects i) D := (hD i).some
  let q (p : PairIndex (T := T)) := intoD (Sum.inr (Sum.inr p))
  refine ⟨{
    object := D
    inverse alpha := (intoD (Sum.inl alpha)).val.comp (inverseMap alpha)
    singleton t := intoD (Sum.inr (Sum.inl t))
    left p := (q p).val.old.toFun (pair p).left
    right p := (q p).val.old.toFun (pair p).right
    distinct p := fun h => (pair p).distinct ((q p).val.old.injective h)
    colour p := ((q p).val.old.colours _ _).trans (pair p).colour
    left_label p := ((q p).val.labels _).trans (pair p).left_label
    right_label p := ((q p).val.labels _).trans (pair p).right_label }⟩

end CCO.UnfilteredEP.FiniteAge.RamseyProvider
