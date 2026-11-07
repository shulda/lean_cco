import CCO.TerminalHiddenHN.BinaryCodec
import CCO.UnaryHN.RawEncoding.OrderedReadout

/-! A GLOBAL order in the same hidden universe, with one binary order
symbol for EVERY ordered pair of hidden sorts. Terms use exactly the
underlying unary graphs, independently of the chosen host order. -/

universe u v w
namespace CCO.TerminalHiddenHN
noncomputable section
variable (L : CCO.UnarySupport.Signature.{u}) (hbin : ∀ R, L.arity R = 2)

abbrev orderedLanguage : CCO.FullCode.Language.{u} where
  Sorts := L.Sorts
  Func := L.Func
  Unary := PEmpty
  Binary := L.Rel ⊕ (L.Sorts × L.Sorts)
  input := L.input
  output := L.output
  unarySort := PEmpty.elim
  leftSort
    | .inl R => (binaryLanguage L hbin).leftSort R
    | .inr p => p.1
  rightSort
    | .inl R => (binaryLanguage L hbin).rightSort R
    | .inr p => p.2
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteUnary := inferInstance
  finiteBinary := inferInstance

def orderedStructure {V : Type v} (C : CCO.UnarySupport.Structure L V) [LinearOrder V] :
    CCO.FullCode.Structure (orderedLanguage L hbin) V where
  sort := C.sort
  func := C.func
  functional := C.functional
  func_sorted := C.func_sorted
  unary := PEmpty.elim
  unary_sorted U := PEmpty.elim U
  binary
    | .inl R, x, y => (binaryStructure L hbin C).binary R x y
    | .inr p, x, y => C.sort x = p.1 ∧ C.sort y = p.2 ∧ x < y
  binary_sorted R x y h := by
    cases R with
    | inl R => exact (binaryStructure L hbin C).binary_sorted R x y h
    | inr p => exact ⟨h.1,h.2.1⟩

def orderedBinaryReduct {V : Type v}
    (M : CCO.FullCode.Structure (orderedLanguage L hbin) V) :
    CCO.FullCode.Structure (binaryLanguage L hbin) V where
  sort := M.sort
  func := M.func
  functional := M.functional
  func_sorted := M.func_sorted
  unary := PEmpty.elim
  unary_sorted U := PEmpty.elim U
  binary R := M.binary (.inl R)
  binary_sorted R := M.binary_sorted (.inl R)

def orderedReductEmbedding {V : Type v} {W : Type w}
    {M : CCO.FullCode.Structure (orderedLanguage L hbin) V}
    {N : CCO.FullCode.Structure (orderedLanguage L hbin) W}
    (e : CCO.FullCode.Structure.Embedding M N) :
    CCO.FullCode.Structure.Embedding (orderedBinaryReduct L hbin M) (orderedBinaryReduct L hbin N) where
  point := e.point
  injective := e.injective
  sort_eq := e.sort_eq
  map_func := e.map_func
  reflect_func := e.reflect_func
  unary_iff U := PEmpty.elim U
  binary_iff R := e.binary_iff (.inl R)

/-- Forget only the order comparisons; every original unary domain and
binary cylinder remains on the SAME point map. -/
def orderedBinaryEmbedding {V : Type v} {W : Type w}
    {C : CCO.UnarySupport.Structure L V} {D : CCO.UnarySupport.Structure L W}
    [LinearOrder V] [LinearOrder W]
    (e : CCO.FullCode.Structure.Embedding (orderedStructure L hbin C) (orderedStructure L hbin D)) :
    CCO.FullCode.Structure.Embedding (binaryStructure L hbin C) (binaryStructure L hbin D) where
  point := e.point
  injective := e.injective
  sort_eq := e.sort_eq
  map_func := e.map_func
  reflect_func := e.reflect_func
  unary_iff U := PEmpty.elim U
  binary_iff R := e.binary_iff (.inl R)

def orderedEmbedding {V : Type v} {W : Type w}
    {C : CCO.UnarySupport.Structure L V} {D : CCO.UnarySupport.Structure L W}
    [LinearOrder V] [LinearOrder W] (e : CCO.UnaryHN.Raw.OrderedEmbedding C D) :
    CCO.FullCode.Structure.Embedding (orderedStructure L hbin C) (orderedStructure L hbin D) where
  point := e.point
  injective := e.injective
  sort_eq := e.sort_eq
  map_func := e.map_func
  reflect_func := e.reflect_func
  unary_iff U := PEmpty.elim U
  binary_iff R x y := by
    cases R with
    | inl R => exact (binaryEmbedding L hbin e.toEmbedding).binary_iff R x y
    | inr p =>
      change (D.sort (e.point x) = p.1 ∧ D.sort (e.point y) = p.2 ∧ e.point x < e.point y) ↔
        (C.sort x = p.1 ∧ C.sort y = p.2 ∧ x < y)
      rw [e.sort_eq x,e.sort_eq y,e.order_iff x y]

def orderedEmbeddingInverse {V : Type v} {W : Type w}
    {C : CCO.UnarySupport.Structure L V} {D : CCO.UnarySupport.Structure L W}
    [LinearOrder V] [LinearOrder W]
    (e : CCO.FullCode.Structure.Embedding (orderedStructure L hbin C) (orderedStructure L hbin D)) :
    CCO.UnaryHN.Raw.OrderedEmbedding C D where
  toEmbedding := binaryEmbeddingInverse L hbin (orderedBinaryEmbedding L hbin e)
  order_iff x y := by
    have h := e.binary_iff (.inr (C.sort x,C.sort y)) x y
    have hx : D.sort (e.point x) = C.sort x := e.sort_eq x
    have hy : D.sort (e.point y) = C.sort y := e.sort_eq y
    change (D.sort (e.point x) = C.sort x ∧ D.sort (e.point y) = C.sort y ∧ e.point x < e.point y) ↔
      (C.sort x = C.sort x ∧ C.sort y = C.sort y ∧ x < y) at h
    change e.point x < e.point y ↔ x < y
    simpa only [hx,hy,true_and] using h

def orderedEmbeddingEquiv {V : Type v} {W : Type w}
    (C : CCO.UnarySupport.Structure L V) (D : CCO.UnarySupport.Structure L W)
    [LinearOrder V] [LinearOrder W] :
    CCO.UnaryHN.Raw.OrderedEmbedding C D ≃
      CCO.FullCode.Structure.Embedding (orderedStructure L hbin C) (orderedStructure L hbin D) where
  toFun := orderedEmbedding L hbin
  invFun := orderedEmbeddingInverse L hbin
  left_inv e := by apply CCO.UnaryHN.Raw.OrderedEmbedding.ext; rfl
  right_inv e := by apply CCO.FullCode.Structure.Embedding.ext; intro x; rfl

theorem orderedEmbedding_comp {Z : Type*} {V : Type v} {W : Type w}
    {C : CCO.UnarySupport.Structure L V} {D : CCO.UnarySupport.Structure L W}
    {E : CCO.UnarySupport.Structure L Z}
    [LinearOrder V] [LinearOrder W] [LinearOrder Z]
    (g : CCO.UnaryHN.Raw.OrderedEmbedding D E) (f : CCO.UnaryHN.Raw.OrderedEmbedding C D) :
    orderedEmbedding L hbin (g.compose f) =
      (orderedEmbedding L hbin g).comp (orderedEmbedding L hbin f) := by
  apply CCO.FullCode.Structure.Embedding.ext
  intro x
  rfl

def baseTermToOrdered : {s t : L.Sorts} →
    CCO.FullCode.Term (binaryLanguage L hbin) s t → CCO.FullCode.Term (orderedLanguage L hbin) s t
  | _, _, .id s => CCO.FullCode.Term.id (L := orderedLanguage L hbin) s
  | _, _, .app F q => CCO.FullCode.Term.app (L := orderedLanguage L hbin) F (baseTermToOrdered q)

def orderedTermToBase : {s t : L.Sorts} →
    CCO.FullCode.Term (orderedLanguage L hbin) s t → CCO.FullCode.Term (binaryLanguage L hbin) s t
  | _, _, .id s => CCO.FullCode.Term.id (L := binaryLanguage L hbin) s
  | _, _, .app F q => CCO.FullCode.Term.app (L := binaryLanguage L hbin) F (orderedTermToBase q)

@[simp] theorem orderedTermToBase_baseTermToOrdered {s t : L.Sorts}
    (q : CCO.FullCode.Term (binaryLanguage L hbin) s t) :
    orderedTermToBase L hbin (baseTermToOrdered L hbin q) = q := by
  exact CCO.FullCode.Term.rec (L := binaryLanguage L hbin)
    (motive := fun _ _ a => orderedTermToBase L hbin (baseTermToOrdered L hbin a) = a)
    (fun _ => rfl)
    (fun F {_} _ ih => congrArg (CCO.FullCode.Term.app (L := binaryLanguage L hbin) F) ih) q

@[simp] theorem baseTermToOrdered_orderedTermToBase {s t : L.Sorts}
    (q : CCO.FullCode.Term (orderedLanguage L hbin) s t) :
    baseTermToOrdered L hbin (orderedTermToBase L hbin q) = q := by
  exact CCO.FullCode.Term.rec (L := orderedLanguage L hbin)
    (motive := fun _ _ a => baseTermToOrdered L hbin (orderedTermToBase L hbin a) = a)
    (fun _ => rfl)
    (fun F {_} _ ih => congrArg (CCO.FullCode.Term.app (L := orderedLanguage L hbin) F) ih) q

/-- Function-only evaluation forgets the host order completely. In
particular no host order must embed in a preselected ambient order. -/
theorem orderedTermToBase_eval {V : Type v} (C : CCO.UnarySupport.Structure L V)
    [LinearOrder V] {s t : L.Sorts} (q : CCO.FullCode.Term (orderedLanguage L hbin) s t) (x : V) :
    q.eval (orderedStructure L hbin C) x =
      (orderedTermToBase L hbin q).eval (binaryStructure L hbin C) x := by
  exact CCO.FullCode.Term.rec (L := orderedLanguage L hbin)
    (motive := fun _ _ a => a.eval (orderedStructure L hbin C) x =
      (orderedTermToBase L hbin a).eval (binaryStructure L hbin C) x)
    (fun _ => rfl)
    (fun F {_} q ih => by
      change {y | ∃ z, z ∈ q.eval (orderedStructure L hbin C) x ∧ y ∈ C.func F z} = _
      rw [ih]
      rfl) q

theorem baseTermToOrdered_eval {V : Type v} (C : CCO.UnarySupport.Structure L V)
    [LinearOrder V] {s t : L.Sorts} (q : CCO.FullCode.Term (binaryLanguage L hbin) s t) (x : V) :
    (baseTermToOrdered L hbin q).eval (orderedStructure L hbin C) x =
      q.eval (binaryStructure L hbin C) x := by
  rw [orderedTermToBase_eval,orderedTermToBase_baseTermToOrdered]

section Fresh
variable (U : CCO.UnaryFreshFrames.Language.{u})
variable [Finite U.Sorts] [Finite U.Func] [Finite U.Rel]
variable (hU : ∀ R, U.arity R = 2)

def freshTermToOrdered {s t : U.Sorts} (q : CCO.UnaryFreshFrames.Term U s t) :
    CCO.FullCode.Term (orderedLanguage (CCO.HiddenSAPReadings.partialSignature U) hU) s t :=
  baseTermToOrdered _ hU (freshTermToFull U hU q)

def orderedTermToFresh {s t : U.Sorts}
    (q : CCO.FullCode.Term (orderedLanguage (CCO.HiddenSAPReadings.partialSignature U) hU) s t) :
    CCO.UnaryFreshFrames.Term U s t :=
  fullTermToFresh U hU (orderedTermToBase _ hU q)

@[simp] theorem orderedTermToFresh_freshTermToOrdered {s t : U.Sorts}
    (q : CCO.UnaryFreshFrames.Term U s t) :
    orderedTermToFresh U hU (freshTermToOrdered U hU q) = q := by
  unfold orderedTermToFresh freshTermToOrdered
  exact (congrArg (fullTermToFresh U hU)
    (orderedTermToBase_baseTermToOrdered (CCO.HiddenSAPReadings.partialSignature U) hU
      (freshTermToFull U hU q))).trans (fullTermToFresh_freshTermToFull U hU q)

@[simp] theorem freshTermToOrdered_orderedTermToFresh {s t : U.Sorts}
    (q : CCO.FullCode.Term (orderedLanguage (CCO.HiddenSAPReadings.partialSignature U) hU) s t) :
    freshTermToOrdered U hU (orderedTermToFresh U hU q) = q := by
  unfold orderedTermToFresh freshTermToOrdered
  exact (congrArg (baseTermToOrdered (CCO.HiddenSAPReadings.partialSignature U) hU)
    (freshTermToFull_fullTermToFresh U hU
      (orderedTermToBase (CCO.HiddenSAPReadings.partialSignature U) hU q))).trans
    (baseTermToOrdered_orderedTermToBase (CCO.HiddenSAPReadings.partialSignature U) hU q)

theorem freshTermToOrdered_eval {V : Type v} (C : CCO.UnaryFreshFrames.Structure U V)
    [LinearOrder V] {s t : U.Sorts} (q : CCO.UnaryFreshFrames.Term U s t)
    (x y : V) (hx : C.sort x = s) :
    y ∈ (freshTermToOrdered U hU q).eval
      (orderedStructure (CCO.HiddenSAPReadings.partialSignature U) hU
        (CCO.HiddenSAPReadings.partialTarget C)) x ↔ y = C.eval q x := by
  unfold freshTermToOrdered
  have he := baseTermToOrdered_eval (CCO.HiddenSAPReadings.partialSignature U) hU
    (CCO.HiddenSAPReadings.partialTarget C) (freshTermToFull U hU q) x
  have hm := Iff.of_eq (congrArg (fun T : Set V => y ∈ T) he)
  exact hm.trans (freshTermToFull_eval U hU C q x y hx)

end Fresh
end
end CCO.TerminalHiddenHN
