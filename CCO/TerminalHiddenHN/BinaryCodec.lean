import CCO.FullCode.Terms
import Lean.Elab.Tactic.Omega
import CCO.UnarySupport.TypedTerms
import CCO.HiddenSAPReadings.SourceSupport

/-! Faithful binary views of the original partial unary language.
All original relation symbols and the literal partial function graphs
are retained. The term codec changes syntax, never values or domains. -/

universe u v w
namespace CCO.TerminalHiddenHN
noncomputable section

variable (L : CCO.UnarySupport.Signature.{u}) (hbin : ∀ R, L.arity R = 2)

def binaryFirst (R : L.Rel) : Fin (L.arity R) := Fin.cast (hbin R).symm 0
def binarySecond (R : L.Rel) : Fin (L.arity R) := Fin.cast (hbin R).symm 1

def binaryTuple {V : Type v} (R : L.Rel) (x y : V) : Fin (L.arity R) → V :=
  fun i => if i.val = 0 then x else y

@[simp] theorem binaryTuple_first {V : Type v} (R : L.Rel) (x y : V) :
    binaryTuple L R x y (binaryFirst L hbin R) = x := by simp [binaryTuple,binaryFirst]
@[simp] theorem binaryTuple_second {V : Type v} (R : L.Rel) (x y : V) :
    binaryTuple L R x y (binarySecond L hbin R) = y := by simp [binaryTuple,binarySecond]

theorem binaryTuple_eta {V : Type v} (R : L.Rel) (xs : Fin (L.arity R) → V) :
    binaryTuple L R (xs (binaryFirst L hbin R)) (xs (binarySecond L hbin R)) = xs := by
  funext i
  have hi := i.isLt
  have hn := hbin R
  have hv : i.val = 0 ∨ i.val = 1 := by omega
  rcases hv with hv | hv
  · have he : i = binaryFirst L hbin R := Fin.ext hv
    subst i
    exact binaryTuple_first L hbin R _ _
  · have he : i = binarySecond L hbin R := Fin.ext hv
    subst i
    exact binaryTuple_second L hbin R _ _

abbrev binaryLanguage : CCO.FullCode.Language.{u} where
  Sorts := L.Sorts
  Func := L.Func
  Unary := PEmpty
  Binary := L.Rel
  input := L.input
  output := L.output
  unarySort := PEmpty.elim
  leftSort R := L.argument R (binaryFirst L hbin R)
  rightSort R := L.argument R (binarySecond L hbin R)
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteUnary := inferInstance
  finiteBinary := inferInstance

def binaryStructure {V : Type v} (C : CCO.UnarySupport.Structure L V) :
    CCO.FullCode.Structure (binaryLanguage L hbin) V where
  sort := C.sort
  func := C.func
  functional := C.functional
  func_sorted := C.func_sorted
  unary := PEmpty.elim
  unary_sorted U := PEmpty.elim U
  binary R x y := C.rel R (binaryTuple L R x y)
  binary_sorted R x y h := by
    exact ⟨by simpa using C.rel_sorted R _ h (binaryFirst L hbin R),
      by simpa using C.rel_sorted R _ h (binarySecond L hbin R)⟩

def supportTermToFull {s t : L.Sorts}
    (q : CCO.UnarySupport.Structure.Term L s t) :
    CCO.FullCode.Term (binaryLanguage L hbin) s t :=
  CCO.UnarySupport.Structure.Term.rec (L := L)
    (motive := fun t _ => CCO.FullCode.Term (binaryLanguage L hbin) s t)
    (CCO.FullCode.Term.id (L := binaryLanguage L hbin) s)
    (fun F _ ih => CCO.FullCode.Term.app (L := binaryLanguage L hbin) F ih) q

def fullTermToSupport {s t : L.Sorts}
    (q : CCO.FullCode.Term (binaryLanguage L hbin) s t) :
    CCO.UnarySupport.Structure.Term L s t :=
  CCO.FullCode.Term.rec (L := binaryLanguage L hbin)
    (motive := fun s t _ => CCO.UnarySupport.Structure.Term L s t)
    (fun s => CCO.UnarySupport.Structure.Term.var (L := L) s)
    (fun F {s} _ ih => CCO.UnarySupport.Structure.Term.func (L := L) F ih) q

@[simp] theorem fullTermToSupport_supportTermToFull {s t : L.Sorts}
    (q : CCO.UnarySupport.Structure.Term L s t) :
    fullTermToSupport L hbin (supportTermToFull L hbin q) = q := by
  induction q with
  | var => rfl
  | func F q ih => exact congrArg (CCO.UnarySupport.Structure.Term.func F) ih

@[simp] theorem supportTermToFull_fullTermToSupport {s t : L.Sorts}
    (q : CCO.FullCode.Term (binaryLanguage L hbin) s t) :
    supportTermToFull L hbin (fullTermToSupport L hbin q) = q := by
  exact CCO.FullCode.Term.rec (L := binaryLanguage L hbin)
    (motive := fun _ _ a => supportTermToFull L hbin (fullTermToSupport L hbin a) = a)
    (fun _ => rfl)
    (fun F {_} _ ih => congrArg (CCO.FullCode.Term.app (L := binaryLanguage L hbin) F) ih) q

theorem supportTermToFull_eval {V : Type v} (C : CCO.UnarySupport.Structure L V)
    {s t : L.Sorts} (q : CCO.UnarySupport.Structure.Term L s t) (x : V) :
    (supportTermToFull L hbin q).eval (binaryStructure L hbin C) x = C.eval q x := by
  induction q with
  | var => rfl
  | func F q ih =>
    change {y | ∃ z, z ∈ (supportTermToFull L hbin q).eval (binaryStructure L hbin C) x ∧
      y ∈ C.func F z} = _
    rw [ih]
    rfl

section Fresh
variable (U : CCO.UnaryFreshFrames.Language.{u})
variable [Finite U.Sorts] [Finite U.Func] [Finite U.Rel]
variable (hU : ∀ R, U.arity R = 2)

def freshTermToFull {s t : U.Sorts} (q : CCO.UnaryFreshFrames.Term U s t) :
    CCO.FullCode.Term (binaryLanguage (CCO.HiddenSAPReadings.partialSignature U) hU) s t :=
  CCO.UnaryFreshFrames.Term.rec (L := U)
    (motive := fun t _ => CCO.FullCode.Term
      (binaryLanguage (CCO.HiddenSAPReadings.partialSignature U) hU) s t)
    (CCO.FullCode.Term.id (L := binaryLanguage (CCO.HiddenSAPReadings.partialSignature U) hU) s)
    (fun F _ ih => CCO.FullCode.Term.app
      (L := binaryLanguage (CCO.HiddenSAPReadings.partialSignature U) hU) F ih) q

def fullTermToFresh {s t : U.Sorts}
    (q : CCO.FullCode.Term (binaryLanguage (CCO.HiddenSAPReadings.partialSignature U) hU) s t) :
    CCO.UnaryFreshFrames.Term U s t :=
  CCO.FullCode.Term.rec (L := binaryLanguage (CCO.HiddenSAPReadings.partialSignature U) hU)
    (motive := fun s t _ => CCO.UnaryFreshFrames.Term U s t)
    (fun s => CCO.UnaryFreshFrames.Term.id (L := U) s)
    (fun F {s} _ ih => CCO.UnaryFreshFrames.Term.func (L := U) F ih) q

@[simp] theorem fullTermToFresh_freshTermToFull {s t : U.Sorts}
    (q : CCO.UnaryFreshFrames.Term U s t) :
    fullTermToFresh U hU (freshTermToFull U hU q) = q := by
  induction q with
  | id => rfl
  | func F q ih => exact congrArg (CCO.UnaryFreshFrames.Term.func F) ih

@[simp] theorem freshTermToFull_fullTermToFresh {s t : U.Sorts}
    (q : CCO.FullCode.Term (binaryLanguage (CCO.HiddenSAPReadings.partialSignature U) hU) s t) :
    freshTermToFull U hU (fullTermToFresh U hU q) = q := by
  exact CCO.FullCode.Term.rec (L := binaryLanguage (CCO.HiddenSAPReadings.partialSignature U) hU)
    (motive := fun _ _ a => freshTermToFull U hU (fullTermToFresh U hU a) = a)
    (fun _ => rfl)
    (fun F {_} _ ih => congrArg (CCO.FullCode.Term.app
      (L := binaryLanguage (CCO.HiddenSAPReadings.partialSignature U) hU) F) ih) q

/-- On the declared input sort, graph evaluation is EXACTLY the actual
total named evaluation. Off-sort identities are never displayed graphs. -/
theorem freshTermToFull_eval {V : Type v} (C : CCO.UnaryFreshFrames.Structure U V)
    {s t : U.Sorts} (q : CCO.UnaryFreshFrames.Term U s t) (x y : V) (hx : C.sort x = s) :
    y ∈ (freshTermToFull U hU q).eval
      (binaryStructure (CCO.HiddenSAPReadings.partialSignature U) hU
        (CCO.HiddenSAPReadings.partialTarget C)) x ↔ y = C.eval q x := by
  induction q generalizing y with
  | id => rfl
  | func F q ih =>
    change (∃ z, z ∈ (freshTermToFull U hU q).eval
      (binaryStructure (CCO.HiddenSAPReadings.partialSignature U) hU
        (CCO.HiddenSAPReadings.partialTarget C)) x ∧
        y ∈ (CCO.HiddenSAPReadings.partialTarget C).func F z) ↔ _
    have hs : C.sort (C.eval q x) = U.input F := C.eval_sort q hx
    constructor
    · rintro ⟨z,hz,hy⟩
      have he := (ih z).mp hz
      subst z
      simpa only [CCO.HiddenSAPReadings.partialTarget,if_pos hs,Set.mem_singleton_iff,CCO.UnaryFreshFrames.Structure.eval] using hy
    · intro hy
      refine ⟨C.eval q x,(ih _).mpr rfl,?_⟩
      simpa only [CCO.HiddenSAPReadings.partialTarget,if_pos hs,Set.mem_singleton_iff,CCO.UnaryFreshFrames.Structure.eval] using hy

end Fresh
end
end CCO.TerminalHiddenHN
