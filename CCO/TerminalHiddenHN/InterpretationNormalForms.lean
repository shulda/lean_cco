import CCO.TerminalHiddenHN.InterpretationFunctions
import CCO.FullCode.EmbeddingBijection
import Mathlib.Data.Fintype.EquivFin

/-! Finite normal forms at EVERY hidden input of a literal A02
interpretation. The finite family consists of actual term functions,
with exact input/output sorts. The only source hypothesis is original
homogeneity; SAP, NR2, covers and CCO do not occur in these interfaces.
Global orders change no function graph, including on orphan inputs. -/

universe u v w r l k z
namespace CCO.TerminalHiddenHN
namespace RealInterpretation
open CCO.UnaryFreshFrames
noncomputable section

variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {U : CCO.UnaryFreshFrames.Language.{max u l}} {V : Type k}
variable {P : CCO.UnaryFreshFrames.Structure U V}

/-- Keep the interpretation and source witness explicit in the data,
so the finite-family instances refer to this precise actual model. -/
def FunctionFamily (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) (s t : U.Sorts) : Set (P.Carrier s → V) :=
  {f | ∃ q : CCO.UnaryFreshFrames.Term U s t, f = P.termFunction q}

theorem functionFamily_finite (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) (s t : U.Sorts) :
    (FunctionFamily D H s t).Finite := by
  apply (namedFunctions_finite S H D s).subset
  rintro f ⟨q,hq⟩
  exact ⟨t,q,hq⟩

instance functionFamily_finiteType (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) (s t : U.Sorts) :
    Finite (FunctionFamily D H s t) :=
  (functionFamily_finite D H s t).to_subtype

noncomputable instance functionFamily_fintype (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) (s t : U.Sorts) :
    Fintype (FunctionFamily D H s t) := Fintype.ofFinite _

def functionCount (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) (s t : U.Sorts) : ℕ :=
  Fintype.card (FunctionFamily D H s t)

def functionEnumeration (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) (s t : U.Sorts) :
    FunctionFamily D H s t ≃ Fin (functionCount D H s t) :=
  Fintype.equivFin _

def functionRepresentative (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) {s t : U.Sorts} (f : FunctionFamily D H s t) :
    CCO.UnaryFreshFrames.Term U s t := Classical.choose f.property

theorem functionRepresentative_spec (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) {s t : U.Sorts} (f : FunctionFamily D H s t) :
    P.termFunction (functionRepresentative D H f) = f.val :=
  (Classical.choose_spec f.property).symm

def normalTerm (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) (s t : U.Sorts)
    (i : Fin (functionCount D H s t)) : CCO.UnaryFreshFrames.Term U s t :=
  functionRepresentative D H ((functionEnumeration D H s t).symm i)

def normalIndex (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) {s t : U.Sorts}
    (q : CCO.UnaryFreshFrames.Term U s t) : Fin (functionCount D H s t) :=
  functionEnumeration D H s t ⟨P.termFunction q,⟨q,rfl⟩⟩

theorem normalTerm_function (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) {s t : U.Sorts}
    (q : CCO.UnaryFreshFrames.Term U s t) :
    P.termFunction (normalTerm D H s t (normalIndex D H q)) = P.termFunction q := by
  exact (functionRepresentative_spec D H _).trans
    (congrArg Subtype.val ((functionEnumeration D H s t).symm_apply_apply
      ⟨P.termFunction q,⟨q,rfl⟩⟩))

theorem normalTerm_eval (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) {s t : U.Sorts}
    (q : CCO.UnaryFreshFrames.Term U s t) (x : V) (hx : P.sort x = s) :
    P.eval q x = P.eval (normalTerm D H s t (normalIndex D H q)) x :=
  (congrFun (normalTerm_function D H q) ⟨x,hx⟩).symm

theorem normal_identity_eval (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) (s : U.Sorts) (x : V) (hx : P.sort x = s) :
    P.eval (normalTerm D H s s (normalIndex D H (CCO.UnaryFreshFrames.Term.id s))) x = x :=
  (normalTerm_eval D H (CCO.UnaryFreshFrames.Term.id s) x hx).symm

def freshTermToCode (D : RealInterpretation (G := G) S U P)
    {s t : U.Sorts} (q : CCO.UnaryFreshFrames.Term U s t) :
    CCO.FullCode.Term D.binaryLanguage s t := by
  letI := D.finiteSorts
  letI := D.finiteFuncs
  letI := D.finiteRels
  exact freshTermToFull U D.binary q

def codeTermToFresh (D : RealInterpretation (G := G) S U P)
    {s t : U.Sorts} (q : CCO.FullCode.Term D.binaryLanguage s t) :
    CCO.UnaryFreshFrames.Term U s t := by
  letI := D.finiteSorts
  letI := D.finiteFuncs
  letI := D.finiteRels
  exact fullTermToFresh U D.binary q

theorem freshTermToCode_codeTermToFresh (D : RealInterpretation (G := G) S U P)
    {s t : U.Sorts} (q : CCO.FullCode.Term D.binaryLanguage s t) :
    freshTermToCode D (codeTermToFresh D q) = q := by
  letI := D.finiteSorts
  letI := D.finiteFuncs
  letI := D.finiteRels
  exact freshTermToFull_fullTermToFresh U D.binary q

theorem freshTermToCode_eval (D : RealInterpretation (G := G) S U P)
    {s t : U.Sorts} (q : CCO.UnaryFreshFrames.Term U s t)
    (x y : V) (hx : P.sort x = s) :
    y ∈ (freshTermToCode D q).eval D.binaryModel x ↔ y = P.eval q x := by
  letI := D.finiteSorts
  letI := D.finiteFuncs
  letI := D.finiteRels
  exact freshTermToFull_eval U D.binary P q x y hx

theorem codeTerm_eval (D : RealInterpretation (G := G) S U P)
    {s t : U.Sorts} (q : CCO.FullCode.Term D.binaryLanguage s t)
    (x y : V) (hx : P.sort x = s) :
    y ∈ q.eval D.binaryModel x ↔ y = P.eval (codeTermToFresh D q) x := by
  have h := freshTermToCode_eval D (codeTermToFresh D q) x y hx
  have he := freshTermToCode_codeTermToFresh D q
  have hm := Iff.of_eq (congrArg
    (fun a : CCO.FullCode.Term D.binaryLanguage s t => y ∈ a.eval D.binaryModel x) he)
  exact hm.symm.trans h

def normalForms (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) : CCO.FullCode.NormalForms D.binaryLanguage where
  count := functionCount D H
  form s t i := freshTermToCode D (normalTerm D H s t i)
  normalize q := normalIndex D H (codeTermToFresh D q)

theorem normalForms_valid (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) : (D.normalForms H).Valid D.binaryModel := by
  intro s t q x hx
  apply Set.ext
  intro y
  change y ∈ q.eval D.binaryModel x ↔
    y ∈ (freshTermToCode D
      (normalTerm D H s t (normalIndex D H (codeTermToFresh D q)))).eval D.binaryModel x
  have hleft := codeTerm_eval D q x y hx
  have heq := normalTerm_eval D H (codeTermToFresh D q) x hx
  have hright := freshTermToCode_eval D
    (normalTerm D H s t (normalIndex D H (codeTermToFresh D q))) x y hx
  exact hleft.trans ((Iff.of_eq (congrArg (fun a => y = a) heq)).trans hright.symm)

def orderedNormalForms (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) : CCO.FullCode.NormalForms D.orderedLanguage where
  count := (D.normalForms H).count
  form s t i := baseTermToOrdered D.partialSig D.binary ((D.normalForms H).form s t i)
  normalize q := (D.normalForms H).normalize (orderedTermToBase D.partialSig D.binary q)

theorem orderedNormalForms_valid_of_binary (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) {W : Type z}
    (C : CCO.UnarySupport.Structure D.partialSig W) [LinearOrder W]
    (hC : (D.normalForms H).Valid (binaryStructure D.partialSig D.binary C)) :
    (D.orderedNormalForms H).Valid (orderedStructure D.partialSig D.binary C) := by
  intro s t q x hx
  change q.eval (orderedStructure D.partialSig D.binary C) x =
    (baseTermToOrdered D.partialSig D.binary
      ((D.normalForms H).form s t
        ((D.normalForms H).normalize (orderedTermToBase D.partialSig D.binary q)))).eval
      (orderedStructure D.partialSig D.binary C) x
  rw [orderedTermToBase_eval,baseTermToOrdered_eval]
  exact hC s t (orderedTermToBase D.partialSig D.binary q) x hx

/-- Full induced embedding reflects the complete partial function
domains, so the actual finite forms inherit to any underlying member. -/
theorem normalForms_valid_of_embedding (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) {W : Type z}
    (C : CCO.UnarySupport.Structure D.partialSig W) (e : C.Embedding D.partialModel) :
    (D.normalForms H).Valid (binaryStructure D.partialSig D.binary C) :=
  CCO.FullCode.NormalForms.valid_of_embedding (D.normalForms H)
    (binaryEmbedding D.partialSig D.binary e) (D.normalForms_valid H)

/-- EVERY global order on EVERY embedded underlying member has the
same normal forms. No order embedding into a prechosen ambient order is
required, and proper quotient inputs need no real root in that host. -/
theorem orderedNormalForms_valid_of_embedding (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) {W : Type z}
    (C : CCO.UnarySupport.Structure D.partialSig W) [LinearOrder W]
    (e : C.Embedding D.partialModel) :
    (D.orderedNormalForms H).Valid (orderedStructure D.partialSig D.binary C) :=
  orderedNormalForms_valid_of_binary D H C (normalForms_valid_of_embedding D H C e)

theorem orderedNormalForms_valid (D : RealInterpretation (G := G) S U P)
    (H : HomogeneousSource S G) [LinearOrder V] :
    (D.orderedNormalForms H).Valid D.orderedModel :=
  orderedNormalForms_valid_of_binary D H D.partialModel (D.normalForms_valid H)

end
end RealInterpretation
end CCO.TerminalHiddenHN
