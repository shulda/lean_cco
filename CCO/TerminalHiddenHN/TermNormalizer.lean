import CCO.TerminalHiddenHN.SemanticFunctions
import Mathlib.Data.Fintype.EquivFin

/-! A finite list of genuine typed terms represents every actual semantic
function, including identity and applicable compositions. The enumeration
is by FUNCTIONS at each exact input/output sort, never by syntactic words. -/

universe u v w r
namespace CCO.TerminalHiddenHN
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))

def termFunctionCount (s t : (Lang S H sap hCover).Sorts) : ℕ :=
  Fintype.card (TermFunctionSet S H sap hCover s t)

def termFunctionEnumeration (s t : (Lang S H sap hCover).Sorts) :
    TermFunctionSet S H sap hCover s t ≃ Fin (termFunctionCount S H sap hCover s t) :=
  Fintype.equivFin _

def normalTerm (s t : (Lang S H sap hCover).Sorts)
    (k : Fin (termFunctionCount S H sap hCover s t)) :
    CCO.UnaryFreshFrames.Term (Lang S H sap hCover) s t :=
  termFunctionRepresentative S H sap hCover
    ((termFunctionEnumeration S H sap hCover s t).symm k)

def normalTermIndex {s t : (Lang S H sap hCover).Sorts}
    (q : CCO.UnaryFreshFrames.Term (Lang S H sap hCover) s t) :
    Fin (termFunctionCount S H sap hCover s t) :=
  termFunctionEnumeration S H sap hCover s t
    ⟨(Hidden S H sap hCover).termFunction q,⟨q,rfl⟩⟩

theorem normalTerm_function {s t : (Lang S H sap hCover).Sorts}
    (q : CCO.UnaryFreshFrames.Term (Lang S H sap hCover) s t) :
    (Hidden S H sap hCover).termFunction
        (normalTerm S H sap hCover s t (normalTermIndex S H sap hCover q)) =
      (Hidden S H sap hCover).termFunction q := by
  exact (termFunctionRepresentative_spec S H sap hCover _).trans
    (congrArg Subtype.val ((termFunctionEnumeration S H sap hCover s t).symm_apply_apply
      ⟨(Hidden S H sap hCover).termFunction q,⟨q,rfl⟩⟩))

/-- The same one normal form works at EVERY input point of its hidden
sort, including proper quotient inputs with no real root in a finite host. -/
theorem normalTerm_eval {s t : (Lang S H sap hCover).Sorts}
    (q : CCO.UnaryFreshFrames.Term (Lang S H sap hCover) s t)
    (x : Values S H) (hx : (Hidden S H sap hCover).sort x = s) :
    (Hidden S H sap hCover).eval q x =
      (Hidden S H sap hCover).eval
        (normalTerm S H sap hCover s t (normalTermIndex S H sap hCover q)) x := by
  exact (congrFun (normalTerm_function S H sap hCover q) ⟨x,hx⟩).symm

theorem normal_identity_eval (s : (Lang S H sap hCover).Sorts)
    (x : Values S H) (hx : (Hidden S H sap hCover).sort x = s) :
    (Hidden S H sap hCover).eval
      (normalTerm S H sap hCover s s
        (normalTermIndex S H sap hCover (CCO.UnaryFreshFrames.Term.id s))) x = x :=
  (normalTerm_eval S H sap hCover (CCO.UnaryFreshFrames.Term.id s) x hx).symm

end
end CCO.TerminalHiddenHN
