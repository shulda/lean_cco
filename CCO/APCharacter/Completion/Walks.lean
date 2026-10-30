import CCO.APCharacter.Completion.Identity
import CCO.RawExact.Convolution
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-! Literal specified-edge walks and their RAW endpoint words. Missing edges
are not inequalities, and the empty walk has the original logical diagonal. -/
universe u v w z
namespace CCO.APCharacter.Completion
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} (D : PartialDiagram S V)

def graph : SimpleGraph V where
  Adj x y := ∃ h : x ≠ y, ∃ a, D.edge x y h = some a
  symm.symm := by
    rintro x y ⟨h,a,ha⟩
    exact ⟨h.symm,S.conv a,(D.edge_reverse x y h a).mp ha⟩
  loopless.irrefl := by
    rintro x ⟨h,_⟩
    exact h rfl

noncomputable def edgeAtom {x y : V} (h : (graph D).Adj x y) :
    S.Atom (D.vertexSort x) (D.vertexSort y) := Classical.choose h.choose_spec

theorem edgeAtom_spec {x y : V} (h : (graph D).Adj x y) :
    D.edge x y h.choose = some (edgeAtom D h) := Classical.choose_spec h.choose_spec

theorem edgeAtom_unique {x y : V} (h : (graph D).Adj x y)
    (hne : x ≠ y) (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : D.edge x y hne = some a) : edgeAtom D h = a :=
  Option.some.inj ((edgeAtom_spec D h).symm.trans ha)

noncomputable def walkWord {x y : V} (p : (graph D).Walk x y) :
    RawWord S (D.vertexSort x) (D.vertexSort y) :=
  match p with
  | .nil => .nil _
  | .cons h p => .atom (edgeAtom D h) (walkWord p)

/-- Every actual graph homomorphism realizes every literal walk at its
SAME prescribed real endpoints. No choice of new endpoints is made. -/
theorem hom_realizes_walk (f : DiagramHom D) {x y : V}
    (p : (graph D).Walk x y) :
    RawWord.relation S (walkWord D p) (f.point x) (f.point y) := by
  induction p with
  | nil => rfl
  | @cons x z y h p ih =>
    exact ⟨f.point z,f.preserves_edge x z h.choose (edgeAtom D h)
      (edgeAtom_spec D h),ih⟩

/-- C28: one OLD homomorphism gives a common actual endpoint atom for all
simple paths (indeed for all walks), including a disconnected empty family. -/
theorem hom_common_path_endpoint (f : DiagramHom D) (x y : V) :
    ∃ a b, ∀ p : (graph D).Path x y,
      RawWord.relation S (walkWord D p.val) a b :=
  ⟨f.point x,f.point y,fun p => hom_realizes_walk D f p.val⟩

/-- Only finiteness of the old vertex set is needed to enumerate all simple
path constraints used by the completion procedure. -/
noncomputable def pathFintype (x y : V) : Fintype ((graph D).Path x y) := by
  letI : Finite V := D.finite_type
  letI := Fintype.ofFinite V
  letI : DecidableEq V := Classical.decEq V
  letI : DecidableRel (graph D).Adj := Classical.decRel _
  infer_instance

end CCO.APCharacter.Completion
