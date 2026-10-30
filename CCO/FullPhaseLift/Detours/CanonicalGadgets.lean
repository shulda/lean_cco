import CCO.FullPhaseLift.Detours.Gadgets
import CCO.FullPhaseLift.Detours.Support
import CCO.FullPhaseLift.Canonical.Source

/-! Actual full signed detours for the ONE canonical all-arity language.
The working table U may already be the canonical definitional expansion.
The source witness and each complete edge factor use the SAME old values. -/
set_option backward.isDefEq.respectTransparency.types false
universe v t
namespace CCO.FullPhaseLift.Detours
open APCharacter RigidGroupoid.Geometry Canonical
noncomputable section
variable {L : Signature} {M : Type v} {U : BoolTable L M} {hsym : SameSortSymmetric U}
variable {G : Type t} [Group G] [∀ i, MulAction G (Carrier U i)]
variable {H : HomogeneousSource (Canonical.source U hsym) G}
variable {C : ExactCalculus (Canonical.source U hsym)} {r : UnaryName U}
variable {A : Kernel (Canonical.source U hsym) r}
variable {P : SourcePhase (Canonical.source U hsym) H C A}

namespace ActivePath
variable {b c : Reached (Canonical.source U hsym) A}
variable {a : (Canonical.source U hsym).Atom b.val c.val} {ε η : Bit}
variable (W : ActivePath P b c a ε η)

def fullPoint : Fin 4 → M := (pack U).symm ∘ W.point

def fullEmbedding : Fin 4 ↪ M :=
  ⟨W.fullPoint,(pack U).symm.injective.comp W.distinct⟩

def fullDiagram : Full.Partial L (Fin 4) := fullPath U W.fullPoint

theorem fullRealizes : Full.Realizes U W.fullDiagram W.fullPoint := fullPath_realizes U W.fullPoint

theorem fullConsistent : Full.Consistent U W.fullDiagram := fullPath_consistent U W.fullEmbedding

def edgeFactors : Fin 3 → Full.FrozenFactor U W.fullDiagram := edgeFactor U W.fullEmbedding

theorem fullHigherCovered : Full.HigherCovered W.edgeFactors := fullPath_higherCovered U W.fullEmbedding

theorem fullHighNone (r : Fin L.size) (xs : Fin (L.arity r) → Fin 4)
    (hs : ¬Full.SmallSupport xs) : W.fullDiagram r xs = none :=
  fullPath_high_none U W.fullPoint r xs hs

theorem fullRootPairNone (r : Fin L.size) (xs : Fin (L.arity r) → Fin 4)
    (hx : ∃ a, xs a = 0) (hy : ∃ b, xs b = 3) : W.fullDiagram r xs = none :=
  fullPath_root_pair_none U W.fullPoint (by decide) r xs hx hy

/-- Every original signed tuple on any retained edge is read literally,
including repeated-coordinate tests at arbitrarily large original arity. -/
theorem fullEdge (e : Fin 3) (r : Fin L.size) (xs : Fin (L.arity r) → Fin 2) :
    W.fullDiagram r (edgeVertex e ∘ xs) = some (U r (W.fullPoint ∘ edgeVertex e ∘ xs)) :=
  fullPath_edge U W.fullPoint e r xs

theorem leftProfile : profile U (W.fullPoint ∘ edgeVertex (0 : Fin 3)) = W.left.val := by
  have hp : W.fullPoint ∘ edgeVertex (0 : Fin 3) = ![W.x.val,W.u.val] := by
    funext k
    fin_cases k <;> rfl
  rw [hp]
  exact ((Canonical.colour_some_iff U W.x W.u W.left).mp W.left_colour).2

theorem middleProfile : profile U (W.fullPoint ∘ edgeVertex (1 : Fin 3)) = W.middle.val := by
  have hp : W.fullPoint ∘ edgeVertex (1 : Fin 3) = ![W.u.val,W.v.val] := by
    funext k
    fin_cases k <;> rfl
  rw [hp]
  exact ((Canonical.colour_some_iff U W.u W.v W.middle).mp W.middle_colour).2

theorem rightProfile : profile U (W.fullPoint ∘ edgeVertex (2 : Fin 3)) = W.right.val := by
  have hp : W.fullPoint ∘ edgeVertex (2 : Fin 3) = ![W.v.val,W.y.val] := by
    funext k
    fin_cases k <;> rfl
  rw [hp]
  exact ((Canonical.colour_some_iff U W.v W.y W.right).mp W.right_colour).2
end ActivePath

namespace InactivePath
variable {i j : UnaryName U} {a : (Canonical.source U hsym).Atom i j} {ε η : Bit}
variable (W : InactivePath P i j a ε η)

def fullPoint : Fin 3 → M := (pack U).symm ∘ W.point

def fullEmbedding : Fin 3 ↪ M :=
  ⟨W.fullPoint,(pack U).symm.injective.comp W.distinct⟩

def fullDiagram : Full.Partial L (Fin 3) := fullPath U W.fullPoint

theorem fullRealizes : Full.Realizes U W.fullDiagram W.fullPoint := fullPath_realizes U W.fullPoint

theorem fullConsistent : Full.Consistent U W.fullDiagram := fullPath_consistent U W.fullEmbedding

def edgeFactors : Fin 2 → Full.FrozenFactor U W.fullDiagram := edgeFactor U W.fullEmbedding

theorem fullHigherCovered : Full.HigherCovered W.edgeFactors := fullPath_higherCovered U W.fullEmbedding

theorem fullHighNone (r : Fin L.size) (xs : Fin (L.arity r) → Fin 3)
    (hs : ¬Full.SmallSupport xs) : W.fullDiagram r xs = none :=
  fullPath_high_none U W.fullPoint r xs hs

theorem fullRootPairNone (r : Fin L.size) (xs : Fin (L.arity r) → Fin 3)
    (hx : ∃ a, xs a = 0) (hy : ∃ b, xs b = 2) : W.fullDiagram r xs = none :=
  fullPath_root_pair_none U W.fullPoint (by decide) r xs hx hy

theorem fullEdge (e : Fin 2) (r : Fin L.size) (xs : Fin (L.arity r) → Fin 2) :
    W.fullDiagram r (edgeVertex e ∘ xs) = some (U r (W.fullPoint ∘ edgeVertex e ∘ xs)) :=
  fullPath_edge U W.fullPoint e r xs

theorem leftProfile : profile U (W.fullPoint ∘ edgeVertex (0 : Fin 2)) = W.left.val := by
  have hp : W.fullPoint ∘ edgeVertex (0 : Fin 2) = ![W.x.val,W.z.val] := by
    funext k
    fin_cases k <;> rfl
  rw [hp]
  exact ((Canonical.colour_some_iff U W.x W.z W.left).mp W.left_colour).2

theorem rightProfile : profile U (W.fullPoint ∘ edgeVertex (1 : Fin 2)) = W.right.val := by
  have hp : W.fullPoint ∘ edgeVertex (1 : Fin 2) = ![W.z.val,W.y.val] := by
    funext k
    fin_cases k <;> rfl
  rw [hp]
  exact ((Canonical.colour_some_iff U W.z W.y W.right).mp W.right_colour).2
end InactivePath

end
end CCO.FullPhaseLift.Detours
