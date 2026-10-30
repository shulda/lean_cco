import CCO.FullPhaseLift.Detours.Paths
import CCO.FullPhaseLift.Detours.BinaryPath

/-! Literal root-free binary path gadgets. Internal vertices are fresh
FORMAL line indices; no chord or root edge is imported from the actual
source tuple that witnesses their consistency. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.FullPhaseLift.Detours
open APCharacter RigidGroupoid.Geometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable {P : SourcePhase S H C A}

namespace ActivePath
variable {b c : Reached S A} {a : S.Atom b.val c.val} {ε η : Bit}
variable (W : ActivePath P b c a ε η)

def diagram : PartialDiagram S (Fin 4) := binaryPath W.point

theorem root_unspecified : W.diagram.edge 0 3 (by decide) = none :=
  binaryPath_root_unspecified W.point (by decide) (by decide)

def actual_realization : DiagramHom W.diagram := binaryPath_realization W.point

theorem actual_injective : W.actual_realization.IsInjective := W.distinct

theorem legal : P.masks.LocalLegal W.diagram (W.mark ∘ W.point) :=
  binaryPath_legal W.point P.masks W.mark W.global

theorem displayed_edges :
    W.diagram.edge 0 1 (by decide) = some W.left ∧
    W.diagram.edge 1 2 (by decide) = some W.middle ∧
    W.diagram.edge 2 3 (by decide) = some W.right := by
  classical
  simpa [diagram,binaryPath,point,Adjacent] using
    And.intro W.left_colour (And.intro W.middle_colour W.right_colour)

end ActivePath

namespace InactivePath
variable {i j : ι} {a : S.Atom i j} {ε η : Bit}
variable (W : InactivePath P i j a ε η)

def diagram : PartialDiagram S (Fin 3) := binaryPath W.point

theorem root_unspecified : W.diagram.edge 0 2 (by decide) = none :=
  binaryPath_root_unspecified W.point (by decide) (by decide)

def actual_realization : DiagramHom W.diagram := binaryPath_realization W.point

theorem actual_injective : W.actual_realization.IsInjective := W.distinct

theorem legal : P.masks.LocalLegal W.diagram (W.mark ∘ W.point) :=
  binaryPath_legal W.point P.masks W.mark W.global

theorem displayed_edges : W.diagram.edge 0 1 (by decide) = some W.left ∧
    W.diagram.edge 1 2 (by decide) = some W.right := by
  classical
  simpa [diagram,binaryPath,point,Adjacent] using And.intro W.left_colour W.right_colour

end InactivePath

/-- The active case has three edges, and every other endpoint case has
two. Both constructors already contain actual global root-bit extensions,
real distinct witnesses and proved all-output phase safety. -/
theorem exists_phase_safe_detour (P : SourcePhase S H C A) (sap : AgeSAP S)
    {i j : ι} (a : S.Atom i j) (ε η : Bit) (ha : P.allows (some a) ε η) :
    (∃ (hi : Nonempty (Bridge S A i)) (hj : Nonempty (Bridge S A j)),
      Nonempty (ActivePath P ⟨i,hi⟩ ⟨j,hj⟩ a ε η)) ∨
      Nonempty (InactivePath P i j a ε η) := by
  classical
  by_cases hi : Nonempty (Bridge S A i)
  · by_cases hj : Nonempty (Bridge S A j)
    · exact Or.inl ⟨hi,hj,exists_active_path P sap ⟨i,hi⟩ ⟨j,hj⟩ a ε η ha⟩
    · exact Or.inr (exists_inactive_path P sap (Or.inr hj) a ε η ha)
  · exact Or.inr (exists_inactive_path P sap (Or.inl hi) a ε η ha)

end
end CCO.FullPhaseLift.Detours
