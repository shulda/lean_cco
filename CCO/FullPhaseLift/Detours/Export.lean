import CCO.FullPhaseLift.Detours.CanonicalGadgets

/-! B048 C17 source export. Both actual path choices carry the SAME
all-arity signed full edge data, their root pair is unspecified, and ALL
possible STRONG outputs satisfy the requested endpoint phases. -/
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

/-- Full and STRONG conclusions are separate fields; no cylinder is
postulated exact or reachable, and no quotient identity is a diversity atom. -/
def Certified : Prop :=
  SignedPathCertificate U W.fullPoint W.fullDiagram ∧
  a ∈ PositiveWord.profile (Canonical.source U hsym) W.word ∧
  PositiveWord.profile (Canonical.source U hsym) W.word ⊆ {d | P.allows (some d) ε η} ∧
  W.diagram.edge 0 3 (by decide) = none ∧
  ∀ x y, PositiveWord.represented (Canonical.source U hsym) W.word x y →
    cylinder (Canonical.source U hsym) (Reached.kernel H C b) (Reached.kernel H C c) a x y

theorem certified (sap : AgeSAP (Canonical.source U hsym)) : W.Certified :=
  ⟨fullPath_certificate U W.fullEmbedding (by decide),W.root_mem_profile sap,
    W.phase_safe sap,W.root_unspecified,W.represented_bound⟩
end ActivePath

namespace InactivePath
variable {i j : UnaryName U} {a : (Canonical.source U hsym).Atom i j} {ε η : Bit}
variable (W : InactivePath P i j a ε η)

def Certified : Prop :=
  SignedPathCertificate U W.fullPoint W.fullDiagram ∧
  a ∈ PositiveWord.profile (Canonical.source U hsym) W.word ∧
  PositiveWord.profile (Canonical.source U hsym) W.word ⊆ {d | P.allows (some d) ε η} ∧
  W.diagram.edge 0 2 (by decide) = none

theorem certified : W.Certified :=
  ⟨fullPath_certificate U W.fullEmbedding (by decide),W.root_mem_profile,
    W.phase_safe,W.root_unspecified⟩
end InactivePath

/-- Root-free phase-safe private detours for the ACTUAL canonical source.
The allowed root atom is distinct-point and all internal FORMAL vertices
are fresh line indices. No full-old SAP or marked-source SAP is assumed.
The working full table U can be the canonical definitional expansion. -/
theorem root_free_phase_safe (P : SourcePhase (Canonical.source U hsym) H C A)
    (sap : AgeSAP (Canonical.source U hsym)) {i j : UnaryName U}
    (a : (Canonical.source U hsym).Atom i j) (ε η : Bit)
    (ha : P.allows (some a) ε η) :
    (∃ (hi : Nonempty (Bridge (Canonical.source U hsym) A i))
       (hj : Nonempty (Bridge (Canonical.source U hsym) A j))
       (W : ActivePath P ⟨i,hi⟩ ⟨j,hj⟩ a ε η), W.Certified) ∨
    (∃ W : InactivePath P i j a ε η, W.Certified) := by
  obtain h | h := exists_phase_safe_detour P sap a ε η ha
  · obtain ⟨hi,hj,⟨W⟩⟩ := h
    exact Or.inl ⟨hi,hj,W,W.certified sap⟩
  · obtain ⟨W⟩ := h
    exact Or.inr ⟨W,W.certified⟩

end
end CCO.FullPhaseLift.Detours
