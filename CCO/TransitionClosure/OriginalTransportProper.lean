import CCO.TransitionClosure.OriginalSAPTransportNoncollapse
import CCO.QuotientTransport.Lattice

/-!
# B049 source07 C25-C30: actual proper quotient targets

The already accepted B040 canonical quotient map is a bijection.
Here properness (not Top) is proved directly from the literal
surjective source relation and the equality of canonical labels.
This proof is independent of original SAP. By contrast the previously
proved original-source SAP lemma excludes equality (Id) at the
target, and both obligations are kept separate before hidden
coordinate naming.

No quotient SAP, hidden SAP, NR2, CCO or named RAW-exactness is
inferred from invariant quotient transport.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {G : Type t} [Group G]
variable {A : Type v} {B : Type w} [MulAction G A] [MulAction G B]

open CCO.QuotientTransport

/-- The FULL invariant target of the actual canonical B040
transport is proper whenever its actual source is proper.
This is genuine NOT-TOP, rather than nonidentity. No SAP,
CCO or quotient-level homogeneity is needed. -/
theorem original_transport_target_proper
    {E : InvEq G A} {R : Rel A B}
    (T : Transport E R) (hE : E ≠ ⊤) :
    T.target ≠ ⊤ := by
  intro hF
  apply hE
  apply InvEq.ext
  intro x x'
  constructor
  · intro _
    exact (InvEq.top_apply x x').mpr trivial
  · intro _
    obtain ⟨y,hy⟩ := T.serial x
    obtain ⟨y',hy'⟩ := T.serial x'
    have hTarget : T.target y y' := by
      rw [hF]
      exact (InvEq.top_apply y y').mpr trivial
    have hLabel : T.label y = T.label y' := hTarget
    rw [T.label_edge hy, T.label_edge hy'] at hLabel
    exact Quotient.exact hLabel

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original

/-- The original FULL finite-colour J is proper as a B040
invariant source if and only if it is proper in the full
original ColourEq lattice. Both compare ACTUAL real pairs;
no represented-exact sublattice is involved. -/
theorem original_colourEq_proper_as_invariant
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (hJ : J ≠ ⊤) :
    originalColourEqAsInvEq S H J ≠ ⊤ := by
  intro hE
  apply hJ
  apply ColourEq.ext
  intro x y
  have hTop : (originalColourEqAsInvEq S H J) x y := by
    rw [hE]
    exact (InvEq.top_apply x y).mpr trivial
  exact ⟨fun _ => trivial,fun _ => hTop⟩

/-- Real ORIGINAL source instance with both required strict
inequalities on the canonically transported target F:
F ≠ Top follows from a proper original J and B040;
F > Id follows separately from original old SAP and J > Id.

The quotient carriers, nonempty original typed RAW relation
R, its literal RAW R;Rᵒᵖ kernel bound, and SAME original group
action are all displayed. The source theorem does NOT assert
that F is already a terminal RAW-represented named quotient.
-/
theorem original_source_transport_target_proper_nonidentity
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (J : ColourEq S i)
    (hJbot : (⊥ : ColourEq S i) < J)
    (hJtop : J < (⊤ : ColourEq S i))
    (R : Rel (X i) (X j))
    (hInv : Invariant (G := G) R)
    (hNonempty : ∃ x : X i, ∃ y : X j, R x y)
    (hKernel : ∀ x x' : X i,
      compose R (converse R) x x' → J x x') :
    ∃ T : Transport (originalColourEqAsInvEq S H J) R,
      T.target ≠ ⊤ ∧
      (∃ y z : X j, T.target y z ∧ y ≠ z) := by
  obtain ⟨T, hNonId⟩ :=
    original_source_transport_nonidentity_target
      S H sap J hJbot R hInv hNonempty hKernel
  have hProper : (originalColourEqAsInvEq S H J) ≠ ⊤ :=
    original_colourEq_proper_as_invariant S H J (ne_of_lt hJtop)
  exact ⟨T,original_transport_target_proper T hProper,hNonId⟩

end CCO.TransitionClosure
