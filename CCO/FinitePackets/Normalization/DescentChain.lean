import CCO.FinitePackets.Normalization.DescentSource
import CCO.FinitePackets.Normalization.TerminalThin
import CCO.StrongExact.TriangleFullness

/-!
# Finite chains of actual source-preserving exact quotients

Termination measures the diversity palette of the CURRENT source at every
step. The constructors record literal quotients, their exact finite kernels,
and all inherited source data. A terminal source needs no quotient step.
-/

universe v w t z

namespace CCO.FinitePackets.Normalization

open CCO.ParityHasse.Original CCO.FinitePackets.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

theorem noFiniteExactKernel_iff :
    NoFiniteExactKernel S ↔ IsEmpty (FiniteExactKernel S) := by
  constructor
  · intro h
    exact ⟨fun K => K.proper (h K.kernel K.finite K.exact K.represents)⟩
  · intro h K hfin B hB
    by_contra hK
    exact h.false ⟨K, hfin, B, hB, hK⟩

variable {G : Type t} [Group G]

namespace SourceNode

noncomputable def palette (N : SourceNode.{v,t} G) : Nat := Nat.card (N.source.Atom () ())

/-- Ordinary AP is inherited at every node from its proved tuple homogeneity. -/
theorem amalgamation (N : SourceNode.{v,t} G) : AgeAP N.source :=
  AtomicSource.ageAP_of_homogeneous N.homogeneous

/-- Triangle fullness at every node, with the actual complete diagram and
arbitrary finite vertex universe. No SAP preservation is asserted. -/
theorem triangles (N : SourceNode.{v,t} G) {V : Type z}
    (A : CompleteDiagram (S := N.source) V) (hsmall : A.SmallRealizable) :
    ∃ f : DiagramHom A.diagram, f.IsInjective :=
  A.triangleFullness_of_homogeneous_CCO N.homogeneous
    (semanticCCO_change_universe N.source N.cycles) hsmall

noncomputable def next (N : SourceNode.{v,t} G) (K : FiniteExactKernel N.source) :
    SourceNode.{v,t} G :=
  quotientNode N.source N.homogeneous N.cycles K

theorem palette_next_lt (N : SourceNode.{v,t} G) (K : FiniteExactKernel N.source) :
    (N.next K).palette < N.palette :=
  exactQuotient_palette_lt N.source N.homogeneous N.cycles K

/-- Each successor is definitionally the ACTUAL exact quotient of the
preceding node, with inherited source properties rather than an opaque law. -/
inductive Chain : SourceNode.{v,t} G → SourceNode.{v,t} G → Nat → Type (max (v + 1) t)
  | refl (N : SourceNode.{v,t} G) : Chain N N 0
  | step (N : SourceNode.{v,t} G) (K : FiniteExactKernel N.source)
      {T : SourceNode.{v,t} G} {n : Nat} (tail : Chain (N.next K) T n) :
      Chain N T (n + 1)

/-- The map of a chain is the literal composite of its actual quotient maps. -/
noncomputable def Chain.projection {N T : SourceNode.{v,t} G} {n : Nat} :
    Chain N T n → N.Carrier → T.Carrier
  | .refl _ => id
  | .step _ _ tail => tail.projection ∘ Quotient.mk''

theorem Chain.projection_surjective {N T : SourceNode.{v,t} G} {n : Nat}
    (chain : Chain N T n) : Function.Surjective chain.projection := by
  induction chain with
  | refl N => exact Function.surjective_id
  | step N K tail ih => exact ih.comp Quotient.mk''_surjective

theorem Chain.projection_equivariant {N T : SourceNode.{v,t} G} {n : Nat}
    (chain : Chain N T n) (g : G) (x : N.Carrier) :
    chain.projection (g • x) = g • chain.projection x := by
  induction chain with
  | refl N => rfl
  | step N K tail ih => exact ih (Quotient.mk'' x)

/-- Every countable actual source node has a finite literal quotient chain
to an exact-kernel-free source, of length bounded by its initial palette. -/
theorem finite_normalization (N : SourceNode.{v,t} G) :
    ∃ T : SourceNode.{v,t} G, ∃ n : Nat,
      Nonempty (Chain N T n) ∧ NoFiniteExactKernel T.source ∧ n ≤ N.palette := by
  classical
  generalize h : N.palette = d
  induction d using Nat.strong_induction_on generalizing N with
  | h d ih =>
    by_cases hterm : NoFiniteExactKernel N.source
    · exact ⟨N, 0, ⟨Chain.refl N⟩, hterm, Nat.zero_le _⟩
    · have hn : Nonempty (FiniteExactKernel N.source) := by
        by_contra hn
        have he : IsEmpty (FiniteExactKernel N.source) :=
          ⟨fun K => hn ⟨K⟩⟩
        exact hterm ((noFiniteExactKernel_iff N.source).mpr he)
      obtain ⟨K⟩ := hn
      have hdrop : (N.next K).palette < d := (N.palette_next_lt K).trans_eq h
      obtain ⟨T, n, ⟨tail⟩, ht, hlen⟩ := ih _ hdrop (N.next K) rfl
      refine ⟨T, n + 1, ⟨Chain.step N K tail⟩, ht, ?_⟩
      omega

/-- A singleton node cannot have a nonidentity invariant kernel; it is
already terminal and admits a genuine zero-length normalization. -/
theorem singleton_terminal (N : SourceNode.{v,t} G) [Subsingleton N.Carrier] :
    NoFiniteExactKernel N.source := by
  intro K _ _ _
  apply ColourEq.ext
  intro x y
  change K x y ↔ x = y
  exact ⟨fun _ => Subsingleton.elim _ _, fun h => h ▸ K.val.refl x⟩

/-- The terminal finite bottom is thin as a consequence of normalization,
not as a substitute stopping condition. The converse is not asserted. -/
theorem finite_normalization_thin (N : SourceNode.{v,t} G) :
    ∃ T : SourceNode.{v,t} G, ∃ n : Nat,
      Nonempty (Chain N T n) ∧ NoFiniteExactKernel T.source ∧
        ThinBottom T.source (sigma T.source T.homogeneous ⊥) ∧ n ≤ N.palette := by
  obtain ⟨T, n, hchain, ht, hlen⟩ := N.finite_normalization
  exact ⟨T, n, hchain, ht,
    terminal_greatest_finite_packet_thin T.source T.homogeneous ht, hlen⟩

end SourceNode

variable [MulAction G M] (H : HomogeneousSource S G)

/-- General initial palettes need not live in the carrier universe. The
first actual quotient enters the fixed carrier-universe tail; the zero-step
case retains the original source literally, with no recoding of its palette. -/
theorem finite_exact_normalization [Countable M]
    (cco : SemanticCCO.{0,v,v,w} S) :
    NoFiniteExactKernel S ∨
      ∃ K : FiniteExactKernel S, ∃ T : SourceNode.{v,t} G, ∃ n : Nat,
        Nonempty (SourceNode.Chain (quotientNode S H cco K) T n) ∧
        NoFiniteExactKernel T.source ∧ n + 1 ≤ Nat.card (S.Atom () ()) := by
  classical
  by_cases hterm : NoFiniteExactKernel S
  · exact Or.inl hterm
  · right
    have hn : Nonempty (FiniteExactKernel S) := by
      by_contra hn
      have he : IsEmpty (FiniteExactKernel S) := ⟨fun K => hn ⟨K⟩⟩
      exact hterm ((noFiniteExactKernel_iff S).mpr he)
    obtain ⟨K⟩ := hn
    obtain ⟨T, n, hchain, ht, hlen⟩ := SourceNode.finite_normalization (quotientNode S H cco K)
    refine ⟨K, T, n, hchain, ht, ?_⟩
    have hdrop := exactQuotient_palette_lt S H cco K
    change n ≤ Nat.card ((exactQuotientSource S H K).Atom () ()) at hlen
    omega

/-- The complete geometric normalization export for an arbitrary initial
palette universe: an actual zero-step source or a finite quotient chain
ending at an exact-kernel-free source with thin greatest finite packet. -/
theorem finite_exact_normalization_thin [Countable M]
    (cco : SemanticCCO.{0,v,v,w} S) :
    (NoFiniteExactKernel S ∧ ThinBottom S (sigma S H ⊥)) ∨
      ∃ K : FiniteExactKernel S, ∃ T : SourceNode.{v,t} G, ∃ n : Nat,
        Nonempty (SourceNode.Chain (quotientNode S H cco K) T n) ∧
        NoFiniteExactKernel T.source ∧
        ThinBottom T.source (sigma T.source T.homogeneous ⊥) ∧
        n + 1 ≤ Nat.card (S.Atom () ()) := by
  obtain ht | ⟨K, T, n, hchain, ht, hlen⟩ := finite_exact_normalization S H cco
  · exact Or.inl ⟨ht, terminal_greatest_finite_packet_thin S H ht⟩
  · exact Or.inr ⟨K, T, n, hchain, ht,
      terminal_greatest_finite_packet_thin T.source T.homogeneous ht, hlen⟩

end CCO.FinitePackets.Normalization
