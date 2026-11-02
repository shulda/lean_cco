import CCO.TransitionClosure.OriginalStrongWholeTransitionGraph

/-!
# B049 source07 C49/QT-Graph: original real-pair type tests the FULL quotient graph

For the literal B040 canonical transition R:a→b with source original
FULL J and target K=Rᵒᵖ;J;R, take ANY old REAL diversity pair x,y of
genuine fine type c. Then the following tests are equivalent:

1. the real old J/K classes of x,y are matched by the B040 bijection;
2. c belongs to the FULL old diversity spectrum of the RAW J;R;K
   sandwich (including possible old equality exterior steps).

The forward implication is the actual B040 quotient-edge law.
For the reverse implication one obtains a real witness of the RAW
sandwich at a possibly different old pair u,v of the SAME colour c.
ONE original homogeneous G motion aligns u,v with x,y; the full
original invariant J,K and R transport along this SAME motion,
so x,y itself is in the literal RAW sandwich. No independent
quotient action, quotient SAP/CCO, hidden completion or synthetic
STRONG identity is used.

Under original SAP, nonzero proper J and identity-free nonempty R,
the already compiled source07 C47 formula identifies that RAW
spectrum with the WHOLE genuine positive STRONG composition
J° * R° * K°, yielding precisely the source's real-pair
QT-Graph iff condition. The hidden equal-coordinate diagonal
remains a separate logical quotient equality test.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.QuotientTransport
open CCO.TerminalLattice

/-- Complete C49 real original representative test for the actual
FULL RAW J;R;K graph. Every old fine type c with an actual old
c-representative pair x,y characterizes the WHOLE canonical
quotient graph. No old SAP, old CCO, terminal NR2 or assumed
quotient group is needed for this RAW form. -/
theorem original_full_transport_graph_iff_real_pair_raw_spectrum
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (x : X i) (y : X j) (c : S.Atom i j)
    (hxy : S.colour x y = some c) :
    T.quotientEquiv (Quotient.mk J.val x) =
        Quotient.mk (originalTransportTargetColourEq S H J T).val y ↔
      c ∈ S.diversityGuard (originalRawFullTypedSandwich S J
        (originalTransportTargetColourEq S H J T) R) := by
  let K : ColourEq S j := originalTransportTargetColourEq S H J T
  constructor
  · intro hGraph
    have hRaw : originalRawFullTypedSandwich S J K R x y :=
      (original_raw_full_transport_sandwich_iff_graph S H J T x y).mpr hGraph
    exact ⟨x,y,hRaw,hxy⟩
  · rintro ⟨u,v,hRaw,huv⟩
    obtain ⟨g,hgu,hgv⟩ :=
      S.pair_homogeneous_of_homogeneous H
        u x v y (huv.trans hxy.symm)
    obtain ⟨p,q,hJup,hRpq,hKqv⟩ := hRaw
    have hJMove : J (g • u) (g • p) :=
      (colourInvariant_groupInvariant S H J.property) g u p hJup
    have hKMove : K (g • q) (g • v) :=
      (colourInvariant_groupInvariant S H K.property) g q v hKqv
    have hRawXY : originalRawFullTypedSandwich S J K R x y := by
      refine ⟨g • p,g • q,?_,T.invariant g p q hRpq,?_⟩
      · simpa only [hgu] using hJMove
      · simpa only [hgv] using hKMove
    exact (original_raw_full_transport_sandwich_iff_graph
      S H J T x y).mp hRawXY

/-- Exact original source07 C49/QT-Graph STRONG form:
a real old atomic representative pair x,y has its old fine type
inside the FULL positive STRONG graph profile J°*R°*K° iff
the actual B040 quotient transition maps [x]_J to [y]_K.
Here source J is proper and nonzero, and ANY true old
diversity atom a in the identity-free R supplies the real
source condition, not an assumed positive presentation of
the whole many-atom relation R. -/
theorem original_full_transport_graph_iff_real_pair_strong_whole
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (J : ColourEq S i)
    (hJbot : (⊥ : ColourEq S i) < J)
    (hJtop : J < (⊤ : ColourEq S i))
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (a : S.Atom i j) (ha : a ∈ S.diversityGuard R)
    (x : X i) (y : X j) (c : S.Atom i j)
    (hxy : S.colour x y = some c) :
    T.quotientEquiv (Quotient.mk J.val x) =
        Quotient.mk (originalTransportTargetColourEq S H J T).val y ↔
      c ∈ S.product (originalEquivDiversityPalette S J)
        (S.product (S.diversityGuard R)
          (originalEquivDiversityPalette S
            (originalTransportTargetColourEq S H J T))) := by
  rw [← original_full_transport_raw_guard_eq_strong_whole
    S H sap J hJbot hJtop T a ha]
  exact original_full_transport_graph_iff_real_pair_raw_spectrum
    S H J T x y c hxy

end CCO.TransitionClosure
