import CCO.TransitionClosure.OriginalTransitionGraphSpectrum

/-!
# B049 source07 C46: the graph of a quotient transition is ONE complete OLD G-orbital

For a true original homogeneous source S with the SAME old full
ambient group G on every named sort, let T be an actual B040
quotient transport along an original typed invariant RAW relation R.

Take ANY genuine old diversity atom a in R and an actual old
a-pair (x,y). Every pair of quotient classes on the graph of T
contains a real a-edge (the separately proved C44/C45 result).
Original homogeneous TWO-POINT transitivity transports (x,y)
to that edge by ONE actual g in the ORIGINAL group G.

Conversely, every old-G translate of the a-pair has its quotient
class pair on the graph, since original atom a is wholly inside
the real R by the accepted atomic-transport theorem.

This proves the WHOLE graph is EXACTLY ONE complete same-old-G
pair orbit, including when the two original named sorts differ.
No quotient-reduct automorphism group, hidden group action,
quotient SAP/CCO or guessed quotient homogeneity enters.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.QuotientTransport

/-- TRUE full original-G typed orbit of a pair of original
quotient-class coordinates, possibly on DIFFERENT named
original sorts. The action is always the same ORIGINAL G
acting on the REAL old representatives, never an independently
postulated quotient reduct action. -/
def originalTypedQuotientPairOldGroupOrbit
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (x : X i) (y : X j) :
    Quotient J.val → Quotient K.val → Prop :=
  fun q r => ∃ g : G,
    Quotient.mk J.val (g • x) = q ∧
    Quotient.mk K.val (g • y) = r

/-- Source07 C46 literal completeness:
a quotient pair (q,r) belongs to the graph of the
ACTUAL B040 quotient bijection iff it is an ORIGINAL-G
translate of the quotient classes of one actual a-pair.
No action on hidden quotients is inferred from their age. -/
theorem original_transport_graph_is_old_group_pair_orbit
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (a : S.Atom i j) (ha : a ∈ S.diversityGuard R)
    (x : X i) (y : X j) (hxy : S.atomRel a x y) :
    ∀ q : Quotient J.val,
      ∀ r : Quotient (originalTransportTargetColourEq S H J T).val,
      (T.quotientEquiv q = r ↔
        originalTypedQuotientPairOldGroupOrbit S H J
          (originalTransportTargetColourEq S H J T) x y q r) := by
  intro q r
  constructor
  · intro hGraph
    obtain ⟨u,v,hqu,hrv,huv⟩ :=
      (original_transport_graph_iff_atom_in_pair_spectrum
        S H J T a ha q r).mp hGraph
    obtain ⟨g,hgx,hgy⟩ :=
      S.pair_homogeneous_of_homogeneous H
        x u y v (hxy.trans huv.symm)
    exact ⟨g,by simpa only [hgx] using hqu,
      by simpa only [hgy] using hrv⟩
  · rintro ⟨g,hq,hr⟩
    apply (original_transport_graph_iff_atom_in_pair_spectrum
      S H J T a ha q r).mpr
    refine ⟨g • x,g • y,hq,hr,?_⟩
    exact (S.colourInvariant_of_homogeneous H g x y).trans hxy

/-- C46 without even choosing an old a-pair in the hypothesis:
EVERY nonempty identity-free quotient transition has a concrete
real original atomic orbit representative. The graph contains
ALL and ONLY the translates of this representative by one
element of the ORIGINAL ambient group. -/
theorem original_transport_graph_one_complete_old_group_orbit
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (a : S.Atom i j) (ha : a ∈ S.diversityGuard R) :
    ∃ (x : X i) (y : X j), S.atomRel a x y ∧
      ∀ q : Quotient J.val,
        ∀ r : Quotient (originalTransportTargetColourEq S H J T).val,
        (T.quotientEquiv q = r ↔
          originalTypedQuotientPairOldGroupOrbit S H J
            (originalTransportTargetColourEq S H J T) x y q r) := by
  obtain ⟨x,y,hxy⟩ := S.realized a
  exact ⟨x,y,hxy,
    original_transport_graph_is_old_group_pair_orbit
      S H J T a ha x y hxy⟩

end CCO.TransitionClosure
