import CCO.TransitionClosure.OriginalAtomicTransport

/-!
# B052 C04–C05: exact compatibility of two named RAW root branches

If two genuinely nonempty ORIGINAL-G invariant typed RAW relations
R and Q contain the SAME ACTUAL original fine diversity atom a,
and are both quotient-functional over the SAME original FULL J,
then their canonical predecessor labels agree at EVERY old target
point. Hence the literal B040 full target kernels and quotient
bijections are identical after the PROVED target equality,
not after an unrelated quotient chart choice.

The proof selects actual old a-predecessors and successors using
the accepted B049 atomic transport. The inclusion of the ENTIRE
a-orbital into each RAW relation is proved from actual original
two-point homogeneity, not inferred from a single overlapping
witness. No hidden SAP, CCO, NR2 or independent quotient action.
This is the precise source-level compatibility underpinning
intersection-forced and branch-forced root-signature identities.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.QuotientTransport
open CCO.ParityHasse.Original

/-- Full B052 C04: two actual quotient-functional original
RAW relations sharing a true OLD atomic type give the SAME
literal invariant FULL target equivalence and SAME quotient
function on every original source J-class. This equality
does not imply R=Q as relations, and is valid across old sorts. -/
theorem original_shared_atom_raw_transports_agree
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    (R Q : QuotientTransport.Rel (X i) (X j))
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (U : Transport (originalColourEqAsInvEq S H J) Q)
    (a : S.Atom i j)
    (haR : a ∈ S.diversityGuard R)
    (haQ : a ∈ S.diversityGuard Q) :
    ∃ hTarget : T.target = U.target,
      ∀ q : Quotient J.val,
        InvEq.quotientCongr hTarget (T.quotientEquiv q) =
          U.quotientEquiv q := by
  have hInsideR : ∀ x : X i, ∀ y : X j,
      S.atomRel a x y → R x y :=
    original_invariant_raw_contains_full_atom S H R T.invariant a haR
  have hInsideQ : ∀ x : X i, ∀ y : X j,
      S.atomRel a x y → Q x y :=
    original_invariant_raw_contains_full_atom S H Q U.invariant a haQ
  obtain ⟨Ta,_,_⟩ :=
    original_atomic_transport_agrees_with_whole_raw
      S H J R T a haR
  have hLabel : ∀ y : X j, T.label y = U.label y := by
    intro y
    obtain ⟨x,hxy⟩ := Ta.coserial y
    rw [T.label_edge (hInsideR x y hxy),
      U.label_edge (hInsideQ x y hxy)]
  have hTarget : T.target = U.target := by
    apply InvEq.ext
    intro y z
    change T.label y = T.label z ↔ U.label y = U.label z
    rw [hLabel y, hLabel z]
  refine ⟨hTarget, ?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
      obtain ⟨y,hxy⟩ := Ta.serial x
      change InvEq.quotientCongr hTarget
        (T.quotientEquiv (Quotient.mk'' x)) =
        U.quotientEquiv (Quotient.mk'' x)
      rw [T.quotientEquiv_edge (hInsideR x y hxy),
        U.quotientEquiv_edge (hInsideQ x y hxy),
        InvEq.quotientCongr_mk]

/-- B052 C05 root-pair result: a literal actual a-edge
present in R and Q gives the exact two direct transition
equations on the SAME real source and target representatives,
and the target equivalences are proved identical.
There is no invented binary hidden orbital or branching
quotient section. -/
theorem original_shared_atom_root_pair_consistent
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    (R Q : QuotientTransport.Rel (X i) (X j))
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (U : Transport (originalColourEqAsInvEq S H J) Q)
    (a : S.Atom i j)
    (haR : a ∈ S.diversityGuard R)
    (haQ : a ∈ S.diversityGuard Q)
    (x : X i) (y : X j) (hxy : S.atomRel a x y) :
    ∃ hTarget : T.target = U.target,
      (T.quotientEquiv (Quotient.mk J.val x) =
        Quotient.mk T.target.val y) ∧
      (U.quotientEquiv (Quotient.mk J.val x) =
        Quotient.mk U.target.val y) ∧
      InvEq.quotientCongr hTarget
        (T.quotientEquiv (Quotient.mk J.val x)) =
          U.quotientEquiv (Quotient.mk J.val x) := by
  obtain ⟨hTarget,hMaps⟩ :=
    original_shared_atom_raw_transports_agree
      S H J R Q T U a haR haQ
  have hTR : R x y :=
    original_invariant_raw_contains_full_atom
      S H R T.invariant a haR x y hxy
  have hUQ : Q x y :=
    original_invariant_raw_contains_full_atom
      S H Q U.invariant a haQ x y hxy
  exact ⟨hTarget,T.quotientEquiv_edge hTR,
    U.quotientEquiv_edge hUQ,hMaps _⟩

end CCO.UnaryTermsReturn
