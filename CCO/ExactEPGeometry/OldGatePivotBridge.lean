import CCO.ExactEPGeometry.OldGateActualProvider
import CCO.ExactEPGeometry.OriginalPivotTrace
import CCO.APCharacter.GateSource

/-!
# B062 C38–C43: choose the SAME real current pivot and full gate provider

The current homogeneous AP+HOM CCO source has a real original unary-reduct
projection to the fixed initial source. Given an ACTUAL current diversity
orbital c with no odd closed walk, the fixed parent old orbital is
P.atom p p c. Its full current point relation is LITERALLY c, by the
injective atom names and real point/colour projection.

Both parity intervals are actual even/connectivity equivalences. The
original one is a genuine full-invariant cover (connectivity need NOT
be RAW exact). The real C28 typed (TP) gives their complete pointwise
trace identities, and the original even interval is genuine RAW exact.

Crucially the SAME selected current MaximalGate M produces BOTH the
maximal ORIGINAL exact lift L_p(M.kernel) and the ACTUAL AP-character
SourcePhase for the next full-character step. This does not silently
claim that a previously, separately chosen SourcePhase remembers M:
connecting such historical choices requires an explicit provenance
certificate and is not part of this theorem.

No source/quotient SAP, fake quotient section or extra axiom.
-/

universe u v w t

namespace CCO.ExactEPGeometry.OldGatePivotBridge

open APCharacter APCharacter.Towers
open CCO.ExactEPGeometry
open CCO.ExactEPGeometry.PrefixExactRestriction
open CCO.ExactEPGeometry.OldGateMaximality
open CCO.ParityHasse.Original
open CCO.ParityHasse.Relative
open CCO.RigidGroupoid.Geometry

noncomputable section

/-- An old diversity orbital picked by the REAL current atom map has
exactly the current c-relation on this specific realized current sort.
The reverse direction uses the proved injectivity of the unary
binary-name map, not a fictitious new atom or quotient SAP. -/
theorem current_parent_atom_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    {p : B.Sorts} (c : B.source.Atom p p)
    (x y : B.Point p) :
    OriginalPivotTrace.currentTrace A B P
        (A.source.atomRel (P.atom p p c)) x y ↔
      B.source.atomRel c x y :=
  (ProjectedWords.atom_iff A.source B.source P c x y).symm

/-- C38–C43 one-step source construction with the SAME actual selected
current odd pivot c and maximal current provider M.

If c has the genuine current no-odd-walk certificate, we CONSTRUCT:
1) the original even RAW-exact and full connectivity equivalences;
2) the REAL current MaximalGate at the c-parity cover;
3) the maximal original exact lift of its chosen kernel, via E1–E3;
4) the actual AP-only SourcePhase for EXACTLY that same chosen gate.

The proof also identifies the old Y and X literally, so a consumer
cannot substitute a different old atom or a different maximal gate. -/
theorem actual_pivot_and_selected_gate
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts)
    (c : B.source.Atom p p)
    (hNoOdd : ∀ x : B.Point p, ∀ n : Nat, Odd n →
        ¬relPow (B.source.atomRel c) n x x) :
    ∃ (Yold : ExactEq A.source (P.parent p))
      (Uold : ColourEq A.source (P.parent p))
      (M : MaximalGate B.source B.homogeneous
        (evenColourEq B.source B.homogeneous c)
        (connectivityColourEq B.source B.homogeneous c)),
      Yold.val =
        evenColourEq A.source A.homogeneous (P.atom p p c) ∧
      Uold =
        connectivityColourEq A.source A.homogeneous (P.atom p p c) ∧
      Maximal (OriginalGateCandidate A.source (P.parent p)
        Yold Uold)
        (PrefixExactLargestLift.largest A B P transport tp p
          (⟨M.kernel,M.maximal.1.1⟩ : ExactEq B.source p)) ∧
      Nonempty (SourcePhase B.source B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco)
        (APCharacter.MaximalGate.kernel B.source B.homogeneous
          (evenColourEq B.source B.homogeneous c)
          (connectivityColourEq B.source B.homogeneous c) M)) := by
  let oldc : A.source.Atom (P.parent p) (P.parent p) := P.atom p p c
  have hAtom : OriginalPivotTrace.currentTrace A B P
      (A.source.atomRel oldc) = B.source.atomRel c := by
    funext x y
    exact propext (current_parent_atom_iff A B P c x y)
  obtain ⟨x₀,y₀,hc⟩ := B.source.realized c
  have hNE : TRel.Nonempty
      (OriginalPivotTrace.currentTrace A B P
        (A.source.atomRel oldc)) :=
    ⟨x₀,y₀,(current_parent_atom_iff A B P c x₀ y₀).mpr hc⟩
  have hCurrentNoOdd :
      ∀ x : B.Point p, ∀ n : Nat, Odd n →
        ¬relPow (OriginalPivotTrace.currentTrace A B P
          (A.source.atomRel oldc)) n x x := by
    intro x n hn h
    exact hNoOdd x n hn (by simpa only [hAtom] using h)
  have hOldNoOdd :=
    OriginalPivotTrace.original_atom_no_odd A B P tp oldc hNE
      hCurrentNoOdd
  obtain ⟨DY,DO,hYEq,hOEq⟩ :=
    parity_profiles_nonempty_exact A.source A.homogeneous oldc
  let Yold : ExactEq A.source (P.parent p) :=
    ⟨evenColourEq A.source A.homogeneous oldc,
      ⟨DY,by funext x y; exact propext (hYEq x y)⟩⟩
  let Uold : ColourEq A.source (P.parent p) :=
    connectivityColourEq A.source A.homogeneous oldc
  let Ycur : ColourEq B.source p :=
    evenColourEq B.source B.homogeneous c
  let Ucur : ColourEq B.source p :=
    connectivityColourEq B.source B.homogeneous c
  have hOldCover : Yold.val ⋖ Uold :=
    parity_seed_cover A.source A.homogeneous oldc hOldNoOdd
  have hCurrentCover : Ycur ⋖ Ucur :=
    parity_seed_cover B.source B.homogeneous c hNoOdd
  have hE4 := OriginalPivotTrace.original_atom_E4 A B P tp oldc hNE
  have hYcur : Ycur = (rho A B P transport p Yold).val := by
    apply ColourEq.ext B.source p
    intro x y
    change EvenWalk (B.source.atomRel c) x y ↔
      (rho A B P transport p Yold) x y
    rw [rho_iff A B P transport p Yold x y]
    change EvenWalk (B.source.atomRel c) x y ↔
      (evenColourEq A.source A.homogeneous oldc) (P.point p x) (P.point p y)
    simpa only [hAtom] using (hE4.1 x y).symm
  have hUtrace : ∀ x y : B.Point p,
      Ucur x y ↔ Uold (P.point p x) (P.point p y) := by
    intro x y
    change ConnectedWalk (B.source.atomRel c) x y ↔
      (connectivityColourEq A.source A.homogeneous oldc)
        (P.point p x) (P.point p y)
    simpa only [hAtom] using (hE4.2.2 x y).symm
  obtain ⟨EY,EO,hEY,hEO⟩ :=
    parity_profiles_nonempty_exact B.source B.homogeneous c
  have hCurrentYExact : Exact B.source Ycur := by
    refine ⟨EY,?_⟩
    funext x y
    exact propext (hEY x y)
  have hCurrentSymm :
      ∀ x y : B.Point p, B.source.atomRel c x y →
        B.source.atomRel c y x := by
    intro x y h
    simpa only [AtomicSource.atomRel,B.source.symmetricLoop]
      using (B.source.colour_swap x y c).mp h
  have hCurrentOdd (x y : B.Point p) :
      OddWalk (B.source.atomRel c) x y ↔
        odd Ycur.val Ucur.val x y := by
    constructor
    · intro h
      refine ⟨(connectivity_eq_even_union_odd
        B.source B.homogeneous c x y).mpr (Or.inr h),?_⟩
      intro he
      exact even_odd_disjoint (B.source.atomRel c)
        hCurrentSymm hNoOdd x y ⟨he,h⟩
    · rintro ⟨hconn,hnot⟩
      exact ((connectivity_eq_even_union_odd
        B.source B.homogeneous c x y).mp hconn).resolve_left hnot
  have hCurrentOddExact : Exact B.source (odd Ycur.val Ucur.val) := by
    refine ⟨EO,?_⟩
    funext x y
    exact propext ((hEO x y).trans (hCurrentOdd x y))
  let a : B.Point p := Classical.choice (B.source.nonemptySort p)
  have hTwo : relativeIndex Ycur.val Ucur.val a = 2 :=
    parity_seed_index_two B.source B.homogeneous c hNoOdd a
  obtain ⟨M⟩ := exists_maximalGate B.source B.homogeneous B.cco
    Ycur Ucur hCurrentYExact
    (even_le_connectivity B.source B.homogeneous c)
    hCurrentOddExact a hTwo
  have hGate :=
    OldGateActualProvider.lift_actual_maximal_gate
      A B P transport tp p Yold Uold Ycur Ucur
      hYcur hOldCover hUtrace hCurrentCover M
  have hPhase :=
    APCharacter.MaximalGate.actual_phase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Ycur Ucur M
  exact ⟨Yold,Uold,M,rfl,rfl,hGate,hPhase⟩

end
end CCO.ExactEPGeometry.OldGatePivotBridge
