import CCO.TransitionClosure.OriginalNamedHiddenCoordinates
import CCO.TransitionClosure.OriginalAtomicTransport
import CCO.TransitionClosure.OriginalConverseIdentity
import CCO.StrongExact.ProfileSemantics

/-!
# B049 original source07 C50-C52: ACTUAL named atomic quotient branch

A positive old typed STRONG word gives a true nonempty invariant OLD
diversity relation, without guessing an equality-inclusive STRONG unit:
its menu is realized by original SAP, and literal old pair colours are
preserved by the ORIGINAL homogeneous action. A source-functional
positive branch therefore has a genuine accepted B040 transport.

The finite original symbol language has a transition symbol for each
ACTUAL hidden source coordinate and genuine diversity atom with the
literal atomic kernel bound t;tᵒᵖ <= J. Its B040 canonical bijection
has an actual terminal-NR2 represented hidden target.

For any quotient-functional WHOLE original invariant RAW relation R
and ANY old atom t in its diversity guard, the already proved real
atomic-transport theorem constructs precisely that finite source
symbol and proves that its interpreted quotient function agrees with
the whole R transition, modulo their proved identical target kernel.
Thus a genuinely positive whole branch is already named, without
asserting R = t or replacing the finite source language by the
unbounded term syntax. There is no SAP/CCO on hidden quotients.

Finally, with genuine old equality at the source, SAP converse
rigidity shows that EVERY actual R-edge is literal original equality,
so a transition cannot create a new visible original point or a
cross-sort real coordinate. This is distinct from the nonzero-hidden
SAP noncollapse proof.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.QuotientTransport

/-- A positive OLD STRONG profile is an ACTUAL invariant nonempty
old typed RAW diversity relation. The old SAP assumption is used
only to realize at least ONE genuine fine profile atom, NOT to
assert a quotient SAP or an external branch-representability axiom.
There is no logical equality letter in this relation. -/
noncomputable def originalPositiveStrongBranchRelation
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (p : PositiveWord S i j) :
    OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j := by
  let P : S.Menu i j := PositiveWord.profile S p
  let R : OriginalInvariantTypedRel (X := X) (G := G) i j :=
    ⟨S.menuRel P, by
      intro g x y hXY
      obtain ⟨a,ha,hColour⟩ := hXY
      exact ⟨a,ha,(S.colourInvariant_of_homogeneous H g x y).trans hColour⟩⟩
  have hNonempty : TRel.Nonempty R.val := by
    obtain ⟨a,ha⟩ := PositiveWord.profile_nonempty_of_SAP S H sap p
    obtain ⟨x,y,hxy⟩ := S.realized a
    exact ⟨x,y,⟨a,ha,hxy⟩⟩
  exact ⟨R,hNonempty⟩

/-- The true OLD diversity colour menu of the represented
positive branch is EXACTLY its original STRONG word profile;
real equality is not adjoined. -/
theorem originalPositiveStrongBranchRelation_guard
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (p : PositiveWord S i j) :
    S.diversityGuard
      (originalPositiveStrongBranchRelation S H sap p).val.val =
        PositiveWord.profile S p := by
  change S.diversityGuard
    (S.menuRel (PositiveWord.profile S p)) = PositiveWord.profile S p
  exact S.diversityGuard_menuRel (PositiveWord.profile S p)

/-- Literal B040 canonical quotient transport for a TRUE positive
old STRONG branch, under EXACT source kernel condition
P;Pᵒᵖ <= J. The old R relation is the actually realized
diversity menu of its positive word, not an invented quotient
action or a zero-diversity identity step. -/
noncomputable def originalPositiveStrongBranch_transport
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (J : ColourEq S i) (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j,
        S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J x z) :
    Transport (originalColourEqAsInvEq S H J)
      (originalPositiveStrongBranchRelation S H sap p).val.val := by
  let R := originalPositiveStrongBranchRelation S H sap p
  exact typed_quotient_transport
    (originalColourEqAsInvEq S H J) R.val.val
    R.val.property R.property
    (S.original_sort_transitive_of_homogeneous H i)
    (S.original_sort_transitive_of_homogeneous H j)
    (by
      intro x z hxz
      exact hKernel x z hxz)

/-- The genuinely FINITE family of identity-free OLD ATOMIC
quotient-transition SYMBOLS between original sorts i,j:
one actual represented hidden source coordinate J and ONE
original diversity fine atom t with the real kernel condition
t;tᵒᵖ <= J. No arbitrary invariant many-atom relation
is declared a primitive symbol. -/
abbrev OriginalNamedAtomicTransitionSymbol
    (H : HomogeneousSource S G) (i j : ι) :=
  {d : OriginalNamedHiddenCoordinate S H i × S.Atom i j //
    ∀ x z : X i, ∀ y : X j,
      S.atomRel d.2 x y → S.atomRel d.2 z y → d.1.val x z}

/-- Atomic symbols are genuinely finite, even when their old
real-point and quotient-point carriers are infinite. -/
theorem originalNamedAtomicTransitionSymbol_finite
    (H : HomogeneousSource S G) {i j : ι} :
    Finite (OriginalNamedAtomicTransitionSymbol S H i j) := by
  haveI : Finite (OriginalNamedHiddenCoordinate S H i) :=
    original_named_hidden_coordinates_finite S H
  letI : Fintype (S.Atom i j) := S.finiteAtom i j
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- EACH genuine identity-free primitive atom symbol carries its
OWN accepted B040 canonical transport. Its kernel assumption
is the explicit original atomic relation constraint on the
symbol, while homogeneity supplies invariant/serial/coserial
real witnesses. No separate chosen quotient chart. -/
noncomputable def originalNamedAtomicTransitionSymbol_transport
    (H : HomogeneousSource S G)
    {i j : ι} (d : OriginalNamedAtomicTransitionSymbol S H i j) :
    Transport (originalColourEqAsInvEq S H d.val.1.val)
      (S.atomRel d.val.2) := by
  let E := originalColourEqAsInvEq S H d.val.1.val
  exact typed_quotient_transport E (S.atomRel d.val.2)
    (by
      intro g x y hxy
      exact (S.colourInvariant_of_homogeneous H g x y).trans hxy)
    (S.realized d.val.2)
    (S.original_sort_transitive_of_homogeneous H i)
    (S.original_sort_transitive_of_homogeneous H j)
    (by
      intro x z hxz
      obtain ⟨y,hxy,hzy⟩ := hxz
      exact d.property x z y hxy hzy)

/-- The genuine named hidden target of one primitive atomic
transition. Original SAP excludes the equality target, and
terminal FULL NR2 produces one actual original RAW word naming
the full transported proper MI. -/
noncomputable def originalNamedAtomicTransitionSymbol_target
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (d : OriginalNamedAtomicTransitionSymbol S H i j) :
    OriginalNamedHiddenCoordinate S H j :=
  original_named_hidden_transport_target S H sap nr2 d.val.1
    (originalNamedAtomicTransitionSymbol_transport S H d)

/-- The semantics of a TRUE one-atom named quotient transition,
a canonical B040 bijection between the actual old source and
new named hidden target coordinate classes. -/
noncomputable def originalNamedAtomicTransitionSymbol_function
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (d : OriginalNamedAtomicTransitionSymbol S H i j) :
    Quotient d.val.1.val.val →
      Quotient (originalNamedAtomicTransitionSymbol_target
        S H sap nr2 d).val.val :=
  fun q => (originalNamedAtomicTransitionSymbol_transport S H d).quotientEquiv q

/-- EXACT SOURCE07 C50/C51 for an ACTUAL whole original
quotient-functional invariant RAW relation R: any fine t∈R°
already gives ONE true finite named primitive atomic symbol.
The atomic and whole B040 target kernels are equal, and their
unary quotient functions agree at EVERY input quotient class,
after the canonical equality transport. This does NOT
identify R and t as old binary relations. -/
theorem original_named_whole_transport_has_atomic_symbol
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (D : OriginalNamedHiddenCoordinate S H i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H D.val) R)
    (a : S.Atom i j) (ha : a ∈ S.diversityGuard R) :
    ∃ d : OriginalNamedAtomicTransitionSymbol S H i j,
      d.val.1 = D ∧ d.val.2 = a ∧
      ∃ hK :
          (originalNamedAtomicTransitionSymbol_transport S H d).target =
            T.target,
        ∀ q : Quotient D.val.val,
          InvEq.quotientCongr hK
            ((originalNamedAtomicTransitionSymbol_transport S H d).quotientEquiv q) =
              original_named_hidden_transport_function S H sap nr2 D T q := by
  have hInside : ∀ x : X i, ∀ y : X j,
      S.atomRel a x y → R x y :=
    original_invariant_raw_contains_full_atom S H R T.invariant a ha
  let d : OriginalNamedAtomicTransitionSymbol S H i j :=
    ⟨⟨D,a⟩, by
      intro x z y hxy hzy
      exact T.kernel x z y (hInside x y hxy) (hInside z y hzy)⟩
  obtain ⟨Ta,_,⟨hK,hFunctions⟩⟩ :=
    original_atomic_transport_agrees_with_whole_raw S H D.val R T a ha
  have hTa : originalNamedAtomicTransitionSymbol_transport S H d = Ta :=
    Subsingleton.elim _ _
  refine ⟨d,rfl,rfl,?_⟩
  rw [hTa]
  exact ⟨hK,fun q => (hFunctions q)⟩

/-- SOURCE07 selected QT-Atom for a genuinely POSITIVE original
typed STRONG word profile, with no extra invariant-R provider
and no assumed atomic transport: the actual positive branch
R=S.menuRel(profile p) is proved nonempty and invariant, its
kernel input is EXACT P;Pᵒᵖ<=J, and ANY atom a∈profile p
names the ENTIRE quotient map via one finite old atomic
transition symbol. The terminal target is represented proper MI
by B040/original SAP/NR2, not a newly hypothesized hidden object. -/
theorem original_named_positive_branch_has_atomic_symbol
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j,
        S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → D.val x z)
    (a : S.Atom i j) (ha : a ∈ PositiveWord.profile S p) :
    ∃ d : OriginalNamedAtomicTransitionSymbol S H i j,
      d.val.1 = D ∧ d.val.2 = a ∧
      ∃ hK :
        (originalNamedAtomicTransitionSymbol_transport S H d).target =
          (originalPositiveStrongBranch_transport
            S H sap D.val p hKernel).target,
        ∀ q : Quotient D.val.val,
          InvEq.quotientCongr hK
            ((originalNamedAtomicTransitionSymbol_transport S H d).quotientEquiv q) =
              original_named_hidden_transport_function S H sap nr2 D
                (originalPositiveStrongBranch_transport
                  S H sap D.val p hKernel) q := by
  have hAtom : a ∈ S.diversityGuard
      (originalPositiveStrongBranchRelation S H sap p).val.val := by
    rw [originalPositiveStrongBranchRelation_guard S H sap p]
    exact ha
  exact original_named_whole_transport_has_atomic_symbol S H sap nr2
    D (originalPositiveStrongBranch_transport S H sap D.val p hKernel) a hAtom

/-- C52 original real-coordinate firewall, in literal OLD terms:
an ACTUAL transport whose source kernel is old identity
R;Rᵒᵖ<=Id cannot carry even ONE real edge between distinct
tagged original points. This is the original SAP converse
rigidity theorem applied to the actual old B040 kernel,
NOT an argument about hidden quotient SAP. -/
theorem original_real_source_transport_edges_are_identity
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι}
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport
      (originalColourEqAsInvEq S H (⊥ : ColourEq S i)) R) :
    ∀ x : X i, ∀ y : X j, R x y →
      (⟨i,x⟩ : Sigma X) = ⟨j,y⟩ := by
  have hKernel : ∀ x z : X i,
      QuotientTransport.compose R
        (QuotientTransport.converse R) x z → x = z := by
    intro x z h
    have hh := T.kernel x z (Classical.choose h)
      (Classical.choose_spec h).1 (Classical.choose_spec h).2
    exact hh
  exact original_SAP_converse_kernel_identity_edges
    S H sap R T.invariant hKernel

/-- C52 no real-sort creation: every original real input
has one actual RAW outgoing edge and its endpoint is the
SAME original real tagged point, including the original
sort name. Seriality is B040, and no new visible real
coordinate can arise from transition closure. -/
theorem original_real_source_transport_no_new_point
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι}
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport
      (originalColourEqAsInvEq S H (⊥ : ColourEq S i)) R)
    (x : X i) :
    ∃ y : X j, R x y ∧
      (⟨i,x⟩ : Sigma X) = ⟨j,y⟩ := by
  obtain ⟨y,hR⟩ := T.serial x
  exact ⟨y,hR,
    original_real_source_transport_edges_are_identity S H sap T x y hR⟩

end CCO.TransitionClosure
