import CCO.TransitionClosure.OriginalFiniteUnaryNormals
import CCO.TransitionClosure.OriginalTransportUpwardRewrite

/-!
# B049 source07 C35-C40: semantic closure of OLD unary normal patterns

The finite normal-pattern family consists of one REAL original
upward projection E≤J followed by one genuine canonical B040
transition q_(R,J). The earlier files proved finiteness of
the actual semantic functions, not of their written expressions.

This file proves the two local rewriting rules required for
the SOURCE normal-form induction:
(1) a further upward quotient projection on the TARGET can be
    moved to the ORIGINAL source via the complete B040 interval
    pullback, giving another normal pattern, with its target
    exactly the requested full original L and the same function;
(2) a further canonical transition on the TARGET composes with
    the OLD RAW relation R, giving another normal pattern and
    the actual composed quotient function.

All equalities are pointwise on true original quotient classes
with precisely specified setoid congruences. The original
ambient G and full invariant colour equivalences are retained;
there is no hidden SAP/CCO, NR2, independent quotient section,
finite syntax assumption or identity-labelled STRONG atom.
The separate final source theorem must still identify the
whole generated term language and its represented coordinates.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open CCO.ParityHasse.Original
open CCO.QuotientTransport

/-- SOURCE C35 local TQU construction:
if an existing normal map E→F is followed by a genuine FULL
upward map F→L, its literal B040 pullback H0 of L is a FULL
original source equivalence above the old intermediate J.
Keep the SAME original RAW relation R, and replace J by H0.
The result is another genuine finite normal datum E→L.

All source and target carriers remain real ORIGINAL quotients.
This is a data-level rewrite, not an unproved normal-form oracle.
-/
noncomputable def originalCanonicalUnaryNormalDatum_after_up
    (H : HomogeneousSource S G)
    {i j : ι} (N : OriginalCanonicalUnaryNormalDatum S (G := G) i j)
    (L : ColourEq S j)
    (hFL : originalTransportTargetColourEq S H N.val.2.val.1
        (originalCanonicalRawTransitionDatum_transport S H N.val.2) ≤ L) :
    OriginalCanonicalUnaryNormalDatum S (G := G) i j := by
  let D := N.val.2
  let T := originalCanonicalRawTransitionDatum_transport S H D
  let LV := originalColourEqAsInvEq S H L
  have hTL : T.target ≤ LV := by
    intro y z hyz
    exact hFL hyz
  let H0 : ColourEq S i :=
    (originalFullColourEqInvEqOrderIso S H).symm (T.pull LV hTL)
  have hJH0 : D.val.1 ≤ H0 := by
    intro x z hxz
    exact T.source_le_pull LV hTL hxz
  let D' : OriginalCanonicalRawTransitionDatum S (G := G) i j :=
    ⟨⟨H0,D.val.2⟩, by
      intro x z h
      exact hJH0 (D.property x z h)⟩
  exact ⟨⟨N.val.1,D'⟩,N.property.trans hJH0⟩

/-- C35 exact semantics of a final upward rewrite:
the new REAL FULL target kernel is precisely the
requested original L, not merely an isomorphic unrelated
quotient. The equality follows from the proved B040
full interval inverse and proof irrelevance for the
two instances of the SAME canonical transport proposition.
-/
theorem originalCanonicalUnaryNormalDatum_after_up_target
    (H : HomogeneousSource S G)
    {i j : ι} (N : OriginalCanonicalUnaryNormalDatum S (G := G) i j)
    (L : ColourEq S j)
    (hFL : originalTransportTargetColourEq S H N.val.2.val.1
        (originalCanonicalRawTransitionDatum_transport S H N.val.2) ≤ L) :
    let N' := originalCanonicalUnaryNormalDatum_after_up S H N L hFL
    originalTransportTargetColourEq S H N'.val.2.val.1
      (originalCanonicalRawTransitionDatum_transport S H N'.val.2) = L := by
  let D := N.val.2
  let T := originalCanonicalRawTransitionDatum_transport S H D
  let LV := originalColourEqAsInvEq S H L
  have hTL : T.target ≤ LV := by
    intro y z hyz
    exact hFL hyz
  let N' := originalCanonicalUnaryNormalDatum_after_up S H N L hFL
  let T' := originalCanonicalRawTransitionDatum_transport S H N'.val.2
  have hTJ : T' = T.enlarge (T.source_le_pull LV hTL) :=
    Subsingleton.elim _ _
  have hTargets : T'.target = LV := by
    rw [hTJ]
    exact T.push_pull LV hTL
  apply ColourEq.ext
  intro y z
  change T'.target y z ↔ L y z
  rw [hTargets]
  exact Iff.rfl

/-- The actual normal data are CLOSED under addition of an
upward FULL quotient map, with POINTWISE equality of the
resulting functions after the precise proven target
kernel congruence. There is no hidden re-labelling by
a second quotient chart. This is the essential local
TQU rule for mixed-term normalisation. -/
theorem originalCanonicalUnaryNormalDatum_after_up_semantics
    (H : HomogeneousSource S G)
    {i j : ι} (N : OriginalCanonicalUnaryNormalDatum S (G := G) i j)
    (L : ColourEq S j)
    (hFL : originalTransportTargetColourEq S H N.val.2.val.1
        (originalCanonicalRawTransitionDatum_transport S H N.val.2) ≤ L) :
    let D := N.val.2
    let T := originalCanonicalRawTransitionDatum_transport S H D
    let LV := originalColourEqAsInvEq S H L
    let hTL : T.target ≤ LV := fun y z hyz => hFL hyz
    let N' := originalCanonicalUnaryNormalDatum_after_up S H N L hFL
    let T' := originalCanonicalRawTransitionDatum_transport S H N'.val.2
    ∃ hTarget : T'.target = LV,
      ∀ q : Quotient N.val.1.val,
        Quot.mapRight hTL
          ((originalCanonicalUnaryNormalDatum_function S H N).2.2 q) =
          InvEq.quotientCongr hTarget
            ((originalCanonicalUnaryNormalDatum_function S H N').2.2 q) := by
  let D := N.val.2
  let T := originalCanonicalRawTransitionDatum_transport S H D
  let LV := originalColourEqAsInvEq S H L
  have hTL : T.target ≤ LV := by
    intro y z hyz
    exact hFL hyz
  let N' := originalCanonicalUnaryNormalDatum_after_up S H N L hFL
  let T' := originalCanonicalRawTransitionDatum_transport S H N'.val.2
  have hTJ : T' = T.enlarge (T.source_le_pull LV hTL) :=
    Subsingleton.elim _ _
  have hTarget : T'.target = LV := by
    rw [hTJ]
    exact T.push_pull LV hTL
  refine ⟨hTarget,?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
    obtain ⟨y,hxy⟩ := T.serial x
    change Quot.mapRight hTL
      (T.quotientEquiv (Quotient.mk'' x)) =
        InvEq.quotientCongr hTarget
          (T'.quotientEquiv (Quotient.mk'' x))
    rw [T.quotientEquiv_edge hxy,
      T'.quotientEquiv_edge hxy]
    exact (InvEq.quotientCongr_mk hTarget y).symm

/-- SOURCE C33/C38: following a finite normal map by one
more genuinely compatible original RAW canonical transition
replaces its RAW relation by the literal OLD relational product.
The initial E≤J remains unchanged, and the result stays
inside the finite family of normal data. -/
def originalCanonicalUnaryNormalDatum_after_transition
    (H : HomogeneousSource S G)
    {i j k : ι}
    (N : OriginalCanonicalUnaryNormalDatum S (G := G) i j)
    (Q : OriginalNonemptyInvariantTypedRel (X := X) (G := G) j k)
    (U : Transport
      (originalCanonicalRawTransitionDatum_transport S H N.val.2).target
      Q.val.val) :
    OriginalCanonicalUnaryNormalDatum S (G := G) i k :=
  ⟨⟨N.val.1,
     originalCanonicalRawTransitionDatum_comp S H N.val.2 Q U⟩,
    N.property⟩

/-- The normal-family closure for a final canonical transition
preserves the POINTWISE true quotient map after the EXACT
B040 composite target congruence. This consumes the prior
proved actual old RAW datum composition theorem, not an
abstract categorical functoriality assumption.
-/
theorem originalCanonicalUnaryNormalDatum_after_transition_semantics
    (H : HomogeneousSource S G)
    {i j k : ι}
    (N : OriginalCanonicalUnaryNormalDatum S (G := G) i j)
    (Q : OriginalNonemptyInvariantTypedRel (X := X) (G := G) j k)
    (U : Transport
      (originalCanonicalRawTransitionDatum_transport S H N.val.2).target
      Q.val.val)
    (q : Quotient N.val.1.val) :
    let D := N.val.2
    let T := originalCanonicalRawTransitionDatum_transport S H D
    let N' := originalCanonicalUnaryNormalDatum_after_transition S H N Q U
    InvEq.quotientCongr (T.composite_target U)
      ((originalCanonicalUnaryNormalDatum_function S H N').2.2 q) =
      U.quotientEquiv
        ((originalCanonicalUnaryNormalDatum_function S H N).2.2 q) := by
  let D := N.val.2
  let T := originalCanonicalRawTransitionDatum_transport S H D
  change InvEq.quotientCongr (T.composite_target U)
      ((originalCanonicalRawTransitionDatum_transport S H
          (originalCanonicalRawTransitionDatum_comp S H D Q U)).quotientEquiv
        (Quot.mapRight N.property q)) =
        U.quotientEquiv (T.quotientEquiv
          (Quot.mapRight N.property q))
  exact originalCanonicalRawTransitionDatum_comp_semantics
    S H D Q U (Quot.mapRight N.property q)

end CCO.TransitionClosure
