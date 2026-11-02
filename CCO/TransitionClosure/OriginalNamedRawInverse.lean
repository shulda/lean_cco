import CCO.TransitionClosure.OriginalNamedRawUnaryLanguage

/-!
# B049 source07 C33/C39-C40: named inverse RAW quotient transitions

Every genuine old source07 named transition q_(R,J) is an ACTUAL
B040 quotient bijection J→K, K=Rᵒᵖ;J;R on the original old named sorts.

The converse old invariant relation Rᵒᵖ is itself nonempty,
identity-free and finitely named. Its literal source kernel bound
Rᵒᵖ;R ⊆ K follows from the actual B040 target_iff, using
reflexivity of J. Hence the converse is a legal named primitive,
whose transported target kernel is LITERALLY J. This is not a
new inverse axiom, a hypothetical quotient section or an assumed
quotient SAP.

The two actual B040 quotient maps are functional inverses:
their composite is the old quotient identity after the proved
exact kernel equality. Thus the already compiled named RAW
unary grammar includes each required primitive inverse as one
more genuine original RAW-converse transition term.

No extra generated functions, new visible sorts, added STRONG
identity atom, quotient-group action, SAP/CCO or source change.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.QuotientTransport

/-- Genuine original G-invariant nonempty OLD converse RAW
relation; it retains ALL old equality-containing RAW information,
including the actual diagonal when present. No STRONG identity
letter or false quotient-action provider is introduced. -/
def originalNonemptyInvariantTypedRel_converse
    {i j : ι}
    (R : OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j) :
    OriginalNonemptyInvariantTypedRel (X := X) (G := G) j i := by
  let Q : OriginalInvariantTypedRel (X := X) (G := G) j i :=
    ⟨fun y x => R.val.val x y, by
      intro g y x hxy
      exact R.val.property g x y hxy⟩
  refine ⟨Q, ?_⟩
  obtain ⟨x,y,hxy⟩ := R.property
  exact ⟨y,x,hxy⟩

/-- SOURCE07 source-tight inverse SYMBOL: Rᵒᵖ is a genuine
OLD nonempty invariant RAW relation, with no actual identity
because R has none. Its kernel bound Rᵒᵖ;R ⊆ K is derived
from T.target_iff of the ORIGINAL B040 transport, while
K is the already proved ACTUAL terminal RAW-represented
proper hidden target. No new target-representation premise. -/
noncomputable def originalNamedRawTransitionSymbol_converse
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (d : OriginalNamedRawTransitionSymbol S H i j) :
    OriginalNamedRawTransitionSymbol S H j i := by
  let T := originalNamedRawTransitionSymbol_transport S H d
  let K := originalNamedRawTransitionSymbol_target S H sap nr2 d
  let Q := originalNonemptyInvariantTypedRel_converse d.val.2
  refine ⟨⟨K,Q⟩, ?_⟩
  constructor
  · intro y z h
    obtain ⟨x,hxy,hxz⟩ := h
    change d.val.2.val.val x y at hxy
    change d.val.2.val.val x z at hxz
    have hK : T.target y z :=
      (T.target_iff y z).mpr
        ⟨x,x,hxy,(originalColourEqAsInvEq S H d.val.1.val).val.refl x,hxz⟩
    exact hK
  · intro y x hyx heq
    change d.val.2.val.val x y at hyx
    exact d.property.2 x y hyx heq.symm

/-- The REAL target kernel of the converse B040 transport is
LITERALLY the original source J, not an unrelated isomorphic
quotient chart. The two inclusions are proved using actual old
R-edge witnesses and the original transported target kernel. -/
theorem originalNamedRawTransitionSymbol_converse_target_eq_source
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (d : OriginalNamedRawTransitionSymbol S H i j) :
    let T := originalNamedRawTransitionSymbol_transport S H d
    let U := originalNamedRawTransitionSymbol_transport S H
      (originalNamedRawTransitionSymbol_converse S H sap nr2 d)
    U.target = originalColourEqAsInvEq S H d.val.1.val := by
  let T := originalNamedRawTransitionSymbol_transport S H d
  let U := originalNamedRawTransitionSymbol_transport S H
    (originalNamedRawTransitionSymbol_converse S H sap nr2 d)
  apply InvEq.ext
  intro x z
  rw [U.target_iff]
  constructor
  · rintro ⟨y,y',hxy,hKyy',hzy'⟩
    change d.val.2.val.val x y at hxy
    change d.val.2.val.val z y' at hzy'
    have hKyy' : T.target y y' := by
      change T.target y y' at hKyy'
      exact hKyy'
    obtain ⟨u,v,huy,hJuv,hvy'⟩ := (T.target_iff y y').mp hKyy'
    exact (originalColourEqAsInvEq S H d.val.1.val).val.trans
      (T.kernel x u y hxy huy)
      ((originalColourEqAsInvEq S H d.val.1.val).val.trans
        hJuv (T.kernel v z y' hvy' hzy'))
  · intro hJxz
    obtain ⟨y,hxy⟩ := T.serial x
    obtain ⟨y',hzy'⟩ := T.serial z
    have hKyy' : T.target y y' :=
      (T.target_iff y y').mpr ⟨x,z,hxy,hJxz,hzy'⟩
    have hyx : (originalNamedRawTransitionSymbol_converse S H sap nr2 d).val.2.val.val y x := by
      change d.val.2.val.val x y
      exact hxy
    have hy'z : (originalNamedRawTransitionSymbol_converse S H sap nr2 d).val.2.val.val y' z := by
      change d.val.2.val.val z y'
      exact hzy'
    exact ⟨y,y',hyx,hKyy',hy'z⟩

/-- The converse primitive's ACTUALLY NAMED target is exactly
the source named full proper MI D itself. This equality uses
proof irrelevance for its already-proved RAW representation,
not an abstract equivalence or a second quotient chart. -/
theorem originalNamedRawTransitionSymbol_converse_target_name
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (d : OriginalNamedRawTransitionSymbol S H i j) :
    originalNamedRawTransitionSymbol_target S H sap nr2
      (originalNamedRawTransitionSymbol_converse S H sap nr2 d) =
        d.val.1 := by
  have hTarget :=
    originalNamedRawTransitionSymbol_converse_target_eq_source S H sap nr2 d
  apply Subtype.ext
  apply ColourEq.ext
  intro x z
  change
    (originalNamedRawTransitionSymbol_transport S H
      (originalNamedRawTransitionSymbol_converse S H sap nr2 d)).target x z ↔
        d.val.1.val x z
  rw [hTarget]
  exact Iff.rfl

/-- The two actual accepted B040 quotient bijections for a
primitive old RAW relation and its named genuine converse
compose to the literal ORIGINAL source quotient identity,
after the PROVED same-target equality congruence. -/
theorem originalNamedRawTransitionSymbol_converse_quotient_inverse
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (d : OriginalNamedRawTransitionSymbol S H i j)
    (q : Quotient d.val.1.val.val) :
    let T := originalNamedRawTransitionSymbol_transport S H d
    let U := originalNamedRawTransitionSymbol_transport S H
      (originalNamedRawTransitionSymbol_converse S H sap nr2 d)
    InvEq.quotientCongr
      (originalNamedRawTransitionSymbol_converse_target_eq_source
        S H sap nr2 d)
      (U.quotientEquiv (T.quotientEquiv q)) = q := by
  let T := originalNamedRawTransitionSymbol_transport S H d
  let U := originalNamedRawTransitionSymbol_transport S H
    (originalNamedRawTransitionSymbol_converse S H sap nr2 d)
  change InvEq.quotientCongr
    (originalNamedRawTransitionSymbol_converse_target_eq_source S H sap nr2 d)
      (U.quotientEquiv (T.quotientEquiv q)) = q
  induction q using Quotient.inductionOn with
  | _ x =>
      obtain ⟨y,hxy⟩ := T.serial x
      have hyx : (originalNamedRawTransitionSymbol_converse S H sap nr2 d).val.2.val.val y x := by
        change d.val.2.val.val x y
        exact hxy
      change InvEq.quotientCongr
          (originalNamedRawTransitionSymbol_converse_target_eq_source S H sap nr2 d)
          (U.quotientEquiv (T.quotientEquiv (Quotient.mk'' x))) =
            Quotient.mk'' x
      rw [T.quotientEquiv_edge hxy]
      exact (congrArg
        (InvEq.quotientCongr
          (originalNamedRawTransitionSymbol_converse_target_eq_source
            S H sap nr2 d))
          (U.quotientEquiv_edge hyx)).trans
        (InvEq.quotientCongr_mk
          (originalNamedRawTransitionSymbol_converse_target_eq_source
            S H sap nr2 d) x)

/-- An actual TERM for the inverse of ANY named primitive RAW
quotient transition is already present in the original source07
generated named hidden unary grammar: start with the exact
named B040 target, apply ONE true converse RAW primitive, and
rewrite its proven named target to the original source coordinate.
This introduces no extra inverse-function symbol or new carrier. -/
noncomputable def originalNamedRawUnaryTerm_inverse_symbol
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (d : OriginalNamedRawTransitionSymbol S H i j) :
    OriginalNamedRawUnaryTerm S H sap nr2
      (originalNamedRawTransitionSymbol_target S H sap nr2 d) d.val.1 := by
  let dinv := originalNamedRawTransitionSymbol_converse S H sap nr2 d
  let w : OriginalNamedRawUnaryTerm S H sap nr2
      (originalNamedRawTransitionSymbol_target S H sap nr2 d)
      (originalNamedRawTransitionSymbol_target S H sap nr2 dinv) :=
    .transition dinv
      (.ident (originalNamedRawTransitionSymbol_target S H sap nr2 d))
  have heq : originalNamedRawTransitionSymbol_target S H sap nr2 dinv = d.val.1 :=
    originalNamedRawTransitionSymbol_converse_target_name S H sap nr2 d
  exact heq ▸ w

end CCO.TransitionClosure
