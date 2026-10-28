import CCO.ParityHasse.Relative.Gate
import CCO.ParityHasse.Relative.QuotientGraph
import CCO.RawExact.CanonicalQuotients

/-! C25–26: the gate on a genuine equivariant quotient, all quotient
exact-equivalence consumers, and its nonidentity original bridge. -/
universe u v w t q
namespace CCO.ParityHasse.Relative
open Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
variable {Q : Type q} [MulAction G Q]

include H cco in
/-- Any nontrivial actual quotient exact equivalence pulls back to an
ORIGINAL exact equivalence strictly above K; original maximality applies. -/
theorem quotient_gate_dominance (Y U : ColourEq S i) (M : MaximalGate S H Y U)
    (π : X i → Q) (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (hK : GroupActions.kernel π = M.kernel)
    (Z : Setoid Q) (hZ : OrbitalExact G Q Z) (hZnon : (⊥ : Setoid Q) < Z) :
    ∀ q r, imageRelation π (gate S M.kernel U Y) q r → Z q r := by
  have exZ := actual_quotient_exact_pullback S H cco π surjπ equivπ M.kernel hK M.maximal.1.1 Z hZ
  let oldZ : ColourEq S i :=
    ⟨Setoid.comap π Z,exZ.colourInvariant S H⟩
  have hle : M.kernel ≤ oldZ := by
    intro x y hxy
    have he : π x = π y := by rw [← hK] at hxy; exact hxy
    change Z (π x) (π y)
    simpa only [he] using Z.refl (π x)
  have hlt : M.kernel < oldZ := by
    refine lt_iff_le_not_ge.mpr ⟨hle,?_⟩
    intro hrev
    apply hZnon.not_ge
    intro q r hqr
    obtain ⟨x,rfl⟩ := surjπ q
    obtain ⟨y,rfl⟩ := surjπ r
    have hk : M.kernel x y := hrev hqr
    rw [← hK] at hk
    exact hk
  have hd := M.dominant oldZ exZ hlt
  rintro q r ⟨x,y,rfl,rfl,hxy⟩
  exact hd x y hxy

include H in
noncomputable def quotientGateInvolution (Y U : ColourEq S i) (M : MaximalGate S H Y U)
    (π : X i → Q) (surjπ : Function.Surjective π)
    (hK : GroupActions.kernel π = M.kernel) :
    InvolutionGraph (imageRelation π (gate S M.kernel U Y)) :=
  involutionGraph _
    (imageRelation_serial π surjπ _
      (invariant_nonempty_serial S H (M.exact.colourInvariant S H) M.exact.nonempty))
    (imageRelation_symm π _ (colourInvariant_symmetric S (M.exact.colourInvariant S H)))
    (imageRelation_square π surjπ M.kernel.val hK _ M.bisaturated M.square)
    (imageRelation_irreflexive π M.kernel.val hK _ M.disjoint)

include H in
 theorem quotientGateInvolution_equivariant (Y U : ColourEq S i) (M : MaximalGate S H Y U)
    (π : X i → Q) (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (hK : GroupActions.kernel π = M.kernel) :
    ∀ (g : G) q, (quotientGateInvolution S H Y U M π surjπ hK).map (g • q) =
      g • (quotientGateInvolution S H Y U M π surjπ hK).map q := by
  apply InvolutionGraph.equivariant
  exact imageRelation_invariant π equivπ _
    (colourInvariant_groupInvariant S H (M.exact.colourInvariant S H))

include H in
 theorem quotient_gate_actual_orbital (Y U : ColourEq S i) (M : MaximalGate S H Y U)
    (π : X i → Q) (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (hK : GroupActions.kernel π = M.kernel) (q : Q) :
    imageRelation π (gate S M.kernel U Y) =
      GroupActions.orbital (G := G) q ((quotientGateInvolution S H Y U M π surjπ hK).map q) := by
  apply InvolutionGraph.actual_orbital
  · exact imageRelation_invariant π equivπ _
      (colourInvariant_groupInvariant S H (M.exact.colourInvariant S H))
  · intro q r
    obtain ⟨x,rfl⟩ := surjπ q
    obtain ⟨y,rfl⟩ := surjπ r
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x y
    exact ⟨g,by rw [← equivπ,hg]⟩

include H in
/-- The quotient gate is itself full exact, because it is ONE actual
orbital; no arbitrary exact old-to-quotient descent theorem is assumed. -/
theorem quotient_gate_exact (Y U : ColourEq S i) (M : MaximalGate S H Y U)
    (π : X i → Q) (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (hK : GroupActions.kernel π = M.kernel) (q : Q) :
    OrbitalExact G Q (imageRelation π (gate S M.kernel U Y)) := by
  let I := quotientGateInvolution S H Y U M π surjπ hK
  have horb := quotient_gate_actual_orbital S H Y U M π surjπ equivπ hK q
  refine ⟨[OrbitalWord.atom q (I.map q) .nil],?_,q,I.map q,(I.graph _ _).mpr rfl⟩
  calc
    orbitalEvaluate G Q [OrbitalWord.atom q (I.map q) .nil] =
        GroupActions.orbital (G := G) q (I.map q) := by
      funext x y; apply propext
      simp [orbitalEvaluate,OrbitalWord.relation,mul,RawSymmetric.compose]
    _ = _ := horb.symm

/-- The real source bridge equations retain the kernel K; only its image
on quotient classes has genuine functionality. -/
structure ExactIsotropyBridge (K : ColourEq S i) where
  relation : Rel (X i)
  exact : Exact S relation
  saturated : Bisaturated K.val relation
  left_inverse : mul relation (fun x y => relation y x) = K
  right_inverse : mul (fun x y => relation y x) relation = K
  nonidentity : relation ≠ K

include H in
 theorem maximalGate_bridge (Y U : ColourEq S i) (M : MaximalGate S H Y U) :
    Nonempty (ExactIsotropyBridge S M.kernel) := by
  have hs : (fun x y => gate S M.kernel U Y y x) = gate S M.kernel U Y := by
    funext x y; apply propext
    exact ⟨colourInvariant_symmetric S (M.exact.colourInvariant S H) y x,
      colourInvariant_symmetric S (M.exact.colourInvariant S H) x y⟩
  refine ⟨⟨gate S M.kernel U Y,M.exact,M.bisaturated,?_,?_,?_⟩⟩
  · rw [hs]; exact M.square
  · rw [hs]; exact M.square
  · intro heq
    obtain ⟨x,y,hxy⟩ := M.exact.nonempty
    exact M.disjoint x y hxy (by rw [← heq]; exact hxy)

/-- Canonical quotient action on the ACTUAL K-classes of original points. -/
@[instance_reducible] def quotientAction (K : ColourEq S i) : MulAction G (Quotient K.val) := by
  letI : RawExact.CanonicalQuotients.Invariant G K.val :=
    ⟨colourInvariant_groupInvariant S H K.2⟩
  exact RawExact.CanonicalQuotients.quotientMulAction K.val

 theorem quotientProjection_equivariant (K : ColourEq S i) :
    letI := quotientAction S H K
    ∀ (g : G) (x : X i), Quotient.mk K.val (g • x) = g • Quotient.mk K.val x := by
  intro g x
  rfl

include H cco in
/-- Literal M/K consumer. It produces the actual fixed-point-free,
equivariant involution and domination of EVERY nonidentity full exact
quotient equivalence. No source provider remains in this instance. -/
theorem actual_class_gate (Y U : ColourEq S i) (hY : Exact S Y) (hYU : Y ≤ U)
    (hO : Exact S (odd Y.val U.val)) (a : X i)
    (htwo : relativeIndex Y.val U.val a = 2) :
    ∃ M : MaximalGate S H Y U,
      letI := quotientAction S H M.kernel
      ∃ I : InvolutionGraph (imageRelation (Quotient.mk M.kernel.val) (gate S M.kernel U Y)),
        (∀ (g : G) q, I.map (g • q) = g • I.map q) ∧
        OrbitalExact G (Quotient M.kernel.val)
          (imageRelation (Quotient.mk M.kernel.val) (gate S M.kernel U Y)) ∧
        (∀ Z : Setoid (Quotient M.kernel.val),
          OrbitalExact G (Quotient M.kernel.val) Z → (⊥ : Setoid _) < Z →
          ∀ q r, imageRelation (Quotient.mk M.kernel.val) (gate S M.kernel U Y) q r → Z q r) ∧
        Nonempty (ExactIsotropyBridge S M.kernel) := by
  obtain ⟨M⟩ := exists_maximalGate S H cco Y U hY hYU hO a htwo
  refine ⟨M,?_⟩
  letI := quotientAction S H M.kernel
  let π := Quotient.mk M.kernel.val
  have surj : Function.Surjective π := Quotient.mk_surjective
  have equivπ := quotientProjection_equivariant S H M.kernel
  have hk : GroupActions.kernel π = M.kernel := by
    funext x y; exact propext Quotient.eq
  refine ⟨quotientGateInvolution S H Y U M π surj hk,
    quotientGateInvolution_equivariant S H Y U M π surj equivπ hk,
    quotient_gate_exact S H Y U M π surj equivπ hk (π a),?_,maximalGate_bridge S H Y U M⟩
  exact quotient_gate_dominance S H cco Y U M π surj equivπ hk

end CCO.ParityHasse.Relative
