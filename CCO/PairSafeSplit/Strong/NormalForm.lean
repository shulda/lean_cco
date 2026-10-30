import CCO.PairSafeSplit.Strong.PathSyntax
import CCO.PairSafeSplit.Strong.RealizationTriangles
import CCO.PairSafeSplit.Strong.RealizationAtoms
import CCO.PairSafeSplit.Strong.WordFamily
import CCO.PairSafeSplit.SAP.Source

/-! The formal FULL old path support is read on the WHOLE canonical child
source over fixed actual endpoints. Only after the independently proved new
SAP do we guard the actual represented word on both sources. -/

universe u v w t
namespace CCO.PairSafeSplit.Strong
open APCharacter RigidGroupoid.Geometry
open APCharacter.SourceAge.UnarySource
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : Identification S H (P.completion_property cco))

include H in
private theorem full_exact_colour_iff {i j : ι} {R : TRel X i j} (hR : FullExact S R)
    {x x' : X i} {y y' : X j} (hc : S.colour x y = S.colour x' y') :
    R x y ↔ R x' y' := by
  obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' hc
  constructor
  · intro h
    simpa only [hgx,hgy] using hR.invariant S H g x y h
  · intro h
    have hx : g⁻¹ • x' = x := by rw [← hgx,inv_smul_smul]
    have hy : g⁻¹ • y' = y := by rw [← hgy,inv_smul_smul]
    simpa only [hx,hy] using hR.invariant S H g⁻¹ x' y' h

private theorem support_colour_iff {c d : Rank.Child (β I)} (p : LiftedPath I c d)
    {x x' : X c.1} {y y' : X d.1} (hc : S.colour x y = S.colour x' y') :
    p.oldPrefix.support x y ↔ p.oldPrefix.support x' y' := by
  rw [(p.oldPrefix.normal_form H C (P.calculus cco)).1]
  change (_ ∧ P.masks.allowed (S.colour x y) _ _) ↔
    (_ ∧ P.masks.allowed (S.colour x' y') _ _)
  rw [full_exact_colour_iff (H := H) (p.oldPrefix.word_exact C) hc,hc]

/-- This is actual new-source composition, not just a formal support
identity: every old midpoint is transported over these same endpoints. -/
theorem represented_iff_support {c d : Rank.Child (β I)} (p : LiftedPath I c d)
    (x : Rank.Point (β I) (tag I) c) (z : Rank.Point (β I) (tag I) d) :
    PositiveWord.represented (source I) p.word x z ↔ p.oldPrefix.support x.val z.val := by
  induction p generalizing x with
  | edge a =>
    change (source I).colour x z = some a ↔ S.colour x.val z.val = some a.val
    exact Rank.colour_some_iff S (β I) (tag I) x z a
  | @snoc m n p a ih =>
    change PositiveWord.represented (source I)
      (PositiveWord.append (source I) p.word (.single a)) x z ↔ _
    rw [PositiveWord.represented_append]
    change (∃ y, PositiveWord.represented (source I) p.word x y ∧
      (source I).colour y z = some a) ↔
      P.masks.masked (TRel.comp p.oldPrefix.support (S.atomRel a.val)) _ _ x.val z.val
    constructor
    · rintro ⟨y,hxy,hyz⟩
      exact ⟨⟨y.val,(ih x y).mp hxy,
        (Rank.colour_some_iff S (β I) (tag I) y z a).mp hyz⟩,endpoint_allowed I x z⟩
    · rintro ⟨⟨y,hxy,hyz⟩,_⟩
      have hm : P.allows (S.colour x.val y) c.2.val m.2.val := by
        have h := hxy
        rw [(p.oldPrefix.normal_form H C (P.calculus cco)).1] at h
        exact h.2
      have hn : P.allows (S.colour y z.val) m.2.val n.2.val := by
        change S.colour y z.val = some a.val at hyz
        rw [hyz]
        exact atom_allowed I a
      obtain ⟨y',he,he'⟩ := Realization.midpoint_readout P cco I x z y hm hn
      refine ⟨y',(ih x y').mpr ((support_colour_iff P cco I p he.symm).mp hxy),?_⟩
      apply (Rank.colour_some_iff S (β I) (tag I) y' z a).mpr
      exact he'.trans hyz

/-- FULL represented path normal form in the actual canonical source;
logical Id outputs and repeated points have not been discarded. -/
theorem represented_lifted_path {c d : Rank.Child (β I)} (p : LiftedPath I c d)
    (x : Rank.Point (β I) (tag I) c) (z : Rank.Point (β I) (tag I) d) :
    PositiveWord.represented (source I) p.word x z ↔
      PositiveWord.represented S (forgetWord I p.word) x.val z.val := by
  rw [represented_iff_support P cco I p x z,
    (p.oldPrefix.normal_form H C (P.calculus cco)).1,p.old_word_relation]
  exact and_iff_left (endpoint_allowed I x z)

theorem represented_normal_form {c d : Rank.Child (β I)}
    (p : PositiveWord (source I) c d)
    (x : Rank.Point (β I) (tag I) c) (z : Rank.Point (β I) (tag I) d) :
    PositiveWord.represented (source I) p x z ↔
      PositiveWord.represented S (forgetWord I p) x.val z.val := by
  simpa only [LiftedPath.word_ofWord] using
    represented_lifted_path P cco I (LiftedPath.ofWord p) x z

/-- Both diversity guards are taken only AFTER actual marked SAP has
been established independently from original SAP. -/
theorem profile_normal_form (sap : AgeSAP S) {c d : Rank.Child (β I)}
    (p : PositiveWord (source I) c d) (a : (source I).Atom c d) :
    a ∈ PositiveWord.profile (source I) p ↔
      a.val ∈ PositiveWord.profile S (forgetWord I p) := by
  obtain ⟨x,y,hc⟩ := (source I).realized a
  have hcOld := (Rank.colour_some_iff S (β I) (tag I) x y a).mp hc
  rw [profile_iff_represented (source I) (homogeneous I) (SAP.unary_source_sap P cco I sap) p hc,
    represented_normal_form P cco I p x y,
    ← profile_iff_represented S H sap (forgetWord I p) hcOld]

/-- The literal original-atom image of every actual lifted positive
STRONG profile is the old STRONG profile intersected with its endpoint
mask, including fixed inactive labels and repeated sort labels. -/
theorem profile_image_normal_form (sap : AgeSAP S) {c d : Rank.Child (β I)}
    (p : PositiveWord (source I) c d) :
    Subtype.val '' PositiveWord.profile (source I) p =
      {a | a ∈ PositiveWord.profile S (forgetWord I p) ∧
        P.allows (some a) c.2.val d.2.val} := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨(profile_normal_form P cco I sap p b).mp hb,atom_allowed I b⟩
  · rintro ⟨ha,hm⟩
    obtain ⟨b,hb⟩ := Realization.atom_exists_of_allowed P cco I a hm
    refine ⟨b,(profile_normal_form P cco I sap p b).mpr ?_,hb⟩
    rwa [hb]

end
end CCO.PairSafeSplit.Strong
