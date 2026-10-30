import CCO.StabilizerSAP
import CCO.ParityHasse.Original.OrbitalAlgebra

/-! Old SAP infinitude, before any marked-source or STRONG argument.
All bases are finite sets of actual tagged original real points. -/

universe u v w t
namespace CCO.PairSafeSplit.Infinity
open ParityHasse.Original RealAction
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- A finite stabilizer-invariant old real set contains no point outside
its parameter base. This stronger semantic statement needs no formula oracle. -/
theorem finite_invariant_subset_base (H : HomogeneousSource S G) (sap : AgeSAP S)
    (B : FiniteInduced (X := X)) (T : Set (Sigma X)) (hT : T.Finite)
    (hinv : ∀ g : G, g ∈ pointwiseStabilizer B.vertices →
      ∀ x ∈ T, g • x ∈ T) : T ⊆ B.vertices := by
  intro x hx
  by_contra hxB
  have hInf := infinite_stabilizer_orbit_of_SAP S H sap B x hxB
  apply hInf
  apply hT.subset
  rintro y ⟨g,hg,rfl⟩
  exact hinv g hg x hx

/-- Literal realized complete one-point qf type: the finite conjunction
of the sort/diagonal and all two oriented spoke colours to the base. -/
def typeFibre (B : FiniteInduced (X := X)) {i : ι} (x : X i) : Set (X i) :=
  {y | SameTypeOver S B (⟨i,x⟩ : Sigma X) ⟨i,y⟩}

theorem typeFibre_self (B : FiniteInduced (X := X)) {i : ι} (x : X i) :
    x ∈ typeFibre S B x := ⟨rfl,fun _ _ => rfl,fun _ _ => rfl⟩

/-- The complete finite type is the actual old pointwise-stabilizer orbit. -/
theorem typeFibre_iff_orbit (H : HomogeneousSource S G)
    (B : FiniteInduced (X := X)) {i : ι} (x y : X i) :
    y ∈ typeFibre S B x ↔ (⟨i,y⟩ : Sigma X) ∈ orbitOver (G := G) B.vertices ⟨i,x⟩ := by
  constructor
  · exact sameTypeOver_orbit S H B _ _
  · rintro ⟨g,hg,hxy⟩
    have hcol := H.preserves_colours
    refine ⟨?_,?_,?_⟩
    · rw [← hxy]
      exact (hcol g _ _).symm
    · intro b hb
      have hfix := hg b hb
      simpa only [hxy,hfix] using (hcol g (⟨i,x⟩ : Sigma X) b).symm
    · intro b hb
      have hfix := hg b hb
      simpa only [hxy,hfix] using (hcol g b (⟨i,x⟩ : Sigma X)).symm

theorem typeFibre_avoids (H : HomogeneousSource S G)
    (B : FiniteInduced (X := X)) {i : ι} (x y : X i)
    (hx : (⟨i,x⟩ : Sigma X) ∉ B.vertices) (hy : y ∈ typeFibre S B x) :
    (⟨i,y⟩ : Sigma X) ∉ B.vertices := by
  exact Set.disjoint_left.mp (orbitOver_disjoint_base B.vertices ⟨i,x⟩ hx)
    ((typeFibre_iff_orbit S H B x y).mp hy)

theorem typeFibre_motion (H : HomogeneousSource S G)
    (B : FiniteInduced (X := X)) {i : ι} (x y : X i)
    (hy : y ∈ typeFibre S B x) (g : G)
    (hg : g ∈ pointwiseStabilizer B.vertices) :
    g • y ∈ typeFibre S B x := by
  apply (typeFibre_iff_orbit S H B x (g • y)).mpr
  obtain ⟨k,hk,hky⟩ := (typeFibre_iff_orbit S H B x y).mp hy
  refine ⟨g*k,Subgroup.mul_mem _ hg hk,?_⟩
  rw [mul_smul,hky]
  rfl

theorem typeFibre_infinite (H : HomogeneousSource S G) (sap : AgeSAP S)
    (B : FiniteInduced (X := X)) {i : ι} (x : X i)
    (hx : (⟨i,x⟩ : Sigma X) ∉ B.vertices) : (typeFibre S B x).Infinite := by
  intro hf
  have hi := infinite_stabilizer_orbit_of_SAP S H sap B ⟨i,x⟩ hx
  apply hi
  apply (hf.image (Sigma.mk i)).subset
  rintro z hz
  obtain ⟨g,hg,rfl⟩ := hz
  exact ⟨g • x,(typeFibre_iff_orbit S H B x (g • x)).mpr ⟨g,hg,rfl⟩,rfl⟩

/-- A nontrivial invariant equivalence has a genuinely different point in
each class, by original transitivity; finite original sorts are not assumed. -/
theorem class_has_other (H : HomogeneousSource S G) {i : ι}
    (E : ColourEq S i) (hE : ⊥ < E) (x : X i) : ∃ y, E x y ∧ x ≠ y := by
  have hnot : ¬ E ≤ ⊥ := not_le_of_gt hE
  have hex : ∃ a b, E a b ∧ a ≠ b := by
    by_contra hn
    apply hnot
    intro a b hab
    change a = b
    by_contra hne
    exact hn ⟨a,b,hab,hne⟩
  obtain ⟨a,b,hab,hne⟩ := hex
  obtain ⟨g,hgx⟩ := S.original_sort_transitive_of_homogeneous H i a x
  refine ⟨g • b,?_,?_⟩
  · simpa only [hgx] using colourInvariant_groupInvariant S H E.2 g a b hab
  · intro he
    apply hne
    have hh : g • a = g • b := hgx.trans he
    simpa only [inv_smul_smul] using congrArg (fun z : X i => g⁻¹ • z) hh

theorem equivalence_class_infinite (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (E : ColourEq S i) (hE : ⊥ < E) (x : X i) :
    Set.Infinite {y : X i | E x y} := by
  intro hf
  obtain ⟨y,hxy,hne⟩ := class_has_other S H E hE x
  let B : FiniteInduced (X := X) := ⟨{⟨i,x⟩},Set.finite_singleton _⟩
  have inv : ∀ g : G, g ∈ pointwiseStabilizer B.vertices →
      ∀ z ∈ (Sigma.mk i '' {y : X i | E x y}), g • z ∈ (Sigma.mk i '' {y : X i | E x y}) := by
    intro g hg z hz
    obtain ⟨a,ha,rfl⟩ := hz
    have hgx : g • x = x := by
      simpa only [Sigma.smul_mk,Sigma.mk.injEq,heq_eq_eq,true_and]
        using hg ⟨i,x⟩ (Set.mem_singleton _)
    refine ⟨g • a,?_,rfl⟩
    change E x (g • a)
    simpa only [hgx] using colourInvariant_groupInvariant S H E.2 g x a ha
  have hsub := finite_invariant_subset_base S H sap B _ (hf.image (Sigma.mk i)) inv
  have hEq : (⟨i,y⟩ : Sigma X) = ⟨i,x⟩ := hsub ⟨y,hxy,rfl⟩
  apply hne
  simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hEq.symm

/-- The key old-SAP fact: a realized one-point fibre meets its actual
nontrivial gate class infinitely. No marked-source SAP is used. -/
theorem type_class_infinite (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (E : ColourEq S i) (hE : ⊥ < E)
    (B : FiniteInduced (X := X)) (x : X i)
    (hx : (⟨i,x⟩ : Sigma X) ∉ B.vertices) :
    Set.Infinite (typeFibre S B x ∩ {y | E x y}) := by
  intro hf
  have hc := equivalence_class_infinite S H sap E hE x
  have hi : (Sigma.mk i '' {y : X i | E x y}).Infinite :=
    hc.image (by intro a ha b hb h; exact eq_of_heq (Sigma.mk.inj h).2)
  obtain ⟨p,hp,hpnot⟩ := hi.exists_notMem_finite
    ((hf.image (Sigma.mk i)).union B.finite_vertices)
  obtain ⟨y,hxy,rfl⟩ := hp
  have hyT : y ∉ typeFibre S B x ∩ {z | E x z} := by
    intro hy
    exact hpnot (Or.inl ⟨y,hy,rfl⟩)
  have hne : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
    intro he
    have ex : x = y := eq_of_heq (Sigma.mk.inj he).2
    apply hyT
    rw [← ex]
    exact ⟨typeFibre_self S B x,E.val.refl x⟩
  let B' : FiniteInduced (X := X) :=
    ⟨Set.insert (⟨i,y⟩ : Sigma X) B.vertices,B.finite_vertices.insert _⟩
  let T : Set (Sigma X) := Sigma.mk i '' (typeFibre S B x ∩ {z | E x z})
  have inv : ∀ g : G, g ∈ pointwiseStabilizer B'.vertices →
      ∀ z ∈ T, g • z ∈ T := by
    intro g hg z hz
    obtain ⟨a,ha,rfl⟩ := hz
    have hgB : g ∈ pointwiseStabilizer B.vertices :=
      fun b hb => hg b (Or.inr hb)
    have hgy : g • y = y := by
      simpa only [Sigma.smul_mk,Sigma.mk.injEq,heq_eq_eq,true_and]
        using hg ⟨i,y⟩ (Or.inl rfl)
    refine ⟨g • a,⟨typeFibre_motion S H B x a ha.1 g hgB,?_⟩,rfl⟩
    have hya : E y a := E.val.trans (E.val.symm hxy) ha.2
    have hnew := colourInvariant_groupInvariant S H E.2 g y a hya
    rw [hgy] at hnew
    exact E.val.trans hxy hnew
  have hsub := finite_invariant_subset_base S H sap B' T (hf.image _) inv
  have hxb : (⟨i,x⟩ : Sigma X) ∈ B'.vertices :=
    hsub ⟨x,⟨typeFibre_self S B x,E.val.refl x⟩,rfl⟩
  rcases hxb with he | hb
  · exact hne he
  · exact hx hb

end CCO.PairSafeSplit.Infinity
