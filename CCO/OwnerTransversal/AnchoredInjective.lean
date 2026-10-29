import CCO.OwnerTransversal.AnchoredCompletion
import CCO.StabilizerSAP

/-! The OPTIONAL original-SAP branch.  During a repair only displayed
neighbour images are fixed; one formal image is replaced and all protected
formal images stay literally unchanged. -/
universe v w t z
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

include H in
/-- C08, including the entire finite owner list. Representatives are
chosen outside BOTH C and the moving point before original SAP is used. -/
theorem fresh_fixed_owners_of_SAP (sap : AgeSAP S) (E : ColourEq S ())
    (hInfinite : ∀ x : M, Set.Infinite {y : M | E x y})
    {J : Type z} [Finite J] (roots : J → M)
    (C Z : Finset M) (x : M) (hx : x ∉ C) :
    ∃ g : G, (∀ c ∈ C, g • c = c) ∧
      (∀ j, E (roots j) (g • roots j)) ∧ g • x ∉ Z := by
  classical
  letI := Fintype.ofFinite J
  have hreps : ∀ j, ∃ b : M, E (roots j) b ∧ b ∉ insert x C :=
    fun j => (hInfinite (roots j)).exists_notMem_finset (insert x C)
  let b : J → M := fun j => (hreps j).choose
  have hb (j : J) : E (roots j) (b j) ∧ b j ∉ insert x C := (hreps j).choose_spec
  let C' := C ∪ Finset.univ.image b
  have hx' : x ∉ C' := by
    intro hh
    rcases Finset.mem_union.mp hh with hC | hB
    · exact hx hC
    · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hB
      exact (hb j).2 (hj ▸ Finset.mem_insert_self x C)
  let tag : M → Sigma (fun _ : Unit => M) := fun y => ⟨(),y⟩
  let B : FiniteInduced (X := fun _ : Unit => M) := {
    vertices := tag '' (C' : Set M)
    finite_vertices := C'.finite_toSet.image tag }
  have hxB : tag x ∉ B.vertices := by
    rintro ⟨y,hy,hxy⟩
    have hyx : y = x := congrArg (fun p : Sigma (fun _ : Unit => M) => p.2) hxy
    exact hx' (hyx ▸ hy)
  obtain ⟨y,⟨g,hg,hgx⟩,hyZ⟩ := RealAction.orbit_has_fresh_point_of_SAP S H sap B
    (tag x) hxB (tag '' (Z : Set M)) (Z.finite_toSet.image tag)
  have hfix : ∀ c ∈ C', g • c = c := by
    intro c hc
    have hh := hg (tag c) ⟨c,hc,rfl⟩
    change (⟨(),g • c⟩ : Sigma (fun _ : Unit => M)) = ⟨(),c⟩ at hh
    exact congrArg (fun p : Sigma (fun _ : Unit => M) => p.2) hh
  refine ⟨g,fun c hc => hfix c (Finset.mem_union_left _ hc),?_,?_⟩
  · intro j
    have hgb : g • b j = b j := hfix _
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
    have hh := colourInvariant_groupInvariant S H E.property g _ _ (hb j).1
    rw [hgb] at hh
    exact E.val.trans (hb j).1 (E.val.symm hh)
  · intro hz
    apply hyZ
    refine ⟨g • x,hz,?_⟩
    exact hgx

/-- The actual named-owner stabilizer orbit is infinite, not merely
nontrivial.  This formulation also handles an empty owner list. -/
def namedRealOrbit (E : ColourEq S ()) {J : Type z} (roots : J → M)
    (C : Finset M) (x : M) : Set M :=
  {y | ∃ g : G, (∀ c ∈ C, g • c = c) ∧
    (∀ j, E (roots j) (g • roots j)) ∧ g • x = y}

include H in
theorem infinite_named_orbit_of_SAP (sap : AgeSAP S) (E : ColourEq S ())
    (hInfinite : ∀ x : M, Set.Infinite {y : M | E x y})
    {J : Type z} [Finite J] (roots : J → M)
    (C : Finset M) (x : M) (hx : x ∉ C) :
    (namedRealOrbit S (G := G) E roots C x).Infinite := by
  classical
  intro hfin
  obtain ⟨g,hg,hown,hfresh⟩ := fresh_fixed_owners_of_SAP S H sap E hInfinite roots C hfin.toFinset x hx
  exact hfresh (hfin.mem_toFinset.mpr ⟨g,hg,hown,rfl⟩)

noncomputable def collisionPairs {V : Type} [Fintype V] (f : V → M) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ f p.1 = f p.2)

include H in
/-- One-image repair. C contains exactly the recorded neighbour images;
the rest of the anchor and unrecorded collision target are not fixed. -/
theorem repair_record_collision {V : Type} [Fintype V]
    (D : RawRecords S V) (sap : AgeSAP S) (E : ColourEq S ())
    (hInfinite : ∀ x : M, Set.Infinite {y : M | E x y})
    (owner f : V → M) (hf : RawRecords.Hom S D f)
    (hOwner : ∀ x, E (owner x) (f x))
    (A : Finset V) (x y : V) (hxy : x ≠ y) (hfx : f x = f y) (hxA : x ∉ A) :
    ∃ f' : V → M, RawRecords.Hom S D f' ∧ (∀ u, E (owner u) (f' u)) ∧
      (∀ a ∈ A, f' a = f a) ∧
      (collisionPairs f').card < (collisionPairs f).card := by
  classical
  let neighbours : Finset V := Finset.univ.filter (fun u => (D.edge x u).isSome)
  let C := neighbours.image f
  have hxC : f x ∉ C := by
    rintro hh
    obtain ⟨u,hu,huf⟩ := Finset.mem_image.mp hh
    have hu' : (D.edge x u).isSome := (Finset.mem_filter.mp hu).2
    cases he : D.edge x u with
    | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at hu'
    | some a =>
      have hc := hf x u a he
      rw [huf,(S.colour_none_iff _ _).mpr rfl] at hc
      cases hc
  obtain ⟨g,hg,hown,hfresh⟩ := fresh_fixed_owners_of_SAP S H sap E hInfinite
    (fun _ : Unit => f x) C (Finset.univ.image f) (f x) hxC
  let f' := Function.update f x (g • f x)
  have hfresh' : ∀ u, g • f x ≠ f u := by
    intro u hh
    exact hfresh (Finset.mem_image.mpr ⟨u,Finset.mem_univ _,hh.symm⟩)
  have hEdge (u : V) (a : S.Atom () ()) (ha : D.edge x u = some a) :
      g • f u = f u := by
    apply hg
    exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp only [ha,Option.isSome_some]⟩,rfl⟩
  have hhom : RawRecords.Hom S D f' := by
    intro u v a ha
    by_cases hu : u = x
    · subst u
      have hv : v ≠ x := by intro hh; subst v; rw [D.diagonal] at ha; cases ha
      simp only [f',Function.update_self,Function.update_of_ne hv]
      rw [← hEdge v a ha]
      exact (S.colourInvariant_of_homogeneous H g _ _).trans (hf x v a ha)
    · by_cases hv : v = x
      · subst v
        have har : D.edge x u = some a := (D.symmetric x u).trans ha
        simp only [f',Function.update_self,Function.update_of_ne hu]
        rw [colour_symmetric S (f u) (g • f x)]
        rw [← hEdge u a har]
        exact (S.colourInvariant_of_homogeneous H g _ _).trans (hf x u a har)
      · simpa only [f',Function.update_of_ne hu,Function.update_of_ne hv] using hf u v a ha
  have hown' : ∀ u, E (owner u) (f' u) := by
    intro u
    by_cases hu : u = x
    · subst u
      simpa only [f',Function.update_self] using E.val.trans (hOwner x) (hown ())
    · simpa only [f',Function.update_of_ne hu] using hOwner u
  have hfix : ∀ a ∈ A, f' a = f a := by
    intro a ha
    apply Function.update_of_ne
    intro hh
    exact hxA (hh ▸ ha)
  have hSub : collisionPairs f' ⊆ collisionPairs f := by
    intro p hp
    obtain ⟨_,hne,heq⟩ := Finset.mem_filter.mp hp
    have hp1 : p.1 ≠ x := by
      intro hh
      subst hh
      exact hfresh' p.2 (by simpa only [f',Function.update_self,Function.update_of_ne hne.symm] using heq)
    have hp2 : p.2 ≠ x := by
      intro hh
      rw [hh] at heq hne
      exact hfresh' p.1 (by simpa only [f',Function.update_self,Function.update_of_ne hne] using heq.symm)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,
      by simpa only [f',Function.update_of_ne hp1,Function.update_of_ne hp2] using heq⟩
  have hStrict : collisionPairs f' ⊂ collisionPairs f := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hSub,?_⟩
    intro heq
    have hmem : (x,y) ∈ collisionPairs f := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy,hfx⟩
    rw [← heq] at hmem
    have hh := (Finset.mem_filter.mp hmem).2.2
    exact hfresh' y (by simpa only [f',Function.update_self,Function.update_of_ne hxy.symm] using hh)
  exact ⟨f',hhom,hown',hfix,Finset.card_lt_card hStrict⟩

include H in
/-- C09: finite descent on ALL ordered colliding pairs.  Injectivity
only separates formal vertices; unspecified records remain unspecified. -/
theorem injectivize_records {V : Type} [Finite V]
    (D : RawRecords S V) (sap : AgeSAP S) (E : ColourEq S ())
    (hInfinite : ∀ x : M, Set.Infinite {y : M | E x y})
    (owner f : V → M) (hf : RawRecords.Hom S D f)
    (hOwner : ∀ x, E (owner x) (f x))
    (A : Finset V) (complete : RawRecords.CompleteOn S D A) :
    ∃ g : V → M, RawRecords.Hom S D g ∧ (∀ u, E (owner u) (g u)) ∧
      (∀ a ∈ A, g a = f a) ∧ Function.Injective g := by
  classical
  letI := Fintype.ofFinite V
  have aux : ∀ n, ∀ f : V → M, (collisionPairs f).card = n →
      RawRecords.Hom S D f → (∀ x, E (owner x) (f x)) →
      ∃ g : V → M, RawRecords.Hom S D g ∧ (∀ u, E (owner u) (g u)) ∧
        (∀ a ∈ A, g a = f a) ∧ Function.Injective g := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hn hf hown
      by_cases hinj : Function.Injective f
      · exact ⟨f,hf,hown,fun _ _ => rfl,hinj⟩
      · have hh : ∃ x y, x ≠ y ∧ f x = f y := by
          unfold Function.Injective at hinj
          push_neg at hinj
          obtain ⟨x,y,hfx,hxy⟩ := hinj
          exact ⟨x,y,hxy,hfx⟩
        obtain ⟨x,y,hxy,hfx⟩ := hh
        have hOutside : x ∉ A ∨ y ∉ A := by
          by_contra hnot
          push_neg at hnot
          obtain ⟨a,ha⟩ := complete x hnot.1 y hnot.2 hxy
          have hc := hf x y a ha
          rw [hfx,(S.colour_none_iff _ _).mpr rfl] at hc
          cases hc
        have hRepair : ∃ f' : V → M, RawRecords.Hom S D f' ∧
            (∀ u, E (owner u) (f' u)) ∧ (∀ a ∈ A, f' a = f a) ∧
            (collisionPairs f').card < (collisionPairs f).card := by
          rcases hOutside with hx | hy
          · exact repair_record_collision S H D sap E hInfinite owner f hf hown A x y hxy hfx hx
          · exact repair_record_collision S H D sap E hInfinite owner f hf hown A y x hxy.symm hfx.symm hy
        obtain ⟨f',hf',hown',hfix,hlt⟩ := hRepair
        obtain ⟨g,hg,hgown,hgfix,hginj⟩ := ih (collisionPairs f').card (by omega) f' rfl hf' hown'
        exact ⟨g,hg,hgown,fun a ha => (hgfix a ha).trans (hfix a ha),hginj⟩
  exact aux _ f rfl hf hOwner

end CCO.OwnerTransversal
