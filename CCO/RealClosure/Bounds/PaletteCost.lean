import CCO.RealClosure.Bounds.ExactDirections
import CCO.RealClosure.Bounds.Palette
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Finite.Lattice

/-! B011 C06–08: actual facet classes, different-centre exact CRT avoidance,
and the exponential cost in actual old atoms outside the finite packet. -/
noncomputable section
universe v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original ExactCRT RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

/-- Finitely many F-classes inside one E-class, with finite intersections,
force that actual E-class finite. There is no exactness hypothesis. -/
theorem finite_class_of_finite_relative (E F : ColourEq S ())
    (hEF : FiniteClasses S (E ⊓ F)) (x : M)
    [Finite (RelativeClass F.val E.val x)] : Finite (ClassPoint S () E x) := by
  classical
  let A := ClassPoint S () E x
  let Q := RelativeClass F.val E.val x
  let f : A → Q := fun z => Quotient.mk _ z
  have fib : ∀ q : Q, Finite {z : A // f z = q} := by
    intro q
    by_cases hn : Nonempty {z : A // f z = q}
    · let u := Classical.choice hn
      letI := hEF u.val.val
      let g : {z : A // f z = q} → ClassPoint S () (E ⊓ F) u.val.val := fun z =>
        ⟨z.val.val,⟨E.val.trans (E.val.symm u.val.property) z.val.property,by
          have hh := Quotient.exact (u.property.trans z.property.symm)
          exact hh⟩⟩
      apply Finite.of_injective g
      intro z z' h
      have hv : z.val.val = z'.val.val := congrArg
        (fun p : ClassPoint S () (E ⊓ F) u.val.val => p.val) h
      exact Subtype.ext (Subtype.ext hv)
    · letI : IsEmpty {z : A // f z = q} := not_nonempty_iff.mp hn
      infer_instance
  letI : Fintype Q := Fintype.ofFinite Q
  letI : ∀ q : Q, Fintype {z : A // f z = q} := fun q => by
    letI := fib q
    exact Fintype.ofFinite _
  let g : A → Σ q : Q, {z : A // f z = q} := fun z => ⟨f z,z,rfl⟩
  exact Finite.of_injective g (fun z z' h =>
    congrArg (fun p : Σ q : Q, {z : A // f z = q} => p.2.val) h)

/-- An infinite actual relative-class set permits choosing a whole lower
class missing ANY displayed finite point set. -/
theorem relative_class_avoiding_points (E F : ColourEq S ()) (x : M)
    [Infinite (RelativeClass E.val F.val x)] (s : Set M) (hs : s.Finite) :
    ∃ y, F x y ∧ ∀ z ∈ s, ¬ E y z := by
  classical
  let Q := RelativeClass E.val F.val x
  let f : Q → Quotient E.val := relativeClassToQuotient E.val F.val x
  let forbidden : Set (Quotient E.val) := (Quotient.mk E.val) '' s
  have hforbidden : forbidden.Finite := hs.image _
  have hbad : (f ⁻¹' forbidden).Finite :=
    Set.Finite.preimage (relativeClassToQuotient_injective E.val F.val x).injOn hforbidden
  obtain ⟨q,hq⟩ := hbad.exists_notMem
  obtain ⟨y,rfl⟩ := Quotient.exists_rep q
  refine ⟨y.val,y.property,?_⟩
  intro z hz hyz
  apply hq
  exact ⟨z,hz,Quotient.sound (E.val.symm hyz)⟩

variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
local instance : DecidableEq (Direction S) := Classical.decEq _

/-- The actual deleted-facet quotient is INFINITE. Its finiteness would
make the infinite selected direction class a finite union of finite Kfin
classes. This includes singleton S, whose facet is Kfin. -/
theorem facet_relative_classes_infinite {s : Finset (Direction S)} {D : Direction S}
    (hD : D ∈ s) (x : M) :
    Infinite (RelativeClass (directionSpan S H cco (s.erase D)).val
      (directionSpan S H cco s).val x) := by
  classical
  apply not_finite_iff_infinite.mp
  intro hfin
  let B := exactAsColour S H cco (directionSpan S H cco {D})
  let T := exactAsColour S H cco (directionSpan S H cco (s.erase D))
  let A := exactAsColour S H cco (directionSpan S H cco s)
  have hBA : B ≤ A := directionSpan_mono S H cco (Finset.singleton_subset_iff.mpr hD)
  have hBT : FiniteClasses S (B ⊓ T) := by
    change FiniteClasses S
      (exactAsColour S H cco (directionSpan S H cco {D} ⊓ directionSpan S H cco (s.erase D)))
    rw [singleton_inf_deleted_facet S H cco]
    exact finiteExactPacket_finite S H cco
  letI : Finite (RelativeClass T.val A.val x) := hfin
  letI : Finite (RelativeClass T.val B.val x) := Finite.of_injective
    (relativeInclusion T.val B.val A.val hBA x)
    (relativeInclusion_injective T.val B.val A.val hBA x)
  have hBx : Finite (ClassPoint S () B x) := finite_class_of_finite_relative S B T hBT x
  have hB : FiniteClasses S B := (finiteClasses_iff_at S H B x).mpr hBx
  exact D.property.1 (finiteClasses_of_le S
    (direction_le_span S H cco (s := {D}) (by simp)) hB)

private theorem erased_facets_union {s : Finset (Direction S)} {D E : Direction S}
    (hD : D ∈ s) (hE : E ∈ s) (hne : D ≠ E) : (s.erase D) ∪ (s.erase E) = s := by
  classical
  apply Finset.Subset.antisymm
  · exact Finset.union_subset (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  · intro J hJ
    by_cases he : J = D
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
        ⟨fun h => hne (he.symm.trans h),hJ⟩)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hJ⟩)

/-- Different-centre ACTUAL exact-class Helly yields one real point outside
F[x] and every deleted facet. Each chosen facet class misses the finite
POINT set F[x]; F itself is not passed to exact Helly. -/
theorem exists_span_facet_avoiding_point (s : Finset (Direction S)) (hs : s.Nonempty)
    (x : M) : ∃ y, (directionSpan S H cco s).val x y ∧
      ¬ finitePacket S H x y ∧
      ∀ D ∈ s, ¬ (directionSpan S H cco (s.erase D)).val x y := by
  classical
  let A := directionSpan S H cco s
  let F := finitePacket S H
  let forbidden : Set M := {z | F x z}
  have hf : forbidden.Finite := by
    letI : Finite forbidden := finitePacket_finite S H x
    exact Set.toFinite _
  let E : ↥s → ExactOriginal S H cco := fun D => directionSpan S H cco (s.erase D.val)
  have get (D : ↥s) : ∃ y, A.val x y ∧ ∀ z ∈ forbidden, ¬ (E D).val y z := by
    letI : Infinite (RelativeClass (exactAsColour S H cco (E D)).val
        (exactAsColour S H cco A).val x) :=
      facet_relative_classes_infinite S H cco D.property x
    exact relative_class_avoiding_points S (exactAsColour S H cco (E D))
      (exactAsColour S H cco A) x forbidden hf
  let centre : ↥s → M := fun D => Classical.choose (get D)
  have hc (D : ↥s) : A.val x (centre D) ∧
      ∀ z ∈ forbidden, ¬ (E D).val (centre D) z := Classical.choose_spec (get D)
  have pair : ∀ D J : ↥s, ∃ z, (E D).val (centre D) z ∧ (E J).val (centre J) z := by
    intro D J
    by_cases he : D = J
    · subst J
      exact ⟨centre D,(E D).val.refl _,(E D).val.refl _⟩
    · have hv : D.val ≠ J.val := fun h => he (Subtype.ext h)
      have hjoin : E D ⊔ E J = A := by
        rw [← directionSpan_union]
        exact congrArg (directionSpan S H cco)
          (erased_facets_union S D.property J.property hv)
      have ha : A.val (centre D) (centre J) := A.val.trans (A.val.symm (hc D).1) (hc J).1
      have hh : ((E D).val ⊔ (E J).val) (centre D) (centre J) := by
        change (E D ⊔ E J).val (centre D) (centre J)
        rw [hjoin]
        exact ha
      obtain ⟨z,hd,hj⟩ := (sup_relation_iff S H
        (exactAsColour S H cco (E D)) (exactAsColour S H cco (E J)) _ _).mp hh
      exact ⟨z,hd,(E J).val.symm hj⟩
  obtain ⟨y,hy⟩ := exactEq_classHelly S H (semanticCCO_change_universe S cco) E centre pair
  let D₀ : ↥s := ⟨Classical.choose hs,Classical.choose_spec hs⟩
  refine ⟨y,?_,?_,?_⟩
  · exact A.val.trans (hc D₀).1
      ((directionSpan_mono S H cco (Finset.erase_subset _ _)) (hy D₀))
  · intro hF
    exact (hc D₀).2 y hF (hy D₀)
  · intro D hD hxy
    let d : ↥s := ⟨D,hD⟩
    have hcx : (E d).val (centre d) x := (E d).val.trans (hy d) ((E d).val.symm hxy)
    exact (hc d).2 x (F.val.refl x) hcx

/-- One actual OLD colour for each nonempty subset, with all exact Boolean
facet tests and the NONEXACT packet exclusion retained. -/
theorem exists_direction_palette_colour (s : Finset (Direction S)) (hs : s.Nonempty)
    (x : M) : ∃ p : OutsideAtom S H,
      p.val ∈ diversitySupport S (exactAsColour S H cco (directionSpan S H cco s)) ∧
      ∀ D ∈ s, p.val ∉ diversitySupport S
        (exactAsColour S H cco (directionSpan S H cco (s.erase D))) := by
  obtain ⟨y,hA,hF,hfacet⟩ := exists_span_facet_avoiding_point S H cco s hs x
  have hne : x ≠ y := by
    intro he
    subst y
    exact hF ((finitePacket S H).val.refl x)
  obtain ⟨p,hp⟩ := col_some_of_ne S hne
  have hnot : p ∉ diversitySupport S (finitePacket S H) := by
    intro h
    exact hF ((mem_diversitySupport S _ hp).mp h)
  refine ⟨⟨p,hnot⟩,(mem_diversitySupport S _ hp).mpr hA,?_⟩
  intro D hD hm
  exact hfacet D hD ((mem_diversitySupport S _ hp).mp hm)

noncomputable def directionPaletteColour (x : M)
    (s : {s : Finset (Direction S) // s.Nonempty}) : OutsideAtom S H :=
  Classical.choose (exists_direction_palette_colour S H cco s.val s.property x)

theorem directionPaletteColour_spec (x : M)
    (s : {s : Finset (Direction S) // s.Nonempty}) :
    (directionPaletteColour S H cco x s).val ∈
      diversitySupport S (exactAsColour S H cco (directionSpan S H cco s.val)) ∧
    ∀ D ∈ s.val, (directionPaletteColour S H cco x s).val ∉ diversitySupport S
      (exactAsColour S H cco (directionSpan S H cco (s.val.erase D))) :=
  Classical.choose_spec (exists_direction_palette_colour S H cco s.val s.property x)

/-- Equality of the old colour forces inclusion of the selected directions:
Boolean meet then puts it in a forbidden deleted facet. -/
theorem directionPaletteColour_injective (x : M) :
    Function.Injective (directionPaletteColour S H cco x) := by
  have go : ∀ s t : {s : Finset (Direction S) // s.Nonempty},
      directionPaletteColour S H cco x s = directionPaletteColour S H cco x t → s.val ⊆ t.val := by
    intro s t he D hD
    by_contra hDt
    have hs := (directionPaletteColour_spec S H cco x s).1
    have ht := (directionPaletteColour_spec S H cco x t).1
    rw [← he] at ht
    obtain ⟨u,v,hcol⟩ := colour_realized S (some (directionPaletteColour S H cco x s).val)
    have hboth : (directionSpan S H cco s.val ⊓ directionSpan S H cco t.val).val u v :=
      ⟨(mem_diversitySupport S _ hcol).mp hs,(mem_diversitySupport S _ hcol).mp ht⟩
    rw [directionSpan_inf] at hboth
    have hsub : s.val ∩ t.val ⊆ s.val.erase D := by
      intro J hJ
      obtain ⟨hJs,hJt⟩ := Finset.mem_inter.mp hJ
      exact Finset.mem_erase.mpr ⟨fun hj => hDt (hj ▸ hJt),hJs⟩
    have hf := directionSpan_mono S H cco hsub hboth
    exact (directionPaletteColour_spec S H cco x s).2 D hD
      ((mem_diversitySupport S _ hcol).mpr hf)
  intro s t he
  exact Subtype.ext (Finset.Subset.antisymm (go s t he) (go t s he.symm))

include cco

/-- Empty subset gets none; nonempty subsets get DIFFERENT actual diversity
atoms outside F. This proves the cardinal bound without subtracting an
unproved-finite cardinal or treating r=0 separately by an extra premise. -/
theorem direction_palette_power_bound :
    2 ^ directionCount S ≤ outsideAtomCount S H + 1 := by
  classical
  obtain ⟨x⟩ := S.nonemptySort ()
  letI := S.finiteAtom () ()
  letI : Fintype (Direction S) := Fintype.ofFinite _
  let f : Finset (Direction S) → Option (OutsideAtom S H) := fun s =>
    if h : s.Nonempty then some (directionPaletteColour S H cco x ⟨s,h⟩) else none
  have hf : Function.Injective f := by
    intro s t he
    by_cases hs : s.Nonempty <;> by_cases ht : t.Nonempty
    · have hh : some (directionPaletteColour S H cco x ⟨s,hs⟩) =
          some (directionPaletteColour S H cco x ⟨t,ht⟩) := by
        simpa only [f,dif_pos hs,dif_pos ht] using he
      exact congrArg Subtype.val (directionPaletteColour_injective S H cco x (Option.some.inj hh))
    · have hh : some (directionPaletteColour S H cco x ⟨s,hs⟩) = none := by
        simpa only [f,dif_pos hs,dif_neg ht] using he
      cases hh
    · have hh : none = some (directionPaletteColour S H cco x ⟨t,ht⟩) := by
        simpa only [f,dif_neg hs,dif_pos ht] using he
      cases hh
    · exact (Finset.not_nonempty_iff_eq_empty.mp hs).trans
        (Finset.not_nonempty_iff_eq_empty.mp ht).symm
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [directionCount,outsideAtomCount,Nat.card_eq_fintype_card,
    Fintype.card_finset,Fintype.card_option] using hc

theorem direction_palette_bound : 2 ^ directionCount S - 1 ≤ outsideAtomCount S H := by
  have h := direction_palette_power_bound S H cco
  omega

theorem direction_log_bound : directionCount S ≤ Nat.log 2 (outsideAtomCount S H + 1) :=
  Nat.le_log_of_pow_le (by decide) (direction_palette_power_bound S H cco)

end CCO.RealClosure.Bounds
