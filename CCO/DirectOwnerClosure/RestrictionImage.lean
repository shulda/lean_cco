import CCO.DirectOwnerClosure.HarmlessOwners

/-! C18--C19: the ambient named stabilizer restricts to an IMAGE subgroup
of the full induced group. Neither injectivity nor surjectivity of restriction
is used. In particular induced homogeneity is not an input. -/
universe v w t
namespace CCO.DirectOwnerClosure
open ParityHasse.Original RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def pointwiseFixers (K : Type*) [Group K] [MulAction K M] (A : Finset M) : Subgroup K where
  carrier := {g | ∀ a ∈ A, g • a = a}
  one_mem' := fun _ _ => one_smul _ _
  mul_mem' := by intro g h hg hh a ha; rw [mul_smul,hh a ha,hg a ha]
  inv_mem' := by
    intro g hg a ha
    exact (congrArg (fun x => g⁻¹ • x) (hg a ha).symm).trans (inv_smul_smul g a)

def ownerStabilizer (E : ColourEq S ()) (B : Finset (Owner S E)) : Subgroup (FullAut S) where
  carrier := {g | ∀ b ∈ B, FixesOwner S E b g}
  one_mem' := fun b _ => E.val.refl b.out
  mul_mem' := by
    intro g h hg hh b hb
    apply (fixesOwner_iff S E b (g*h) b.out (Quotient.out_eq b)).mpr
    have hhb := (fixesOwner_iff S E b h b.out (Quotient.out_eq b)).mp (hh b hb)
    exact (fixesOwner_iff S E b g (h.val b.out) hhb).mp (hg b hb)
  inv_mem' := by
    intro g hg b hb
    have he := (fullAut_equivalence S E g⁻¹ b.out (g.val b.out)).mpr (hg b hb)
    change E (g.val.symm b.out) (g.val.symm (g.val b.out)) at he
    have he' : E (g.val.symm b.out) b.out := by
      simpa only [Equiv.symm_apply_apply] using he
    exact E.val.symm he'

def ambientStabilizer (E : ColourEq S ()) (B : Finset (Owner S E)) (A : Finset M) :
    Subgroup (FullAut S) := pointwiseFixers (FullAut S) A ⊓ ownerStabilizer S E B

theorem owner_preserved (E : ColourEq S ()) (B : Finset (Owner S E))
    (g : FullAut S) (hg : g ∈ ownerStabilizer S E B) (x : M)
    (hx : owner S E x ∈ B) : owner S E (g.val x) = owner S E x :=
  (fixesOwner_iff S E (owner S E x) g x rfl).mp (hg _ hx)

/-- The actual restriction homomorphism exists without thinness and also
on the empty carrier. Its target is the FULL owner-named language. -/
def restriction (E : ColourEq S ()) (B : Finset (Owner S E)) (A : Finset M) :
    ambientStabilizer S E B A →* NamedAut S E B where
  toFun g := by
    let e : Equiv.Perm (OwnerUnion S E B) := {
      toFun x := ⟨g.val.val x.val,by
        rw [owner_preserved S E B g.val g.property.2 x.val x.property]
        exact x.property⟩
      invFun x := ⟨g.val.val.symm x.val,by
        change owner S E ((g.val⁻¹).val x.val) ∈ B
        rw [owner_preserved S E B g.val⁻¹
          ((ownerStabilizer S E B).inv_mem g.property.2) x.val x.property]
        exact x.property⟩
      left_inv x := Subtype.ext (g.val.val.symm_apply_apply x.val)
      right_inv x := Subtype.ext (g.val.val.apply_symm_apply x.val) }
    refine ⟨e,?_,?_⟩
    · intro b x
      change owner S E (g.val.val x.val) = b ↔ owner S E x.val = b
      rw [owner_preserved S E B g.val g.property.2 x.val x.property]
    · intro c x y
      change col S (g.val.val x.val) (g.val.val y.val) = c ↔ col S x.val y.val = c
      rw [fullAut_colour]
  map_one' := by apply Subtype.ext; apply Equiv.ext; intro x; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Equiv.ext; intro x; rfl

theorem restriction_apply (E : ColourEq S ()) (B : Finset (Owner S E)) (A : Finset M)
    (g : ambientStabilizer S E B A) (x : OwnerUnion S E B) :
    ((restriction S E B A g).val x).val = g.val.val x.val := rfl

/-- D03's subgroup is literally the range, with no faithfulness or
extension assumption about the restriction homomorphism. -/
def restrictionImage (E : ColourEq S ()) (B : Finset (Owner S E)) (A : Finset M) :
    Subgroup (NamedAut S E B) := (restriction S E B A).range

theorem restriction_fixes_base [DecidableEq M] (E : ColourEq S ())
    (B : Finset (Owner S E)) (A : Finset (OwnerUnion S E B))
    (g : ambientStabilizer S E B (realBase S E B A)) (a : OwnerUnion S E B) (ha : a ∈ A) :
    (restriction S E B (realBase S E B A) g).val a = a := by
  apply Subtype.ext
  exact g.property.1 a.val (Finset.mem_image.mpr ⟨a,ha,rfl⟩)

theorem restrictionImage_le_fixers [DecidableEq M] (E : ColourEq S ())
    (B : Finset (Owner S E)) (A : Finset (OwnerUnion S E B)) :
    restrictionImage S E B (realBase S E B A) ≤ pointwiseFixers (NamedAut S E B) A := by
  rintro g ⟨h,rfl⟩ a ha
  exact restriction_fixes_base S E B A h a ha

def imageOrbit (E : ColourEq S ()) (B : Finset (Owner S E)) (A : Finset M)
    (x : OwnerUnion S E B) : Set (OwnerUnion S E B) :=
  {y | ∃ g : restrictionImage S E B A, g.val.val x = y}

/-- C18: equality of the ambient orbit with the restriction-IMAGE orbit,
as actual original real points. -/
theorem imageOrbit_eq_ambient (E : ColourEq S ()) (B : Finset (Owner S E))
    (A : Finset M) (x : OwnerUnion S E B) :
    Subtype.val '' imageOrbit S E B A x = ownerOrbit S E B A x.val := by
  ext y
  constructor
  · rintro ⟨z,⟨g,hgz⟩,rfl⟩
    obtain ⟨h,hh⟩ := g.property
    refine ⟨h.val,h.property.1,h.property.2,?_⟩
    have hz : (restriction S E B A h).val x = z := by rw [hh]; exact hgz
    exact congrArg Subtype.val hz
  · rintro ⟨g,hg,hB,hgx⟩
    let h : ambientStabilizer S E B A := ⟨g,hg,hB⟩
    let z := (restriction S E B A h).val x
    refine ⟨z,?_,hgx⟩
    exact ⟨⟨restriction S E B A h,⟨h,rfl⟩⟩,rfl⟩

theorem imageOrbit_subset_fullOrbit [DecidableEq M] (E : ColourEq S ())
    (B : Finset (Owner S E)) (A : Finset (OwnerUnion S E B)) (x : OwnerUnion S E B) :
    imageOrbit S E B (realBase S E B A) x ⊆ orbitOver (NamedAut S E B) A x := by
  rintro y ⟨g,hgy⟩
  exact ⟨g.val,restrictionImage_le_fixers S E B A g.property,hgy⟩

variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

/-- C19: infinite ambient named-owner orbits force infinite FULL induced
orbits. No induced homogeneity or joint lifting occurs. -/
theorem outside_packet_induced_not_algebraic [DecidableEq M] [Infinite M]
    (cco : SemanticCCO.{0,v,0,w} S) {E : ColourEq S ()} (hE : UniqueDirection S E)
    (B : Finset (Owner S E)) (A : Finset (OwnerUnion S E B)) (x : OwnerUnion S E B)
    (hx : x.val ∉ packetHull S H (realBase S E B A)) :
    x ∉ algebraicClosure (NamedAut S E B) A := by
  intro halg
  have hfin := halg.subset (imageOrbit_subset_fullOrbit S E B A x)
  have hfambient := hfin.image Subtype.val
  rw [imageOrbit_eq_ambient S E B (realBase S E B A) x] at hfambient
  have howner : x.val ∈ ownerClosure S E B (realBase S E B A) := hfambient
  rw [named_owner_acl S H cco hE B (realBase S E B A)] at howner
  exact hx howner

end CCO.DirectOwnerClosure
