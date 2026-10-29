import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Set.Finite.Basic

/-! Generic invariant full-packet trimming. The acting group need not be
the full automorphism group, abelian, finite, or an elementary two-group.
Root correction uses ONE element of its given global thin subgroup. -/
universe u v w z
namespace CCO.FullRows.Trim
variable {V : Type u} (K : Type v) [Group K] [MulAction K V]

def orbitSet (T : Set V) : Set V := {x | ∃ k : K, ∃ y ∈ T, k • y = x}

def packetHull (F : Setoid V) (A : Set V) : Set V :=
  {x | ∃ a ∈ A, F.r x a}

def orbitTrim (F : Setoid V) (A : Set V) : Set V := orbitSet K (packetHull F A)

theorem subset_orbitSet (T : Set V) : T ⊆ orbitSet K T :=
  fun x hx => ⟨1,x,hx,one_smul K x⟩

theorem orbitSet_smul (T : Set V) (k : K) {x : V} (hx : x ∈ orbitSet K T) :
    k • x ∈ orbitSet K T := by
  obtain ⟨g,y,hy,rfl⟩ := hx
  exact ⟨k*g,y,hy,mul_smul k g y⟩

theorem orbitSet_smul_iff (T : Set V) (k : K) (x : V) :
    k • x ∈ orbitSet K T ↔ x ∈ orbitSet K T := by
  constructor
  · intro hx
    simpa only [inv_smul_smul] using orbitSet_smul K T k⁻¹ hx
  · exact orbitSet_smul K T k

variable {K}

theorem subset_packetHull (F : Setoid V) (A : Set V) : A ⊆ packetHull F A :=
  fun x hx => ⟨x,hx,F.iseqv.refl x⟩

theorem packetHull_closed (F : Setoid V) (A : Set V) {x y : V}
    (hxy : F.r x y) (hy : y ∈ packetHull F A) : x ∈ packetHull F A := by
  obtain ⟨a,ha,hya⟩ := hy
  exact ⟨a,ha,F.iseqv.trans hxy hya⟩

theorem hull_subset_trim (F : Setoid V) (A : Set V) :
    packetHull F A ⊆ orbitTrim K F A := subset_orbitSet K _

theorem source_subset_trim (F : Setoid V) (A : Set V) : A ⊆ orbitTrim K F A :=
  (subset_packetHull F A).trans (hull_subset_trim F A)

theorem trim_finite [Finite V] (F : Setoid V) (A : Set V) :
    (orbitTrim K F A).Finite := Set.toFinite _

theorem trim_full_packets (F : Setoid V) (A : Set V)
    (hF : ∀ (k : K) {x y : V}, F.r x y → F.r (k • x) (k • y))
    {x y : V} (hxy : F.r x y) (hy : y ∈ orbitTrim K F A) : x ∈ orbitTrim K F A := by
  obtain ⟨k,u,hu,rfl⟩ := hy
  refine ⟨k,k⁻¹ • x,?_,by simp⟩
  apply packetHull_closed F A (y:=u) _ hu
  simpa only [inv_smul_smul] using hF k⁻¹ hxy

/-- Restriction to the invariant induced subset; no faithfulness is asserted. -/
def restrictPerm (F : Setoid V) (A : Set V) (k : K) :
    Equiv.Perm {x : V // x ∈ orbitTrim K F A} where
  toFun := fun x => ⟨k • x.val,orbitSet_smul K _ k x.property⟩
  invFun := fun x => ⟨k⁻¹ • x.val,orbitSet_smul K _ k⁻¹ x.property⟩
  left_inv := by intro x; apply Subtype.ext; simp
  right_inv := by intro x; apply Subtype.ext; simp

def restrictHom (F : Setoid V) (A : Set V) :
    K →* Equiv.Perm {x : V // x ∈ orbitTrim K F A} where
  toFun := restrictPerm F A
  map_one' := by ext x; simp [restrictPerm]
  map_mul' := by intro g h; ext x; simp [restrictPerm,mul_smul]

theorem restrict_preserves_colour {Atom : Type w} (colour : V → V → Atom)
    (hcolour : ∀ (k : K) x y, colour (k • x) (k • y) = colour x y)
    (F : Setoid V) (A : Set V) (k : K)
    (x y : {x : V // x ∈ orbitTrim K F A}) :
    colour (restrictPerm F A k x).val (restrictPerm F A k y).val = colour x.val y.val :=
  hcolour k x.val y.val

theorem thin_preserves_hull (F : Setoid V) (A : Set V) (G : Subgroup K)
    (hG : ∀ (g : G) (x : V), F.r ((g:K) • x) x) (g : G)
    {x : V} (hx : x ∈ packetHull F A) : (g:K) • x ∈ packetHull F A :=
  packetHull_closed F A (hG g x) hx

/-- GIVEN any whole-set transporter, one GLOBAL thin correction roots a chosen point. -/
theorem root_correction (F : Setoid V) (A Z : Set V) (G : Subgroup K)
    (hG : ∀ (g : G) (x : V), F.r ((g:K) • x) x)
    (hregular : ∀ x y, F.r x y → ∃ g : G, (g:K) • x = y)
    (delta : K) (hdelta : ∀ x ∈ Z, delta • x ∈ packetHull F A)
    (z : V) (hz : z ∈ Z) :
    ∃ k : K, (∀ x ∈ Z, k • x ∈ packetHull F A) ∧ k • z ∈ A := by
  obtain ⟨a,ha,hza⟩ := hdelta z hz
  obtain ⟨g,hg⟩ := hregular (delta • z) a hza
  refine ⟨(g:K)*delta,?_,?_⟩
  · intro x hx
    rw [mul_smul]
    exact thin_preserves_hull F A G hG g (hdelta x hx)
  · rw [mul_smul,hg]
    exact ha

theorem single_packet_root_correction (F : Setoid V) (A Z : Set V) (G : Subgroup K)
    (hF : ∀ (k : K) {x y : V}, F.r x y → F.r (k • x) (k • y))
    (hG : ∀ (g : G) (x : V), F.r ((g:K) • x) x)
    (hregular : ∀ x y, F.r x y → ∃ g : G, (g:K) • x = y)
    (hZ : Z ⊆ orbitTrim K F A) (z : V) (hz : z ∈ Z)
    (hpacket : ∀ x ∈ Z, F.r x z) :
    ∃ k : K, (∀ x ∈ Z, k • x ∈ packetHull F A) ∧ k • z ∈ A := by
  obtain ⟨beta,u,hu,huz⟩ := hZ hz
  have hdelta : ∀ x ∈ Z, beta⁻¹ • x ∈ packetHull F A := by
    intro x hx
    apply packetHull_closed F A (y:=u) _ hu
    have hh := hF beta⁻¹ (hpacket x hx)
    rw [← huz,inv_smul_smul] at hh
    exact hh
  exact root_correction F A Z G hG hregular beta⁻¹ hdelta z hz

theorem owner_image {B : Type w} [MulAction K B] (F : Setoid V) (A : Set V)
    (pi : V → B) (hpi : ∀ (k : K) x, pi (k • x) = k • pi x) :
    pi '' orbitTrim K F A = orbitSet K (pi '' packetHull F A) := by
  ext b
  constructor
  · rintro ⟨x,⟨k,y,hy,hx⟩,rfl⟩
    exact ⟨k,pi y,⟨y,hy,rfl⟩,by rw [← hpi,hx]⟩
  · rintro ⟨k,_,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨k • y,⟨k,y,hy,rfl⟩,hpi k y⟩

/-- This is coverage of the STIPULATED target B, not of any finer owner set. -/
theorem owner_coverage {B : Type w} [MulAction K B] (F : Setoid V) (A : Set V)
    (pi : V → B) (hpi : ∀ (k : K) x, pi (k • x) = k • pi x)
    (hcover : orbitSet K (pi '' A) = Set.univ) :
    pi '' orbitTrim K F A = Set.univ := by
  apply Set.eq_univ_of_forall
  intro b
  have hb : b ∈ orbitSet K (pi '' A) := by rw [hcover]; trivial
  obtain ⟨k,_,⟨a,ha,rfl⟩,hk⟩ := hb
  refine ⟨k • a,⟨k,a,subset_packetHull F A ha,rfl⟩,?_⟩
  exact (hpi k a).trans hk

end CCO.FullRows.Trim
