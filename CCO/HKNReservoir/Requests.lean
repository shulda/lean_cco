import CCO.HKNReservoir.SourceAutomorphisms
import AllThoseEPPA.Relabelling
import AllThoseEPPA.Irreducible
import Mathlib.Data.Fintype.Powerset

universe u v w z x
namespace CCO.HKNReservoir
noncomputable section
open AllThoseEPPA
variable {B : Type u} {K : Type v} {Atom : Type w} {Γ : Type z} [Group Γ]
variable (tag : Γ →* Equiv.Perm B) {V : Type x}

/-- Original requests retain their language component even on empty domain.
Functional closure is NOT required until their saturation is constructed. -/
structure Request (D : Data B K Atom V) where
  lang : Γ
  point : PartialEquiv V V
  owner : ∀ x ∈ point.source, D.owner (point x) = tag lang (D.owner x)
  fine : ∀ a x y, x ∈ point.source → y ∈ point.source → (D.fine a (point x) (point y) ↔ D.fine a x y)

/-- Every global component gives a distinct genuine empty partial request. -/
def emptyRequest (D : Data B K Atom V) (γ : Γ) : Structure.PartialAutomorphism (action tag) (encode D) where
  lang := γ
  toPartialEquiv := PartialEquiv.ofSet ∅
  source_closed := (isClosed_encode_iff D ∅).mpr (by intro k x hx; exact False.elim hx)
  target_closed := (isClosed_encode_iff D ∅).mpr (by intro k x hx; exact False.elim hx)
  map_rel_iff := by
    intro n R xs hx
    exact False.elim (hx (Language.firstIndex R))
  map_func := by
    intro n F xs hx
    cases F with
    | translate k => exact False.elim (hx 0)

@[simp] theorem emptyRequest_lang (D : Data B K Atom V) (γ : Γ) : (emptyRequest tag D γ).lang = γ := rfl
@[simp] theorem emptyRequest_source (D : Data B K Atom V) (γ : Γ) : (emptyRequest tag D γ).source = ∅ := rfl
@[simp] theorem emptyRequest_target (D : Data B K Atom V) (γ : Γ) : (emptyRequest tag D γ).target = ∅ := rfl

theorem emptyRequest_distinct (D : Data B K Atom V) {γ δ : Γ} (hne : γ ≠ δ) :
    emptyRequest tag D γ ≠ emptyRequest tag D δ := fun he => hne (congrArg (·.lang) he)

/-- A finite owner group gives the actual finite relabel orbit. -/
theorem finite_relabel_orbit [Finite Γ] (D : Structure (Signature B K Atom) V) : D.HasFiniteRelabelOrbit (action tag) := Set.finite_range _

/-- A complete diversity structure cannot split freely, even if it has
only one regular packet (or fewer than two vertices). -/
theorem encode_irreducible_of_complete (D : Data B K Atom V)
    (hD : ∀ x y, x ≠ y → ∃ a, D.fine a x y) : (encode D).IsIrreducible := by
  constructor
  intro d
  obtain ⟨x,hx⟩ := (Set.ne_univ_iff_exists_notMem d.left).mp d.left_proper
  obtain ⟨y,hy⟩ := (Set.ne_univ_iff_exists_notMem d.right).mp d.right_proper
  have hyl : y ∈ d.left := by
    have hh : y ∈ d.left ∪ d.right := d.cover ▸ Set.mem_univ y
    exact hh.resolve_right hy
  have hxy : x ≠ y := fun he => hx (he ▸ hyl)
  obtain ⟨a,ha⟩ := hD x y hxy
  rcases d.rel_local (.fine a) (![x,y]) ha with hl | hr
  · exact hx (hl 0)
  · exact hy (hr 1)

theorem finite_partialEquiv [Finite V] : Finite (PartialEquiv V V) := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  apply Finite.of_injective (fun p : PartialEquiv V V => (p.toFun,p.invFun,p.source))
  intro p q he
  apply PartialEquiv.ext
  · exact fun x => congrFun (congrArg Prod.fst he) x
  · exact fun x => congrFun (congrArg (fun z => z.2.1) he) x
  · exact congrArg (fun z => z.2.2) he

theorem finite_requests [Finite Γ] [Finite V] (D : Data B K Atom V) : Finite (Request tag D) := by
  letI := finite_partialEquiv (V:=V)
  apply Finite.of_injective (fun p : Request tag D => (p.lang,p.point))
  intro p q he
  cases p with | mk pl pp po pf =>
    cases q with | mk ql qp qo qf =>
      have hl : pl=ql := congrArg Prod.fst he
      have hp : pp=qp := congrArg Prod.snd he
      cases hl; cases hp; rfl

/-- Orbit saturation uses genuine named functions, with no equality
relation added to the HKN language. -/
def saturation (D : Data B K Atom V) (T : Set V) : Set V := {x | ∃ k y, y ∈ T ∧ D.move k y = x}

theorem saturation_closed [Group K] (D : Data B K Atom V)
    (hm : ∀ g h x, D.move (g*h) x = D.move g (D.move h x)) (T : Set V) :
    (encode D).IsClosed (saturation D T) := by
  rw [isClosed_encode_iff]
  rintro g _ ⟨h,y,hy,rfl⟩
  exact ⟨g*h,y,hy,hm g h y⟩

theorem subset_saturation [Group K] (D : Data B K Atom V) (h1 : ∀ x, D.move 1 x = x) (T : Set V) : T ⊆ saturation D T :=
  fun x hx => ⟨1,x,hx,h1 x⟩

/-- Package an actual bijection between closed subsets as an external
partial automorphism, including exact singleton function-value equality. -/
def partialOfBijOn [Nonempty V] (D : Data B K Atom V) (γ : Γ) (f : V → V)
    (S T : Set V) (hf : Set.BijOn f S T) (hS : (encode D).IsClosed S) (hT : (encode D).IsClosed T)
    (ho : ∀ x ∈ S, D.owner (f x) = tag γ (D.owner x))
    (hc : ∀ a x y, x ∈ S → y ∈ S → (D.fine a (f x) (f y) ↔ D.fine a x y))
    (hm : ∀ k x, x ∈ S → f (D.move k x) = D.move k (f x)) :
    Structure.PartialAutomorphism (action tag) (encode D) where
  lang := γ
  toPartialEquiv := hf.toPartialEquiv f S T
  source_closed := hS
  target_closed := hT
  map_rel_iff := by
    intro n R xs hxs
    cases R with
    | owner b =>
      change D.owner (f (xs 0)) = tag γ b ↔ D.owner (xs 0) = b
      rw [ho (xs 0) (hxs 0)]
      exact (tag γ).injective.eq_iff
    | fine a => exact hc a (xs 0) (xs 1) (hxs 0) (hxs 1)
  map_func := by
    intro n F xs hxs
    cases F with
    | translate k =>
      change f '' {D.move k (xs 0)} = {D.move k (f (xs 0))}
      rw [Set.image_singleton,hm k (xs 0) (hxs 0)]

/-- The whole symbol inventory is finite, not just each arity fibre. -/
def relationSymbolsEquiv : (Σ n, Rel B K Atom n) ≃ B ⊕ Atom where
  toFun | ⟨_,.owner b⟩ => Sum.inl b | ⟨_,.fine a⟩ => Sum.inr a
  invFun | Sum.inl b => ⟨1,.owner b⟩ | Sum.inr a => ⟨2,.fine a⟩
  left_inv := by rintro ⟨_,R⟩; cases R <;> rfl
  right_inv := by intro x; cases x <;> rfl

def functionSymbolsEquiv : (Σ n, Func B K Atom n) ≃ K where
  toFun | ⟨_,.translate k⟩ => k
  invFun k := ⟨1,.translate k⟩
  left_inv := by rintro ⟨_,F⟩; cases F; rfl
  right_inv _ := rfl

theorem finite_signature [Finite B] [Finite K] [Finite Atom] :
    Finite (Σ n, Rel B K Atom n) ∧ Finite (Σ n, Func B K Atom n) :=
  ⟨Finite.of_injective (relationSymbolsEquiv (B:=B) (K:=K) (Atom:=Atom)).toFun (relationSymbolsEquiv).injective,
    Finite.of_injective (functionSymbolsEquiv (B:=B) (K:=K) (Atom:=Atom)).toFun (functionSymbolsEquiv).injective⟩

section ActualSource
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open OwnerTransversal
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type z} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

theorem source_finite_signature :
    Finite (Σ n, Rel ↥B (ResidualData.PacketGroup S H) (S.Atom () ()) n) ∧
      Finite (Σ n, Func ↥B (ResidualData.PacketGroup S H) (S.Atom () ()) n) := by
  letI := S.finiteAtom () ()
  letI := FinitePackets.Normalization.translation_finite S (finitePacket S H) H (R.packet_thin S H)
  exact finite_signature

/-- Completeness of the actual named source discharges irreducibility
of every closed finite source, including a single full packet. -/
theorem finiteSource_irreducible (A : Set (SourceCarrier S H R B))
    (hA : (sourceStructure S H R B hB).IsClosed A) :
    (encode (finiteSourceData S H R B hB A hA)).IsIrreducible := by
  apply encode_irreducible_of_complete
  intro x y hxy
  exact source_fine_complete S H R B hB (fun he => hxy (Subtype.ext he))
end ActualSource

end
end CCO.HKNReservoir
