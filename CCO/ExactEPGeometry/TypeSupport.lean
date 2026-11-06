import CCO.RawOrbitals

/-!
# B062: literal traces and finite-type supports

The old relation is an actual equality-inclusive relation on ONE original
carrier. The map `typ` lists only realized prefix unary types; every fiber
is assumed transitive under the actual prefix automorphism action when that
assumption is used.

These lemmas prove the elementary trace facts C04/C11 and the structural
part of C44–C46/C49. They do NOT assert preservation of empty atomic meets,
the AP-only mask-primality contract, or reverse trace-product equality.
-/

universe u v

namespace CCO.ExactEPGeometry

variable {A : Type u} {T : Type v}

/-- The actual relation on two designated fibers. Middle points in typed
composition must belong to the explicitly displayed middle fiber. -/
def trace (typ : A → T) (R : A → A → Prop)
    (s t : T) : TRel (fun q : T => { x : A // typ x = q }) s t :=
  fun x y => R x.val y.val

theorem trace_inter (typ : A → T) (R S : A → A → Prop)
    (s t : T) :
    trace typ (fun x y => R x y ∧ S x y) s t =
      fun x y => trace typ R s t x y ∧ trace typ S s t x y := rfl

theorem trace_union (typ : A → T) (R S : A → A → Prop)
    (s t : T) :
    trace typ (fun x y => R x y ∨ S x y) s t =
      fun x y => trace typ R s t x y ∨ trace typ S s t x y := rfl

theorem trace_converse (typ : A → T) (R : A → A → Prop)
    (s t : T) :
    trace typ (fun x y => R y x) t s =
      TRel.converse (trace typ R s t) := rfl

theorem trace_ident (typ : A → T) (s : T) :
    trace typ (fun x y => x = y) s s =
      TRel.ident (fun q : T => { x : A // typ x = q }) s := by
  funext x y
  apply propext
  constructor
  · exact fun h => Subtype.ext h
  · exact fun h => congrArg Subtype.val h

theorem trace_top (typ : A → T) (s t : T) :
    trace typ (fun _ _ => True) s t =
      TRel.top (fun q : T => { x : A // typ x = q }) s t := rfl

/-- The unconditional direction of (TP), with an ACTUAL middle vertex
of the displayed fiber. The reverse is conditional on the real AP-only
Peirce/mask/marked-age providers and is deliberately not asserted here. -/
theorem trace_comp_forward (typ : A → T)
    (R S : A → A → Prop) (s t w : T)
    (x : { a : A // typ a = s }) (z : { a : A // typ a = w })
    (h : TRel.comp (trace typ R s t) (trace typ S t w) x z) :
    trace typ (RawSymmetric.compose R S) s w x z := by
  obtain ⟨y, hxy, hyz⟩ := h
  exact ⟨y.val, hxy, hyz⟩

/-- Actual finite-type support of an invariant old relation. In contrast
to a formal colour algebra, the existential witnesses are real points. -/
def typeSupport (typ : A → T) (R : A → A → Prop) : T → T → Prop :=
  fun s t => ∃ x y : A, typ x = s ∧ typ y = t ∧ R x y

theorem typeSupport_union (typ : A → T) (R S : A → A → Prop) :
    typeSupport typ (fun x y => R x y ∨ S x y) =
      (fun s t => typeSupport typ R s t ∨ typeSupport typ S s t) := by
  funext s t
  apply propext
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    rcases h with hR | hS
    · exact Or.inl ⟨x, y, hx, hy, hR⟩
    · exact Or.inr ⟨x, y, hx, hy, hS⟩
  · rintro (hR | hS)
    · obtain ⟨x, y, hx, hy, h⟩ := hR
      exact ⟨x, y, hx, hy, Or.inl h⟩
    · obtain ⟨x, y, hx, hy, h⟩ := hS
      exact ⟨x, y, hx, hy, Or.inr h⟩

theorem typeSupport_converse (typ : A → T) (R : A → A → Prop) :
    typeSupport typ (fun x y => R y x) =
      (fun s t => typeSupport typ R t s) := by
  funext s t
  apply propext
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    exact ⟨y, x, hy, hx, h⟩
  · rintro ⟨y, x, hy, hx, h⟩
    exact ⟨x, y, hx, hy, h⟩

theorem typeSupport_ident (typ : A → T)
    (hSurj : Function.Surjective typ) :
    typeSupport typ (fun x y => x = y) =
      (fun s t => s = t) := by
  funext s t
  apply propext
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    cases hxy
    exact hx.symm.trans hy
  · intro hst
    subst t
    obtain ⟨x, hx⟩ := hSurj s
    exact ⟨x, x, hx, hx, rfl⟩

/-- The actual homogeneous-prefix properties needed to align two points
of the SAME complete unary type. Invariance of typ prevents transport from
changing the outer type of a pair. -/
structure TypeHomogeneous (typ : A → T) (G : Type*) [Group G]
    [MulAction G A] : Prop where
  type_invariant : ∀ (g : G) (x : A), typ (g • x) = typ x
  fiber_transitive : ∀ x y : A, typ x = typ y → ∃ g : G, g • x = y

/-- C45: type support respects REAL represented composition. The proof
aligns the two independently witnessed middle points by an automorphism
preserving the original second factor. -/
theorem typeSupport_comp {G : Type*} [Group G] [MulAction G A]
    (typ : A → T) (R S : A → A → Prop)
    (H : TypeHomogeneous typ G)
    (invS : ∀ (g : G) x y, S x y → S (g • x) (g • y)) :
    typeSupport typ (RawSymmetric.compose R S) =
      RawSymmetric.compose (typeSupport typ R) (typeSupport typ S) := by
  funext s t
  apply propext
  constructor
  · rintro ⟨x, z, hx, hz, y, hxy, hyz⟩
    exact ⟨typ y, ⟨x, y, hx, rfl, hxy⟩, ⟨y, z, rfl, hz, hyz⟩⟩
  · rintro ⟨m, ⟨x, y, hx, hy, hxy⟩, ⟨y', z, hy', hz, hy'z⟩⟩
    obtain ⟨g, hgy⟩ := H.fiber_transitive y' y (hy'.trans hy.symm)
    refine ⟨x, g • z, hx, ?_, y, hxy, ?_⟩
    · exact (H.type_invariant g z).trans hz
    · simpa only [hgy] using invS g y' z hy'z

/-- C46: an actual invariant equivalence induces an equivalence on ALL
realized complete unary types, not on arbitrary uninhabited nominal labels. -/
theorem typeSupport_equiv {G : Type*} [Group G] [MulAction G A]
    (typ : A → T) (E : A → A → Prop)
    (H : TypeHomogeneous typ G)
    (hSurj : Function.Surjective typ)
    (hE : RawSymmetric.EquivRel E)
    (invE : ∀ (g : G) x y, E x y → E (g • x) (g • y)) :
    RawSymmetric.EquivRel (typeSupport typ E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    obtain ⟨x, hx⟩ := hSurj s
    exact ⟨x, x, hx, hx, hE.refl x⟩
  · rintro s t ⟨x, y, hx, hy, hxy⟩
    exact ⟨y, x, hy, hx, hE.symm x y hxy⟩
  · rintro s t w ⟨x, y, hx, hy, hxy⟩
      ⟨y', z, hy', hz, hy'z⟩
    obtain ⟨g, hgy⟩ := H.fiber_transitive y' y (hy'.trans hy.symm)
    refine ⟨x, g • z, hx, ?_, hE.trans x y (g • z) hxy ?_⟩
    · exact (H.type_invariant g z).trans hz
    · simpa only [hgy] using invE g y' z hy'z

/-- C49: the whole class of a particular point occupies every unary
type in its image-equivalence class. The witness is transported INSIDE
the original relation by a genuine type-preserving automorphism. -/
theorem typeSupport_occupancy {G : Type*} [Group G] [MulAction G A]
    (typ : A → T) (E : A → A → Prop)
    (H : TypeHomogeneous typ G)
    (invE : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (x : A) (t : T) :
    typeSupport typ E (typ x) t ↔
      ∃ y : A, typ y = t ∧ E x y := by
  constructor
  · rintro ⟨x', y, hx', hy, hxy⟩
    obtain ⟨g, hgx⟩ := H.fiber_transitive x' x hx'
    refine ⟨g • y, (H.type_invariant g y).trans hy, ?_⟩
    simpa only [hgx] using invE g x' y hxy
  · rintro ⟨y, hy, hxy⟩
    exact ⟨x, y, rfl, hy, hxy⟩

end CCO.ExactEPGeometry
