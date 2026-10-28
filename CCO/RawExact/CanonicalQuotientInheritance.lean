import CCO.RawExact.CanonicalQuotientCCO

/-!
# C28: all standing properties of actual canonical exact quotients

The actual finite orbital source, finite tuple homogeneity, triangle
fullness, ordinary AP and semantic CCO are assembled from their proved
source theorems. Singleton families give each individual ACTUAL exact
quotient. The identity quotient is canonically identified with original
real points by its literal projection equation; no general quotient
section or coherent choice of lifts is asserted.
-/

universe v w t

namespace CCO.RawExact.CanonicalQuotients

variable {A : Type v}

/-- Canonical identification of a genuine identity quotient with its
original real universe. This is specific to the true equality relation. -/
def identityEquiv (J : Setoid A) (hJ : ∀ x y, J x y ↔ x = y) : Quotient J ≃ A where
  toFun := Quotient.lift id (fun x y h => (hJ x y).mp h)
  invFun := Quotient.mk''
  left_inv q := Quotient.inductionOn q (fun _ => rfl)
  right_inv _ := rfl

theorem identityEquiv_projection (J : Setoid A) (hJ : ∀ x y, J x y ↔ x = y) (x : A) :
    identityEquiv J hJ (Quotient.mk'' x) = x := rfl

theorem identityEquiv_equivariant {G : Type t} [Group G] [MulAction G A]
    (J : Setoid A) [Invariant G J] (hJ : ∀ x y, J x y ↔ x = y)
    (g : G) (q : Quotient J) :
    identityEquiv J hJ (g • q) = g • identityEquiv J hJ q := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

variable (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]

/-- The full C28 source-property record for the concrete ACTUAL
canonical quotient source. Its finite complete symmetric orbital
language is carried by `source S H E` itself. -/
structure SourceProperties (H : HomogeneousSource S G)
    {family : Finset (Setoid A)} (E : ExactData S family) : Prop where
  finite_sorts : Finite (Index family)
  nonempty : ∀ k : Index family, Nonempty (Carrier k)
  countable : Countable (Sigma (fun k : Index family => Carrier k))
  transitive :
    letI : ∀ k : Index family, MulAction G (Carrier k) := action S H E
    ∀ (k : Index family) (x y : Carrier k), ∃ g : G, g • x = y
  actual_pair_orbits :
    letI : ∀ k : Index family, MulAction G (Carrier k) := action S H E
    ∀ {k l : Index family} (x : Carrier k) (y : Carrier l)
      (x' : Carrier k) (y' : Carrier l),
      (source S H E).colour x y = (source S H E).colour x' y' ↔
        GroupActions.orbital (G := G) x y x' y'
  homogeneous :
    letI : ∀ k : Index family, MulAction G (Carrier k) := action S H E
    HomogeneousSource (source S H E) G
  triangles :
    letI : ∀ k : Index family, MulAction G (Carrier k) := action S H E
    ∀ {V : Type v} [Finite V]
      (D : ActualOrbitalDiagram G (fun k : Index family => Carrier k) V),
      D.TrianglesLegal →
      ∃ point : ∀ p, Carrier (D.sort p),
        (∀ p q, D.relation p q (point p) (point q)) ∧
        Function.Injective (fun p => (⟨D.sort p, point p⟩ : Sigma (fun k : Index family => Carrier k)))
  amalgamation : AgeAP (source S H E)
  cycles : SemanticCCO.{v,v,v,v} (source S H E)

/-- C28 complete actual source inheritance. Every component is supplied
by a proved source theorem; no abstract source/property provider remains. -/
theorem source_properties [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    {family : Finset (Setoid A)} (E : ExactData S family) : SourceProperties S H E := by
  refine ⟨inferInstance, nonempty_carrier S, countable_tagged family,
    transitive_carrier S H E, source_colour_eq_iff_orbital S H E,
    homogeneous S H cco E,
    triangle_fullness S H cco E, ageAP S H cco E, semanticCCO S H cco E⟩

/-- The single canonical index for a chosen actual equivalence. -/
def singletonIndex (J : Setoid A) : Index ({J} : Finset (Setoid A)) :=
  ⟨J, Finset.mem_singleton_self J⟩

theorem singletonIndex_unique (J : Setoid A) (k : Index ({J} : Finset (Setoid A))) :
    k = singletonIndex J :=
  Subtype.ext (Finset.mem_singleton.mp k.property)

/-- Its actual carrier is definitionally the requested quotient of A. -/
theorem singleton_carrier (J : Setoid A) : Carrier (singletonIndex J) = Quotient J := rfl

/-- Exactness data for one ACTUAL equivalence relation; no new named sort
is produced by a second presentation of the same relation. -/
def singletonData (J : Setoid A) (B : NonemptyExact S () ())
    (hB : evaluate S B.words = J.r) : ExactData S ({J} : Finset (Setoid A)) where
  exact := fun _ => B
  represents := by
    intro k
    have hk : k.val = J := Finset.mem_singleton.mp k.property
    rw [hk]
    exact hB

/-- Every individual actual full-exact quotient inherits the standing
properties in its ACTUAL finite complete symmetric orbital language.
The sole source sort is `singletonIndex J`, whose carrier is Quotient J. -/
theorem singleton_source_properties [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (J : Setoid A) (B : NonemptyExact S () ()) (hB : evaluate S B.words = J.r) :
    SourceProperties S H (singletonData S J B hB) :=
  source_properties S H cco (singletonData S J B hB)

end CCO.RawExact.CanonicalQuotients
