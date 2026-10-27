import CCO.Injectivization

/-!
# Homomorphic versus STRONG endpoint diversity colours

For any finite specified diversity diagram, a real homomorphic endpoint
colour is obtainable with all formal vertices injective, provided the
source age has SAP and the original complete colouring is homogeneous.
This applies to finite positively labelled paths and is the semantic
heart of the guarded positive-word correspondence. No CCO, RAW Helly,
NR2, or extra orbit-infinitude assumption is made.
-/

universe u v w

namespace CCO.AtomicSource

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)
variable {V : Type w}
variable (D : PartialDiagram S V)

/-- Diversity colours between the terminal images of an arbitrary
homomorphism, with actual literal ordered endpoint sorts. -/
def guardedEndpoint (u v : V) :
    S.Menu (D.vertexSort u) (D.vertexSort v) :=
  {a | ∃ f : DiagramHom D, S.colour (f.point u) (f.point v) = some a}

/-- The same endpoint colours when the entire finite diagram is realized
injectively on original real points, not merely on its terminals. -/
def strongEndpoint (u v : V) :
    S.Menu (D.vertexSort u) (D.vertexSort v) :=
  {a | ∃ f : DiagramHom D, f.IsInjective ∧
    S.colour (f.point u) (f.point v) = some a}

/-- Arbitrary finite homomorphic diversity endpoint profiles equal their
fully injective STRONG profiles under actual age-SAP and homogeneity.
The original two terminal images are kept fixed throughout the repair. -/
theorem guardedEndpoint_eq_strongEndpoint_of_SAP
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (u v : V) :
    S.guardedEndpoint D u v = S.strongEndpoint D u v := by
  ext a
  constructor
  · rintro ⟨f, hcol⟩
    have hne : f.image u ≠ f.image v :=
      S.atomRel_ne hcol
    let T : Set V := {u, v}
    have hPin : ∀ x ∈ T, ∀ y ∈ T,
        f.image x = f.image y → x = y := by
      intro x hx y hy heq
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl
      · rcases hy with rfl | rfl
        · rfl
        · exact False.elim (hne heq)
      · rcases hy with rfl | rfl
        · exact False.elim (hne heq.symm)
        · rfl
    obtain ⟨f', hinj, hfix, _⟩ :=
      DiagramHom.injectivize_of_SAP H sap f T hPin
        (∅ : Set (Sigma X)) Set.finite_empty
    have hU : f'.point u = f.point u := by
      have h := hfix u (by simp [T])
      change (⟨D.vertexSort u, f'.point u⟩ : Sigma X) =
        (⟨D.vertexSort u, f.point u⟩ : Sigma X) at h
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
    have hV : f'.point v = f.point v := by
      have h := hfix v (by simp [T])
      change (⟨D.vertexSort v, f'.point v⟩ : Sigma X) =
        (⟨D.vertexSort v, f.point v⟩ : Sigma X) at h
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
    exact ⟨f', hinj, by simpa only [hU, hV] using hcol⟩
  · rintro ⟨f, _, hcol⟩
    exact ⟨f, hcol⟩

end CCO.AtomicSource
