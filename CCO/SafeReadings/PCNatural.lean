import CCO.SafeReadings.MenuCalculus
import CCO.StrongExact.FinitePC

/-! Naturality of the SAME synchronous finite PC iteration, including
empty Boolean menus. Only the displayed pure action and initial
transport are used; no choice of a second fixed network occurs. -/
universe u v w z a b
namespace CCO.SafeReadings
open Selectors StrongPC
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} (D : PartialDiagram S V)
variable {Γ : Type a} [Group Γ] {N : Type b}

abbrev mapPair (σ : V ≃ V) (p : DistinctPair V) : DistinctPair V :=
  ⟨σ p.src,σ p.dst,fun h => p.ne (σ.injective h)⟩

private theorem names_step (A : PureTagAction S Γ N) (M : Network D)
    (p : DistinctPair V) (n : N) :
    n ∈ names S A.label ⟨D.vertexSort p.src,D.vertexSort p.dst,step D M p⟩ ↔
      n ∈ names S A.label ⟨D.vertexSort p.src,D.vertexSort p.dst,M p⟩ ∧
      ∀ z (hxz : p.src ≠ z) (hzy : z ≠ p.dst),
        n ∈ names S A.label ⟨D.vertexSort p.src,D.vertexSort p.dst,
          S.product (M ⟨p.src,z,hxz⟩) (M ⟨z,p.dst,hzy⟩)⟩ := by
  constructor
  · rintro ⟨c,hc,hn⟩
    exact ⟨⟨c,hc.1,hn⟩,fun z hxz hzy => ⟨c,hc.2 z hxz hzy,hn⟩⟩
  · rintro ⟨⟨c,hc,hn⟩,h⟩
    refine ⟨c,⟨hc,?_⟩,hn⟩
    intro z hxz hzy
    obtain ⟨d,hd,hdn⟩ := h z hxz hzy
    have he : c = d := A.label_injective _ _ (hn.trans hdn.symm)
    exact he.symm ▸ hd

private theorem names_product_transport (A : PureTagAction S Γ N) (g : Γ)
    {i j k i' j' k' : ι} (P : S.Menu i j) (Q : S.Menu j k)
    (P' : S.Menu i' j') (Q' : S.Menu j' k')
    (hP : A.act g ⟨i,j,P⟩ = ⟨i',j',P'⟩)
    (hQ : A.act g ⟨j,k,Q⟩ = ⟨j',k',Q'⟩) :
    names S A.label ⟨i',k',S.product P' Q'⟩ = names S A.label ⟨i,k,S.product P Q⟩ := by
  have hp := A.product g ⟨i,j,k,P,Q,rfl,rfl,rfl⟩
  rw [hP,hQ] at hp
  have he : A.act g ⟨i,k,S.product P Q⟩ = ⟨i',k',S.product P' Q'⟩ := by
    obtain ⟨i₀,j₀,k₀,P₀,Q₀,h₁,h₂,h₃⟩ := hp
    cases h₁; cases h₂
    exact h₃
  have h := congrArg (names S A.label) he
  rw [A.literal] at h
  exact h.symm

/-- One synchronous step transports through every middle vertex by σ. -/
theorem step_covariant (σ : V ≃ V) (A : PureTagAction S Γ N) (g : Γ)
    (hSort : ∀ x, D.vertexSort (σ x) = A.tag g (D.vertexSort x))
    (M : Network D)
    (hM : ∀ p, A.act g ⟨D.vertexSort p.src,D.vertexSort p.dst,M p⟩ =
      ⟨D.vertexSort (σ p.src),D.vertexSort (σ p.dst),M (mapPair σ p)⟩) (p : DistinctPair V) :
    A.act g ⟨D.vertexSort p.src,D.vertexSort p.dst,step D M p⟩ =
      ⟨D.vertexSort (σ p.src),D.vertexSort (σ p.dst),step D M (mapPair σ p)⟩ := by
  have hnames (q : DistinctPair V) :
      names S A.label ⟨D.vertexSort (σ q.src),D.vertexSort (σ q.dst),M (mapPair σ q)⟩ =
      names S A.label ⟨D.vertexSort q.src,D.vertexSort q.dst,M q⟩ := by
    have h := congrArg (names S A.label) (hM q)
    rw [A.literal] at h
    exact h.symm
  apply A.tagged_names_injective
  · exact ⟨(A.source g _).trans (hSort p.src).symm,
      (A.target g _).trans (hSort p.dst).symm⟩
  · rw [A.literal]
    ext n
    rw [names_step S D A M p,names_step S D A M (mapPair σ p)]
    constructor
    · rintro ⟨hn,h⟩
      refine ⟨(hnames p).symm ▸ hn,?_⟩
      intro z hxz hzy
      obtain ⟨z,rfl⟩ := σ.surjective z
      have hx : p.src ≠ z := fun he => hxz (congrArg σ he)
      have hy : z ≠ p.dst := fun he => hzy (congrArg σ he)
      have hp := names_product_transport S A g
        (M ⟨p.src,z,hx⟩) (M ⟨z,p.dst,hy⟩)
        (M (mapPair σ ⟨p.src,z,hx⟩)) (M (mapPair σ ⟨z,p.dst,hy⟩))
        (hM ⟨p.src,z,hx⟩) (hM ⟨z,p.dst,hy⟩)
      exact hp.symm ▸ h z hx hy
    · rintro ⟨hn,h⟩
      refine ⟨hnames p ▸ hn,?_⟩
      intro z hxz hzy
      have hx : (mapPair σ p).src ≠ σ z := fun he => hxz (σ.injective he)
      have hy : σ z ≠ (mapPair σ p).dst := fun he => hzy (σ.injective he)
      have hp := names_product_transport S A g
        (M ⟨p.src,z,hxz⟩) (M ⟨z,p.dst,hzy⟩)
        (M (mapPair σ ⟨p.src,z,hxz⟩)) (M (mapPair σ ⟨z,p.dst,hzy⟩))
        (hM ⟨p.src,z,hxz⟩) (hM ⟨z,p.dst,hzy⟩)
      exact hp ▸ h (σ z) hx hy

/-- Every iterate, with the SAME iteration index, is natural. -/
theorem iterate_covariant (σ : V ≃ V) (A : PureTagAction S Γ N) (g : Γ)
    (hSort : ∀ x, D.vertexSort (σ x) = A.tag g (D.vertexSort x))
    (hInitial : ∀ p, A.act g ⟨D.vertexSort p.src,D.vertexSort p.dst,initial D p⟩ =
      ⟨D.vertexSort (σ p.src),D.vertexSort (σ p.dst),initial D (mapPair σ p)⟩)
    (n : Nat) (p : DistinctPair V) :
    A.act g ⟨D.vertexSort p.src,D.vertexSort p.dst,iterate D (initial D) n p⟩ =
      ⟨D.vertexSort (σ p.src),D.vertexSort (σ p.dst),iterate D (initial D) n (mapPair σ p)⟩ := by
  induction n generalizing p with
  | zero => exact hInitial p
  | succ n ih => exact step_covariant S D σ A g hSort _ ih p

/-- The canonical fixed network transports, using its actual fixedIndex D. -/
theorem fixedNetwork_covariant (σ : V ≃ V) (A : PureTagAction S Γ N) (g : Γ)
    (hSort : ∀ x, D.vertexSort (σ x) = A.tag g (D.vertexSort x))
    (hInitial : ∀ p, A.act g ⟨D.vertexSort p.src,D.vertexSort p.dst,initial D p⟩ =
      ⟨D.vertexSort (σ p.src),D.vertexSort (σ p.dst),initial D (mapPair σ p)⟩)
    (p : DistinctPair V) :
    A.act g ⟨D.vertexSort p.src,D.vertexSort p.dst,fixedNetwork D p⟩ =
      ⟨D.vertexSort (σ p.src),D.vertexSort (σ p.dst),fixedNetwork D (mapPair σ p)⟩ :=
  iterate_covariant S D σ A g hSort hInitial (fixedIndex D) p

end CCO.SafeReadings
