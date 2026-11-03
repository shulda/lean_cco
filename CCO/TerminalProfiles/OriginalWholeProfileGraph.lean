import CCO.TerminalProfiles.OriginalWholeProfileConnectivityEq
import CCO.PositiveWords

/-!
# B051 TWP: actual W-graph versus full original typed-word RAW graph

The represented whole positive old word R may have loops from genuinely
returning typed paths. Its distinct-point edges are EXACTLY the old
STRONG word-profile W edges by original SAP and pair homogeneity.
Adding/removing those RAW diagonal loops cannot change finite-walk
connectivity. Consequently the stabilized diversity palette is
precisely connectedness of the source's UNDIRECTED OLD W-graph,
not a different quotient graph or an invented positive identity.
-/

universe u v w t

namespace CCO.TerminalProfiles

open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- The genuine old diversity connectedness of one whole typed
positive word is the actual connectedness of its STRONG W-graph.
The only difference between the represented OLD RAW word and W
consists of possible logical diagonal edges. -/
theorem originalWholeProfileConnectedPalette_eq_strong_graph
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (word : PositiveWord S i i) :
    originalWholeProfileConnectedPalette S word =
      S.diversityGuard (fun x y : X i => ∃ n : Nat,
        relPow (S.menuRel (PositiveWord.profile S word)) n x y) := by
  let R : X i → X i → Prop := PositiveWord.represented S word
  let W : S.Menu i i := PositiveWord.profile S word
  let M : X i → X i → Prop := S.menuRel W
  have hInv : TRel.Invariant (G := G) R :=
    PositiveWord.represented_invariant_of_homogeneous S H word
  have hColour : ColourInvariant S i R :=
    groupInvariant_colourInvariant S H hInv
  have hGuard : S.diversityGuard R = W :=
    PositiveWord.diversityGuard_represented_eq_profile_of_SAP S H sap word
  have hMR : ∀ x y : X i, M x y → R x y := by
    intro x y
    rintro ⟨a,ha,hxy⟩
    have haR : a ∈ S.diversityGuard R := by
      rw [hGuard]
      exact ha
    obtain ⟨u,v,hRuv,huv⟩ := haR
    exact (hColour u v x y (huv.trans hxy.symm)).mp hRuv
  have hRM : ∀ x y : X i, R x y → x = y ∨ M x y := by
    intro x y hxy
    by_cases heq : x = y
    · exact Or.inl heq
    · right
      have htag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
        intro h
        apply heq
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h
      obtain ⟨a,hcol⟩ := S.some_colour_of_ne x y htag
      have haR : a ∈ S.diversityGuard R := ⟨x,y,hxy,hcol⟩
      have haW : a ∈ W := by
        rw [←hGuard]
        exact haR
      exact ⟨a,haW,hcol⟩
  have hRwalk : ∀ n x y, relPow R n x y →
      ∃ k : Nat, relPow M k x y := by
    intro n
    induction n with
    | zero =>
        intro x y h
        exact ⟨0,h⟩
    | succ n ih =>
        intro x y h
        obtain ⟨z,hxz,hzy⟩ := h
        obtain ⟨k,hMy⟩ := ih z y hzy
        rcases hRM x z hxz with heq | hMxz
        · subst z
          exact ⟨k,hMy⟩
        · exact ⟨k+1,⟨z,hMxz,hMy⟩⟩
  have hMwalk : ∀ n x y, relPow M n x y →
      relPow R n x y := by
    intro n
    induction n with
    | zero =>
        intro x y h
        exact h
    | succ n ih =>
        intro x y h
        obtain ⟨z,hxz,hzy⟩ := h
        exact ⟨z,hMR x z hxz,ih z y hzy⟩
  apply Set.ext
  intro a
  constructor
  · rintro ⟨x,y,⟨n,hxy⟩,hcol⟩
    obtain ⟨k,hMy⟩ := hRwalk n x y hxy
    exact ⟨x,y,⟨k,hMy⟩,hcol⟩
  · rintro ⟨x,y,⟨n,hxy⟩,hcol⟩
    exact ⟨x,y,⟨n,hMwalk n x y hxy⟩,hcol⟩

end CCO.TerminalProfiles
