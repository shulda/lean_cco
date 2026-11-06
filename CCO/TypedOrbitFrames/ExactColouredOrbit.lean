import CCO.TypedOrbitFrames.OrbitClassCounting
import CCO.TypedOrbitFrames.OrbitForkIntersection
import CCO.TypedOrbitFrames.OrbitPrimeIntersection
import CCO.TypedOrbitFrames.OrbitUnforcedSpokes
import CCO.StrongExact.ProfileSemantics

/-!
# Source11 T02: exact-coloured typed orbit infinitude

The complete actual one-point type, full named unary closure, original
proper represented FULL MI, old SAP, original HOM CCO and terminal FULL
NR2 are the source inputs. Every local fork, exact/PC, finite intersection,
pure-power cycle, whole-diagram and common-base alignment obligation is
discharged. No hidden homogeneity/SAP or orbit infinitude provider occurs.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TerminalLattice CCO.TransitionClosure
open CCO.UnaryTermsReturn CCO.RealClosure.Bounds

universe u v w z r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {B : Type z} [Finite B] (base : B ↪ Sigma X)
variable {i : ι} (q : X i)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

/-- The genuine STRONG two-copy spoke domain, before choosing an atom.
Its old anchor has its actual named sort, possibly different from i. -/
def originalSpokeForkMenu {j : ι} (d : X j) : S.Menu i i :=
  {e | ∃ (x z : X i) (y : X j),
    S.colour x y = S.colour q d ∧ S.colour z y = S.colour q d ∧
      S.colour x z = some e}

theorem original_spoke_fork_menu_eq_product
    {j : ι} (d : X j) (a : S.Atom i j)
    (hSpoke : S.colour q d = some a) :
    originalSpokeForkMenu S q d = S.product {a} {S.conv a} := by
  ext e
  constructor
  · rintro ⟨x,z,y,hxy,hzy,hxz⟩
    exact ⟨a,rfl,S.conv a,rfl,x,y,z,hxy.trans hSpoke,
      (S.colour_swap z y a).mp (hzy.trans hSpoke),hxz⟩
  · rintro ⟨a',ha,b,hb,x,y,z,hxy,hyz,hxz⟩
    have haa : a' = a := ha
    have hbb : b = S.conv a := hb
    subst a'
    subst b
    refine ⟨x,z,y,hxy.trans hSpoke.symm,?_,hxz⟩
    have hzy := (S.colour_swap y z (S.conv a)).mp hyz
    rw [S.conv_invol] at hzy
    exact hzy.trans hSpoke.symm

/-- Source11's actual common external diversity atom is obtained from
old two-copy SAP nonemptiness and repeated source07 STRONG primality.
The empty old base uses properness of J, with no diagonal in the menu. -/
theorem original_unforced_exact_type_external_fork_atom
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S)
    (J : OriginalNamedHiddenCoordinate S H i)
    (hunforced :
      originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val q)
        ∉ originalCompletedRealBaseClosure S H sap nr2 (Set.range base)) :
    ∃ e : S.Atom i i, OriginalOrbitForks S base q e ∧
      e ∉ originalEquivDiversityPalette S J.val := by
  classical
  have hq := original_unforced_projection_root_outside_real_base
    S H sap nr2 (Set.range base) J q hunforced
  have hProper := original_named_hidden_full_proper S H J
  obtain ⟨auxiliary,_,_⟩ := Set.not_subset.mp
    (original_proper_equivalence_diversity_top_exits S J.val hProper)
  obtain ⟨e₀,he₀⟩ := original_common_spoke_fork_atom_exists
    S base q H sap hq auxiliary
  letI : Fintype B := Fintype.ofFinite B
  let index : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  let menus : List (S.Menu i i) :=
    List.ofFn (fun k => originalSpokeForkMenu S q (base (index k)).2)
  have hMenu (A : S.Menu i i) (hA : A ∈ menus) :
      ∃ d : B, A = originalSpokeForkMenu S q (base d).2 := by
    obtain ⟨k,hk⟩ := List.mem_ofFn.mp hA
    exact ⟨index k,hk.symm⟩
  have hExact : ∀ A ∈ menus, StrongExact.Exact S A := by
    intro A hA
    obtain ⟨d,rfl⟩ := hMenu A hA
    obtain ⟨a,ha⟩ := S.some_colour_of_ne q (base d).2 (by
      intro hh
      exact hq ⟨d,hh.symm⟩)
    rw [original_spoke_fork_menu_eq_product S q (base d).2 a ha]
    exact StrongExact.exact_product_singletons_of_SAP S H sap a (S.conv a)
  have hEach : ∀ A ∈ menus, ¬ A ⊆ originalEquivDiversityPalette S J.val := by
    intro A hA
    obtain ⟨d,rfl⟩ := hMenu A hA
    obtain ⟨a,ha⟩ := S.some_colour_of_ne q (base d).2 (by
      intro hh
      exact hq ⟨d,hh.symm⟩)
    rw [original_spoke_fork_menu_eq_product S q (base d).2 a ha]
    exact original_unforced_actual_spoke_profile_exits S H sap nr2
      (Set.range base) J q hunforced (base d).2 ⟨d,rfl⟩ a ha
  have hNonempty : (originalStrongMenuIntersection S menus).Nonempty := by
    refine ⟨e₀,?_⟩
    intro A hA
    obtain ⟨d,rfl⟩ := hMenu A hA
    exact he₀ d
  have hExit := original_named_hidden_finite_strong_intersection_exits
    S H sap cco nr2 J menus hExact hEach hNonempty
  have hWitness : ∃ e, e ∈ originalStrongMenuIntersection S menus ∧
      e ∉ originalEquivDiversityPalette S J.val := by
    by_contra h
    apply hExit
    intro e he
    by_contra hnot
    exact h ⟨e,he,hnot⟩
  obtain ⟨e,he,hOutside⟩ := hWitness
  refine ⟨e,?_,hOutside⟩
  intro d
  apply he (originalSpokeForkMenu S q (base d).2)
  apply List.mem_ofFn.mpr
  refine ⟨index.symm d,?_⟩
  exact congrArg (fun d : B => originalSpokeForkMenu S q (base d).2)
    (index.apply_symm_apply d)

/-- `lem:typed-exact-orbit-infinitude`: the realisations of the EXACT
complete old atomic one-point type over a finite COMPLETE original base
occupy infinitely many actual J-classes, whenever F_J(q) is outside its
FULL named quotient-transition closure. All providers are source instances. -/
theorem original_typed_exact_coloured_orbit_infinitude
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S)
    (J : OriginalNamedHiddenCoordinate S H i)
    (hunforced :
      originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val q)
        ∉ originalCompletedRealBaseClosure S H sap nr2 (Set.range base)) :
    (originalExactTypeClasses S base q J.val).Infinite := by
  obtain ⟨e,hfork,hOutside⟩ := original_unforced_exact_type_external_fork_atom
    S base q H sap cco nr2 J hunforced
  exact original_exact_type_classes_infinite_of_external_fork_atom
    S base q H sap (semanticCCO_change_universe S cco)
      (sortNR2_of_originalNR2 S H nr2)
      (original_unforced_projection_root_outside_real_base
        S H sap nr2 (Set.range base) J q hunforced)
      J.val e hfork hOutside

end CCO.TypedOrbitFrames
