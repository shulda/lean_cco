import CCO.ExactCRT.TypedPullback

/-!
# Exact convolution from two support-word Helly applications

Only actual pair orbitals, their represented Peirce law and word-support Helly
are used. No homogeneous-source or CCO hypothesis is imposed on this algebra.
In particular this applies to the original ambient action on actual quotients.
-/

universe u v w t

namespace CCO.RigidGroupoid.Geometry.Quotient

open RawExact

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (hOrbit : ∀ {i j} (x : X i) (y : X j) (x' : X i) (y' : X j),
  S.colour x y = S.colour x' y' ↔ GroupActions.orbital (G := G) x y x' y')

include hOrbit

theorem colourInvariant {i j : ι} : S.ColourInvariant (G := G) (i := i) (j := j) := by
  intro g x y
  exact ((hOrbit x y (g • x) (g • y)).mpr ⟨g,rfl,rfl⟩).symm

theorem transitive (i : ι) (x y : X i) : ∃ g : G, g • x = y := by
  have hc : S.colour x x = S.colour y y := by
    rw [(S.colour_none_iff x x).mpr rfl, (S.colour_none_iff y y).mpr rfl]
  obtain ⟨g,hg,_⟩ := (hOrbit x x y y).mp hc
  exact ⟨g,hg⟩

theorem wordInvariant {i j : ι} (w : RawWord S i j) :
    TRel.Invariant (G := G) (RawWord.relation S w) := by
  induction w with
  | nil i =>
      intro g x y hxy
      exact congrArg (fun a => g • a) hxy
  | identity tail ih => exact ih
  | atom a tail ih =>
      rintro g x z ⟨y,hxy,hyz⟩
      exact ⟨g • y,(colourInvariant S hOrbit g x y).trans hxy,ih g y z hyz⟩

theorem presentationInvariant {i j : ι} (P : Presentation S i j) :
    TRel.Invariant (G := G) (evaluate S P) := by
  intro g x y h w hw
  exact wordInvariant S hOrbit w g x y (h w hw)

omit hOrbit
/-- The real optional colour is always ONE word, including logical equality. -/
theorem exists_colour_word {i j : ι} (x : X i) (y : X j) :
    ∃ w : RawWord S i j, RawWord.relation S w = S.rawAtomRel (S.colour x y) := by
  cases hc : S.colour x y with
  | some a =>
      refine ⟨.atom a (.nil j), ?_⟩
      change TRel.comp (S.atomRel a) (TRel.ident X j) = _
      rw [TRel.comp_ident]
      rfl
  | none =>
      have heq := (S.colour_none_iff x y).mp hc
      cases heq
      refine ⟨.nil i, ?_⟩
      exact (exactIdentityAtom_relation S i).symm.trans (exactIdentityAtom_is_optional_none S i)

include hOrbit

/-- The two explicit word families implement the two atomic Peirce rotations.
The empty restriction-list cases are included in the same proof.
-/
theorem convolution_of_wordHelly (helly : WordProfileHelly S)
    {i j k : ι} (D : NonemptyExact S i j) (F : NonemptyExact S j k) :
    TRel.comp (evaluate S D.words) (evaluate S F.words) =
      evaluate S (pairWords S D.words F.words) := by
  funext x z
  apply propext
  constructor
  · exact comp_subset_pairWords S D.words F.words x z
  · intro hPairs
    obtain ⟨c,hc⟩ := exists_colour_word S x z
    have hcxz : RawWord.relation S c x z := by rw [hc]; rfl
    have hcne : TRel.Nonempty (RawWord.relation S c) := ⟨x,z,hcxz⟩
    let cq (q : RawWord S j k) := RawWord.append S c (RawWord.reverse S q)
    have cqrel (q : RawWord S j k) : RawWord.relation S (cq q) =
        TRel.comp (RawWord.relation S c) (TRel.converse (RawWord.relation S q)) := by
      rw [RawWord.relation_append,RawWord.relation_reverse]
    have pp (p) (hp : p ∈ D.words) (q) (hq : q ∈ D.words) :
        TRel.Nonempty (fun a b => RawWord.relation S p a b ∧ RawWord.relation S q a b) := by
      obtain ⟨a,b,hab⟩ := D.nonempty
      exact ⟨a,b,hab p hp,hab q hq⟩
    have cross (p) (hp : p ∈ D.words) (q) (hq : q ∈ F.words) :
        TRel.Nonempty (fun a b => RawWord.relation S p a b ∧ RawWord.relation S (cq q) a b) := by
      have hm : RawWord.append S p q ∈ pairWords S D.words F.words :=
        List.mem_flatMap.mpr ⟨p,hp,List.mem_map.mpr ⟨q,hq,rfl⟩⟩
      have hh := hPairs _ hm
      rw [RawWord.relation_append] at hh
      obtain ⟨b,hp',hq'⟩ := hh
      exact ⟨x,b,hp',by rw [cqrel]; exact ⟨z,hcxz,hq'⟩⟩
    have cc (p) (hp : p ∈ F.words) (q) (hq : q ∈ F.words) :
        TRel.Nonempty (fun a b => RawWord.relation S (cq p) a b ∧ RawWord.relation S (cq q) a b) := by
      obtain ⟨b,d,hbd⟩ := F.nonempty
      obtain ⟨a,had⟩ := TRel.invariant_coserial (G := G) (RawWord.relation S c)
        (transitive S hOrbit k) (wordInvariant S hOrbit c) hcne d
      exact ⟨a,b,by rw [cqrel]; exact ⟨d,had,hbd p hp⟩,
        by rw [cqrel]; exact ⟨d,had,hbd q hq⟩⟩
    let L := D.words ++ F.words.map cq
    have pairL : ∀ p ∈ L, ∀ q ∈ L, TRel.Nonempty
        (fun a b => RawWord.relation S p a b ∧ RawWord.relation S q a b) := by
      intro p hp q hq
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hq with hq | hq
        · exact pp p hp q hq
        · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
          exact cross p hp r hr
      · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
        rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨a,b,hq',hr'⟩ := cross q hq r hr
          exact ⟨a,b,hr',hq'⟩
        · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hq
          exact cc r hr s hs
    obtain ⟨a,b,hab⟩ := helly L
      (fun p hp => by obtain ⟨a,b,h,_⟩ := pairL p hp p hp; exact ⟨a,b,h⟩) pairL
    have hDab : evaluate S D.words a b := fun p hp => hab p (List.mem_append_left _ hp)
    obtain ⟨d,hd⟩ := exists_colour_word S a b
    have hdab : RawWord.relation S d a b := by rw [hd]; rfl
    let dc := RawWord.append S (RawWord.reverse S d) c
    have dcrel : RawWord.relation S dc = TRel.comp
        (TRel.converse (RawWord.relation S d)) (RawWord.relation S c) := by
      rw [RawWord.relation_append,RawWord.relation_reverse]
    have cross2 (q) (hq : q ∈ F.words) : TRel.Nonempty
        (fun b z => RawWord.relation S q b z ∧ RawWord.relation S dc b z) := by
      have hh := hab (cq q) (List.mem_append_right _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
      rw [cqrel] at hh
      obtain ⟨z',hcz,hq'⟩ := hh
      exact ⟨b,z',hq',by rw [dcrel]; exact ⟨a,hdab,hcz⟩⟩
    have dcne : TRel.Nonempty (RawWord.relation S dc) := by
      obtain ⟨z',haz⟩ := TRel.invariant_serial (G := G) (RawWord.relation S c)
        (transitive S hOrbit i) (wordInvariant S hOrbit c) hcne a
      exact ⟨b,z',by rw [dcrel]; exact ⟨a,hdab,haz⟩⟩
    let M := F.words ++ [dc]
    have pairM : ∀ p ∈ M, ∀ q ∈ M, TRel.Nonempty
        (fun b z => RawWord.relation S p b z ∧ RawWord.relation S q b z) := by
      intro p hp q hq
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨b,z,hbz⟩ := F.nonempty
          exact ⟨b,z,hbz p hp,hbz q hq⟩
        · have hqe : q = dc := List.mem_singleton.mp hq
          subst q
          exact cross2 p hp
      · have hpe : p = dc := List.mem_singleton.mp hp
        subst p
        rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨b,z,hq',hdc⟩ := cross2 q hq
          exact ⟨b,z,hdc,hq'⟩
        · have hqe : q = dc := List.mem_singleton.mp hq
          subst q
          obtain ⟨b,z,h⟩ := dcne
          exact ⟨b,z,h,h⟩
    obtain ⟨b',z',hbz⟩ := helly M
      (fun p hp => by obtain ⟨a,b,h,_⟩ := pairM p hp p hp; exact ⟨a,b,h⟩) pairM
    have hF : evaluate S F.words b' z' := fun q hq => hbz q (List.mem_append_left _ hq)
    have hh := hbz dc (List.mem_append_right _ (by simp))
    rw [dcrel] at hh
    obtain ⟨a',hda,hca⟩ := hh
    have hcolour : S.colour a b = S.colour a' b' := by
      rw [hd] at hda
      exact hda.symm
    obtain ⟨g,hga,hgb⟩ := (hOrbit a b a' b').mp hcolour
    have hD' : evaluate S D.words a' b' := by
      simpa only [hga,hgb] using presentationInvariant S hOrbit D.words g a b hDab
    have horb : GroupActions.orbital (G := G) x z a' z' := by
      rw [hc] at hca
      exact (hOrbit x z a' z').mp hca.symm
    exact ((TRel.actual_orbital_peirce x z (evaluate S D.words) (evaluate S F.words)
      (presentationInvariant S hOrbit D.words) (presentationInvariant S hOrbit F.words)).mpr
        ⟨a',z',horb,⟨b',hD',hF⟩⟩) x z (GroupActions.orbital_nonempty x z)

end CCO.RigidGroupoid.Geometry.Quotient
