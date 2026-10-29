import CCO.Selectors.SourceSelectors

/-! Actual evaluated finite-menu families. Original exactness and safe
trace membership remain DIFFERENT predicates. Raw gates and contractions
are reused only on their family-generic types; every calculus instance
must prove these displayed fields. -/
universe u v w z t
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

structure MenuCalculus (Q : Family S) : Prop where
  nonempty : ∀ {i j} {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ Q → D.Nonempty
  top : ∀ i j, (⟨i,j,Set.univ⟩ : TaggedMenu S) ∈ Q
  singleton : ∀ {i j} (a : S.Atom i j), (⟨i,j,{a}⟩ : TaggedMenu S) ∈ Q
  opposite : ∀ {D}, D ∈ Q → flip S D ∈ Q
  product : ∀ {i j k} {D : S.Menu i j} {E : S.Menu j k},
    (⟨i,j,D⟩ : TaggedMenu S) ∈ Q → (⟨j,k,E⟩ : TaggedMenu S) ∈ Q → ⟨i,k,S.product D E⟩ ∈ Q
  inter : ∀ {i j} {D E : S.Menu i j},
    (⟨i,j,D⟩ : TaggedMenu S) ∈ Q → (⟨i,j,E⟩ : TaggedMenu S) ∈ Q →
      (D ∩ E).Nonempty → ⟨i,j,D ∩ E⟩ ∈ Q
  helly : ∀ {i j} (menus : List (S.Menu i j)),
    (∀ D ∈ menus, (⟨i,j,D⟩ : TaggedMenu S) ∈ Q) →
    (∀ D ∈ menus, ∀ E ∈ menus, (D ∩ E).Nonempty) →
      (StrongExact.meetMenus S menus).Nonempty
  distrib : ∀ {i j k} {P : S.Menu i j} {D E : S.Menu j k},
    (⟨i,j,P⟩ : TaggedMenu S) ∈ Q → (⟨j,k,D⟩ : TaggedMenu S) ∈ Q →
    (⟨j,k,E⟩ : TaggedMenu S) ∈ Q → (D ∩ E).Nonempty →
      S.product P (D ∩ E) = S.product P D ∩ S.product P E

structure Current (Q J : Family S) : Prop where
  member : J ⊆ Q
  singleton : ∀ {i j} (a : S.Atom i j), (⟨i,j,{a}⟩ : TaggedMenu S) ∈ J
  opposite : ∀ {D}, D ∈ J → flip S D ∈ J
  downward : ∀ {i j} {D E : S.Menu i j},
    (⟨i,j,D⟩ : TaggedMenu S) ∈ J → (⟨i,j,E⟩ : TaggedMenu S) ∈ Q → E ⊆ D → ⟨i,j,E⟩ ∈ J

structure Filter (Q F : Family S) : Prop where
  member : F ⊆ Q
  opposite : ∀ {D}, D ∈ F → flip S D ∈ F
  left : ∀ {i j k} (P : S.Menu i j), (⟨i,j,P⟩ : TaggedMenu S) ∈ Q →
    ∀ {D : S.Menu j k}, (⟨j,k,D⟩ : TaggedMenu S) ∈ F → ⟨i,k,S.product P D⟩ ∈ F
  right : ∀ {i j k} (P : S.Menu j k), (⟨j,k,P⟩ : TaggedMenu S) ∈ Q →
    ∀ {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ F → ⟨i,k,S.product D P⟩ ∈ F

variable {Λ : Type z} [Group Λ] {N : Type t}

/-- Symmetric ORIGINAL fine names, also on cross-sort converses. -/
def LiteralConverse (A : PureTagAction S Λ N) : Prop :=
  ∀ {i j} (a : S.Atom i j), A.label (S.conv a) = A.label a

/-- Generation closes under ALL ambient Q multipliers. It is not an
application of the original-H inductive generation to traced menus. -/
inductive Generated (Q : Family S) (A : PureTagAction S Λ N) (seed : TaggedMenu S) : TaggedMenu S → Prop
  | seed : Generated Q A seed seed
  | opposite {D} : Generated Q A seed D → Generated Q A seed (flip S D)
  | left {i j k} (P : S.Menu i j) (hP : (⟨i,j,P⟩ : TaggedMenu S) ∈ Q) {D : S.Menu j k} :
      Generated Q A seed ⟨j,k,D⟩ → Generated Q A seed ⟨i,k,S.product P D⟩
  | right {i j k} {D : S.Menu i j} (P : S.Menu j k) (hP : (⟨j,k,P⟩ : TaggedMenu S) ∈ Q) :
      Generated Q A seed ⟨i,j,D⟩ → Generated Q A seed ⟨i,k,S.product D P⟩
  | action (g : Λ) {D} : Generated Q A seed D → Generated Q A seed (A.act g D)

def generatedFamily (Q : Family S) (A : PureTagAction S Λ N) (seed : TaggedMenu S) : Family S :=
  {D | Generated S Q A seed D}

def NoReturn (Q : Family S) (A : PureTagAction S Λ N) : Prop :=
  ∀ seed, seed ∈ Q → ∀ D E,
    D ∈ generatedFamily S Q A seed → E ∈ generatedFamily S Q A seed →
    Parallel S D E → generatedFamily S Q A D = generatedFamily S Q A E → D = E

/-- A singleton reading on any proved menu family. Exactness is not
hidden in this type, and no safe palette is constructed by this record. -/
structure SelectorOn (Q : Family S) where
  choose : ∀ {i j} (D : S.Menu i j), (⟨i,j,D⟩ : TaggedMenu S) ∈ Q → S.Atom i j
  member : ∀ {i j} (D : S.Menu i j) (hD), choose D hD ∈ D
  opposite : ∀ {i j} (D : S.Menu i j) (hD) (hOpp),
    choose (S.opposite D) hOpp = S.conv (choose D hD)
  heredity : ∀ {i j} (E D : S.Menu i j) (hE) (hD),
    E ⊆ D → choose D hD ∈ E → choose E hE = choose D hD
  pc : ∀ {i j k} (D : S.Menu i j) (E : S.Menu j k) (P : S.Menu i k) (hD) (hE) (hP),
    S.PC D E P → S.PC {choose D hD} {choose E hE} {choose P hP}

namespace SelectorOn
variable {S} {Q : Family S}
def Covariant (h : SelectorOn S Q) (A : PureTagAction S Λ N) (hQ : A.Invariant Q) : Prop :=
  ∀ g (D : TaggedMenu S) (hD : D ∈ Q),
    A.label (h.choose (A.act g D).2.2 (hQ g D hD)) = A.label (h.choose D.2.2 hD)
end SelectorOn

/-- The original family instance uses accepted actual SAP+CCO results;
no assertion about safe traces is made by this constructor. -/
theorem original_calculus {G : Type*} [Group G] [∀ i, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S) (cco : SemanticCCO.{u,v,0,w} S) :
    MenuCalculus S (originalFamily S) := by
  let C := exactCalculus_of_SAP_CCO S H sap cco
  exact {
    nonempty := fun h => h.1
    top := fun _ _ => StrongExact.exact_top_of_SAP S H sap
    singleton := StrongExact.exact_singleton S
    opposite := C.opposite
    product := C.product
    inter := StrongExact.exact_inter S
    helly := C.helly
    distrib := C.distrib }

end CCO.SafeReadings
