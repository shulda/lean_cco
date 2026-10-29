import CCO.ProfileHelly.Table

universe u v
namespace CCO.ProfileHelly
variable {ι : Type u} (T : Table.{u,v} ι)

/-- A genuinely positive typed word. There is no empty constructor. -/
inductive Word : ι → ι → Type (max u v)
  | single {i j} (a : T.Atom i j) : Word i j
  | cons {i j k} (a : T.Atom i j) (tail : Word j k) : Word i k

namespace Word
variable {T} {i j k l : ι}

def length : {i j : ι} → Word T i j → Nat
  | _,_,single _ => 1
  | _,_,cons _ w => w.length + 1

theorem length_positive (w : Word T i j) : 0 < w.length := by
  cases w <;> simp only [length,Nat.add_pos_right,zero_lt_one]

def profile : {i j : ι} → Word T i j → T.Menu i j
  | _,_,single a => {a}
  | _,_,cons a w => T.product {a} w.profile

def append : {i j k : ι} → Word T i j → Word T j k → Word T i k
  | _,_,_,single a,q => cons a q
  | _,_,_,cons a w,q => cons a (w.append q)

theorem length_append (p : Word T i j) (q : Word T j k) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | single a => simp only [append,length,Nat.add_comm]
  | cons a p ih => simp only [append,length,ih]; omega

theorem profile_append (h : TableLaws T) (p : Word T i j) (q : Word T j k) :
    (p.append q).profile = T.product p.profile q.profile := by
  induction p with
  | single a => rfl
  | cons a p ih =>
    simp only [append,profile,ih]
    exact (h.associative _ _ _).symm

def reverse : {i j : ι} → Word T i j → Word T j i
  | _,_,single a => single (T.conv a)
  | _,_,cons a w => w.reverse.append (single (T.conv a))

theorem profile_reverse (h : TableLaws T) (p : Word T i j) :
    p.reverse.profile = T.opposite p.profile := by
  induction p with
  | single a => exact (T.opposite_singleton a).symm
  | cons a p ih =>
    rw [reverse,profile_append h,ih]
    change T.product (T.opposite p.profile) {T.conv a} = T.opposite (T.product {a} p.profile)
    rw [T.opposite_product,T.opposite_singleton]

theorem profile_nonempty (h : TableLaws T) (p : Word T i j) : p.profile.Nonempty := by
  induction p with
  | single a => exact ⟨a,rfl⟩
  | cons a p ih => exact h.product_nonempty ⟨a,rfl⟩ ih

/-- A finite nonempty family of POSITIVE profiles, allowing duplicates. -/
def Helly : Prop :=
  ∀ (i j : ι) (F : Finset (T.Menu i j)), F.Nonempty →
    (∀ A ∈ F, ∃ w : Word T i j, w.profile = A) →
    (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) → (⋂ A ∈ F, A).Nonempty

end Word
end CCO.ProfileHelly
