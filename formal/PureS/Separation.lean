import PureS.Native

namespace UniformS.Separation

def walk {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | n+1, a => f (walk f n a)
theorem walk_add {α} (f : α → α) (i j a) :
    walk f (i+j) a = walk f j (walk f i a) := by
  induction j <;> simp_all [walk]

/-- The bound is uniform in the initial state and does not use the duration of
    a successful run as input. The witness enumeration is executable. -/
theorem finite_cutoff {Q : Type} (all : List Q) (complete : ∀ q, q ∈ all)
    (f : Q → Q) (accept : Q → Bool) (q : Q) :
    (∃ n, accept (walk f n q) = true) ↔
      (List.range all.length).any (fun n => accept (walk f n q)) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨n,h⟩
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases early : ∃ k < n, accept (walk f k q) = true
      · obtain ⟨k,hk,ha⟩ := early; exact ih k hk ha
      · let visited := (List.range (n+1)).map (fun i => walk f i q)
        have distinct : visited.Nodup := by
          apply List.pairwise_iff_getElem.mpr
          intro i j hi hj hij eqv
          have hj' : j ≤ n := by simp [visited] at hj; omega
          have same : walk f i q = walk f j q := by simpa [visited] using eqv
          apply early
          refine ⟨i+(n-j),by omega,?_⟩
          rw [walk_add, same, ← walk_add]
          simpa [show j+(n-j) = n by omega] using h
        have bound := distinct.length_le_of_subset (fun x _ => complete x)
        have hn : n < all.length := by simp [visited] at bound; omega
        exact ⟨n,List.mem_range.mpr hn,h⟩
  · rintro ⟨k,_,h⟩; exact ⟨k,h⟩

/-- Fixed-length tree registers can grow without bound, alias, duplicate and
    permute old whole trees. Only the observations and control are finite. -/
def Vec (α : Type) : Nat → Type
  | 0 => Unit
  | n+1 => α × Vec α n

def mapV {α β} (f : α → β) : (n : Nat) → Vec α n → Vec β n
  | 0,_ => ()
  | n+1,(a,as) => (f a,mapV f n as)

def getV {α} : (n : Nat) → Vec α n → Fin n → α
  | 0,_,i => Fin.elim0 i
  | n+1,(a,as),i => Fin.cases a (fun j => getV n as j) i

theorem get_map {α β} (f : α → β) (n) (v : Vec α n) (i) :
    getV n (mapV f n v) i = f (getV n v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => rcases v with ⟨a,as⟩; cases i using Fin.cases <;> simp [mapV,getV,ih]

def vectors {α} (all : List α) : (n : Nat) → List (Vec α n)
  | 0 => [()]
  | n+1 => all.flatMap (fun a => (vectors all n).map (fun as => (a,as)))

theorem vectors_complete {α} (all : List α) (covers : ∀ a, a ∈ all) (n) (v : Vec α n) :
    v ∈ vectors all n := by
  induction n with
  | zero => cases v; exact List.Mem.head _
  | succ n ih =>
    rcases v with ⟨a,as⟩
    exact List.mem_flatMap.mpr ⟨a,covers a,List.mem_map.mpr ⟨as,ih as,rfl⟩⟩

theorem vectors_length {α} (all : List α) (n) : (vectors all n).length = all.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have count (xs : List α) :
        (xs.flatMap (fun a => (vectors all n).map (fun as => (a,as)))).length =
        xs.length * (vectors all n).length := by
      induction xs with
      | nil => simp
      | cons x xs hj => simp [hj,Nat.succ_mul,Nat.add_comm]
    exact (count all).trans (by rw [ih,Nat.pow_succ,Nat.mul_comm])

inductive Expr (r : Nat) where
  | s
  | var (i : Fin r)
  | app (l r' : Expr r)

def evalE {α} {r} (s : α) (op : α → α → α) (v : Vec α r) : Expr r → α
  | .s => s
  | .var i => getV r v i
  | .app x y => op (evalE s op v x) (evalE s op v y)

def foldT {Q} (s : Q) (op : Q → Q → Q) : Term → Q
  | .s => s
  | .app l r => op (foldT s op l) (foldT s op r)

theorem eval_folds {Q} {r} (s : Q) (op : Q → Q → Q) (v : Vec Term r) (e : Expr r) :
    foldT s op (evalE S Term.app v e) =
      evalE s op (mapV (foldT s op) r v) e := by
  induction e <;> simp_all [evalE,foldT,get_map]

theorem parallel_folds {Q} {r} (s : Q) (op : Q → Q → Q) (v : Vec Term r) (k) (es : Vec (Expr r) k) :
    mapV (foldT s op) k (mapV (evalE S Term.app v) k es) =
    mapV (evalE s op (mapV (foldT s op) r v)) k es := by
  induction k with
  | zero => rfl
  | succ k ih => rcases es with ⟨e,es⟩; exact Prod.ext (eval_folds s op v e) (ih es)

structure RegisterSystem (Q : Type) (r : Nat) where
  leaf : Q
  node : Q → Q → Q
  choose : Vec Q r → Vec (Expr r) r
  accept : Vec Q r → Bool

def RegisterSystem.obs {Q r} (m : RegisterSystem Q r) := mapV (foldT m.leaf m.node) r
def RegisterSystem.tick {Q r} (m : RegisterSystem Q r) (v : Vec Term r) : Vec Term r :=
  mapV (evalE S Term.app v) r (m.choose (m.obs v))
def RegisterSystem.abstractTick {Q r} (m : RegisterSystem Q r) (v : Vec Q r) : Vec Q r :=
  mapV (evalE m.leaf m.node v) r (m.choose v)

theorem RegisterSystem.orbit {Q r} (m : RegisterSystem Q r) (n) (v) :
    m.obs (walk m.tick n v) = walk m.abstractTick n (m.obs v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [walk]
    exact (parallel_folds m.leaf m.node (walk m.tick n v) r
      (m.choose (m.obs (walk m.tick n v)))).trans (congrArg m.abstractTick ih)

theorem combined_cutoff {Q r} (all : List Q) (covers : ∀ q, q ∈ all)
    (m : RegisterSystem Q r) (v : Vec Term r) :
    (∃ n, m.accept (m.obs (walk m.tick n v)) = true) ↔
    (List.range (all.length ^ r)).any (fun k => m.accept (walk m.abstractTick k (m.obs v))) = true := by
  simp only [m.orbit]
  simpa only [vectors_length] using finite_cutoff (vectors all r)
    (vectors_complete all covers r) m.abstractTick m.accept (m.obs v)

def First {Q r} (m : RegisterSystem Q r) (v : Vec Term r) (n : Nat) : Prop :=
  m.accept (m.obs (walk m.tick n v)) = true ∧
  ∀ j, j < n → m.accept (m.obs (walk m.tick j v)) ≠ true

theorem first_numeric_cutoff {Q r} (all : List Q) (covers : ∀ q, q ∈ all)
    (m : RegisterSystem Q r) (v : Vec Term r) (read : Vec Term r → Option Nat) (y : Nat) :
    (∃ n, First m v n ∧ read (walk m.tick n v) = some y) ↔
      ∃ n, n < all.length^r ∧ First m v n ∧ read (walk m.tick n v) = some y := by
  constructor
  · rintro ⟨n,hf,hy⟩
    obtain ⟨j,hj,hit⟩ := List.any_eq_true.mp ((combined_cutoff all covers m v).mp ⟨n,hf.1⟩)
    have hj' := List.mem_range.mp hj
    have hreal : m.accept (m.obs (walk m.tick j v)) = true := by simpa only [m.orbit] using hit
    have lo : n ≤ j := Nat.le_of_not_gt (fun h => hf.2 j h hreal)
    exact ⟨n,by omega,hf,hy⟩
  · rintro ⟨n,_,hf,hy⟩
    exact ⟨n,hf,hy⟩

end UniformS.Separation
