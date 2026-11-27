import Std

namespace UniformS.Queue
variable {Q A : Type}

abbrev Table (Q A : Type) := Q → A → Q × List A

def pass (d : Table Q A) (q : Q) : List A → Q × List A
  | [] => (q,[])
  | a::as => let (r,u) := d q a
             let (s,v) := pass d r as
             (s,u++v)

def execute (d : Table Q A) : Nat → Q → List A → Option (Q × List A)
  | 0,q,w => some (q,w)
  | _+1,_,[] => none
  | n+1,q,a::as => let (r,u) := d q a; execute d n r (as++u)

theorem prefix_exact (d : Table Q A) (w : List A) (q : Q) (rest : List A) :
    execute d w.length q (w++rest) =
      some ((pass d q w).1, rest++(pass d q w).2) := by
  induction w generalizing q rest with
  | nil => simp [execute,pass]
  | cons a w ih =>
    obtain ⟨r,u,ht⟩ : ∃ r u, d q a = (r,u) := ⟨_,_,rfl⟩
    simp [execute,pass,ht,List.append_assoc,ih]

theorem pass_append (d : Table Q A) (u v : List A) (q) :
    pass d q (u++v) =
      let (r,a) := pass d q u
      let (s,b) := pass d r v
      (s,a++b) := by
  induction u generalizing q with
  | nil => simp [pass]
  | cons x xs ih =>
    obtain ⟨r,a,h₁⟩ : ∃ r a, d q x = (r,a) := ⟨_,_,rfl⟩
    obtain ⟨s,b,h₂⟩ : ∃ s b, pass d r xs = (s,b) := ⟨_,_,rfl⟩
    simp [pass,h₁,ih,h₂,List.append_assoc]

inductive Letter where | unit (j : Nat) | delim (j : Nat) deriving DecidableEq,Repr
def block (j n : Nat) := List.replicate n (Letter.unit j) ++ [.delim j]
def row (cells : List (Nat × Nat)) := cells.flatMap (fun (j,n) => block j n)

inductive Operation where | inc | dec deriving DecidableEq,Repr
def delta (j : Nat) (op : Operation) : Table Bool Letter :=
  fun f a => match op,a with
    | .inc,.delim i => (f,if i == j then [.unit i,.delim i] else [.delim i])
    | .dec,.unit i => if i == j && !f then (true,[]) else (f,[.unit i])
    | _,a => (f,[a])

theorem scan_identity (d : Table Bool Letter) (f : Bool) (l : List Letter)
    (h : ∀ a ∈ l, d f a = (f,[a])) : pass d f l = (f,l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp [pass,h a (List.mem_cons_self ..),ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem other_block (j i n) (hi : i ≠ j) (op f) :
    pass (delta j op) f (block i n) = (f,block i n) := by
  apply scan_identity
  intro a ha
  have h : a = .unit i ∨ a = .delim i := by
    simp [block] at ha; grind
  rcases h with rfl | rfl <;> cases op <;> simp [delta,hi]

theorem other_rows (j) (xs : List (Nat × Nat)) (op f) (h : ∀ a ∈ xs, a.1 ≠ j) :
    pass (delta j op) f (row xs) = (f,row xs) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rcases a with ⟨i,n⟩
    have hi := h (i,n) (List.mem_cons_self ..)
    change i ≠ j at hi
    simp only [row,List.flatMap_cons]
    rw [pass_append,other_block _ _ _ hi]
    simpa [row] using congrArg (fun v : Bool × List Letter => (v.1,block i n ++ v.2))
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem inc_block (j n f) : pass (delta j .inc) f (block j n) = (f,block j (n+1)) := by
  induction n with
  | zero => simp [pass,delta,block]
  | succ n ih =>
    change pass _ _ (.unit j :: block j n) = (f,.unit j :: block j (n+1))
    simp [pass,delta,ih]
theorem dec_pos (j n) : pass (delta j .dec) false (block j (n+1)) = (true,block j n) := by
  change pass _ _ (.unit j :: block j n) = _
  have hb : pass (delta j .dec) true (block j n) = (true,block j n) := by
    apply scan_identity
    intro a _; cases a <;> simp [delta]
  simp [pass,delta,hb]
theorem dec_zero (j) : pass (delta j .dec) false (block j 0) = (false,block j 0) := rfl

def result : Operation → Nat → Bool × Nat
  | .inc,n => (false,n+1)
  | .dec,0 => (false,0)
  | .dec,n+1 => (true,n)

theorem sweep (j n : Nat) (op : Operation) (pre post : List (Nat × Nat))
    (hp : ∀ a ∈ pre, a.1 ≠ j) (hs : ∀ a ∈ post, a.1 ≠ j) :
    let tape := row pre ++ block j n ++ row post
    execute (delta j op) tape.length false tape =
      some ((result op n).1,row pre ++ block j (result op n).2 ++ row post) := by
  dsimp only
  have unit : pass (delta j op) false (block j n) = ((result op n).1,block j (result op n).2) := by
    cases op with
    | inc => exact inc_block .. 
    | dec => cases n with | zero => exact dec_zero _ | succ n => exact dec_pos _ _
  have h := prefix_exact (delta j op) (row pre ++ block j n ++ row post) false []
  simpa [pass_append,other_rows j pre op false hp,unit,other_rows j post op _ hs] using h

end UniformS.Queue
