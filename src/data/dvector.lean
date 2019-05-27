import tactic.basic data.nat.basic

universes u v w

-- todo: move
lemma forall_eq2 {α β} (y : α) (p : α → β → Prop) : (∀x z, x = y → p x z) ↔ ∀ z, p y z :=
⟨λ h z, h y z rfl, λ h x z hxy, by { subst hxy, apply h }⟩

inductive dvector (α : Type u) : ℕ → Type u
| nil {} : dvector 0
| cons : ∀{n} (x : α) (xs : dvector n), dvector (n+1)

inductive dfin : ℕ → Type
| fz {n} : dfin (n+1)
| fs {n} : dfin n → dfin (n+1)

instance has_zero_dfin {n} : has_zero $ dfin (n+1) := ⟨dfin.fz⟩

-- note from Mario --- use dfin to synergize with dvector
namespace dvector

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l
variables {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

@[simp] protected def zero_eq : ∀(xs : dvector α 0), xs = []
| [] := rfl

@[simp] protected def concat : ∀{n : ℕ} (xs : dvector α n) (x : α), dvector α (n+1)
| _ []      x' := [x']
| _ (x::xs) x' := x::concat xs x'

@[simp] protected def nth : ∀{n : ℕ} (xs : dvector α n) (m : ℕ) (h : m < n), α
| _ []      m     h := by { exfalso, exact nat.not_lt_zero m h }
| _ (x::xs) 0     h := x
| _ (x::xs) (m+1) h := nth xs m (lt_of_add_lt_add_right h)

protected def head (xs : dvector α (n+1)) : α :=
xs.nth 0 $ nat.zero_lt_succ n

@[simp] lemma head_cons {x : α} {xs : dvector α n} : (x::xs).head = x := rfl

protected def nth_cons {n : ℕ} (x : α) (xs : dvector α n) (m : ℕ) (h : m < n) :
  dvector.nth (x::xs) (m+1) (nat.succ_lt_succ h) = dvector.nth xs m h :=
by refl

@[reducible, simp] protected def last {n : ℕ} (xs : dvector α (n+1)) : α :=
  xs.nth n (by {repeat{constructor}})

protected def nth' {n : ℕ} (xs : dvector α n) (m : fin n) : α :=
xs.nth m.1 m.2

protected def nth'' : ∀ {n : ℕ} (xs : dvector α n) (m : dfin n), α
| _ (x::xs) dfin.fz       := x
| _ (x::xs) (dfin.fs (m)) := nth'' xs m

protected def mem : ∀{n : ℕ} (x : α) (xs : dvector α n), Prop
| _ x []       := false
| _ x (x'::xs) := x = x' ∨ mem x xs
instance {n : ℕ} : has_mem α (dvector α n) := ⟨dvector.mem⟩

@[simp] lemma mem_nil {x : α} : ¬(x ∈ @dvector.nil α) := id

@[simp] lemma mem_cons {x x' : α} {xs : dvector α n} : x ∈ x'::xs ↔ x = x' ∨ x ∈ xs := iff.rfl

lemma head_mem {xs : dvector α (n+1)} : xs.head ∈ xs := by { cases xs, simp }


protected def pmem : ∀{n : ℕ} (x : α) (xs : dvector α n), Type
| _ x []       := empty
| _ x (x'::xs) := psum (x = x') (pmem x xs)

protected def mem_of_pmem : ∀{n : ℕ} {x : α} {xs : dvector α n} (hx : xs.pmem x), x ∈ xs
| _ x []       hx := by cases hx
| _ x (x'::xs) hx := by cases hx;[exact or.inl hx, exact or.inr (mem_of_pmem hx)]

@[simp] protected def map (f : α → β) : ∀{n : ℕ}, dvector α n → dvector β n
| _ []      := []
| _ (x::xs) := f x :: map xs

@[simp] protected def map2 (f : α → β → γ) : ∀{n : ℕ}, dvector α n → dvector β n → dvector γ n
| _ []      []      := []
| _ (x::xs) (y::ys) := f x y :: map2 xs ys

@[simp] protected lemma map_id : ∀{n : ℕ} (xs : dvector α n), xs.map (λx, x) = xs
| _ []      := rfl
| _ (x::xs) := by { dsimp, simp* }

@[simp] protected lemma map_congr_pmem {f g : α → β} :
  ∀{n : ℕ} {xs : dvector α n} (h : ∀x, xs.pmem x → f x = g x), xs.map f = xs.map g
| _ []      h := rfl
| _ (x::xs) h :=
  begin
    dsimp, congr' 1, exact h x (psum.inl rfl), apply map_congr_pmem,
    intros x hx, apply h, right, exact hx
  end

@[simp] protected lemma map_congr_mem {f g : α → β} {n : ℕ} {xs : dvector α n}
  (h : ∀x, x ∈ xs → f x = g x) : xs.map f = xs.map g :=
dvector.map_congr_pmem $ λx hx, h x $ dvector.mem_of_pmem hx

@[simp] protected lemma map_congr {f g : α → β} (h : ∀x, f x = g x) :
  ∀{n : ℕ} (xs : dvector α n), xs.map f = xs.map g
| _ []      := rfl
| _ (x::xs) := by { dsimp, simp* }

@[simp] protected lemma map_map (g : β → γ) (f : α → β): ∀{n : ℕ} (xs : dvector α n),
  (xs.map f).map g = xs.map (λx, g (f x))
  | _ []      := rfl
  | _ (x::xs) := by { dsimp, simp* }

protected lemma map_inj {f : α → β} (hf : ∀{{x x'}}, f x = f x' → x = x') {n : ℕ}
  {xs xs' : dvector α n} (h : xs.map f = xs'.map f) : xs = xs' :=
begin
  induction xs; cases xs', refl, simp at h, congr;[apply hf, apply xs_ih]; simp [h]
end

@[simp] protected lemma map_concat (f : α → β) : ∀{n : ℕ} (xs : dvector α n) (x : α),
  (xs.concat x).map f = (xs.map f).concat (f x)
| _ []      x' := by refl
| _ (x::xs) x' := by { dsimp, congr' 1, exact map_concat xs x' }

@[simp] protected lemma map_nth (f : α → β) : ∀{n : ℕ} (xs : dvector α n) (m : ℕ) (h : m < n),
  (xs.map f).nth m h = f (xs.nth m h)
| _ []      m     h := by { exfalso, exact nat.not_lt_zero m h }
| _ (x::xs) 0     h := by refl
| _ (x::xs) (m+1) h := by exact map_nth xs m _

protected lemma concat_nth : ∀{n : ℕ} (xs : dvector α n) (x : α) (m : ℕ) (h' : m < n+1)
  (h : m < n), (xs.concat x).nth m h' = xs.nth m h
| _ []      x' m     h' h := by { exfalso, exact nat.not_lt_zero m h }
| _ (x::xs) x' 0     h' h := by refl
| _ (x::xs) x' (m+1) h' h := by { dsimp, exact concat_nth xs x' m _ _ }

@[simp] protected lemma concat_nth_last : ∀{n : ℕ} (xs : dvector α n) (x : α) (h : n < n+1),
  (xs.concat x).nth n h = x
| _ []      x' h := by refl
| _ (x::xs) x' h := by { dsimp, exact concat_nth_last xs x' _ }

@[simp] protected lemma concat_nth_last' : ∀{n : ℕ} (xs : dvector α n) (x : α) (h : n < n+1),
  (xs.concat x).last = x
:= by apply dvector.concat_nth_last

@[simp] protected def append : ∀{n m : ℕ} (xs : dvector α n) (xs' : dvector α m), dvector α (m+n)
| _ _ []       xs := xs
| _ _ (x'::xs) xs' := x'::append xs xs'

@[simp]protected def insert : ∀{n : ℕ} (x : α) (k : ℕ) (xs : dvector α n), dvector α (n+1)
| n x 0 xs := (x::xs)
| 0 x k xs := (x::xs)
| (n+1) x (k+1) (y::ys) := (y::insert x k ys)

@[simp] protected lemma insert_at_zero : ∀{n : ℕ} (x : α) (xs : dvector α n), dvector.insert x 0 xs = (x::xs) := by {intros, induction n; refl} -- why doesn't {intros, refl} work?

@[simp] protected lemma insert_nth : ∀{n : ℕ} (x : α) (k : ℕ) (xs : dvector α n) (h : k < n+1), (dvector.insert x k xs).nth k h = x
| 0 x k xs h := by {cases h, refl, exfalso, apply nat.not_lt_zero, exact h_a}
| n x 0 xs h := by {induction n, refl, simp*}
| (n+1) x (k+1) (y::ys) h := by simp*

protected lemma insert_cons {n k} {x y : α} {v : dvector α n} : (x::(v.insert y k)) = (x::v).insert y (k+1) :=
by {induction v, refl, simp*}

/- Given a proof that n ≤ m, return the nth initial segment of -/
@[simp]protected def trunc : ∀ (n) {m : ℕ} (h : n ≤ m) (xs : dvector α m), dvector α n
| 0 0 _ xs := []
| 0 (m+1) _ xs := []
| (n+1) 0 _ xs := by {exfalso, cases _x}
| (n+1) (m+1) h (x::xs) := (x::@trunc n m (by { simp at h, exact h }) xs)

@[simp]protected lemma trunc_n_n {n : ℕ} {h : n ≤ n} {v : dvector α n} : dvector.trunc n h v = v :=
  by {induction v, refl, solve_by_elim}

@[simp]protected lemma trunc_0_n {n : ℕ} {h : 0 ≤ n} {v : dvector α n} : dvector.trunc 0 h v = [] :=
  by {induction v, refl, simp}

@[simp]protected lemma trunc_nth {n m l: ℕ} {h : n ≤ m} {h' : l < n} {v : dvector α m} : (v.trunc n h).nth l h' = v.nth l (lt_of_lt_of_le h' h) :=
begin
  induction m generalizing n l, have : n = 0, by cases h; simp, subst this, cases h',
  cases n; cases l, {cases h'}, {cases h'}, {cases v, refl},
  cases v, simp only [m_ih, dvector.nth, dvector.trunc]
end

protected lemma nth_irrel1 : ∀{n k : ℕ} {h : k < n + 1} {h' : k < n + 1 + 1} (v : dvector α (n+1)) (x : α),
  (x :: (v.trunc n (nat.le_succ n))).nth k h = (x::v).nth k h' :=
by {intros, apply @dvector.trunc_nth _ _ _ _ (by {simp, exact dec_trivial}) h (x::v)}

protected def cast {n m} (p : n = m) : dvector α n → dvector α m :=
by { subst p, exact id }

@[simp] protected lemma cast_irrel {n m} {p p' : n = m} {v : dvector α n} : v.cast p = v.cast p' := by refl

@[simp] protected lemma cast_rfl {n m} {p : n = m} {q : m = n} {v : dvector α n} : (v.cast p).cast q = v := by {subst p, refl}

protected lemma cast_hrfl {n m} {p : n = m} {v : dvector α n} : v.cast p == v :=
by { subst p, refl }

@[simp] protected lemma cast_trans {n m o} {p : n = m} {q : m = o} {v : dvector α n} : (v.cast p).cast q = v.cast (trans p q) :=
by { subst p, subst q, refl }

@[simp] protected def remove_mth : ∀ {n : ℕ} (m : ℕ) (xs : dvector α (n+1)) , dvector α n
  | 0 _ _  := dvector.nil
  | n 0 (dvector.cons y ys) := ys
  | (n+1) (k+1) (dvector.cons y ys) := dvector.cons y (remove_mth k ys)

protected def tail : ∀ {n : ℕ}, dvector α (n+1) → dvector α n
| _ (x::xs) := xs

@[simp] lemma tail_cons {x : α} {xs : dvector α n} : (x :: xs).tail = xs := rfl

@[simp] def foldr (f : α → β → β) (b : β) : ∀{n}, dvector α n → β
| _ []       := b
| _ (a :: l) := f a (foldr l)

@[simp] def zip : ∀{n}, dvector α n → dvector β n → dvector (α × β) n
| _ [] []               := []
| _ (x :: xs) (y :: ys) := ⟨x, y⟩ :: zip xs ys

@[simp] protected def setprod : ∀{n}, dvector (set α) n → set (dvector α n)
| _ []     := set.univ
| _ (s::l) := { x | x.head ∈ s ∧ x.tail ∈ setprod l }

@[simp] lemma mem_setprod {xs : dvector α n} {l : dvector (set α) n} :
  xs ∈ l.setprod ↔ ∀(x ∈ xs.zip l), prod.fst x ∈ x.snd :=
by { induction l; cases xs, simp, simp [*, or_imp_distrib, forall_and_distrib, forall_eq2] }

open lattice
/-- The finitary infimum -/
def fInf [semilattice_inf_top α] (xs : dvector α n) : α :=
xs.foldr (λ(x b : α), x ⊓ b) ⊤

@[simp] lemma fInf_nil [semilattice_inf_top α] : fInf [] = (⊤ : α) := by refl
@[simp] lemma fInf_cons [semilattice_inf_top α] (x : α) (xs : dvector α n) :
  fInf (x::xs) = x ⊓ fInf xs := by refl

/-- The finitary supremum -/
def fSup [semilattice_sup_bot α] (xs : dvector α n) : α :=
xs.foldr (λ(x b : α), x ⊔ b) ⊥

@[simp] lemma fSup_nil [semilattice_sup_bot α] : fSup [] = (⊥ : α) := by refl
@[simp] lemma fSup_cons [semilattice_sup_bot α] (x : α) (xs : dvector α n) :
  fSup (x::xs) = x ⊔ fSup xs := by refl

/- how to make this protected? -/
inductive rel [setoid α] : ∀{n}, dvector α n → dvector α n → Prop
| rnil : rel [] []
| rcons {n} {x x' : α} {xs xs' : dvector α n} (hx : x ≈ x') (hxs : rel xs xs') :
    rel (x::xs) (x'::xs')
open dvector.rel

protected def rel_refl [setoid α] : ∀{n} (xs : dvector α n), xs.rel xs
| _ []      := rnil
| _ (x::xs) := rcons (setoid.refl _) (rel_refl xs)

protected def rel_symm [setoid α] {n} {{xs xs' : dvector α n}} (h : xs.rel xs') : xs'.rel xs :=
by { induction h; constructor, exact setoid.symm h_hx, exact h_ih }

protected def rel_trans [setoid α] {n} {{xs₁ xs₂ xs₃ : dvector α n}}
  (h₁ : xs₁.rel xs₂) (h₂ : xs₂.rel xs₃) : xs₁.rel xs₃ :=
begin
  induction h₁ generalizing h₂, exact h₂,
  cases h₂, constructor, exact setoid.trans h₁_hx h₂_hx, exact h₁_ih h₂_hxs
end

-- protected def rel [setoid α] : ∀{n}, dvector α n → dvector α n → Prop
-- | _ []      []        := true
-- | _ (x::xs) (x'::xs') := x ≈ x' ∧ rel xs xs'

-- protected def rel_refl [setoid α] : ∀{n} (xs : dvector α n), xs.rel xs
-- | _ []      := trivial
-- | _ (x::xs) := ⟨by refl, rel_refl xs⟩

-- protected def rel_symm [setoid α] : ∀{n} {{xs xs' : dvector α n}}, xs.rel xs' → xs'.rel xs
-- | _ []      []        h := trivial
-- | _ (x::xs) (x'::xs') h := ⟨setoid.symm h.1, rel_symm h.2⟩

-- protected def rel_trans [setoid α] : ∀{n} {{xs₁ xs₂ xs₃ : dvector α n}},
--   xs₁.rel xs₂ → xs₂.rel xs₃ → xs₁.rel xs₃
-- | _ []        []        []        h₁ h₂ := trivial
-- | _ (x₁::xs₁) (x₂::xs₂) (x₃::xs₃) h₁ h₂ := ⟨setoid.trans h₁.1 h₂.1, rel_trans h₁.2 h₂.2⟩

instance setoid [setoid α] : setoid (dvector α n) :=
⟨dvector.rel, dvector.rel_refl, dvector.rel_symm, dvector.rel_trans⟩

def quotient_lift {α : Type u} {β : Sort v} {R : setoid α} : ∀{n} (f : dvector α n → β)
  (h : ∀{{xs xs'}}, xs ≈ xs' → f xs = f xs') (xs : dvector (quotient R) n), β
| _     f h []      := f ([])
| (n+1) f h (x::xs) :=
  begin
    refine quotient.lift
      (λx, quotient_lift (λ xs, f $ x::xs) (λxs xs' hxs, h (rcons (setoid.refl x) hxs)) xs) _ x,
    intros x x' hx, dsimp, congr, apply funext, intro xs, apply h, exact rcons hx xs.rel_refl
  end

def quotient_beta {α : Type u} {β : Sort v} {R : setoid α} {n} (f : dvector α n → β)
  (h : ∀{{xs xs'}}, xs ≈ xs' → f xs = f xs') (xs : dvector α n) :
  (xs.map quotient.mk).quotient_lift f h = f xs :=
begin
  induction xs, refl, apply xs_ih
end

end dvector

namespace tactic.interactive
open interactive lean.parser interactive.types tactic

#print cases
meta def dvector_cases : parse texpr → parse with_ident_list → tactic unit | p ids :=
do e ← i_to_expr p,
   e' ← ids.mfoldl (λ e n,
     do v ← mk_fresh_name, tactic.cases e [`_, n, v], get_local v) e,
   tactic.cases e', skip

end tactic.interactive
