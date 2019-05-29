import data.real.basic data.set.disjointed data.set.intervals
  set_theory.cardinal

open real set function
-- begin move
noncomputable theory

def strict_mono_nat {α} [preorder α] {f : ℕ → α} (h : ∀n, f n < f (n+1)) : strict_mono f :=
by { intros n m hnm, induction hnm with m' hnm' ih, apply h, exact lt.trans ih (h _) }

@[simp] theorem multiset.map_eq_zero
  {α β} {s : multiset α} {f : α → β} : s.map f = 0 ↔ s = 0 :=
by rw [← multiset.card_eq_zero, multiset.card_map, multiset.card_eq_zero]

theorem multiset.exists_min {α β} [decidable_linear_order β]
  {s : multiset α} (f : α → β) (h : s ≠ 0) : ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b :=
begin
  have : (s.map f).to_finset ≠ ∅ :=
    mt (multiset.to_finset_eq_empty.trans multiset.map_eq_zero).1 h,
  cases finset.min_of_ne_empty this with a m,
  rcases multiset.mem_map.1 (multiset.mem_to_finset.1 (finset.mem_of_min m))
    with ⟨a, ha, rfl⟩,
  refine ⟨a, ha, λ b hb, finset.le_min_of_mem _ m⟩,
  exact multiset.mem_to_finset.2 (multiset.mem_map_of_mem _ hb)
end

theorem finset.exists_min {α β} [decidable_linear_order β]
  (s : finset α) (f : α → β) (h : nonempty ↥(↑s : set α)) : ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b :=
begin
  unfreezeI, induction s, apply multiset.exists_min f,
  intro h2,
  rcases h with ⟨⟨x, hx⟩⟩, apply multiset.not_mem_zero x, convert hx,
  exact h2.symm
end

-- def set.to_finset' {α} (s : set α) [fintype α] : finset α :=
-- by { classical, exact finset.univ.filter (∈ s) }

-- @[simp] lemma set.coe_to_finset' {α} (s : set α) [fintype α] : ↑s.to_finset' = s :=
-- by { ext, simp [set.to_finset'] }

theorem set.exists_min {α β} [decidable_linear_order β]
  (s : set α) (f : α → β) (h1 : finite s) (h : nonempty s) : ∃ a, a ∈ s ∧ ∀ b ∈ s, f a ≤ f b :=
begin
  have := (finite.to_finset h1).exists_min f,
  simp at this ⊢, unfreezeI, rcases h with ⟨⟨x, hx⟩⟩,
  exact this x hx
end

lemma not_disjoint_iff {α} {s t : set α} : ¬disjoint s t ↔ ∃x, x ∈ s ∧ x ∈ t :=
by { rw [set.disjoint_iff, subset_empty_iff], apply ne_empty_iff_exists_mem }

lemma order_dual_lt {α} [has_lt α] {x y : order_dual α} :
  x < y ↔ (show α, from y) < (show α, from x) :=
iff.rfl

lemma order_dual_le {α} [has_le α] {x y : order_dual α} :
  x ≤ y ↔ (show α, from y) ≤ (show α, from x) :=
iff.rfl

variable {n : ℕ}

def tail (p : fin (n+1) → ℝ) : fin n → ℝ := λ i, p i.succ
def cons (x : ℝ) (v : fin n → ℝ) : fin (n+1) → ℝ :=
λ j, fin.cases x v j

@[simp] lemma tail_cons (x : ℝ) (p : fin n → ℝ) : tail (cons x p) = p :=
by simp [tail, cons]

@[simp] lemma cons_succ (x : ℝ) (p : fin n → ℝ) (i : fin n) : cons x p i.succ = p i :=
by simp [cons]

@[simp] lemma cons_zero (x : ℝ) (p : fin n → ℝ) : cons x p 0 = x :=
by simp [cons]

lemma forall_fin_succ {P : fin (n+1) → Prop} :
  (∀ i, P i) ↔ P 0 ∧ (∀ i:fin n, P i.succ) :=
⟨λ H, ⟨H 0, λ i, H _⟩, λ ⟨H0, H1⟩ i, fin.cases H0 H1 i⟩

lemma exists_fin_succ {P : fin (n+1) → Prop} :
  (∃ i, P i) ↔ P 0 ∨ (∃i:fin n, P i.succ) :=
⟨λ ⟨i, h⟩, fin.cases or.inl (λ i hi, or.inr ⟨i, hi⟩) i h,
  λ h, or.elim h (λ h, ⟨0, h⟩) $ λ⟨i, hi⟩, ⟨i.succ, hi⟩⟩

lemma Ico_lemma {α} [decidable_linear_order α] {x₁ x₂ y₁ y₂ z₁ z₂ w : α}
  (h₁ : x₁ < y₁) (hy : y₁ < y₂) (h₂ : y₂ < x₂)
  (hz₁ : z₁ ≤ y₂) (hz₂ : y₁ ≤ z₂) (hw : w ∉ Ico y₁ y₂ ∧ w ∈ Ico z₁ z₂) :
  ∃w, w ∈ Ico x₁ x₂ ∧ w ∉ Ico y₁ y₂ ∧ w ∈ Ico z₁ z₂ :=
begin
  simp at hw,
  refine ⟨max x₁ (min w y₂), _, _, _⟩,
  simp [le_refl, lt_trans h₁ (lt_trans hy h₂), h₂],
  simp [lt_irrefl, not_le_of_lt h₁], intros, apply hw.1, assumption,
  simp [hw.2.1, hw.2.2, hz₁, lt_of_lt_of_le h₁ hz₂] at ⊢
end

lemma Ico_disjoint {α} [decidable_linear_order α] {x₁ x₂ y₁ y₂ : α}
  (h : disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂) (hy : y₁ < y₂) (h2 : x₂ ∈ Ico y₁ y₂) :
  y₁ = x₂ :=
begin
  apply le_antisymm h2.1, rw [←not_lt], intro h3,
  apply not_disjoint_iff.mpr ⟨max y₁ x₁, _, _⟩ h,
  simp [le_refl, h3, hx],
  simp [le_refl, hy, lt_trans hx h2.2]
end

/- why is `max_add_add_left` only proven for an instance
`decidable_linear_ordered_cancel_comm_monoid` that is never used in the library? -/
lemma nonempty_Ico_sdiff {α} [decidable_linear_ordered_comm_group α] {x dx y dy : α}
  (h : dy < dx) (hx : 0 < dx) : nonempty ↥(Ico x (x + dx) \ Ico y (y + dy)) :=
begin
  cases lt_or_le x y with h' h',
  { use x, simp* },
  { use max x (x + dy), simp [*, le_refl] }
end

@[simp] lemma add_le_self_right {α} [decidable_linear_ordered_comm_group α] {x y : α} :
  x + y ≤ y ↔ x ≤ 0 :=
by { convert add_le_add_iff_right y, rw [zero_add] }

@[simp] lemma add_le_self_left {α} [decidable_linear_ordered_comm_group α] {x y : α} :
  x + y ≤ x ↔ y ≤ 0 :=
by { convert add_le_add_iff_left x, rw [add_zero] }

@[simp] lemma le_add_self_right {α} [decidable_linear_ordered_comm_group α] {x y : α} :
  y ≤ x + y ↔ 0 ≤ x :=
by { convert add_le_add_iff_right y, rw [zero_add] }

@[simp] lemma le_add_self_left {α} [decidable_linear_ordered_comm_group α] {x y : α} :
  x ≤ x + y ↔ 0 ≤ y :=
by { convert add_le_add_iff_left x, rw [add_zero] }

-- end move


structure cube (n : ℕ) : Type :=
(b : fin n → ℝ) -- bottom-left coordinate
(w : ℝ) -- width
(hw : 0 < w)

namespace cube
lemma hw' (c : cube n) : 0 ≤ c.w := le_of_lt c.hw

def side (c : cube n) (j : fin n) : set ℝ :=
Ico (c.b j) (c.b j + c.w)

@[simp] lemma b_mem_side (c : cube n) (j : fin n) : c.b j ∈ c.side j :=
by simp [side, cube.hw, le_refl]

def to_set (c : cube n) : set (fin n → ℝ) :=
{ x | ∀j, x j ∈ side c j }

def to_set_subset {c c' : cube n} : c.to_set ⊆ c'.to_set ↔ ∀j, c.side j ⊆ c'.side j :=
begin
  split, intros h j x hx,
  let f : fin n → ℝ := λ j', if j' = j then x else c.b j',
  have : f ∈ c.to_set,
  { intro j', by_cases hj' : j' = j, simp [f, hj', if_pos, hx], simp [f, if_neg hj'] },
  convert h this j, simp [f, if_pos],
  intros h f hf j, exact h j (hf j)
end

def to_set_disjoint {c c' : cube n} : disjoint c.to_set c'.to_set ↔
  ∃j, disjoint (c.side j) (c'.side j) :=
begin
  split, intros h, classical, by_contra h', simp [not_disjoint_iff, classical.skolem] at h',
  cases h' with f hf,
  apply not_disjoint_iff.mpr ⟨f, _, _⟩ h; intro j, exact (hf j).1, exact (hf j).2,
  rintro ⟨j, hj⟩, rw [set.disjoint_iff], rintros f ⟨h1f, h2f⟩,
  apply not_disjoint_iff.mpr ⟨f j, h1f j, h2f j⟩ hj
end

lemma b_mem_to_set (c : cube n) : c.b ∈ c.to_set :=
by simp [to_set]

protected def tail (c : cube (n+1)) : cube n :=
⟨tail c.b, c.w, c.hw⟩

lemma side_tail (c : cube (n+1)) (j : fin n) : c.tail.side j = c.side j.succ := rfl

def bottom (c : cube (n+1)) : set (fin (n+1) → ℝ) :=
{ x | x 0 = c.b 0 ∧ tail x ∈ c.tail.to_set }

lemma b_mem_bottom (c : cube (n+1)) : c.b ∈ c.bottom :=
by simp [bottom, to_set, side, cube.hw, le_refl, cube.tail]

def xm (c : cube (n+1)) : ℝ :=
c.b 0 + c.w

lemma b_lt_xm (c : cube (n+1)) : c.b 0 < c.xm := by simp [xm, hw]
lemma b_ne_xm (c : cube (n+1)) : c.b 0 ≠ c.xm := ne_of_lt c.b_lt_xm

def shift_up (c : cube (n+1)) : cube (n+1) :=
⟨cons c.xm $ tail c.b, c.w, c.hw⟩

@[simp] lemma tail_shift_up (c : cube (n+1)) : c.shift_up.tail = c.tail :=
by simp [shift_up, cube.tail]

@[simp] lemma head_shift_up (c : cube (n+1)) : c.shift_up.b 0 = c.xm := rfl

def unit_cube : cube n :=
⟨λ _, 0, 1, by norm_num⟩

@[simp] lemma side_unit_cube {j : fin n} : unit_cube.side j = Ico 0 1 :=
by norm_num [unit_cube, side]

end cube
open cube

variables {ι : Type} [fintype ι] {cs : ι → cube (n+1)} {i i' : ι}

/- disjoint family of cubes -/
def correct (cs : ι → cube n) : Prop :=
pairwise (disjoint on (cube.to_set ∘ cs)) ∧
(⋃(i : ι), (cs i).to_set) = unit_cube.to_set ∧
injective (cube.w ∘ cs) ∧
2 ≤ cardinal.mk ι ∧
3 ≤ n

variable (h : correct cs)

include h
lemma to_set_subset_unit_cube {i} : (cs i).to_set ⊆ unit_cube.to_set :=
by { rw [←h.2.1], exact subset_Union _ i }

lemma side_subset {i j} : (cs i).side j ⊆ Ico 0 1 :=
by { have := to_set_subset_unit_cube h, rw [to_set_subset] at this,
     convert this j, norm_num [unit_cube] }

lemma zero_le_of_mem_side {i j x} (hx : x ∈ (cs i).side j) : 0 ≤ x :=
(side_subset h hx).1

lemma zero_le_of_mem {i p} (hp : p ∈ (cs i).to_set) (j) : 0 ≤ p j :=
zero_le_of_mem_side h (hp j)

lemma zero_le_b {i j} : 0 ≤ (cs i).b j :=
zero_le_of_mem h (cs i).b_mem_to_set j

lemma b_add_w_le_one {j} : (cs i).b j + (cs i).w ≤ 1 :=
by { have := side_subset h, rw [side, Ico_subset_Ico_iff] at this, convert this.2, simp [hw] }

lemma w_ne_one (i : ι) : (cs i).w ≠ 1 :=
begin
  intro hi,
  have := h.2.2.2.1, rw [cardinal.two_le_iff' i] at this, cases this with i' hi',
  -- have := h.1 i i' hi', rw [on_fun, to_set_disjoint] at this,
  -- cases this with j hj,
  let p := (cs i').b,
  have hp : p ∈ (cs i').to_set := (cs i').b_mem_to_set,
  have h2p : p ∈ (cs i).to_set,
  { intro j, split,
    transitivity (0 : ℝ),
    { rw [←add_le_add_iff_right (1 : ℝ)], convert b_add_w_le_one h, rw hi, rw zero_add },
    apply zero_le_b h, apply lt_of_lt_of_le (side_subset h $ (cs i').b_mem_side j).2,
    simp [hi, zero_le_b h] },
  apply not_disjoint_iff.mpr ⟨p, hp, h2p⟩,
  apply h.1, exact hi'.symm
end

lemma shift_up_bottom_subset_bottoms (hc : (cs i).xm ≠ 1) :
  (cs i).shift_up.bottom ⊆ ⋃(i : ι), (cs i).bottom :=
begin
  intros p hp, cases hp with hp0 hps, rw [tail_shift_up] at hps,
  have : p ∈ (unit_cube : cube (n+1)).to_set,
  { simp [to_set, forall_fin_succ, hp0], refine ⟨⟨_, _⟩, _⟩,
    { rw [←zero_add (0 : ℝ)], apply add_le_add, apply zero_le_b h, apply (cs i).hw' },
    { exact lt_of_le_of_ne (b_add_w_le_one h) hc },
    intro j, exact side_subset h (hps j) },
  rw [←h.2.1] at this, rcases this with ⟨_, ⟨i', rfl⟩, hi'⟩,
  rw [mem_Union], use i', refine ⟨_, λ j, hi' j.succ⟩,
  have : i ≠ i', { rintro rfl, apply not_le_of_lt (hi' 0).2, rw [hp0], refl },
  have := h.1 i i' this, rw [on_fun, to_set_disjoint, exists_fin_succ] at this,
  rcases this with h0|⟨j, hj⟩,
  rw [hp0], symmetry, apply Ico_disjoint h0 (by simp [hw]) (by simp [hw]) _,
  convert hi' 0, rw [hp0], refl,
  exfalso, apply not_disjoint_iff.mpr ⟨tail p j, hps j, hi' j.succ⟩ hj
end
omit h

/- A valley is a square on which at least two cubes in the family cs are placed,
  and none of those cubes can be partially outside the square -/
def valley (cs : ι → cube (n+1)) (c : cube (n+1)) : Prop :=
c.bottom ⊆ (⋃(i : ι), (cs i).bottom) ∧
(∀i, (cs i).b 0 = c.b 0 → (∃x, x ∈ (cs i).tail.to_set ∩ c.tail.to_set) →
  (cs i).tail.to_set ⊆ c.tail.to_set) ∧
∀(i : ι), (cs i).w = c.w → (cs i).b 0 ≠ c.b 0

variables {c : cube (n+1)} (v : valley cs c)

/- the bottom of the cube is a valley -/
lemma valley_unit_cube (h : correct cs) : valley cs unit_cube :=
begin
  refine ⟨_, _, _⟩,
  { intro v, simp [bottom],
    intros h0 hv,
    have : v ∈ (unit_cube : cube (n+1)).to_set,
    { dsimp [to_set], rw [forall_fin_succ, h0], split, norm_num [side, unit_cube], exact hv },
    rw [←h.2.1] at this, rcases this with ⟨_, ⟨i, rfl⟩, hi⟩,
    use i,
    split, { apply le_antisymm, rw h0, exact zero_le_b h, exact (hi 0).1 },
    intro j, exact hi _ },
  { intros i hi h', rw to_set_subset, intro j, convert side_subset h, simp [side_tail] },
  { exact λ i hi, false.elim $ w_ne_one h i hi }
end

/- the cubes which lie on the bottom of `c` -/
def bcubes (cs : ι → cube (n+1)) (c : cube (n+1)) : set ι :=
{ i : ι | (cs i).b 0 = c.b 0 ∧ (cs i).tail.to_set ⊆ c.tail.to_set }

lemma tail_sub (hi : i ∈ bcubes cs c) : ∀j, (cs i).tail.side j ⊆ c.tail.side j :=
by { rw [←to_set_subset], exact hi.2 }

lemma bottom_mem_side (hi : i ∈ bcubes cs c) : c.b 0 ∈ (cs i).side 0 :=
by { convert b_mem_side (cs i) _ using 1, rw hi.1 }

lemma b_le_b (hi : i ∈ bcubes cs c) (j : fin n) : c.b j.succ ≤ (cs i).b j.succ :=
begin
  have := tail_sub hi j, dsimp [side] at this, rw [Ico_subset_Ico_iff] at this,
  exact this.1, simp [hw]
end

def on_boundary (hi : i ∈ bcubes cs c) (j : fin n) : Prop :=
c.b j.succ = (cs i).b j.succ ∨ (cs i).b j.succ + (cs i).w = c.b j.succ + c.w

-- def on_same_boundary (hi : i ∈ bcubes cs c) (hi' : i' ∈ bcubes cs c) (j : fin n) : Prop :=
-- (c.tail.b j = (cs i).tail.b j ∧ c.tail.b j = (cs i').tail.b j) ∨
-- ((cs i).tail.b j + (cs i).w = c.tail.b j + c.w ∧ (cs i').tail.b j + (cs i').w = c.tail.b j + c.w)

include h v
lemma w_lt_w (hi : i ∈ bcubes cs c) : (cs i).w < c.w :=
begin
  apply lt_of_le_of_ne _ (λ h2i, v.2.2 i h2i hi.1),
  have j : fin n := ⟨1, nat.le_of_succ_le_succ h.2.2.2.2⟩,
  have := tail_sub hi j,
  dsimp [side] at this, rw [Ico_subset_Ico_iff] at this, dsimp [cube.tail] at this,
  rw [←add_le_add_iff_left (tail (cs i).b j)],
  refine le_trans this.2 _, rw [add_le_add_iff_right], apply this.1,
  simp [hw]
end

open cardinal
lemma two_le_mk_bcubes : 2 ≤ cardinal.mk (bcubes cs c) :=
begin
  rw [two_le_iff],
  rcases v.1 c.b_mem_bottom with ⟨_, ⟨i, rfl⟩, hi⟩,
  have h2i : i ∈ bcubes cs c := ⟨hi.1.symm, v.2.1 i hi.1.symm ⟨tail c.b, hi.2, λ j, c.b_mem_side j.succ⟩⟩,
  let j : fin (n+1) := ⟨2, h.2.2.2.2⟩,
  have hj : 0 ≠ j := by { intro h', have := congr_arg fin.val h', contradiction },
  let p : fin (n+1) → ℝ := λ j', if j' = j then c.b j + (cs i).w else c.b j',
  have hp : p ∈ c.bottom,
  { split, simp [bottom, p, if_neg hj], intro j', simp [tail, side_tail],
    by_cases hj' : j'.succ = j,
    simp [p, -add_comm, if_pos hj', side, hj', hw', w_lt_w h v h2i],
    simp [p, -add_comm, if_neg hj'] },
  rcases v.1 hp with ⟨_, ⟨i', rfl⟩, hi'⟩,
  have h2i' : i' ∈ bcubes cs c := ⟨hi'.1.symm, v.2.1 i' hi'.1.symm ⟨tail p, hi'.2, hp.2⟩⟩,
  refine ⟨⟨i, h2i⟩, ⟨i', h2i'⟩, _⟩,
  intro hii', cases congr_arg subtype.val hii',
  apply not_le_of_lt (hi'.2 ⟨1, nat.le_of_succ_le_succ h.2.2.2.2⟩).2,
  simp [-add_comm, tail, cube.tail, p], rw [if_pos], simp [-add_comm],
  convert (hi.2 _).1, refl
end

lemma nonempty_bcubes : nonempty (bcubes cs c) :=
begin
  rw [←ne_zero_iff_nonempty], intro h', have := two_le_mk_bcubes h v, rw h' at this,
  apply not_lt_of_le this, rw [←nat.cast_two, ←nat.cast_zero, nat_cast_lt], norm_num
end

lemma exists_mi : ∃(i : ι), i ∈ bcubes cs c ∧ ∀(i' ∈ bcubes cs c),
  (cs i).w ≤ (cs i').w :=
(bcubes cs c).exists_min (λ i, (cs i).w) (finite.of_fintype _)
  (nonempty_bcubes h v)

/- the (index for the) cube with the minimal size on the bottom of `c` -/
def mi : ι :=
classical.some $ exists_mi h v

variables {h v}
lemma mi_mem_bcubes : mi h v ∈ bcubes cs c :=
(classical.some_spec $ exists_mi h v).1

lemma mi_minimal (hi : i ∈ bcubes cs c) : (cs $ mi h v).w ≤ (cs i).w :=
(classical.some_spec $ exists_mi h v).2 i hi

lemma mi_strict_minimal (hii' : mi h v ≠ i) (hi : i ∈ bcubes cs c) :
  (cs $ mi h v).w < (cs i).w :=
by { apply lt_of_le_of_ne (mi_minimal hi), apply h.2.2.1.ne, apply hii' }

lemma mi_xm_ne_one : (cs $ mi h v).xm ≠ 1 :=
begin
  apply ne_of_lt, rcases (two_le_iff' _).mp (two_le_mk_bcubes h v) with ⟨⟨i, hi⟩, h2i⟩,
  swap, exact ⟨mi h v, mi_mem_bcubes⟩,
  apply lt_of_lt_of_le _ (b_add_w_le_one h), exact i, exact 0,
  rw [xm, mi_mem_bcubes.1, hi.1, real.add_lt_add_iff_left],
  apply mi_strict_minimal _ hi, intro h', apply h2i, rw subtype.ext, exact h'
end

lemma smallest_on_boundary {j} (bi : on_boundary (mi_mem_bcubes : mi h v ∈ _) j) :
  ∃(x : ℝ), x ∈ c.side j.succ \ (cs $ mi h v).side j.succ ∧
  ∀{{i'}} (hi' : i' ∈ bcubes cs c), i' ≠ mi h v →
    (cs $ mi h v).b j.succ ∈ (cs i').side j.succ → x ∈ (cs i').side j.succ :=
begin
  let i := mi h v, have hi : i ∈ bcubes cs c := mi_mem_bcubes,
  cases bi,
  { refine ⟨(cs i).b j.succ + (cs i).w, ⟨_, _⟩, _⟩,
    { simp [side, bi, hw', w_lt_w h v hi] },
    { intro h', simpa [i, lt_irrefl] using h'.2 },
    intros i' hi' i'_i h2i', sorry
  },
  sorry
end

variables (h v)
lemma mi_not_on_boundary (j : fin n) : ¬on_boundary (mi_mem_bcubes : mi h v ∈ _) j :=
begin
  let i := mi h v, have hi : i ∈ bcubes cs c := mi_mem_bcubes,
  rcases (two_le_iff' j).mp _ with ⟨j', hj'⟩, swap,
  { rw [mk_fin, ←nat.cast_two, nat_cast_le], apply nat.le_of_succ_le_succ h.2.2.2.2 },
  intro hj,
  rcases smallest_on_boundary hj with ⟨x, ⟨hx, h2x⟩, h3x⟩,
  let p : fin (n+1) → ℝ := cons (c.b 0) (λ j₂, if j₂ = j then x else (cs i).b j₂.succ),
  have hp : p ∈ c.bottom,
  { simp [bottom, p, to_set, tail, side_tail], intro j₂,
    by_cases hj₂ : j₂ = j, simp [hj₂, hx],
    simp [hj₂], apply tail_sub hi, apply b_mem_side },
  rcases v.1 hp with ⟨_, ⟨i', rfl⟩, hi'⟩,
  have h2i' : i' ∈ bcubes cs c := ⟨hi'.1.symm, v.2.1 i' hi'.1.symm ⟨tail p, hi'.2, hp.2⟩⟩,
  have i_i' : i ≠ i', { rintro rfl, simpa [p, side_tail, i, h2x] using hi'.2 j },
  -- have h3i' : (cs i').b j.succ = (cs i).b j.succ + (cs i).w,
  -- { have := h.1 i i' i_i', rw [on_fun, to_set_disjoint, exists_fin_succ] at this,
  --   rcases this with h0|⟨j₂, hj₂⟩,
  --   { exfalso, apply not_disjoint_iff.mpr ⟨c.b 0, bottom_mem_side hi, bottom_mem_side h2i'⟩ h0 },
  --   have : j₂ = j,
  --   { by_contra h2j₂, apply not_disjoint_iff.mpr ⟨p j₂.succ, _, hi'.2 j₂⟩ hj₂, simp [p, h2j₂] },
  --   rw this at hj₂,
  --   apply Ico_disjoint hj₂ (by simp [hw]) (by simp [hw]), convert hi'.2 j, simp [p] },
  have : nonempty ↥((cs i').tail.side j' \ (cs i).tail.side j'),
  { apply nonempty_Ico_sdiff, apply mi_strict_minimal i_i' h2i', apply hw },
  rcases this with ⟨⟨x', hx'⟩⟩,
  let p' : fin (n+1) → ℝ :=
  cons (c.b 0) (λ j₂, if j₂ = j' then x' else (cs i).b j₂.succ),
  have hp' : p' ∈ c.bottom,
  { simp [bottom, p', to_set, tail, side_tail], intro j₂,
    by_cases hj₂ : j₂ = j', simp [hj₂], apply tail_sub h2i', apply hx'.1,
    simp [hj₂], apply tail_sub hi, apply b_mem_side },
  rcases v.1 hp' with ⟨_, ⟨i'', rfl⟩, hi''⟩,
  have h2i'' : i'' ∈ bcubes cs c := ⟨hi''.1.symm, v.2.1 i'' hi''.1.symm ⟨tail p', hi''.2, hp'.2⟩⟩,
  have i'_i'' : i' ≠ i'',
  { rintro ⟨⟩,
    have : (cs i).b ∈ (cs i').to_set,
    { simp [to_set, forall_fin_succ, hi.1, bottom_mem_side h2i'],
    intro j₂, by_cases hj₂ : j₂ = j, simpa [side_tail, p', hj', hj₂] using hi''.2 j,
    simpa [hj₂] using hi'.2 j₂ },
    apply not_disjoint_iff.mpr ⟨(cs i).b, (cs i).b_mem_to_set, this⟩ (h.1 i i' i_i') },
  have i_i'' : i ≠ i'', { intro h, induction h, simpa [hx'.2] using hi''.2 j' },
  apply not.elim _ (h.1 i' i'' i'_i''),
  simp [on_fun, to_set_disjoint, not_disjoint_iff, forall_fin_succ],
  refine ⟨⟨c.b 0, bottom_mem_side h2i', bottom_mem_side h2i''⟩, _⟩,
  intro j₂,
  by_cases hj₂ : j₂ = j,
  { cases hj₂, refine ⟨x, _, _⟩,
    { convert hi'.2 j, simp [p] },
    apply h3x h2i'' i_i''.symm, convert hi''.2 j, simp [p', hj'] },
  by_cases h2j₂ : j₂ = j',
  { cases h2j₂, refine ⟨x', hx'.1, _⟩, convert hi''.2 j', simp },
  refine ⟨(cs i).b j₂.succ, _, _⟩,
  { convert hi'.2 j₂, simp [hj₂] },
  { convert hi''.2 j₂, simp [h2j₂] }
end

variables {h v}
lemma mi_not_on_boundary' (j : fin n) : c.tail.b j < (cs (mi h v)).tail.b j ∧
  (cs (mi h v)).tail.b j + (cs (mi h v)).w < c.tail.b j + c.w :=
begin
  have := mi_not_on_boundary h v j,
  simp only [on_boundary, not_or_distrib] at this, cases this with h1 h2,
  split,
  apply lt_of_le_of_ne (b_le_b mi_mem_bcubes _) h1,
  apply lt_of_le_of_ne _ h2,
  apply ((Ico_subset_Ico_iff _).mp (tail_sub mi_mem_bcubes j)).2, simp [hw]
end

def valley_mi : valley cs ((cs (mi h v)).shift_up) :=
begin
  let i := mi h v, have hi : i ∈ bcubes cs c := mi_mem_bcubes,
  refine ⟨_, _, _⟩,
  { intro p, apply shift_up_bottom_subset_bottoms h mi_xm_ne_one },
  { rintros i' hi' ⟨p2, hp2, h2p2⟩, simp at hi', classical, by_contra h2i',
    rw [tail_shift_up] at h2p2, simp [not_subset] at h2i', rcases h2i' with ⟨p1, hp1, h2p1⟩,
    have : ∃p3, p3 ∈ (cs i').tail.to_set ∧ p3 ∉ (cs i).tail.to_set ∧ p3 ∈ c.tail.to_set,
    { simp [to_set, not_forall] at h2p1, cases h2p1 with j hj,
      rcases Ico_lemma (mi_not_on_boundary' j).1 (by simp [hw]) (mi_not_on_boundary' j).2
        (le_trans (hp2 j).1 $ le_of_lt (h2p2 j).2)
        (le_trans (h2p2 j).1 $ le_of_lt (hp2 j).2) ⟨hj, hp1 j⟩ with ⟨w, hw, h2w, h3w⟩,
      refine ⟨λ j', if j' = j then w else p2 j', _, _, _⟩,
      { intro j', by_cases h : j' = j, simp [if_pos h], convert h3w,
        simp [if_neg h], exact hp2 j' },
      { simp [to_set, not_forall], use j, rw [if_pos rfl], convert h2w },
      { intro j', by_cases h : j' = j, simp [if_pos h, side_tail], convert hw,
        simp [if_neg h], apply hi.2, apply h2p2 }},
    rcases this with ⟨p3, h1p3, h2p3, h3p3⟩,
    let p := cons (c.b 0) p3,
    have hp : p ∈ c.bottom, { refine ⟨rfl, _⟩, rwa [tail_cons] },
    rcases v.1 hp with ⟨_, ⟨i'', rfl⟩, hi''⟩,
    have h2i'' : i'' ∈ bcubes cs c,
    { use hi''.1.symm, apply v.2.1 i'' hi''.1.symm,
      use tail p, split, exact hi''.2, rw [tail_cons], exact h3p3 },
    have h3i'' : (cs i).w < (cs i'').w,
    { apply mi_strict_minimal _ h2i'', rintro rfl, apply h2p3, convert hi''.2, rw [tail_cons] },
    let p' := cons (cs i).xm p3,
    have hp' : p' ∈ (cs i').to_set,
    { simpa [to_set, forall_fin_succ, p', hi'.symm] using h1p3 },
    have h2p' : p' ∈ (cs i'').to_set,
    { simp [to_set, forall_fin_succ, p'],
      refine ⟨_, by simpa [to_set, p] using hi''.2⟩,
      have : (cs i).b 0 = (cs i'').b 0, { by rw [hi.1, h2i''.1] },
      simp [side, hw', xm, this, h3i''] },
    apply not_disjoint_iff.mpr ⟨p', hp', h2p'⟩,
    apply h.1, rintro rfl, apply (cs i).b_ne_xm, rw [←hi', ←hi''.1, hi.1], refl },
  { intros i' hi', dsimp [shift_up] at hi', cases h.2.2.1 hi', apply b_ne_xm }
end

variables (h)
omit v

noncomputable def sequence_of_cubes : ℕ → { i : ι // valley cs ((cs i).shift_up) }
| 0     := let v := valley_unit_cube h      in ⟨mi h v, valley_mi⟩
| (k+1) := let v := (sequence_of_cubes k).2 in ⟨mi h v, valley_mi⟩

def decreasing_sequence (k : ℕ) : order_dual ℝ :=
(cs (sequence_of_cubes h k).1).w

lemma strict_mono_sequence_of_cubes : strict_mono $ decreasing_sequence h :=
strict_mono_nat $
begin
  intro k, let v := (sequence_of_cubes h k).2, dsimp [decreasing_sequence, sequence_of_cubes],
  apply w_lt_w h v (mi_mem_bcubes : mi h v ∈ _),
end

omit h

theorem cubing_a_cube (h : correct cs) : false :=
begin
  apply not_le_of_lt (lt_omega_iff_fintype.mpr ⟨_inst_1⟩),
  rw [omega, lift_id], fapply mk_le_of_injective, exact λ n, (sequence_of_cubes h n).1,
  intros n m hnm, apply strict_mono.injective (strict_mono_sequence_of_cubes h),
  dsimp only [decreasing_sequence], rw hnm
end
