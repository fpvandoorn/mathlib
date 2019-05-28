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
  (s : set α) (f : α → β) (h1 : finite s) (h : nonempty s) : ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b :=
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

-- end move


structure cube (n : ℕ) : Type :=
(b : fin n → ℝ) -- bottom-left coordinate
(w : ℝ) -- width
(hw : 0 < w)

namespace cube
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

def all : cube n :=
⟨λ _, 0, 1, by norm_num⟩

@[simp] lemma side_all {j : fin n} : cube.all.side j = Ico 0 1 :=
by norm_num [all, side]

end cube
open cube

variables {ι : Type} [fintype ι] {cs : ι → cube (n+1)} {i : ι}

/- disjoint family of cubes -/

def correct (cs : ι → cube n) : Prop :=
pairwise (disjoint on (cube.to_set ∘ cs)) ∧
(⋃(i : ι), (cs i).to_set) = cube.all.to_set ∧
injective (cube.w ∘ cs) ∧
2 ≤ cardinal.mk ι ∧
3 ≤ n

variable (h : correct cs)

include h
lemma to_set_subset_all {i} : (cs i).to_set ⊆ cube.all.to_set :=
by { rw [←h.2.1], exact subset_Union _ i }

lemma side_subset {i j} : (cs i).side j ⊆ Ico 0 1 :=
by { have := to_set_subset_all h, rw [to_set_subset] at this, convert this j, norm_num [all] }

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
  let p := (cs i').b,
  have hp : p ∈ (cs i').to_set := (cs i').b_mem_to_set,
  have h2p : p ∈ (cs i).to_set,
  { intro j, split,
    transitivity (0 : ℝ),
    { rw [←add_le_add_iff_right (1 : ℝ)], convert b_add_w_le_one h, rw hi, rw zero_add },
    apply zero_le_b h,
    apply lt_of_lt_of_le (side_subset h $ (cs i').b_mem_side j).2,
    rw [←zero_add (1 : ℝ), hi, add_le_add_iff_right],
    apply zero_le_b h },
  apply not_disjoint_iff.mpr ⟨p, hp, h2p⟩,
  apply h.1, exact hi'.symm
end

lemma shift_up_bottom_subset_bottoms (hc : (cs i).xm ≠ 1) :
  (cs i).shift_up.bottom ⊆ ⋃(i : ι), (cs i).bottom :=
begin
  intros p hp, cases hp with hp0 hps, rw [tail_shift_up] at hps,
  have : p ∈ (cube.all : cube (n+1)).to_set,
  { simp [to_set, forall_fin_succ, hp0], refine ⟨⟨_, _⟩, _⟩,
    { rw [←zero_add (0 : ℝ)], apply add_le_add, apply zero_le_b h, apply le_of_lt (cs i).hw },
    { exact lt_of_le_of_ne (b_add_w_le_one h) hc },
    intro j, exact side_subset h (hps j) },
  rw [←h.2.1] at this, rcases this with ⟨_, ⟨i', rfl⟩, hi'⟩,
  rw [mem_Union], use i', refine ⟨_, λ j, hi' j.succ⟩,
  apply le_antisymm _ (hi' 0).1,
  rw [←not_lt], intro h2p,
  let p' := cons (max ((cs i).b 0) ((cs i').b 0)) (tail p),
  have hp' : p' ∈ (cs i).to_set,
  { simp [to_set, forall_fin_succ, p'], refine ⟨_, hps⟩, simp [side, le_refl, hw],
    convert h2p, simp [hp0, xm] },
  have h2p' : p' ∈ (cs i').to_set,
  { simp [to_set, forall_fin_succ, p', b_mem_side], refine ⟨_, λ i, hi' i.succ⟩,
  simp [side, le_refl, hw], transitivity p 0,
  rw [←add_zero ((cs i).b 0)], convert add_lt_add_left (cs i).hw _,
  simpa using (hi' 0).2 },
  apply not_disjoint_iff.mpr ⟨p', hp', h2p'⟩,
  apply h.1, rintro rfl, apply not_le_of_lt (hi' 0).2, rw [hp0], refl
end
omit h

/- A valley is a square on which cubes in cs are placed, and none of those cubes can be
  partially outside the square -/
def valley (cs : ι → cube (n+1)) (c : cube (n+1)) : Prop :=
c.bottom ⊆ (⋃(i : ι), (cs i).bottom) ∧
(∀i, (cs i).b 0 = c.b 0 → (∃x, x ∈ (cs i).tail.to_set ∩ c.tail.to_set) →
  (cs i).tail.to_set ⊆ c.tail.to_set) ∧
∀(i : ι), (cs i).w = c.w → (cs i).b 0 ≠ c.b 0

variables {c : cube (n+1)}

lemma valley_all (h : correct cs) : valley cs cube.all :=
begin
  refine ⟨_, _, _⟩,
  { intro v, simp [bottom],
    intros h0 hv,
    have : v ∈ (cube.all : cube (n+1)).to_set,
    { dsimp [to_set], rw [forall_fin_succ, h0], split, norm_num [side, all], exact hv },
    rw [←h.2.1] at this, rcases this with ⟨_, ⟨i, rfl⟩, hi⟩,
    use i,
    split, { apply le_antisymm, rw h0, exact zero_le_b h, exact (hi 0).1 },
    intro j, exact hi _ },
  { intros i hi h', rw to_set_subset, intro j, convert side_subset h, simp [side_tail] },
  { exact λ i hi, false.elim $ w_ne_one h i hi }
end
#print decidable_of_decidable_of_iff
#print fin
#exit
-- set_option pp.implicit true
def main_lemma (h : correct cs) (v : valley cs c) :
  { i : ι // valley cs ((cs i).shift_up) ∧ (cs i).w < c.w } :=
begin
  let is := { i : ι | (cs i).b 0 = c.b 0 ∧ (cs i).tail.to_set ⊆ c.tail.to_set },
  have his : ∀(i ∈ is), (cs i).w < c.w,
  { intros i hi, apply lt_of_le_of_ne _ (λ h2i, v.2.2 i h2i hi.1),
    have j : fin n := ⟨1, nat.le_of_succ_le_succ h.2.2.2.2⟩,
    have := hi.2, rw [to_set_subset] at this, replace this := this j,
    dsimp [side] at this, rw [Ico_subset_Ico_iff] at this, dsimp [cube.tail] at this,
    rw [←add_le_add_iff_left (tail (cs i).b j)],
    refine le_trans this.2 _, rw [add_le_add_iff_right], apply this.1,
    simp [hw] },
  have : 2 ≤ cardinal.mk is,
  { rw [cardinal.two_le_iff],
    rcases v.1 c.b_mem_bottom with ⟨_, ⟨i, rfl⟩, hi⟩,
    have h2i : i ∈ is := ⟨hi.1.symm, v.2.1 i hi.1.symm ⟨tail c.b, hi.2, λ j, c.b_mem_side j.succ⟩⟩,
    let j : fin (n+1) := ⟨2, h.2.2.2.2⟩,
    have hj : 0 ≠ j := by { intro h', have := congr_arg fin.val h', contradiction },
    let p : fin (n+1) → ℝ := λ j', if j' = j then c.b j + (cs i).w else c.b j',
    have hp : p ∈ c.bottom,
    { split, simp [bottom, p, if_neg hj], intro j', simp [tail, side_tail],
      by_cases hj' : j'.succ = j,
      simp [p, -add_comm, if_pos hj', side, hj', le_of_lt (cs i).hw, his i h2i],
      simp [p, -add_comm, if_neg hj'] },
    rcases v.1 hp with ⟨_, ⟨i', rfl⟩, hi'⟩,
    have h2i' : i' ∈ is := ⟨hi'.1.symm, v.2.1 i' hi'.1.symm ⟨tail p, hi'.2, hp.2⟩⟩,
    refine ⟨⟨i, h2i⟩, ⟨i', h2i'⟩, _⟩,
    intro hii', cases congr_arg subtype.val hii',
    sorry,


     },
  have : nonempty is,
  { rcases v.1 c.b_mem_bottom with ⟨_, ⟨i, rfl⟩, hi⟩, use i, use hi.1.symm,
    apply v.2.1 i hi.1.symm, use tail c.b, split, exact hi.2, intro j, apply b_mem_to_set },
  cases classical.indefinite_description _ (is.exists_min (λ i, (cs i).w)
    (finite.of_fintype is) (by simpa)) with i hi1,
  cases classical.indefinite_description _ hi1 with hi h2i, clear hi1,
  have h3i : (cs i).xm ≠ 1,
  { apply ne_of_lt, },
  have h4i : ∀j, (cs i).b j > c.b j ∧ (cs i).b j + (cs i).w < c.b j + c.w,
  { sorry },
  -- refine ⟨i, ⟨_, _, _⟩, _⟩,
  -- { intro p, apply shift_up_bottom_subset_bottoms h h3i },
  -- { rintros i' hi' ⟨p2, hp2, h2p2⟩, simp at hi', classical, by_contra h2i',
  --   rw [tail_shift_up] at h2p2, simp [not_subset] at h2i', rcases h2i' with ⟨p1, hp1, h2p1⟩,
  --   have : ∃p3, p3 ∈ (cs i').tail.to_set ∧ p3 ∉ (cs i).tail.to_set ∧ p3 ∈ c.tail.to_set,
  --   { simp [to_set, not_forall] at h2p1, cases h2p1 with j hj,
  --     rcases Ico_lemma (h4i j.succ).1 (by simp [hw]) (h4i j.succ).2
  --       (le_trans (hp2 j).1 $ le_of_lt (h2p2 j).2)
  --       (le_trans (h2p2 j).1 $ le_of_lt (hp2 j).2) ⟨hj, hp1 j⟩ with ⟨w, hw, h2w, h3w⟩,
  --     refine ⟨λ j', if j' = j then w else p2 j', _, _, _⟩,
  --     { intro j', by_cases h : j' = j, simp [if_pos h], convert h3w,
  --       simp [if_neg h], exact hp2 j' },
  --     { simp [to_set, not_forall], use j, rw [if_pos rfl], convert h2w },
  --     { intro j', by_cases h : j' = j, simp [if_pos h, side_tail], convert hw,
  --       simp [if_neg h], apply hi.2, apply h2p2 }},
  --   rcases this with ⟨p3, h1p3, h2p3, h3p3⟩,
  --   let p := cons (c.b 0) p3,
  --   have hp : p ∈ c.bottom, { refine ⟨rfl, _⟩, rwa [tail_cons] },
  --   rcases v.1 hp with ⟨_, ⟨i'', rfl⟩, hi''⟩,
  --   have h2i'' : i'' ∈ is,
  --   { use hi''.1.symm, apply v.2.1 i'' hi''.1.symm,
  --     use tail p, split, exact hi''.2, rw [tail_cons], exact h3p3 },
  --   have h3i'' : (cs i).w < (cs i'').w,
  --   { apply lt_of_le_of_ne (h2i i'' h2i''), apply h.2.2.1.ne, rintro rfl, apply h2p3,
  --     convert hi''.2, rw [tail_cons] },
  --   let p' := cons (cs i).xm p3,
  --   have hp' : p' ∈ (cs i').to_set,
  --   { simpa [to_set, forall_fin_succ, p', hi'.symm] using h1p3 },
  --   have h2p' : p' ∈ (cs i'').to_set,
  --   { simp [to_set, forall_fin_succ, p'],
  --     refine ⟨_, by simpa [to_set, p] using hi''.2⟩,
  --     have : (cs i).b 0 = (cs i'').b 0, { by rw [hi.1, h2i''.1] },
  --     simp [side, le_of_lt (cs i).hw, xm, this, h3i''] },
  --   apply not_disjoint_iff.mpr ⟨p', hp', h2p'⟩,
  --   apply h.1, rintro rfl, apply (cs i).b_ne_xm, rw [←hi', ←hi''.1, hi.1], refl },
  -- { intros i' hi', dsimp [shift_up] at hi', cases h.2.2.1 hi', apply b_ne_xm },
  -- { exact his i hi }
end

noncomputable def sequence_of_cubes (h : correct cs) : ℕ → { i : ι // valley cs ((cs i).shift_up) }
| 0     := let x := main_lemma h $ valley_all h in ⟨x.1, x.2.1⟩
| (k+1) := let x := main_lemma h (sequence_of_cubes k).2 in ⟨x.1, x.2.1⟩

def decreasing_sequence (h : correct cs) (k : ℕ) : order_dual ℝ :=
(cs (sequence_of_cubes h k).1).w

lemma strict_mono_sequence_of_cubes (h : correct cs) : strict_mono $ decreasing_sequence h :=
strict_mono_nat $ λ k, by { dsimp [decreasing_sequence, sequence_of_cubes],
  exact (main_lemma h (sequence_of_cubes h k).2).2.2 }

open cardinal
theorem cubing_a_cube (h : correct cs) : false :=
begin
  apply not_le_of_lt (lt_omega_iff_fintype.mpr ⟨_inst_1⟩),
  rw [omega, lift_id], fapply mk_le_of_injective, exact λ n, (sequence_of_cubes h n).1,
  intros n m hnm,
  apply strict_mono.injective (strict_mono_sequence_of_cubes h), dsimp only [decreasing_sequence],
  rw hnm
end
