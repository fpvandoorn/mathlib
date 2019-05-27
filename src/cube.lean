import data.real.basic data.set.disjointed data.set.intervals
  set_theory.cardinal data.dvector

open real set function cardinal
-- begin move

def strict_mono_nat {α} [preorder α] {f : ℕ → α} (h : ∀n, f n < f (n+1)) : strict_mono f :=
by { intros n m hnm, induction hnm with m' hnm' ih, apply h, exact lt.trans ih (h _) }

-- end move

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

structure cube : Type :=
(b : dvector ℝ 3) -- bottom-left coordinate
(w : ℝ) -- width
(hw : w > 0)

namespace cube
def to_set (c : cube) : set (dvector ℝ 3) :=
(c.b.map $ λ x, Ico x $ x + c.w).setprod

lemma mem_to_set {x y z : ℝ} {c : cube} : [x, y, z] ∈ c.to_set ↔
  x ∈ Ico c.b.head (c.b.head + c.w) ∧
  y ∈ Ico c.b.tail.head (c.b.tail.head + c.w) ∧
  z ∈ Ico c.b.tail.tail.head (c.b.tail.tail.head + c.w) :=
by sorry --{ simp [bottom, dvector.mem_setprod] }

def bottom (c : cube) : set (dvector ℝ 3) :=
({c.b.head} :: c.b.tail.map (λ x, Ico x $ x + c.w)).setprod

@[simp] lemma mem_bottom {x y z : ℝ} {c : cube} : [x, y, z] ∈ c.bottom ↔
  x = c.b.head ∧
  y ∈ Ico c.b.tail.head (c.b.tail.head + c.w) ∧
  z ∈ Ico c.b.tail.tail.head (c.b.tail.tail.head + c.w) :=
by sorry --{ simp [bottom, dvector.mem_setprod] }

/- interior of the bottom -/
def inbottom (c : cube) : set (dvector ℝ 3) :=
({c.b.head} :: c.b.tail.map (λ x, Ioo x $ x + c.w)).setprod

/- closure of the bottom -/
def clbottom (c : cube) : set (dvector ℝ 3) :=
({c.b.head} :: c.b.tail.map (λ x, Icc x $ x + c.w)).setprod

@[simp] def xm (c : cube) : ℝ :=
c.b.head + c.w

def shift_up (c : cube) : cube :=
⟨c.xm :: c.b.tail, c.w, c.hw⟩

def all : cube :=
⟨[0, 0, 0], 1, by norm_num⟩

end cube
open cube

variables {ι : Type} [fintype ι] {cs : ι → cube} {i : ι}

/- disjoint family of cubes -/

def correct (cs : ι → cube) : Prop :=
pairwise (disjoint on (cube.to_set ∘ cs)) ∧
(⋃(i : ι), (cs i).to_set) = cube.all.to_set ∧
injective (cube.w ∘ cs) ∧
cardinal.mk ι > 1

variable (h : correct cs)

@[reducible] def bottoms (cs : ι → cube) : set (dvector ℝ 3) := ⋃(i : ι), (cs i).bottom

include h
lemma zero_le_b {x} (hx : x ∈ (cs i).b) : 0 ≤ x :=
sorry

lemma b_add_w_le_one {x} (hx : x ∈ (cs i).b) : x + (cs i).w ≤ 1 :=
sorry

lemma w_le_one (i : ι) : (cs i).w ≤ 1 :=
sorry

lemma w_lt_one (i : ι) : (cs i).w < 1 :=
sorry

lemma shift_up_bottom_subset_bottoms (hc : (cs i).xm ≠ 1) :
  (cs i).shift_up.bottom ⊆ bottoms cs :=
sorry

omit h
/- the bottom face of c forms a "valley" -/
def valley (cs : ι → cube) (c : cube) : Prop :=
c.bottom ⊆ bottoms cs ∧
--c.clbottom ∩ (⋃(i : ι), (cs i).inbottom) ⊆ c.inbottom ∧
(∃k > c.b.head, ∀i, k ∈ Ico (cs i).b.head ((cs i).b.head + (cs i).w) →
  c.) ∧
∀(i : ι), (cs i).w = c.w → (cs i).b.head ≠ c.b.head

variables {c : cube} (v : valley cs c)

lemma valley_all (h : correct cs) : valley cs cube.all :=
begin
  refine ⟨_, _, _⟩,
  { rintro l, dvector_cases l with x y z,
    simp only [all, and_imp, mem_bottom, zero_add, dvector.head, dvector.nth, dvector.tail_cons, mem_Ico],
    rintro rfl, intros,
    have : [0, y, z] ∈ cube.all.to_set,
    { simp [cube.all, cube.to_set], split, norm_num, simp* },
    rw [←h.2.1] at this, rcases this with ⟨_, ⟨i, rfl⟩, hi⟩,
    rw [bottoms, mem_Union], use i,
    rw [mem_to_set] at hi, rcases hi with ⟨hx, hy, hz⟩,
    have : 0 = (cs i).b.head,
    { apply le_antisymm, exact zero_le_b h dvector.head_mem, simp at hx, exact hx.1 },
    rw [mem_bottom], use this, simp only [*, true_and] },
  { sorry },
  { exact λ i hi, false.elim $ ne_of_lt (w_lt_one h i) hi }
end

def main_lemma (h : correct cs) (v : valley cs c) :
  { i : ι // valley cs ((cs i).shift_up) ∧ (cs i).w < c.w } :=
begin

end

def sequence_of_cubes (h : correct cs) : ℕ → { i : ι // valley cs ((cs i).shift_up) }
| 0     := let x := main_lemma h $ valley_all h in ⟨x.1, x.2.1⟩
| (n+1) := let x := main_lemma h (sequence_of_cubes n).2 in ⟨x.1, x.2.1⟩

def decreasing_sequence (h : correct cs) (n : ℕ) : order_dual ℝ :=
(cs (sequence_of_cubes h n).1).w

lemma strict_mono_sequence_of_cubes (h : correct cs) : strict_mono $ decreasing_sequence h :=
strict_mono_nat $ λ n, (main_lemma h (sequence_of_cubes h n).2).2.2

theorem cubing_a_cube (h : correct cs) : false :=
begin
  apply not_le_of_lt (lt_omega_iff_fintype.mpr ⟨_inst_1⟩),
  rw [omega, lift_id], fapply mk_le_of_injective, exact λ n, (sequence_of_cubes h n).1,
  intros n m hnm,
  apply strict_mono.injective (strict_mono_sequence_of_cubes h), dsimp only, rw hnm
end

#print infinite
