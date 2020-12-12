/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.prod
/-!
# The product measure space

TODO:

finitary products

-/

noncomputable theory
open fintype set function equiv
open_locale big_operators classical

lemma pi_congr {ι} {α β : ι → Type*} (h : ∀ i, α i = β i) : (Π i, α i) = (Π i, β i) :=
by { cases (show α = β, from funext h), refl }


namespace function

variables {ι : Type*} [decidable_eq ι] {α : ι → Type*} {s : set ι} {i : ι}

def extend_insert (f : Π (j : ι), j ∈ s → α j) (x : α i) (j : ι) (hj : j ∈ insert i s) : α j :=
if h : j = i then by { subst h, exact x } else f j (mem_of_mem_insert_of_ne hj h)

@[simp] def extend_insert_of_mem (f : Π (j : ι), j ∈ s → α j) (x : α i) {j : ι} (hj : j ∈ s)
  (hi : i ∉ s) : extend_insert f x j (mem_insert_of_mem _ hj) = f j hj :=
begin
  have : j ≠ i, { rintro rfl, exact hi hj },
  simp [extend_insert, this]
end

@[simp] def extend_insert_self (f : Π (j : ι), j ∈ s → α j) (x : α i) :
  extend_insert f x i (mem_insert i s) = x :=
by simp [extend_insert]

end function
open function

namespace finset
variables {α : Type*}

lemma mem_insert_coe {s : finset α} {x y : α} : x ∈ insert y s ↔ x ∈ insert y (s : set α) :=
by simp

end finset
open finset


namespace equiv
/-- The type of maps from `true` is equivalent to the codomain. -/
def true_arrow_equiv (α : Sort*) : (true → α) ≃ α :=
⟨λ f, f trivial, λ a u, a, λ f, by { ext ⟨⟩, refl }, λ u, rfl⟩

variables {ι : Type*} (α : ι → Type*)

/- A pi-type over an empty type is equivalent to `punit`. Similar to `pempty_arrow_equiv_punit`. -/
def pi_equiv_punit_of_empty (α : ι → Type*) (e : ι → false) : (Π i : ι, α i) ≃ punit :=
@equiv_punit_of_unique _ ⟨⟨λ x, false.elim (e x)⟩, λ f, funext (λ x, false.elim (e x))⟩

/- A pi-type over the empty set is equivalent to `punit`. Similar to `pi_equiv_punit_of_empty`. -/
def pi_mem_empty_equiv : (Π i ∈ (∅ : set ι), α i) ≃ punit :=
by { refine @equiv_punit_of_unique _ ⟨⟨λ _, false.elim⟩, λ f, funext (λ x, _)⟩, ext, contradiction }

/- A pi-type over the empty `finset` is equivalent to `punit`.
  Definitionally equal to `pi_mem_empty_equiv`. -/
def pi_mem_finset_empty_equiv : (Π i ∈ (∅ : finset ι), α i) ≃ punit :=
pi_mem_empty_equiv α

/- A pi-type over the set `insert i s` is a binary product. -/
def pi_mem_insert_equiv {s : set ι} {i : ι} (hi : i ∉ s) :
  (Π j ∈ (insert i s), α j) ≃ α i × (Π j ∈ s, α j) :=
{ to_fun := λ f, ⟨f i (set.mem_insert _ _), λ j hj, f j (mem_insert_of_mem _ hj)⟩,
  inv_fun := λ xg, extend_insert xg.2 xg.1,
  left_inv := begin
    intro f, ext j (rfl|hj),
    { apply extend_insert_self },
    { exact extend_insert_of_mem _ _ hj hi },
  end,
  right_inv := begin
    rintro ⟨x, g⟩, simp only [true_and, prod.mk.inj_iff, eq_self_iff_true, extend_insert_self],
    ext j hj, exact extend_insert_of_mem _ _ hj hi
  end }

/- A pi-type over the `finset` `insert i s` is a binary product. -/
def pi_mem_finset_insert_equiv {s : finset ι} {i : ι} (hx : i ∉ s) :
  (Π j ∈ (insert i s), α j) ≃ α i × (Π j ∈ s, α j) :=
by { convert pi_mem_insert_equiv α (show i ∉ (s : set ι), from hx),
     apply pi_congr, intro i, rw [finset.mem_insert_coe] }

end equiv
open equiv



namespace list

section
variables {α : Type*}

lemma to_finset_surj_on : surj_on to_finset {l : list α | l.nodup} univ :=
begin
  rintro s -,
  induction s with t hl,
  induction t using quot.ind with l,
  refine ⟨l, hl, (to_finset_eq hl).symm⟩
end

end

variables {ι : Type*} (α : ι → Type*)


/-- The product of a family of types over a list. -/
@[nolint has_inhabited_instance] def tprod (l : list ι) : Type* :=
l.foldr (λ i β, α i × β) punit

/-- A pi-type over a `finset` is equivalent to an iterated product. -/
def pi_finset_equiv_tprod {s : finset ι} {l : list ι} (h : l.to_finset = s)
  (h : l.nodup) : (Π i ∈ s, α i) ≃ l.tprod α :=
begin
  subst s, induction l with i l ih,
  { exact pi_mem_finset_empty_equiv α },
  { rw [to_finset_cons], rw [nodup_cons, ← mem_to_finset] at h,
    refine (pi_mem_finset_insert_equiv α h.1).trans _, exact (equiv.refl _).prod_congr (ih h.2) }
end

/-- A pi-type over a `fintype` is equivalent to an iterated product. -/
lemma pi_fintype_equiv_tprod [fintype ι] :
  ∃ l : list ι, nodup l ∧ nonempty ((Π i, α i) ≃ l.tprod α) :=
begin
  rcases to_finset_surj_on (mem_univ (finset.univ : finset ι)) with ⟨l, h1l, h2l⟩,
  refine ⟨l, h1l, ⟨_⟩⟩,
  refine equiv.trans _ (pi_finset_equiv_tprod _ h2l h1l),
  refine Pi_congr_right _, intro i, rw [eq_true_intro (finset.mem_univ _)],
  exact (true_arrow_equiv _).symm
end

instance : measurable_space punit := ⊤
instance measurable_space.pi_Prop {δ : Prop} {π : δ → Type*} [m : Π a, measurable_space (π a)] :
  measurable_space (Π a, π a) :=
⨆ a, (m a).comap (λ b, b a)

instance tprod.measurable_space [∀ i, measurable_space (α i)] :
  ∀ (l : list ι), measurable_space (l.tprod α)
| []        := punit.measurable_space
| (i :: is) := @prod.measurable_space _ _ _ (tprod.measurable_space is)

def pi_finset_measurable_equiv_tprod [∀ i, measurable_space (α i)]
  {s : finset ι} {l : list ι} (h : l.to_finset = s) :
  measurable_equiv (Π i ∈ s, α i) (l.tprod α) :=
begin
  subst s, induction l with i l ih,
  { exact pi_mem_finset_empty_equiv α },
  { rw [to_finset_cons], rw [nodup_cons, ← mem_to_finset] at h,
    refine (pi_mem_finset_insert_equiv α h.1).trans _, exact (equiv.refl _).prod_congr (ih h.2) }
end

def pi_fintype_measurable_equiv_tprod [fintype ι] [∀ i, measurable_space (α i)] :
  ∃ l : list ι, l.nodup ∧ nonempty (measurable_equiv (Π i, α i) (l.tprod α)) :=
begin
  cases to_finset_surjective (finset.univ : finset ι) with l hl, refine ⟨⟨l, _⟩⟩,
  refine measurable_equiv.trans _ (pi_finset_measurable_equiv_tprod _ hl),
  refine Pi_congr_right _, intro i, rw [eq_true_intro (finset.mem_univ _)],
  -- exact (true_arrow_equiv _).symm
end




-- def tprod_equiv_pi_to_finset : Π (l : list ι), tprod α l ≃ Π i ∈ l.to_finset, α i
-- | []        := (pi_mem_empty_equiv α).symm
-- | (i :: is) := _


-- #print fintype.card_eq_zero_equiv_equiv_pempty
-- #print pi_empty_equiv
lemma pi_fintype_rec {P : Type* → Type*}
  (h0 : P punit)
  (hp : ∀ ⦃α β⦄, P α → P β → P (α × β))
  (he : ∀ ⦃α β⦄, P α → β ≃ α → P β)
  (ι : Type*) [fintype ι] (α : ι → Type*) (h : Π i, P (α i)) : P (Π i, α i) :=
begin
  generalize' hn : fintype.card ι = n,
  induction n,
  { refine he h0 _, refine pi_equiv_punit_of_empty _ _, rwa [← fintype.card_eq_zero_iff],  },
  { have : nonempty ι,
    sorry


  }
end

end list

namespace measure_theory

/- finitary products -/
namespace outer_measure
end outer_measure
open outer_measure measure

section measurable_pi
variables {α : Type*} {β : α → Type*} [Πa, measurable_space (β a)]

lemma is_measurable.pi [encodable α] {t : Π i, set (β i)} (hs : ∀ i, is_measurable (t i)) :
  is_measurable (pi univ t) :=
by { convert is_measurable.Inter (λ i, measurable_pi_apply _ (hs i) : _), simp [pi_def] }

lemma measurable_update (f : Π (a : α), β a) {i : α} : measurable (update f i) :=
begin
  apply measurable_pi_lambda,
  intro j, by_cases hj : j = i,
  { cases hj, convert measurable_id, ext, simp },
  simp_rw [update_noteq hj], apply measurable_const,
end

lemma is_measurable_pi_of_nonempty [encodable α] {t : Π i, set (β i)} (h : (pi univ t).nonempty) :
  is_measurable (pi univ t) ↔ ∀ i, is_measurable (t i) :=
begin
  rcases h with ⟨f, hf⟩, refine ⟨λ hst i, _, is_measurable.pi⟩,
  convert measurable_update f hst, rw [update_preimage_univ_pi], exact λ j _, hf j (mem_univ j)
end

lemma is_measurable_pi [encodable α] {t : Π i, set (β i)} :
  is_measurable (pi univ t) ↔ ∀ i, is_measurable (t i) ∨ ∃ i, t i = ∅ :=
begin
  cases (pi univ t).eq_empty_or_nonempty with h h,
  { have := univ_pi_eq_empty_iff.mp h, simp [h, univ_pi_eq_empty_iff.mp h] },
  { simp [←not_nonempty_iff_eq_empty, univ_pi_nonempty_iff.mp h, is_measurable_pi_of_nonempty h] }
end

lemma measurable_pi {γ} [measurable_space γ] {f : γ → Π i, β i} :
  measurable f ↔ ∀ x, measurable (λ c, f c x) :=
⟨λ hf x, (measurable_pi_apply _).comp hf, measurable_pi_lambda f⟩

end measurable_pi

section measure_pi

variables {ι : Type*} [fintype ι] {α : ι → Type*} {m : Π i, outer_measure (α i)}

/-- An upper bound for the measure in a product space.
  It is defined to be the product of the measures of all its projections.
  For boxes it should be equal to the correct measure. -/
def pi_premeasure (m : Π i, outer_measure (α i)) (s : set (Π i, α i)) : ennreal :=
∏ i, m i (eval i '' s)

@[simp] lemma pi_premeasure_def {s : set (Π i, α i)} :
  pi_premeasure m s = ∏ i, m i (eval i '' s) := rfl

lemma pi_premeasure_pi {s : Π i, set (α i)} (hs : (pi univ s).nonempty) :
  pi_premeasure m (pi univ s) = ∏ i, m i (s i) :=
by simp [hs]

lemma pi_premeasure_pi' [nonempty ι] {s : Π i, set (α i)} :
  pi_premeasure m (pi univ s) = ∏ i, m i (s i) :=
begin
  cases (pi univ s).eq_empty_or_nonempty with h h,
  { rcases univ_pi_eq_empty_iff.mp h with ⟨i, hi⟩,
    have : ∃ i, m i (s i) = 0 := ⟨i, by simp [hi]⟩,
    simpa [h, finset.card_univ, zero_pow (fintype.card_pos_iff.mpr _inst_2),
      @eq_comm _ (0 : ennreal), finset.prod_eq_zero_iff] },
  { simp [h] }
end

lemma pi_premeasure_pi_mono {s t : set (Π i, α i)} (h : s ⊆ t) :
  pi_premeasure m s ≤ pi_premeasure m t :=
finset.prod_le_prod' (λ i _, (m i).mono' (image_subset _ h))

lemma pi_premeasure_pi_eval [nonempty ι] {s : set (Π i, α i)} :
  pi_premeasure m (pi univ (λ i, eval i '' s)) = pi_premeasure m s :=
by simp [pi_premeasure_pi']

namespace outer_measure
/-- `outer_measure.pi m` is the finite product of the outer measures `{m i | i : ι}`.
  It is defined to be the maximal outer measure `n` with the property that
  `n (pi univ s) ≤ ∏ i, m i (s i)`, where `pi univ s` is the product of the sets
  `{ s i | i : ι }`. -/
protected def pi (m : Π i, outer_measure (α i)) : outer_measure (Π i, α i) :=
bounded_by (pi_premeasure m)

lemma pi_pi_le (m : Π i, outer_measure (α i)) (s : Π i, set (α i)) :
  outer_measure.pi m (pi univ s) ≤ ∏ i, m i (s i) :=
by { cases (pi univ s).eq_empty_or_nonempty with h h, simp [h],
     exact (bounded_by_le _).trans_eq (pi_premeasure_pi h) }


lemma le_pi {m : Π i, outer_measure (α i)} {n : outer_measure (Π i, α i)} :
  n ≤ outer_measure.pi m ↔ ∀ (s : Π i, set (α i)), (pi univ s).nonempty →
    n (pi univ s) ≤ ∏ i, m i (s i) :=
begin
  rw [outer_measure.pi, le_bounded_by'], split,
  { intros h s hs, refine (h _ hs).trans_eq (pi_premeasure_pi hs)  },
  { intros h s hs, refine le_trans (n.mono $ subset_pi_eval_image univ s) (h _ _),
    simp [univ_pi_nonempty_iff, hs] }
end

-- lemma pi_pi_false [encodable ι] (s : Π i, set (α i))
--   (h2s : (pi univ s).nonempty) : outer_measure.pi m (pi univ s) = ∏ i, m i (s i) :=
-- begin
--   simp_rw [← pi_premeasure_pi h2s],
--   refine le_antisymm (bounded_by_le _) _,
--   refine le_binfi _, dsimp only, intros t ht,
--   sorry
--   -- refine le_trans _ (ennreal.tsum_le_tsum $ λ i, _),
-- end
end outer_measure

namespace measure

variables [Π i, measurable_space (α i)] (μ : Π i, measure (α i))

protected lemma caratheodory {α} [measurable_space α] (μ : measure α) {s t : set α}
  (hs : is_measurable s) : μ (t ∩ s) + μ (t \ s) = μ t :=
(le_to_outer_measure_caratheodory μ s hs t).symm

lemma pi_caratheodory :
  measurable_space.pi ≤ (outer_measure.pi (λ i, (μ i).to_outer_measure)).caratheodory :=
begin
  refine supr_le _, intros i s hs,
  rw [measurable_space.comap] at hs, rcases hs with ⟨s, hs, rfl⟩,
  apply bounded_by_caratheodory, intro t,
  simp_rw [pi_premeasure_def],
  refine finset.prod_add_prod_le' (finset.mem_univ i) _ _ _,
  { simp [image_inter_preimage, image_diff_preimage, (μ i).caratheodory hs, le_refl] },
  { rintro j - hj, apply mono', apply image_subset, apply inter_subset_left },
  { rintro j - hj, apply mono', apply image_subset, apply diff_subset }
end

/-- `measure.pi μ` is the finite product of the measures `{μ i | i : ι}`.
  It is defined to be the maximal product measure, i.e.
  the maximal measure `ν` with the property that `ν (pi univ s) ≤ ∏ i, μ i (s i)`,
  where `pi univ s` is the product of the sets `{ s i | i : ι }`.
  For sigma-finite measures we know that `ν (pi univ s) = ∏ i, μ i (s i)`. -/
protected def pi : measure (Π i, α i) :=
to_measure (outer_measure.pi (λ i, (μ i).to_outer_measure)) (pi_caratheodory μ)

lemma pi_pi [fintype ι] [encodable ι] [∀ i, sigma_finite (μ i)] (s : Π i, set (α i))
  (h1s : ∀ i, is_measurable (s i))
  (h2s : (pi univ s).nonempty) : measure.pi μ (pi univ s) = ∏ i, μ i (s i) :=
begin
  rw [measure.pi, to_measure_apply _ _ (is_measurable.pi h1s)],
  refine le_antisymm (outer_measure.pi_pi_le _ _) _,
  sorry
  -- rcases fintype.exists_univ_list ι with ⟨l, h1l, h2l⟩,
  -- have := l.foldr _ _,
  -- generalize' hn : fintype.card ι = n,
  -- simp_rw [← to_outer_measure_apply, ← pi_premeasure_pi h2s],
  -- refine le_antisymm (bounded_by_le _) _,
  -- refine le_binfi _, dsimp only, intros t ht,
end

end measure

end measure_pi

end measure_theory

open measure_theory measure_theory.outer_measure

namespace relative

namespace measure_theory
section measure_pi

variables {ι : Type*} {α : ι → Type*} {m : Π i, outer_measure (α i)} (t : finset ι)

/-- An upper bound for the measure in a product space.
  It is defined to be the product of the measures of all its projections.
  For boxes it should be equal to the correct measure. -/
def pi_premeasure (m : Π i, outer_measure (α i)) (s : set (Π i, α i)) : ennreal :=
∏ i in t, m i (eval i '' s)

variable {t}

@[simp] lemma pi_premeasure_def {s : set (Π i, α i)} :
  pi_premeasure t m s = ∏ i in t, m i (eval i '' s) := rfl

lemma pi_premeasure_pi {s : Π i, set (α i)} (hs : (pi univ s).nonempty) :
  pi_premeasure t m (pi t s) = ∏ i in t, m i (s i) :=
by sorry

lemma pi_premeasure_pi' [nonempty ι] {s : Π i, set (α i)} :
  pi_premeasure t m (pi t s) = ∏ i in t, m i (s i) :=
begin
  cases (pi univ s).eq_empty_or_nonempty with h h,
  { rcases univ_pi_eq_empty_iff.mp h with ⟨i, hi⟩,
    have : ∃ i, m i (s i) = 0 := ⟨i, by simp [hi]⟩,
    sorry
    --simpa [h, finset.card_univ, zero_pow (fintype.card_pos_iff.mpr _),
      -- @eq_comm _ (0 : ennreal), finset.prod_eq_zero_iff]
      },
  { simp [h], sorry }
end

lemma pi_premeasure_pi_mono {s s' : set (Π i, α i)} (h : s ⊆ s') :
  pi_premeasure t m s ≤ pi_premeasure t m s' :=
finset.prod_le_prod' (λ i _, (m i).mono' (image_subset _ h))

lemma pi_premeasure_pi_eval [nonempty ι] {s : set (Π i, α i)} :
  pi_premeasure t m (pi t (λ i, eval i '' s)) = pi_premeasure t m s :=
by simp [pi_premeasure_pi']

variable (t)
namespace outer_measure
/-- `outer_measure.pi m` is the finite product of the outer measures `{m i | i : ι}`.
  It is defined to be the maximal outer measure `n` with the property that
  `n (pi univ s) ≤ ∏ i, m i (s i)`, where `pi univ s` is the product of the sets
  `{ s i | i : ι }`. -/
protected def pi (m : Π i, outer_measure (α i)) : outer_measure (Π i, α i) :=
bounded_by (pi_premeasure t m)

variable {t}

lemma pi_pi_le (m : Π i, outer_measure (α i)) (s : Π i, set (α i)) :
  outer_measure.pi t m (pi t s) ≤ ∏ i in t, m i (s i) :=
sorry
-- by { cases (pi univ s).eq_empty_or_nonempty with h h, simp [h],
--      exact (bounded_by_le _).trans_eq (pi_premeasure_pi h) }

lemma le_pi {m : Π i, outer_measure (α i)} {n : outer_measure (Π i, α i)} :
  n ≤ outer_measure.pi t m ↔ ∀ (s : Π i, set (α i)), (pi univ s).nonempty →
    n (pi t s) ≤ ∏ i in t, m i (s i) :=
begin
  sorry
  -- rw [outer_measure.pi, le_bounded_by'], split,
  -- { intros h s hs, refine (h _ hs).trans_eq (pi_premeasure_pi hs)  },
  -- { intros h s hs, refine le_trans (n.mono $ subset_pi_eval_image univ s) (h _ _),
  --   simp [univ_pi_nonempty_iff, hs] }
end

-- lemma pi_pi_false [encodable ι] (s : Π i, set (α i))
--   (h2s : (pi univ s).nonempty) : outer_measure.pi m (pi univ s) = ∏ i, m i (s i) :=
-- begin
--   simp_rw [← pi_premeasure_pi h2s],
--   refine le_antisymm (bounded_by_le _) _,
--   refine le_binfi _, dsimp only, intros t ht,
--   sorry
--   -- refine le_trans _ (ennreal.tsum_le_tsum $ λ i, _),
-- end
end outer_measure

namespace measure

variables [Π i, measurable_space (α i)] (μ : Π i, measure (α i))

protected lemma caratheodory {α} [measurable_space α] (μ : measure α) {s t : set α}
  (hs : is_measurable s) : μ (t ∩ s) + μ (t \ s) = μ t :=
(le_to_outer_measure_caratheodory μ s hs t).symm

lemma pi_caratheodory :
  measurable_space.pi ≤ (outer_measure.pi t (λ i, (μ i).to_outer_measure)).caratheodory :=
begin
  refine supr_le _, intros i s hs,
  rw [measurable_space.comap] at hs, rcases hs with ⟨s, hs, rfl⟩,
  apply bounded_by_caratheodory, intro u,
  simp_rw [pi_premeasure_def],
  refine finset.prod_add_prod_le' (sorry : i ∈ t) _ _ _,
  { simp [image_inter_preimage, image_diff_preimage, (μ i).caratheodory hs, le_refl] },
  { rintro j - hj, apply mono', apply image_subset, apply inter_subset_left },
  { rintro j - hj, apply mono', apply image_subset, apply diff_subset }
end
variable (t)

/-- `measure.pi μ` is the finite product of the measures `{μ i | i : ι}`.
  It is defined to be the maximal product measure, i.e.
  the maximal measure `n` with the property that `ν (pi univ s) = ∏ i, μ i (s i)`,
  where `pi univ s` is the product of the sets `{ s i | i : ι }`. -/
protected def pi : measure (Π i, α i) :=
to_measure (outer_measure.pi t (λ i, (μ i).to_outer_measure)) (pi_caratheodory t μ)

variable {t}

lemma pi_pi [fintype ι] [encodable ι] [∀ i, sigma_finite (μ i)] (s : Π i, set (α i))
  (h1s : ∀ i ∈ (t : set ι), is_measurable (s i))
  (h2s : (pi (t : set ι) s).nonempty) : measure.pi t μ (pi t s) = ∏ i in t, μ i (s i) :=
begin
  rw [measure.pi, to_measure_apply _ _ (is_measurable_pi t.countable_to_set h1s)],
  refine le_antisymm (outer_measure.pi_pi_le _ _) _,
  sorry
  -- rcases fintype.exists_univ_list ι with ⟨l, h1l, h2l⟩,
  -- have := l.foldr _ _,
  -- generalize' hn : fintype.card ι = n,
  -- simp_rw [← to_outer_measure_apply, ← pi_premeasure_pi h2s],
  -- refine le_antisymm (bounded_by_le _) _,
  -- refine le_binfi _, dsimp only, intros t ht,
end

end measure

end measure_pi


end relative

end measure_theory
