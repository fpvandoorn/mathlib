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
open fintype set function
open_locale big_operators classical


namespace list

variables {ι : Type*} (α : ι → Type*)

-- def tprod : list ι → Type*
-- | []        := punit
-- | (i :: is) := α i × tprod is

-- def pi_mem_empty_equiv : (Π i ∈ (∅ : finset ι), α i) ≃ punit :=
-- by { refine @equiv_punit_of_unique _ ⟨⟨λ _, false.elim⟩, λ f, funext (λ x, _)⟩, ext, contradiction }

-- def pi_mem_insert_equiv {s : set ι} {x : ι}
--   :
--   (Π i ∈ (∅ : finset ι), α i) ≃ punit :=
-- by { refine @equiv_punit_of_unique _ ⟨⟨λ _, false.elim⟩, λ f, funext (λ x, _)⟩, ext, contradiction }

-- def tprod_equiv_pi_to_finset : Π (l : list ι), tprod α l ≃ Π i ∈ l.to_finset, α i
-- | []        := (pi_mem_empty_equiv α).symm
-- | (i :: is) := _

/- similar to `pempty_arrow_equiv_punit` -/
def pi_equiv_punit_of_empty (α : ι → Type*) (e : ι → false) : (Π i : ι, α i) ≃ punit :=
@equiv_punit_of_unique _ ⟨⟨λ x, false.elim (e x)⟩, λ f, funext (λ x, false.elim (e x))⟩

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
  the maximal measure `n` with the property that `ν (pi univ s) = ∏ i, μ i (s i)`,
  where `pi univ s` is the product of the sets `{ s i | i : ι }`. -/
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
