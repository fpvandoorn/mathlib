import data.real.pi

set_option profiler true

namespace real

lemma sqrt_two_add_series_step_up' {x z : ℝ} {n : ℕ} (y : ℝ) (hz : sqrt_two_add_series y n ≤ z)
  (h : 2 + x ≤ y ^ 2) (h2 : 0 ≤ y) : sqrt_two_add_series x (n+1) ≤ z :=
begin
  refine le_trans _ hz, rw [sqrt_two_add_series_succ], apply sqrt_two_add_series_monotone_left,
  rw [sqrt_le_left], exact h, exact h2
end

lemma sqrt_two_add_series_step_down' {x z : ℝ} {n : ℕ} (y : ℝ) (hz : z ≤ sqrt_two_add_series y n)
  (h : y ^ 2 ≤ 2 + x) : z ≤ sqrt_two_add_series x (n+1) :=
begin
  apply le_trans hz, rw [sqrt_two_add_series_succ],
  apply sqrt_two_add_series_monotone_left, exact le_sqrt_of_sqr_le h
end

/- currently we use the "slow" certificates (using real computation instead of nat computation),
  because the certificates for nat raise errors during type-checking -/

-- the following lemma takes about 9 seconds
lemma pi_gt_31415 : pi > 3.1415 :=
begin
  refine lt_of_le_of_lt _ (pi_gt_sqrt_two_add_series 6), rw [mul_comm],
  apply le_mul_of_div_le, norm_num, apply le_sqrt_of_sqr_le, rw [le_sub],
  apply sqrt_two_add_series_step_up' (11482/8119),
  apply sqrt_two_add_series_step_up' (5401/2923),
  apply sqrt_two_add_series_step_up' (2348/1197),
  apply sqrt_two_add_series_step_up' (11367/5711),
  apply sqrt_two_add_series_step_up' (25705/12868),
  apply sqrt_two_add_series_step_up' (23235/11621),
  all_goals {norm_num}
end

-- the following lemma takes about 14 seconds
lemma pi_lt_31416 : pi < 3.1416 :=
begin
  refine lt_of_lt_of_le (pi_lt_sqrt_two_add_series 9) _,
  apply add_le_of_le_sub_right, rw [mul_comm], apply mul_le_of_le_div, apply pow_pos, norm_num,
  rw [sqrt_le_left, sub_le],
  apply sqrt_two_add_series_step_down' (4756/3363),
  apply sqrt_two_add_series_step_down' (101211/54775),
  apply sqrt_two_add_series_step_down' (505534/257719),
  apply sqrt_two_add_series_step_down' (83289/41846),
  apply sqrt_two_add_series_step_down' (411278/205887),
  apply sqrt_two_add_series_step_down' (438142/219137),
  apply sqrt_two_add_series_step_down' (451504/225769),
  apply sqrt_two_add_series_step_down' (265603/132804),
  apply sqrt_two_add_series_step_down' (849938/424971),
  all_goals {norm_num}
end

-- the following lemma takes about 15 seconds
lemma pi_gt_3141592 : pi > 3.141592  :=
begin
  refine lt_of_le_of_lt _ (pi_gt_sqrt_two_add_series 10), rw [mul_comm],
  apply le_mul_of_div_le, norm_num, apply le_sqrt_of_sqr_le,
  rw [le_sub],
  apply sqrt_two_add_series_step_up' (11482/8119),
  apply sqrt_two_add_series_step_up' (7792/4217),
  apply sqrt_two_add_series_step_up' (54055/27557),
  apply sqrt_two_add_series_step_up' (949247/476920),
  apply sqrt_two_add_series_step_up' (3310126/1657059),
  apply sqrt_two_add_series_step_up' (2635492/1318143),
  apply sqrt_two_add_series_step_up' (1580265/790192),
  apply sqrt_two_add_series_step_up' (1221775/610899),
  apply sqrt_two_add_series_step_up' (3612247/1806132),
  apply sqrt_two_add_series_step_up' (849943/424972),
  all_goals {norm_num}
end

-- the following lemma takes about 19 seconds
lemma pi_lt_3141593 : pi < 3.141593 :=
begin
  refine lt_of_lt_of_le (pi_lt_sqrt_two_add_series 11) _,
  apply add_le_of_le_sub_right, rw [mul_comm], apply mul_le_of_le_div, apply pow_pos, norm_num,
  rw [sqrt_le_left, sub_le],
  apply sqrt_two_add_series_step_down' (27720/19601),
  apply sqrt_two_add_series_step_down' (56935/30813),
  apply sqrt_two_add_series_step_down' (49359/25163),
  apply sqrt_two_add_series_step_down' (258754/130003),
  apply sqrt_two_add_series_step_down' (113599/56868),
  apply sqrt_two_add_series_step_down' (1101994/551163),
  apply sqrt_two_add_series_step_down' (8671537/4336095),
  apply sqrt_two_add_series_step_down' (3877807/1938940),
  apply sqrt_two_add_series_step_down' (52483813/26242030),
  apply sqrt_two_add_series_step_down' (56946167/28473117),
  apply sqrt_two_add_series_step_down' (23798415/11899211),
  all_goals {norm_num},
end

end real
