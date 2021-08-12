import analysis.special_functions.trigonometric

open real
open_locale real

variables (x y : ℝ)

lemma sin_sub' : sin (x - y) = sin x * cos y - cos x * sin y :=
begin
  sorry
end

/- `neg_mul_eq_neg_mul_symm` may be useful -/
lemma sin_sub_pi : sin (π - x) = sin x :=
begin
  sorry
end

example : (sin x) ^ 2 + (cos x)^2 = 1 := sin_sq_add_cos_sq x

-- this may be useful `le_add_of_nonneg_right`
lemma sin_sq_le_one : sin x ^ 2 ≤ 1 :=
begin 
  sorry
end

lemma sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 :=
begin
  have H : 2*x + x = 3*x := by linarith,
  -- I have no proof for this, but feel it should be pretty easy.
  -- This may be where I make a fool of myself. 
  -- But I believe very highly in Lean (and myself).
  sorry
end
