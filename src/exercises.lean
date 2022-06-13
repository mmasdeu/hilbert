import .hilbert
open_locale classical
noncomputable theory

open IncidencePlane NeutralPlane

-- Exercises
variables {Ω : Type*} [NeutralPlane Ω]

lemma distance_eq (A : Ω) : distance A A = 0 :=
begin
	rw ruler_dist,
	simp only [sub_self, abs_zero],
end

lemma line_through_symm (P Q : Ω) : line_through P Q = line_through Q P :=
begin
	by_cases hPQ : Q = P,
	{
		subst hPQ,
	},
	{
		exact IncidencePlane.incidence hPQ (line_through_right P Q) (line_through_left P Q),
	}
end

lemma distance_symm (A B : Ω) : distance A B = distance B A :=
begin
	rw ruler_dist,
	rw ruler_dist,
	rw line_through_symm,
	rw abs_sub_comm,
end

lemma distance_nonneg (A B : Ω) : 0 ≤ distance A B :=
begin
	rw ruler_dist,
	apply abs_nonneg,
end

lemma distance_nondegenerate (A B : Ω) : distance A B = 0 ↔ A = B :=
begin
	split,
	{
		intro h,
		rw ruler_dist at h,
		set ℓ := line_through A B,
		have h' : ruler ℓ A = ruler ℓ B := eq_of_abs_sub_eq_zero h,
		apply ruler_inj (line_through_left A B) (line_through_right A B) h',
	},
	{
		intro h,
		subst h,
		rw ruler_dist,
		simp only [sub_self, abs_zero],
	}
end

lemma between_swap' (A B C : Ω) : (A * B * C) → (C * B * A) :=
begin
	intro h,
	cases h,
	split,
	{
		rw collinear_of_equal at h_left,
		rw collinear_of_equal,
		finish,
	},
	{
		rw [show distance A C = distance C A, by rw distance_symm] at h_right,
		rw ←h_right,
		rw [show distance C B = distance B C, by rw distance_symm],
		rw [show distance B A = distance A B, by rw distance_symm],
		rw add_comm,
	},
end

lemma between_swap (A B C : Ω) : (A * B * C) ↔ (C * B * A) :=
begin
	split; apply between_swap',
end

@[simp] lemma  between_trivial (A B : Ω) : A * B * B :=
begin
	unfold between,
	split,
	{
		use line_through A B,
		simp,
		exact ⟨line_through_left A B, line_through_right A B⟩
	},
	{
		rw distance_eq,
		exact add_zero (distance A B)
	}
end

@[simp] lemma  between_trivial' (A B : Ω) : A * A * B :=
begin
	rw between_swap,
	exact between_trivial B A,
end

lemma segment_eq (A B : Ω) : A⬝B ≈ B⬝A :=
begin
	simp,
	intro t,
	split;
	{
		intro h,
		rw between_swap,
		tauto,
	},
end

-- We skip the ruler placement postulate. We'll see whether it's needed or not...

meta def linarith' := `[linarith]
lemma abs_sub_of_le (x y : ℝ) (h: x ≤ y . linarith') : |x - y| = y - x :=
begin
	rw abs_of_nonpos (sub_nonpos.mpr h),
	exact neg_sub x y,
end
lemma abs_sub_of_le' (x y : ℝ) (h: y ≤ x . linarith') : |x - y| = x - y :=
begin
	rw abs_of_nonneg (sub_nonneg.mpr h),
end

lemma ruler_dist' (ℓ : Line Ω) {P Q : Ω} (hP : P ∈ ℓ) (hQ : Q ∈ ℓ) : distance P Q = |ruler ℓ P - ruler ℓ Q| :=
begin
	by_cases P = Q,
	{
		rw [h, distance_eq],
		simp only [sub_self, abs_zero],
	},
	{
		rw [incidence h hP hQ, ruler_dist],
	}
end

lemma between_iff_aux (A B C : Ω) : (A * B * C) → C * B * A :=
begin
	intro h,
	split,
	{
		rw collinear_of_equal,
		exact h.1,
	},
	{
		cases h,
		rw distance_symm C B,
		rw distance_symm B A,
		rw distance_symm C A,
		rw ←h_right,
		ring,
	}
end

lemma between_iff (A B C : Ω) : (A * B * C) ↔ C * B * A :=
begin
	split; apply between_iff_aux,
end


lemma between_ruler_aux {A B C : Ω} (ℓ : Line Ω) (hA : A ∈ ℓ) (hB : B ∈ ℓ) (hC : C ∈ ℓ) :
ruler ℓ A ≤ ruler ℓ B ∧ ruler ℓ B ≤ ruler ℓ C → A * B * C :=
begin
	intro h,
	cases h,
	{
		unfold between,
		rw [ruler_dist' ℓ hA hB, ruler_dist' ℓ hB hC, ruler_dist' ℓ hA hC],
		split,
		{
			use ℓ,
			finish,
		},
		repeat {rw abs_sub_of_le},
		ring,
	},
end

lemma between_ruler (A B C : Ω) (ℓ : Line Ω) (hA : A ∈ ℓ) (hB : B ∈ ℓ) (hC : C ∈ ℓ) :
(A * B * C) ↔ ruler ℓ A ≤ ruler ℓ B ∧ ruler ℓ B ≤ ruler ℓ C ∨ ruler ℓ C ≤ ruler ℓ B ∧ ruler ℓ B ≤ ruler ℓ A :=
begin
	split,
	{
		intro h,
		cases h,
		set α := ruler ℓ,
		by_cases H : α A ≤ α B ∧ α B ≤ α C, tauto,
		right,
		rw [ruler_dist' ℓ hA hB, ruler_dist' ℓ hB hC, ruler_dist' ℓ hA hC] at h_right,
		rw [show ruler ℓ = α, by refl] at h_right,
		replace H : α B < α A ∨ α C < α B,
		{
			push_neg at H,
			by_cases hc : α A ≤ α B,
			{
				specialize H hc,
				right, exact H,
			},
			{
				left,
				linarith,
			}
		},
		cases H,
		{
			split,
			{
				by_contradiction hc,
				replace hc : α B < α C, by linarith,
				rw abs_sub_of_le' at h_right,
				rw abs_sub_of_le at h_right,
				by_cases h1 : α A ≤ α C,
				{
					rw abs_sub_of_le at h_right,
					linarith,
				},
				{
					rw abs_sub_of_le' at h_right,
					linarith,
				}
			},
			exact le_of_lt H,			
		},
		{
			split,
			exact le_of_lt H,
			by_contradiction hc,
			replace hc : α A < α B, by linarith,
			rw abs_sub_of_le at h_right,
			rw abs_sub_of_le' at h_right,
			by_cases h1 : α A ≤ α C,
			{
				rw abs_sub_of_le at h_right,
				linarith,
			},
			{
				rw abs_sub_of_le' at h_right,
				linarith,
			}
		}
	},
	{
		intro h,
		cases h,
		{
			apply between_ruler_aux ℓ; assumption,
		},
		{
			rw between_iff,
			apply between_ruler_aux ℓ; assumption,
		}
	}
end

def is_midpoint (P Q M : Ω) := (P * M * Q) ∧ distance P M = distance M Q

lemma midpoint_exists_unique (P Q : Ω) : ∃! M, is_midpoint P Q M :=
begin
	sorry
end

lemma point_construction (r : Ray Ω) (h : ¬ r.degenerate) (d : ℝ) (hd : 0 ≤ d) : 
∃! Q, Q ∈ pts r ∧ distance r.origin Q = d :=
begin
	sorry
end

lemma pasch {T : Triangle Ω} {ℓ : Line Ω} (hT : ¬ T.degenerate) (hℓ : pts ℓ ∩ T.vertices.to_finset ∩ ℓ = ∅)
(h : (pts ℓ ∩ T.A⬝T.B).nonempty) : (pts ℓ ∩ T.B⬝T.C).nonempty ∨ (pts ℓ ∩ T.A⬝T.C).nonempty :=
begin
	sorry
end

lemma isosceles_triangle (T : Triangle Ω) (h : (T.A⬝T.B) ≅ (T.A⬝T.C)) :
(∟ T.A T.B T.C) ≅ (∟ T.A T.C T.B) :=
begin
	set S1 := ▵ T.B T.A T.C,
	set S2 := ▵ T.C T.A T.B,
	simp at h,
	have h1 : (T.B⬝T.A) ≅ (T.C⬝T.A),
	{
		simp,
		rw distance_symm,
		rw h,
		exact distance_symm T.A T.C,
	},
	have h2 : (T.A⬝T.C) ≅ (T.A⬝T.B),
	{
		simp,
		rw distance_symm,
		rw h,
		exact distance_symm T.C T.A,
	},
	have h3 : (∟ T.C T.A T.B) ≅ (∟ T.B T.A T.C),
	{
		apply angle_well_def,
		unfold has_equiv.equiv,
		simp,
	},
	have := (NeutralPlane.SAS S1 S2 h1 h2 h3).2,
	simpa using this.1,
end

-- Theorem 3.3.9
lemma ray_theorem {ℓ : Line Ω} {A B C : Ω} (hA : A ∈ ℓ) (hB : B ∉ ℓ) (hC : C ∈ pts(A=>B)) (hAC : C ≠ A) :
same_side ℓ B C :=
begin
	sorry
end

-- Theorem 3.3.10
lemma point_between_iff_ray_between {A B C D : Ω} (h : ¬ collinear ({A, B, C} : set Ω)) (hD : D ∈ line_through B C)
: (B * D * C) ↔ Ray.between (A=>B) (A=>D) (A=>C)  :=
begin
	sorry
end


lemma same_side.trans (ℓ : Line Ω) {A B C : Ω} : same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
	sorry
end

-- Lemma 3.4.4
lemma ray_betweenness_aux (A B C D : Ω) (hAB : A ≠ B) (h : same_side (line_through A B) C D)
(h' : ¬ D ∈ line_through A C) : C ∈ (∟ B A D).interior ∨ D ∈ (∟ B A C).interior :=
begin
sorry
end

-- Theorem 3.4.5
theorem Ray.between_of_le_measure (A B C D : Ω) (hAB : A ≠ B) (h : same_side (line_through A B) C D) : (∟ B A D).m ≤ (∟ B A C).m ↔ Ray.between (A=>B) (A=>D) (A=>C) :=
begin
sorry
end

-- Theorem 3.5.1
lemma Z_theorem (A D B E: Ω) (hAB : A ≠ D) (h : ¬ same_side (line_through A D) B E) :
(A=>B : set Ω) ∩ D=>E = ∅ :=
begin
sorry
end

theorem crossbar (A B C D : Ω) (h : D ∈ (∟ B A C).interior) :
∃ G : Ω, G ∈ A=>D ∧ G ∈ B⬝C :=
begin
sorry
end

-- Lemma 3.5.1
lemma Angle.interior_of_between {A B C D E : Ω} (D : Ω) (h : C * A * B) (h' : D ∈ (∟ B A E).interior) :
E ∈ (∟ D A C).interior :=
begin
sorry
end

lemma Angle.supplement_of_linear_pair (α β : Angle Ω) :
α.linear_pair β → α.supplementary β :=
begin
sorry
end


-- TOWARDS PROVING PYTHAGORAS' THEOREM

lemma perpendicular_through (ℓ : Line Ω) (P : Ω) (h : P ∉ ℓ): ∃ Q,
Q ∈ ℓ ∧ (line_through P Q) ⊥ ℓ :=
begin
sorry
end

def perpendicular_foot (ℓ : Line Ω) (P : Ω) (h : P ∉ ℓ) : Ω := Exists.some $ perpendicular_through ℓ P h

-- Lemma 4.8.6
lemma perpendicular_between (A B C : Ω) (h0 : C ∉ line_through A B) (h : (∟ C A B).is_acute) (h' : (∟ A B C).is_acute)
: A * (perpendicular_foot (line_through A B) C h0) * B :=
begin
sorry
end