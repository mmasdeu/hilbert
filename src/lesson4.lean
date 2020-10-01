import tactic
import .lesson3

noncomputable theory
open_locale classical

open hilbertplane



section plane_separation

variable {Ω : HilbertPlane}
variables {A B C : Ω.Point}
variables {r s ℓ: Ω.Line}


lemma auxiliary_point (hA : ¬ A ∈ ℓ) (hB : ¬ B ∈ ℓ)
	(hC : ¬ C ∈ ℓ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (h : HilbertPlane.collinear A B C) :
	∃ (D E : Ω.Point), D ∈ ℓ ∧ ¬ E ∈ ℓ ∧ same_side ℓ A E ∧ (D * A * E) ∧
					¬ HilbertPlane.collinear A B E ∧
					¬ HilbertPlane.collinear E C B ∧
					¬ HilbertPlane.collinear A C E  :=
begin
	simp only [collinear_iff] at h,
	obtain ⟨ m, ⟨hAm, hBm, hCm⟩ ⟩ := h,
	have ℓ_not_m : ℓ ≠ m,
	{
		intro h,
		rw← h at hAm,
		tauto,
	},
	have HD : ∃ (D :Ω.Point), D ∈ ℓ ∧ D ∉ m := point_in_line_difference ℓ_not_m,
	push_neg at HD,
	rcases HD with ⟨D ,⟨hDℓ, hDm⟩⟩,
	have HE : ∃ E : Ω.Point, D * A * E := HilbertPlane.B2,
	cases HE with E hE,
	have hDAE : HilbertPlane.collinear D A E := (HilbertPlane.B12 hE).2.2.2,
	rw HilbertPlane.collinear_def at hDAE,
	rcases hDAE with ⟨ 	s, ⟨ hDs,hAs, hEs⟩⟩,
	have ℓ_not_s : ℓ ≠ s,
	{
		intro hℓs,
		rw hℓs at hA,
		exact ℓ_not_m (false.rec (ℓ = m) (hA hAs)),
	},
	have E_notin_ℓ : E ∉ ℓ,
	{
		intro hEℓ,
		apply (HilbertPlane.B12 hE).2.1,
		apply distinct_lines_have_at_most_one_common_point ℓ_not_s hDℓ hDs hEℓ hEs,
	},
	have hAE : same_side ℓ A E,
	{
		unfold same_side,
		repeat {split},
		repeat {assumption},
		suffices : ∀ (X : Ω.Point) , (X ∈ (A#E) → X ∉ ℓ),
		{
            right,
			ext1,
			norm_num,
			intro h,
			apply this,
			simp only [line_segment_simp, set.mem_singleton_iff, set.union_singleton],
			exact h,
		},
		intros X hX,
		simp only [set.mem_insert_iff, line_segment_simp,
			set.mem_singleton_iff, set.mem_union_eq, set.mem_set_of_eq,
			set.union_singleton] at hX,
		rcases hX with ⟨ hX, hX, hX⟩,
		{
			exact E_notin_ℓ,
		},
		{
			rw hX,
			exact hA,
		},
		{
			intro hXℓ,
			have X_is_D : X = D,
			{
				apply distinct_lines_have_at_most_one_common_point ℓ_not_s hXℓ _ hDℓ hDs,
				apply between_points_share_line hAs hEs hX,
			},
			rw X_is_D at hX,
			have AnD : A ≠ D := (HilbertPlane.B12 hE).1.symm,
			have AnE : A ≠ E := (HilbertPlane.B12 hE).2.2.1,
			have DnE : D ≠ E := (HilbertPlane.B12 hE).2.1,
			have HHH := (HilbertPlane.B3 AnD AnE DnE hAs hDs hEs),
			rcases HHH with ⟨ H1,  H2 , H3⟩ | ⟨H1, H2, H3⟩ | ⟨ H1, H2, H3⟩;
			tauto,
		},
	},
	have E_notin_m : E ∉ m,
	{
		intro hEm,
		have hsm : s = m := I12 (HilbertPlane.B12 hE).2.2.1 hAs hEs hAm hEm,
		rw hsm at hDs,
		tauto,
	},
	use [D, E],
	unfold same_side at hAE,
	repeat {split},
	repeat {tauto},
	all_goals
	{
		intro h,
		rw HilbertPlane.collinear_def at h,
		obtain ⟨ t, ⟨ hAt, hBt, hEt⟩⟩ := h,
	},
	work_on_goal 0
	{
		have m_eq_t : m = t,
		apply equal_lines_of_contain_two_points hAB,
		repeat {assumption},
	},
	work_on_goal 1
	{
		have m_eq_t : m = t,
		apply equal_lines_of_contain_two_points hBC,
		repeat {assumption},
	},
    work_on_goal 2
    {
	    have m_eq_t : m = t,
		apply equal_lines_of_contain_two_points hAC,
		repeat {assumption},
    },
	all_goals
	{
		rw← m_eq_t at hAt,
		rw← m_eq_t at hEt,
		tauto,
	},
end

lemma same_side.trans : same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
intro hAB,
intro hBC,
by_cases ¬ HilbertPlane.collinear A B C,
{
	rw collinear_order_irrelevant_v1 at h,
	rw collinear_order_irrelevant_v2 at h,
	exact same_side_trans_of_noncollinear h hAB hBC,
},
{
	-- A B C collinear
	push_neg at h,
	by_cases hAeqB : A = B,
	{
		rw hAeqB,
		exact hBC,
	},
	by_cases hBeqC : B = C,
	{
		rw← hBeqC,
		exact hAB,
	},
	by_cases hAeqC : A = C,
	{
		rw hAeqC,
        apply same_side.refl,
	},
    have H1 := point_on_line_of_same_side hAB,
    have H2 := point_on_line_of_same_side hBC,
    by_cases hAℓ : A ∈ ℓ,
    {
        left,
        split;
        {
            try {rw [←H2, ←H1]},
            exact hAℓ,
        },
    },
    have hBℓ : B ∉ ℓ := λ x, hAℓ (H1.2 x),
    have hCℓ : C ∉ ℓ := λ x, hBℓ (H2.2 x),
	obtain ⟨D,E, ⟨ hDℓ, hEℓ, hAE, hDAE, hABE, hECB, hACE⟩⟩ :=
		auxiliary_point hAℓ hBℓ hCℓ hAeqB hAeqC hBeqC h,
	rw collinear_order_irrelevant_v2 at hABE,
	have hBE : same_side ℓ B E :=
		same_side_trans_of_noncollinear hABE (same_side.symm hAB) hAE,
	have hEC : same_side ℓ E C :=
		same_side_trans_of_noncollinear hECB (same_side.symm hBE) hBC,
	apply same_side_trans_of_noncollinear hACE hAE hEC,
},
end

end plane_separation