import tactic
import .lesson3

noncomputable theory
open_locale classical

open PreHilbertPlane
open HilbertPlane


section plane_separation

variables {Ω : Type*} [HilbertPlane Ω]

variables {A B C : Ω}
variables {ℓ r s : Line Ω}


lemma auxiliary_point (ℓ : Line Ω) (h : collinear A B C) (hA : ¬ A ∈ ℓ) (hB : ¬ B ∈ ℓ)
	(hC : ¬ C ∈ ℓ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)  :
	∃ (D E : Ω), D ∈ ℓ ∧ ¬ E ∈ ℓ ∧ same_side ℓ A E ∧ (D * A * E) ∧
					¬ collinear A B E ∧
					¬ collinear E C B ∧
					¬ collinear A C E  :=
begin
	simp only [collinear_iff] at h,
	obtain ⟨ m, ⟨hAm, hBm, hCm⟩ ⟩ := h,
	obtain rfl | ℓ_not_m := em(ℓ = m),
		tauto,
	have HD : ∃ (D : Ω), D ∈ ℓ ∧ D ∉ m := point_in_line_difference ℓ_not_m,
	rcases HD with ⟨D ,⟨hDℓ, hDm⟩⟩,
	have hDA : D ≠ A,
	{
		intro hda,
		subst hda,
		exact hDm hAm,
	},
	have HE : ∃ E : Ω, D * A * E := HilbertPlane.B2 hDA,
	cases HE with E hE,
	have hDAE : collinear D A E := (HilbertPlane.B12 hE).2.2.2,
	rcases hDAE with ⟨ 	s, ⟨ hDs,hAs, hEs⟩⟩,
	
	have ℓ_not_s : ℓ ≠ s,
	{
		intro hℓs,
		subst hℓs,
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
		right,
		ext1,
		norm_num,
		rintros (rfl | rfl|  h), repeat {assumption},
		{
			intro hxℓ,
			have x_is_D : x = D,
			{
				apply distinct_lines_have_at_most_one_common_point ℓ_not_s,
				repeat {assumption},
				exact between_points_share_line hAs hEs h,
			},
			subst x_is_D,
			have hxAE : collinear x A E := (HilbertPlane.B12 hE).2.2.2,
			have Hfin := HilbertPlane.B3 hxAE,
			unfold xor3 at Hfin,
			tauto,
		},
	},
	have E_notin_m : E ∉ m,
	{
		intro hEm,
		have hsm : s = m := I12 (HilbertPlane.B12 hE).2.2.1 hAs hEs hAm hEm,
		subst hsm,
		tauto,
	},
	use [D, E],
	unfold same_side at hAE,
	repeat {split},
	repeat {tauto},
	all_goals
	{
		intro h,
		rw collinear_iff at h,
		obtain ⟨ t, ⟨ hAt, hBt, hEt⟩⟩ := h,
		have m_eq_t : m = t,
		{
			try {apply equal_lines_of_contain_two_points hAB; assumption,},
			try {apply equal_lines_of_contain_two_points hBC; assumption,},
			try {apply equal_lines_of_contain_two_points hAC; assumption,},
		},
		subst m_eq_t,
		tauto,
	},
end

lemma same_side.trans : same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
intros hAB hBC,
by_cases ¬ collinear A B C,
{
	rw collinear_order_irrelevant_v1 at h,
	rw collinear_order_irrelevant_v2 at h,
	exact same_side_trans_of_noncollinear h hAB hBC,
},
{
	-- A B C collinear
	push_neg at h,
	obtain rfl | hAeqB := em(A = B), assumption,
	obtain rfl | hBeqC := em(B = C), assumption,
	obtain rfl | hAeqC := em(A = C), exact same_side.refl,
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
	obtain ⟨D,E, ⟨ hDℓ, hEℓ, hAE, hDAE, hABE, hECB, hACE⟩⟩ :=
		auxiliary_point ℓ h _ _ _ _ _ _,
	{
		rw collinear_order_irrelevant_v2 at hABE,
		have hBE : same_side ℓ B E :=
			same_side_trans_of_noncollinear hABE (same_side.symm hAB) hAE,
		have hEC : same_side ℓ E C :=
			same_side_trans_of_noncollinear hECB (same_side.symm hBE) hBC,
		apply same_side_trans_of_noncollinear hACE hAE hEC,
	},
	repeat {tauto},
},
end

end plane_separation