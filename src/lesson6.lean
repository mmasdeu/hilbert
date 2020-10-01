import tactic
import .lesson5

noncomputable theory
open_locale classical

open hilbertplane

section plane_separation

variable {Ω : HilbertPlane}
variables {A B C : Ω.Point}
variables {r s ℓ: Ω.Line}

lemma point_neq_of_not_same_side (hA : ¬ A ∈ ℓ) (hB : ¬ B ∈ ℓ)
	(h : ¬ same_side ℓ A B) : A ≠ B :=
begin
	intro H,
	rw H at h,
	apply h same_side.refl,
end

lemma point_in_between_of_in_line_segment (ℓ : Ω.Line):
	¬ A ∈ ℓ → ¬ B ∈ ℓ → C ∈ (A#B) ∩ ℓ → A * C * B :=
begin
	intros hA hB h,
	simp only [set.mem_insert_iff, set.mem_inter_eq,
			line_segment_simp, set.mem_singleton_iff, set.mem_union_eq,
			set.mem_set_of_eq, set.union_singleton] at h,
	rcases h with ⟨( h1| h1) | h2, hC⟩;
	{
		try {rw h1 at hC},
		tauto,
	},
end

lemma at_most_two_classes_of_noncollinear (hA : ¬ A ∈ ℓ) (hB : ¬ B ∈ ℓ) (hC : ¬ C ∈ ℓ)
		(hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C)
		(h : ¬ HilbertPlane.collinear A B C) : same_side ℓ B C :=
begin
	suffices : (B#C) ∩ ℓ = ∅,
	{
		right,
		exact this,
	},
	unfold same_side at hAB,
	push_neg at hAB,
	replace hAB := hAB.2,
	replace hAB : ∃ D : Ω.Point, D ∈ (A#B) ∩ ℓ,
	{
		refine set.not_disjoint_iff.mp _,
		rwa set.disjoint_iff_inter_eq_empty,
	},
	cases hAB with D hD,
	have H' : A * D * B,
	{
		apply point_in_between_of_in_line_segment ℓ,
		repeat {assumption},
	},
	have H := HilbertPlane.B4 h hA hB hC hD.2,
	specialize H H',
	rcases H with ⟨ ⟨E, hE, h1⟩, hF⟩ | ⟨ ⟨E, hE, h1 ⟩, hF⟩,
	{
		push_neg at hF,
		by_contradiction hcontra,
		replace hcontra : set.nonempty ((B#C) ∩ ℓ) := set.nmem_singleton_empty.mp hcontra,
		replace hcontra : ∃ X : Ω.Point, X ∈ (B#C) ∩ ℓ, by exact hcontra,
		cases hcontra with X hX,
		specialize hF X hX.2,
		apply hF,
		apply point_in_between_of_in_line_segment ℓ,
		repeat{assumption},
	},
	{
		exfalso,
		have hF' : ∃ E : Ω.Point, (E ∈  ℓ) ∧ (A * E * C),
		{
			unfold same_side at hAC,
			push_neg at hAC,
			replace hAC := hAC.2,
			replace hAC : ∃ E : Ω.Point, E ∈ (A#C) ∩ ℓ,
			{
				refine set.not_disjoint_iff.mp _,
				rwa set.disjoint_iff_inter_eq_empty,
			},
			cases hAC with E hE,
			use E,
			split,
				exact hE.2,
			{
				apply point_in_between_of_in_line_segment ℓ,
				repeat {assumption},
			},
		},
		exact hA (false.rec (A ∈ ℓ) (hF hF')),
	},
end

lemma same_side.at_most_two_classes	(hA : ¬ A ∈ ℓ) (hB : ¬ B ∈ ℓ) (hC : ¬ C ∈ ℓ)
		(hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C): same_side ℓ B C :=
begin
	by_cases HilbertPlane.collinear A B C,
	{
		have hAneqB : A ≠ B := point_neq_of_not_same_side hA hB hAB,
		have hAneqC : A ≠ C := point_neq_of_not_same_side hA hC hAC,
		rw [collinear_order_irrelevant_v1, ←collinear_order_irrelevant_v2] at h,
		obtain ⟨D,E, ⟨ hDℓ, hEℓ, hCE, hDCE, hCBE, hEAB, hCAE⟩⟩ :=
			auxiliary_point hC hB hA (ne.symm hBneqC) (ne.symm hAneqC) (ne.symm hAneqB) h,
 		have BnE : B ≠ E,
		{
			intro hcontra,
			rw hcontra at h,
			apply hCAE,
			rw [collinear_order_irrelevant_v1, collinear_order_irrelevant_v2],
			exact h,
		},
		have hAnE : ¬ same_side ℓ A E,
		{
			intro hAsE,
			apply hAC,
			apply same_side.trans hAsE,
			apply same_side.symm hCE,
		},
		have hBsE : same_side ℓ B E,
		{
			rw collinear_order_irrelevant_v2 at hEAB,
			apply at_most_two_classes_of_noncollinear hA hB hEℓ,
			repeat {assumption},
		},
		apply same_side.trans hBsE,
		apply same_side.symm hCE,
	},
	apply at_most_two_classes_of_noncollinear hA,
	repeat {assumption},
end

theorem plane_separation (ℓ : Ω.Line):  ∃ S1 S2 : set (Ω.Point),
        S1 ∩ S2 = ∅ ∧ S1 ∪ S2 ∪ ℓ = {P : Ω.Point | tt} ∧
        (∀ A B : Ω.Point, (A ∉ ℓ) → (B ∉ ℓ) → 
			(( A ∈ S1 ∧ B ∈ S1) ∨ (A ∈ S2 ∧ B ∈ S2) ↔ (A#B) ∩ ℓ = ∅)) :=
begin
	have have_AB := same_side.at_least_two_classes ℓ,
	rcases have_AB with ⟨ C, D, hC, hD, H⟩,
	let S1 := {P : Ω.Point | same_side ℓ P C},
	let S2 := {P : Ω.Point | same_side ℓ P D},
	use [S1, S2],
	repeat {split},
	{ -- S1 ∩ S2 = ∅
		ext1,
		norm_num,
		intros h1 h2,
		apply H (same_side.trans (same_side.symm h1) h2),
	},
	{ -- S1 ∪ S2 ∪ ℓ = everything
		ext, norm_num,
		by_cases x ∈ ℓ,
		tauto,
		{
			left,
			by_cases hs : same_side ℓ C x,
				exact or.inl (same_side.symm hs),
			{
				right,
				by_cases hxD : x = D,
					rw hxD,	exact same_side.refl,
				apply same_side.at_most_two_classes,
                repeat {assumption},
			}
		}
	},
	{
		intros A B hA hB,
		split,
		{
			rintros (h | h);
			{ -- same_side A B
				have h1 : same_side ℓ A B,
				{
					apply same_side.trans h.1,
					apply same_side.symm h.2,
				},
				cases h1;
				tauto,
			},
		},
		{
			intro h,
			rw segments_are_symmetric at h,
			by_cases h1 : same_side ℓ A C,
			exact or.inl ⟨h1, same_side.trans (or.inr h) h1⟩,
			{
				right,
				have hAD : same_side ℓ A D,
				{
					replace h1 : ¬ same_side ℓ C A := λ x, h1 (same_side.symm x),
					by_cases hAD : A = D,
					{
						rw hAD,
						exact same_side.refl,
					},
					apply same_side.at_most_two_classes,
					repeat {assumption},
				},
				exact ⟨ hAD, same_side.trans (or.inr h) hAD⟩,
			}
		},
	},
end

end plane_separation
