import tactic
import .lesson5

noncomputable theory
open_locale classical

open PreHilbertPlane
open HilbertPlane

section plane_separation

variables {Ω : Type*} [HilbertPlane Ω]
variables {A B C : Ω}
variables {ℓ r s : Line Ω}


lemma point_neq_of_not_same_side (hA : ¬ A ∈ ℓ) (hB : ¬ B ∈ ℓ)
	(h : ¬ same_side ℓ A B) : A ≠ B :=
begin
	intro H, subst H,
	apply h same_side.refl,
end

lemma point_in_between_of_in_line_segment (ℓ : Line Ω) (hAℓ : A ∉ ℓ) (hBℓ : B ∉ ℓ):
	C ∈ pts (A⬝B) ∩ ℓ → A * C * B :=
begin
	intro h,
	simp only [set.mem_inter_eq, mem_coe_to_mem, segments_are_symmetric,
		Segment.mem_coe_to_mem_pts] at h,
	rcases h with ⟨( h1| h1) | h2, hC⟩,
		tauto,
	{
		apply B11,
		obtain rfl | h2 := h2; tauto,
	},
end

lemma at_most_two_classes_of_noncollinear (hA : ¬ A ∈ ℓ) (hB : ¬ B ∈ ℓ) (hC : ¬ C ∈ ℓ)
		(hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C)
		(h : ¬ collinear A B C) : same_side ℓ B C :=
begin
	suffices : pts (B⬝C) ∩ ℓ = ∅,
	{
		right,
		exact this,
	},
	unfold same_side at hAB,
	push_neg at hAB,
	replace hAB := hAB.2,
	replace hAB : ∃ D : Ω, D ∈ pts (A⬝B) ∩ ℓ,
	{
		refine set.not_disjoint_iff.mp _,
		rwa set.disjoint_iff_inter_eq_empty,
	},
	cases hAB with D hD,
	have H' : A * D * B,
		apply point_in_between_of_in_line_segment ℓ; assumption,
	have H := HilbertPlane.B4 h hA hB hC hD.2,
	specialize H H',
	rcases H with ⟨ ⟨E, hE, h1⟩, hF⟩ | ⟨ ⟨E, hE, h1 ⟩, hF⟩,
	{
		push_neg at hF,
		by_contradiction hcontra,
		change pts (B⬝C) ∩ ℓ ≠ ∅ at hcontra,
		rw set.ne_empty_iff_nonempty at hcontra,
		cases hcontra with X hX,
		specialize hF X hX.2,
		apply hF,
		apply point_in_between_of_in_line_segment ℓ; assumption,
	},
	{
		exfalso,
		have hF' : ∃ E : Ω, (E ∈  ℓ) ∧ (A * E * C),
		{
			unfold same_side at hAC,
			push_neg at hAC,
			replace hAC := hAC.2,
			replace hAC : ∃ E : Ω, E ∈ pts (A⬝C) ∩ ℓ,
			{
				apply set.not_disjoint_iff.mp,
				rwa set.disjoint_iff_inter_eq_empty,
			},
			cases hAC with E hE,
			use E,
			split,
				exact hE.2,
				apply point_in_between_of_in_line_segment ℓ; assumption,
		},
		exact hA (false.rec (A ∈ ℓ) (hF hF')),
	},
end

lemma same_side.at_most_two_classes	(hA : ¬ A ∈ ℓ) (hB : ¬ B ∈ ℓ) (hC : ¬ C ∈ ℓ)
		(hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C): same_side ℓ B C :=
begin
	by_cases collinear A B C,
	{
		have hAneqB : A ≠ B := point_neq_of_not_same_side hA hB hAB,
		have hAneqC : A ≠ C := point_neq_of_not_same_side hA hC hAC,
		rw ←collinear_iff_13 at h,
		obtain ⟨D,E, ⟨ hDℓ, hEℓ, hCE, hDCE, hCBE, hEAB, hCAE⟩⟩ :=
			auxiliary_point ℓ h hC hB hA (ne.symm hBneqC) (ne.symm hAneqC) (ne.symm hAneqB),
		obtain rfl | BnE := em(B = E),
			apply same_side.symm hCE,
		have hAnE : ¬ same_side ℓ A E,
		{
			intro hAsE,
			apply hAC,
			apply same_side.trans hAsE,
			apply same_side.symm hCE,
		},
		have hBsE : same_side ℓ B E,
		{
			rw collinear_iff_123 at hEAB,
			apply at_most_two_classes_of_noncollinear hA hB hEℓ,
			repeat {assumption},
		},
		apply same_side.trans hBsE,
		apply same_side.symm hCE,
	},
	apply at_most_two_classes_of_noncollinear hA; assumption,
end

theorem plane_separation (ℓ : Line Ω):  ∃ S1 S2 : set Ω,
        S1 ∩ S2 = ∅ ∧ S1 ∪ S2 ∪ ℓ = {P : Ω | true} ∧
        (∀ A B : Ω, (A ∉ ℓ) → (B ∉ ℓ) → 
			(( A ∈ S1 ∧ B ∈ S1) ∨ (A ∈ S2 ∧ B ∈ S2) ↔ pts (A⬝B) ∩ ℓ = ∅)) :=
begin
	have have_AB := same_side.at_least_two_classes ℓ,
	rcases have_AB with ⟨ C, D, hC, hD, H⟩,
	let S1 := {P : Ω | same_side ℓ P C},
	let S2 := {P : Ω | same_side ℓ P D},
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
				obtain rfl | hXD := em(x = D),
					apply same_side.refl,
					apply same_side.at_most_two_classes; assumption,
			}
		}
	},
	{
		introv hA hB,
		split,
		{
			rintros (h | h);
			{ -- same_side A B
				have h1 : same_side ℓ A B,
				{
					apply same_side.trans h.1,
					apply same_side.symm h.2,
				},
				cases h1; tauto,
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
					obtain rfl | hAD := em(A = D),
						apply same_side.refl,
						apply same_side.at_most_two_classes; assumption,
				},
				exact ⟨ hAD, same_side.trans (or.inr h) hAD⟩,
			}
		},
	},
end

end plane_separation
