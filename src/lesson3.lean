import tactic
import .lesson2

noncomputable theory
open_locale classical

open hilbertplane

section plane_separation

variable {Ω : HilbertPlane}
variables {A B C : Ω.Point}
variables {r s ℓ: Ω.Line}


definition same_side (ℓ : Ω.Line) (A B: Ω.Point) := (A ∈ ℓ ∧ B ∈ ℓ) ∨ ( (A#B) ∩ ℓ = ∅ )


lemma same_side.refl : same_side ℓ A A :=
begin
    by_cases hA : A ∈ ℓ,
    {
        unfold same_side,
        left,
        exact ⟨hA, hA⟩,
    },
    {
        unfold same_side,
        right,
        have g := point_is_segment A,
        rw g,
        rw set.singleton_inter_eq_empty,
        exact hA,
    }
end

lemma same_side.symm :
		same_side ℓ A B → same_side ℓ B A :=
begin
	unfold same_side,
	intro h,
	rw segments_are_symmetric,
	tauto,
end

lemma point_not_on_line_of_line_segment_not_intersect (h : (A#B) ∩ ℓ = ∅) : A ∉ ℓ ∧ B ∉ ℓ :=
begin
    rw [HilbertPlane.line_segment_def, set.eq_empty_iff_forall_not_mem] at h,
    dsimp,
    split,
    work_on_goal 0 {intro H, apply h A},
    work_on_goal 1 {intro H, apply h B},
    all_goals{
        dsimp,
        split,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true, true_or, eq_self_iff_true],
        assumption,
    },
end

lemma point_on_line_of_same_side (h : same_side ℓ A B) : A ∈ ℓ ↔ B ∈ ℓ :=
begin
    unfold same_side at h,
    cases h,
    tauto,
    {
        have hc := point_not_on_line_of_line_segment_not_intersect h,
        tauto,
    }
end
        
lemma same_side_trans_of_noncollinear (h : ¬ HilbertPlane.collinear A C B):
	same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
	intros hAB hBC,
    unfold same_side at *,
    by_cases hA : A ∈ ℓ,
    {
        left,
        have H1 := point_on_line_of_same_side hAB,
        have H2 := point_on_line_of_same_side hBC,
        split;
        {
            try {rw [←H2,←H1]},
            exact hA,
        }
    },
    replace hAB : (A#B) ∩ ℓ = ∅,
    {
        cases hAB;
        tauto,
    },
    have hB : B ∉ ℓ := (point_not_on_line_of_line_segment_not_intersect hAB).2,
    replace hBC : (B#C) ∩ ℓ = ∅,
    {
        cases hBC;
        tauto,
    },
    have hC : C ∉ ℓ := (point_not_on_line_of_line_segment_not_intersect hBC).2,  
    right,
	rw set.eq_empty_iff_forall_not_mem,
	rintro D ⟨ hDAC, hD⟩,
	have hAD : D ≠ A,
	{
		intro hc,
		rw hc at hD,
		exact hA hD,
	},
	have hCD : D ≠ C,
	{
		intro hc,
		rw hc at hD,
		exact hC hD,
	},
	simp only [set.mem_insert_iff,
		line_segment_simp, set.mem_singleton_iff,
		set.mem_union_eq, set.mem_set_of_eq,
		set.union_singleton] at hDAC,
	replace hDAC : A * D * C, by tauto,
	rcases (HilbertPlane.B4 h hA hC hB hD hDAC) with
		⟨ ⟨E, hE, h1⟩, hF⟩ | ⟨ ⟨E, ⟨ hE, h1⟩ ⟩, hF⟩,
	{
		have l_meets_AB : set.nonempty ((A#B) ∩ ℓ),
		{
			rw set.nonempty_def,
			use E,
			refine set.mem_sep _ hE,
			rw HilbertPlane.line_segment_def,
			right,
			exact h1,
		},
		replace l_meets_AB : ¬ (A#B) ∩ ℓ = ∅ := set.nmem_singleton_empty.mpr l_meets_AB,
        tauto,
	},
	have l_meets_CB : set.nonempty ((C#B) ∩ ℓ),
	{
		rw set.nonempty_def,
		use E,
		dsimp,
		split,
		{
			simp only [set.mem_insert_iff, line_segment_simp, set.mem_singleton_iff, set.mem_union_eq,
set.mem_set_of_eq, set.union_singleton],
			tauto,
		},
        apply hE,
	},
	replace l_meets_CB : ¬ (C#B) ∩ ℓ = ∅ := set.nmem_singleton_empty.mpr l_meets_CB,
	simp only [segments_are_symmetric] at l_meets_CB,
	tauto,
end

end plane_separation
