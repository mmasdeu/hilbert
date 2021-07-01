import tactic
import .lesson6

noncomputable theory
open_locale classical

open PreHilbertPlane
open HilbertPlane

section plane_separation

variables {Ω : Type*} [HilbertPlane Ω]

variables {ℓ r s : Line Ω}
variables {B C D: {x : Ω // x ∈ ℓ}}
variables {A : Ω}

--@[simp] def same_side_of_line (hAℓ : A ∈ ℓ) := λ x y,
--    ((x : Ω) = y) ∨ (¬ (A : Ω) ∈ (x : Ω) ⬝ y)
@[simp] def same_side_of_line (hAℓ : A ∈ ℓ) (B C : {x : Ω // x ∈ ℓ}) := 
    ((B : Ω) = C) ∨ (¬ (A : Ω) ∈ (B : Ω) ⬝ C)

lemma same_side_of_line.refl (hAℓ : A ∈ ℓ) : same_side_of_line hAℓ B B :=
begin
    simp,
end

lemma same_side_of_line.symm (hAℓ : A ∈ ℓ) :
    same_side_of_line hAℓ B C →  same_side_of_line hAℓ C B :=
begin
    simp only [Segment.mem_pts, and_imp, same_side_of_line, mem_coe_to_mem, between_point_symmetric] at *,
    tauto,
end

lemma same_side_line_vs_plane (hr : r ≠ ℓ) (hAℓ : A ∈ ℓ) (hAr : A ∈ r) :
    same_side_of_line hAℓ B C ↔ same_side r B C :=
begin
    obtain rfl | hBC := em(B = C), by exact ⟨ λ h, same_side.refl, λ h, same_side_of_line.refl _⟩,
    cases B with B hB,
    cases C with C hC,
    split,
    {
        intro h,
        unfold same_side_of_line at h,
        unfold same_side,
        rcases h with ⟨h1,h2⟩ | hBAC,
        {
            tauto,
        },
        by_cases hh : (B : Ω) ∈ r ∧ (C : Ω) ∈ r, left, assumption,
        replace hh : (B : Ω) ∉ r ∨ (C : Ω) ∉ r, tauto,
        right,
        unfold pts,
        ext1,
        dsimp,
        rw iff_false,
        push_neg,
        intros H hx,
        rw mem_coe_to_mem at hx,
        rcases H with (H|H|H),
        any_goals {subst H, simp only at hx, exfalso},
        work_on_goal 2 {have hxℓ : x ∈ ℓ := between_points_share_line hB hC H},
        work_on_goal 0 {obtain rfl | ht := em(A = B)},
        work_on_goal 2 {obtain rfl | ht := em(A = C)},
        work_on_goal 4 {obtain rfl | ht := em(A = x)},
        any_goals
        {
                apply hBAC,
                norm_num,
                try {tauto},
        },
        all_goals
        {
            exfalso,
            apply hr,
            apply equal_lines_of_contain_two_points ht,
            try {repeat {assumption}},
        },
    },
    {
        intro H,
        unfold same_side at H,
        rcases H with (⟨H1,H2⟩|H),
        simp,
        repeat{split},
        repeat {assumption},
        {
            right,
            push_neg,
            exfalso,
            apply hr,
            norm_num at hBC,
            apply equal_lines_of_contain_two_points hBC,
            try {repeat {assumption}},
        },
        {
            unfold same_side_of_line,
            right,
            intro hABC,
            rw set.eq_empty_iff_forall_not_mem at H,
            specialize H A,
            apply H,
            simp only [true_and, set.mem_inter_eq, true_or, eq_self_iff_true,
            mem_coe_to_mem, segments_are_symmetric, Segment.mem_coe_to_mem_pts],
            split,
            {
                finish,
            },
            assumption,
        },
    },
end

lemma same_side_of_line.trans (hAℓ : A ∈ ℓ) :
    same_side_of_line hAℓ B C → same_side_of_line hAℓ C D →  same_side_of_line hAℓ B D :=
begin
    obtain ⟨E, hE⟩ := exists_point_not_on_line ℓ,
    let r := line_through_points A E,
    have hEr : E ∈ r := line_through_points_right,
    have hAr : A ∈ r := line_through_points_left,
    obtain rfl | hr := em(r = ℓ), by tauto,
    repeat {rw same_side_line_vs_plane hr},
    {
        exact same_side.trans,
    },
    repeat {assumption},
end

@[simp] theorem same_side_of_line_equiv (hAℓ : A ∈ ℓ) :
(equivalence (same_side_of_line hAℓ))
:= ⟨λ x, same_side_of_line.refl hAℓ,
    λ x y hxy, same_side_of_line.symm hAℓ hxy,
    λ x y z hxy hyz, same_side_of_line.trans hAℓ hxy hyz⟩

lemma at_least_two_classes_line (hAℓ : A ∈ ℓ) : ∃ B C : {x : Ω // x ∈ ℓ}, ¬ same_side_of_line hAℓ B C :=
begin
    sorry
end

lemma at_most_two_classes_line (hAℓ : A ∈ ℓ) : ¬ same_side_of_line hAℓ B C →
     ¬ same_side_of_line hAℓ B D → same_side_of_line hAℓ C D :=
begin
    sorry
end

end plane_separation