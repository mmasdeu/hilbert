import tactic
import data.set
import .lesson2

noncomputable theory
open_locale classical

open PreHilbertPlane
open HilbertPlane
open set

section plane_separation

variables {Ω : Type*} [HilbertPlane Ω]

variables {A B C : Ω}
variables {ℓ r s : Line Ω}


lemma same_side.refl : same_side ℓ A A :=
begin
    by_cases hA : A ∈ ℓ,
        exact or.inl ⟨hA, hA⟩,
    {
        unfold same_side,
        rw [point_is_segment A, set.singleton_inter_eq_empty],
        exact or.inr hA,
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

lemma same_side.symm_iff :
		same_side ℓ A B ↔ same_side ℓ B A :=
begin
    split;
    apply same_side.symm,
end


lemma point_not_on_line_of_line_segment_not_intersect_left (h : (pts (A⬝B) ∩ ℓ) = ∅) : A ∉ ℓ :=
begin
    intro H,
    rw [set.eq_empty_iff_forall_not_mem] at h,
    apply h A,
    simpa,
end

lemma point_not_on_line_of_line_segment_not_intersect_right (h : pts (A⬝B) ∩ ℓ = ∅) : B ∉ ℓ :=
begin
    rw segments_are_symmetric at h,
    exact point_not_on_line_of_line_segment_not_intersect_left h,
end

lemma point_on_line_of_same_side (h : same_side ℓ A B) : A ∈ ℓ ↔ B ∈ ℓ :=
begin
    unfold same_side at h,
    cases h,
    tauto,
    {
        have hcl := point_not_on_line_of_line_segment_not_intersect_left h,
        have hcr := point_not_on_line_of_line_segment_not_intersect_right h,
        tauto,
    }
end
        
lemma same_side_trans_of_noncollinear (h : ¬ collinear_triple A C B):
	same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
	intros hAB hBC,
    unfold same_side at *,
    have H1 := point_on_line_of_same_side hAB,
    have H2 := point_on_line_of_same_side hBC,
    by_cases hA : A ∈ ℓ, by exact or.inl ⟨hA, H2.1 (H1.1 hA)⟩,
    replace hAB : pts (A⬝B) ∩ ℓ = ∅, tauto,
    have hB : B ∉ ℓ := point_not_on_line_of_line_segment_not_intersect_right hAB,
    replace hBC : pts (B⬝C) ∩ ℓ = ∅, tauto,
    have hC : C ∉ ℓ := point_not_on_line_of_line_segment_not_intersect_right hBC,
    right,
	rw set.eq_empty_iff_forall_not_mem,
    -- Now the main part of the proof. AC ∩ ℓ = ∅
    -- So let D be a point in AC and in ℓ. We'll prove False.
	rintro D ⟨ hDAC1, hD⟩,
    obtain rfl | hAD := em(D = A), exact hA hD, -- D ≠ A
    obtain rfl | hCD := em(D = C), exact hC hD, -- D ≠ C
    simp [segments_are_symmetric] at hDAC1,
    have hDAC : A * D * C, by tauto,
	rcases (B4 h hA hC hB hD hDAC) with
		⟨ ⟨E, hE, h1⟩, hF⟩ | ⟨ ⟨E, ⟨ hE, h1⟩ ⟩, hF⟩,
	{
        suffices l_meets_AB : (pts (A⬝B) ∩ ℓ ≠ ∅), by tauto,
        apply set.nmem_singleton_empty.mpr,
        exact ⟨E, ⟨or.inr (or.inr h1), hE⟩⟩,
	},
    {
        suffices l_meets_CB : pts (B⬝C) ∩ ℓ ≠ ∅, by tauto,
        apply set.nmem_singleton_empty.mpr,
        rw [segments_are_symmetric, set.nonempty_def],
        exact ⟨E, ⟨or.inr (or.inr h1), hE⟩⟩,
    },
end

end plane_separation
