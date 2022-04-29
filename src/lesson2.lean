import tactic
import .lesson1

noncomputable theory
open_locale classical
open PreHilbertPlane

variables {Ω : Type*} [HilbertPlane Ω]

variables {A B C D : Ω}
variables {ℓ r s : Line Ω}

lemma point_in_line_difference (h : r ≠ s) :
	∃ A, A ∈ r ∧ A ∉ s :=
begin
	have AB : ∃ A B , A ≠ B ∧ A ∈ r ∧ B ∈ r := I2 r,
	rcases AB with ⟨ A, B, ⟨ hAB, hAr, hBr⟩⟩,
	have h1 : A ∉ s ∨ B ∉ s,
	{
		by_contradiction hcontra,
		apply hAB,
		apply distinct_lines_have_at_most_one_common_point h;
		tauto,
	},
	cases h1 with h_isA h_isB,
	work_on_goal 1 {use A},
	work_on_goal 2 {use B},
	repeat {tauto},
end

lemma equal_lines_of_contain_two_points
	(hAB: A ≠ B)
	(hAr: A ∈ r) (hAs: A ∈ s) (hBr: B ∈ r) (hBs: B ∈ s) :
	r = s :=
begin
	by_contradiction hcontra,
	apply hAB,
	apply distinct_lines_have_at_most_one_common_point; assumption,
end

lemma between_points_share_line (hAr : A ∈ r) (hCr : C ∈ r) : 
	(A * B * C) → B ∈ r :=
begin
	intro h,
	have H := HilbertPlane.B12 h,
	rw collinear at H,
	obtain ⟨hAB, hAC, hBC, ⟨ ℓ, ⟨ hAℓ, hBℓ, hCℓ⟩⟩⟩ := H,
	suffices : r = ℓ, by rwa this,
	apply equal_lines_of_contain_two_points hAC; assumption,
end

lemma between_points_share_line_v2 (hAr : A ∈ r) (hBr : B ∈ r) : 
	(A * B * C) → C ∈ r :=
begin
	intro h,
	have H := HilbertPlane.B12 h,
	rw collinear at H,
	obtain ⟨hAB, hAC, hBC, ⟨ ℓ, ⟨ hAℓ, hBℓ, hCℓ⟩⟩⟩ := H,
	suffices : r = ℓ, by rwa this,
	apply equal_lines_of_contain_two_points hAB; assumption,
end

lemma collinear_of_collinear_collinear (hAB : A ≠ B) (hABC : collinear A B C) (hABD : collinear A B D) :
collinear A C D :=
begin
	obtain ⟨r, hr⟩ := hABC,
	obtain ⟨s, hs⟩ := hABD,
	have hkey : r = s := equal_lines_of_contain_two_points hAB hr.1 hs.1 hr.2.1 hs.2.1,
	subst hkey,
	use r,
	tauto,
end