import .hpdefs
import tactic

open_locale classical
noncomputable theory

open PreHilbertPlane
open Segment
open Ray

variables {Ω : Type*} [HilbertPlane Ω]

variables {A B C : Ω}
variables {ℓ r s : Line Ω}

lemma I11 (h: A ≠ B) : ∃ (ℓ : Line Ω), A ∈ ℓ ∧ B ∈ ℓ := exists_of_exists_unique (I1 h)

lemma I12
    (h: A ≠ B) (hAr: A ∈ r) (hBr : B ∈ r) (hAs : A ∈ s) (hBs : B ∈ s) : r = s :=
begin
    apply (unique_of_exists_unique (I1 h));
    tauto,
end

lemma there_are_two_points : ∃ A B : Ω, (A ≠ B) :=
begin
    rcases I3 with ⟨A, ⟨B, ⟨C, ⟨h1, h2⟩⟩⟩⟩,
    use [A, B],
    exact HilbertPlane.to_PreHilbertPlane,
end

def line_through_points_aux (A B : Ω) : {ℓ : Line Ω // A ∈ ℓ ∧ B ∈ ℓ} :=
begin
    apply classical.indefinite_description,
    by_cases h : A = B,
    {
        subst h,
        have h1 : ∃ C D : Ω, C ≠ D := there_are_two_points,
        obtain ⟨C, D, hC⟩ := h1,
        by_cases h1 : A = C,
        {
            subst h1,
            obtain ⟨ℓ, hAℓ, _⟩ := I11 hC,
            exact ⟨ℓ, hAℓ, hAℓ⟩,
        },
        {
            obtain ⟨ℓ, hAℓ, _⟩ := I11 h1,
            exact ⟨ℓ, hAℓ, hAℓ⟩,
        },
    },
    exact I11 h,
end


def line_through_points (A B : Ω) : Line Ω := (line_through_points_aux A B).1

lemma line_through_points_left {A B : Ω}: A ∈ line_through_points A B :=
(line_through_points_aux A B).2.1

lemma line_through_points_right {A B : Ω}: B ∈ (line_through_points A B) :=
(line_through_points_aux A B).2.2

lemma line_unique {A B : Ω} : A ≠ B → A ∈ ℓ → B ∈ ℓ → ℓ = line_through_points A B :=
λ ab al bl, I12 ab al bl line_through_points_left line_through_points_right

lemma distinct_lines_have_at_most_one_common_point
	(hrs: r ≠ s)
	(hAr: A ∈ r) (hAs: A ∈ s) (hBr: B ∈ r) (hBs: B ∈ s) :
	A = B :=
begin
    by_contradiction hc,
    apply hrs,
    apply I12 hc; assumption,
end

@[simp] lemma between_point_symmetric : (A * B * C) ↔ (C * B * A) :=
begin
    split; exact HilbertPlane.B11,
end

lemma segments_are_symmetric' : pts (A⬝B) ⊆ pts (B⬝A) :=
begin
    intros x hx,
    simp at *,
    rcases hx with (h | h | h); tauto,
end

@[simp] lemma segments_are_symmetric : pts (A⬝B) = B⬝A :=
begin
    apply set.subset.antisymm; exact segments_are_symmetric',
end

@[simp] lemma no_point_between_a_point (A x : Ω) : (A * x * A) ↔ false :=
begin
    split,
    {
        intro h,
        have H := HilbertPlane.B12 h,
        tauto,
    },
    tauto,
end

@[simp] lemma point_is_segment (A : Ω) : pts (A⬝A) = {A} :=
begin
    unfold pts,
    simp,
end

lemma exists_point_on_line (ℓ : Line Ω): ∃ A : Ω, A ∈ ℓ :=
begin
	have I2 := I2' ℓ,
	rcases I2 with ⟨ A, B, hAB, hAℓ, hBℓ⟩,
	exact ⟨A, hAℓ⟩,
end

lemma exists_point_not_on_line (ℓ : Line Ω): ∃ A : Ω, A ∉ ℓ :=
begin
    obtain ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩ := I3,
    specialize h ℓ,
    by_cases hA : A ∈ ℓ,
    {
        by_cases hB : B ∈ ℓ,
        {
            exact ⟨C, h ⟨hA, hB⟩⟩,
        },
        use B,
    },
    use A,
end

lemma collinear_order_irrelevant_v1 {A B C : Ω} : collinear A B C ↔
	collinear B A C:=
begin
	simp only [collinear_iff],
	tauto,
end

lemma collinear_order_irrelevant_v2 {A B C : Ω} : collinear A B C ↔
	collinear B C A:=
begin
	simp only [collinear_iff],
	tauto,
end
