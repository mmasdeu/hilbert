import .hpdefs

open_locale classical
noncomputable theory

open PreHilbertPlane HilbertPlane Segment Ray

variables {Ω : Type*} [HilbertPlane Ω]

variables {A B C : Ω}
variables {ℓ r s : Line Ω}

lemma line_through_left {A B : Ω}: A ∈ line_through A B :=
(line_through_aux A B).2.1

lemma line_through_right {A B : Ω}: B ∈ (line_through A B) :=
(line_through_aux A B).2.2

lemma line_unique {A B : Ω} : A ≠ B → A ∈ ℓ → B ∈ ℓ → ℓ = line_through A B :=
λ ab al bl, I12 ab al bl line_through_left line_through_right

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
    tauto,
end

lemma segments_are_symmetric : pts (A⬝B) = B⬝A :=
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
	have I2 := I2 ℓ,
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
