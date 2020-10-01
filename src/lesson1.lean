import .hpdefs
import tactic

open_locale classical

open hilbertplane

section hilbertplane

variable {Ω : HilbertPlane}
variables {A B C : Ω.Point}
variables {ℓ r s : Ω.Line}

lemma I12
    (h: A ≠ B) (hAr: A ∈ r) (hBr : B ∈ r) (hAs : A ∈ s) (hBs : B ∈ s) : r = s :=
begin
    apply unique_of_exists_unique (HilbertPlane.I1 h);
    tauto,
end

lemma there_are_two_points : ∃ A B : Ω.Point, (A ≠ B) :=
begin
    cases Ω.I3 with A BCh,
    cases BCh with B Ch,
    cases Ch with C h,
    cases h with hh,
    existsi A,
    existsi B,
    exact hh,
end

lemma distinct_lines_have_at_most_one_common_point
	(hrs: r ≠ s)
	(hAr: A ∈ r) (hAs: A ∈ s) (hBr: B ∈ r) (hBs: B ∈ s) :
	A = B :=
begin
    suffices not_A_eq_B : ¬ (A ≠ B),
    cc,
    intro h,
    suffices Q : r = s,
    contradiction,
    exact I12 h hAr hBr hAs hBs,
end

lemma endpoints_are_in_segment : A ∈ (A # B) ∧ B ∈ (A # B) :=
begin
    split; {
    unfold HilbertPlane.line_segment_def,
    finish,
    }
end

@[simp] lemma segments_are_symmetric : (A # B) = (B # A) :=
begin
    suffices : ∀ A B : Ω.Point, (A # B) ⊆ (B # A),
    {
        intros,
        apply set.subset.antisymm;
        solve_by_elim
    },
    intros A B,
    intros x hx,
    rw HilbertPlane.line_segment_def at hx,
    rcases hx with ⟨hA, hB, h2⟩,
    {
        rw HilbertPlane.line_segment_def,
        norm_num,
    },
    {
        rw HilbertPlane.line_segment_def,
        norm_num,
        tauto,
    },
    {
        rw HilbertPlane.line_segment_def,
        norm_num,
        right,
        simp only [set.mem_set_of_eq] at hx,
        apply HilbertPlane.B11,
        exact hx,
    }
end

lemma no_point_between_a_point (A : Ω.Point) : {C : Ω.Point | A * C * A} = ∅ :=
begin
    ext C,
    suffices : ¬ A * C* A, by simpa,
    intro h,
    have g := HilbertPlane.B12 h,
    apply g.2.1,
    refl,
end

lemma point_is_segment (A : Ω.Point) : (A # A) = {A} :=
begin
    unfold HilbertPlane.line_segment_def,
    apply set.subset.antisymm,
    {   
        simp only [no_point_between_a_point,
            insert_emptyc_eq, set.mem_singleton, 
            set.singleton_union, set.pair_eq_singleton],
    },
    apply set.subset_union_of_subset_left
        (set.subset_insert A {A}) {C : HilbertPlane.Point | A * C*A},
end

lemma exists_point_on_line (ℓ : Ω.Line): ∃ A : Ω.Point, A ∈ ℓ :=
begin
	have I2 := HilbertPlane.I2 ℓ,
	rcases I2 with ⟨ A, B, hAB, hAℓ, hBℓ⟩,
	use A,
	exact hAℓ,
end

lemma exists_point_not_on_line (ℓ : Ω.Line): ∃ A : Ω.Point, A ∉ ℓ :=
begin
    have h := HilbertPlane.I3,
    rcases h with ⟨A, B, C, h1⟩,
    rcases h1 with ⟨hAB, hAC, hBC, h4⟩,
    have H := h4 ℓ,
    by_cases hA : A ∈ ℓ,
    by_cases hB : B ∈ ℓ,
    {
    existsi C,
    finish,
    },
    existsi B,
    finish,
    existsi A,
    finish,
end

lemma collinear_order_irrelevant_v1 {A B C : Ω.Point} : HilbertPlane.collinear A B C ↔
	HilbertPlane.collinear B A C:=
begin
	simp only [collinear_iff],
	tauto,
end

lemma collinear_order_irrelevant_v2 {A B C : Ω.Point} : HilbertPlane.collinear A B C ↔
	HilbertPlane.collinear B C A:=
begin
	simp only [collinear_iff],
	tauto,
end

@[simp] lemma line_segment_simp {A B D : Ω.Point}: D ∈ HilbertPlane.line_segment A B ↔ D ∈ {A} ∪ {B} ∪ {X | A * X * B} :=
begin
	simp only [HilbertPlane.line_segment_def, set.mem_insert_iff, set.mem_singleton_iff, set.mem_union_eq, set.mem_set_of_eq,
 set.union_singleton],
end

end hilbertplane