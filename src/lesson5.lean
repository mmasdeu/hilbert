import tactic
import .lesson4

noncomputable theory
open_locale classical

open hilbertplane

section plane_separation

variable {Ω : HilbertPlane}
variables {A B C : Ω.Point}
variables {r s ℓ: Ω.Line}


@[simp] theorem same_side_is_equiv : equivalence (same_side ℓ) :=
begin
    repeat {split},
    {
        intro A,
        exact same_side.refl,
    },
    {
        intros A B,
        exact same_side.symm,
    },
    {
        intros A B C,
        exact same_side.trans,
    }
end

lemma same_side.at_least_two_classes (ℓ : Ω.Line):
      ∃ A B : Ω.Point, (A ∉ ℓ) ∧ (B ∉ ℓ) ∧ (¬ same_side ℓ A B) :=
begin
	rcases exists_point_not_on_line ℓ with ⟨ A, hAℓ⟩,
	rcases exists_point_on_line ℓ with ⟨ D, hDℓ⟩,
	have h2 : ∃ B : Ω.Point, A * D * B := HilbertPlane.B2,
	cases h2 with B hADB,
	use [A, B],
	repeat {split},
	exact hAℓ,
	{
		intro hBℓ,
		replace hADB := HilbertPlane.B11 hADB,
		apply hAℓ (between_points_share_line_v2 hBℓ hDℓ hADB),
	},
	{
        rintro (⟨ hA, hB⟩ | H),
        {
            exact hAℓ hA,
        },
		rw HilbertPlane.line_segment_def at H,
		have hD : D ∈ (HilbertPlane.line_segment A B) ∩ ℓ,
		{
			split,
			{
				rw HilbertPlane.line_segment_def,
				right,
				exact hADB,
			},
	        exact_mod_cast hDℓ,
		},
		have hD' : (A # B) ∩ ℓ ≠ ∅ := set.nonempty.ne_empty (set.nonempty_of_mem hD),
		rw HilbertPlane.line_segment_def at hD',
		tauto,
	}
end

end plane_separation