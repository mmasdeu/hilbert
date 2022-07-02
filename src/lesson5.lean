import tactic
import .lesson4

noncomputable theory
open_locale classical

open PreHilbertPlane
open HilbertPlane

section plane_separation

variables {Ω : Type*} [HilbertPlane Ω]

variables {A B C : Ω}
variables {ℓ r s : Line Ω}

@[simp] theorem same_side_is_equiv : equivalence (same_side ℓ) :=
	⟨λ A, same_side.refl, λ A B, same_side.symm, λ A B C, same_side.trans⟩

lemma same_side.at_least_two_classes (ℓ : Line Ω):
      ∃ A B : Ω, (A ∉ ℓ) ∧ (B ∉ ℓ) ∧ (¬ same_side ℓ A B) :=
begin
	rcases exists_point_not_on_line ℓ with ⟨ A, hAℓ⟩,
	rcases exists_point_on_line ℓ with ⟨ D, hDℓ⟩,
	obtain rfl | hAD := em(A = D), tauto,
	have h2 : ∃ B : Ω, A * D * B := B2 hAD,
	cases h2 with B hADB,
	use [A, B],
	repeat {split},
		exact hAℓ,
		exact λ hBℓ, hAℓ (between_points_share_line_v2 hBℓ hDℓ (HilbertPlane.B11 hADB)),
	{
        rintro (⟨ hA, hB⟩ | H),
            exact hAℓ hA,
		have hD : D ∈ pts (A⬝B) ∩ ℓ,
		{
			simp only [segments_are_symmetric],
			exact ⟨ or.inr (or.inr (B11 hADB)), hDℓ⟩,
		},
		have hD' : pts (A⬝B) ∩ ℓ ≠ ∅ := set.nonempty.ne_empty (set.nonempty_of_mem hD),
		tauto,
	}
end

end plane_separation