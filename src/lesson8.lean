import tactic
import .lesson6

noncomputable theory
open_locale classical

open PreHilbertPlane
open Triangle
open HilbertPlane

variables {Ω : Type*} [HilbertPlane Ω]
variables {A B C D E F : Ω}

namespace Segment

def is_congruent (S T : Segment Ω) : Prop := S ≅ T

@[simp] theorem congruence_is_equiv : equivalence (@is_congruent Ω _) :=
begin
    fconstructor,
    {
        intro A,
        change A ≅ A,
        exact C22 A,
    },
    split,
    {
        intros A B hAB,
        apply C21 A B _ hAB (C22 A),
    },
    {
        intros A B C hAB hAC,
        apply C21 B _ _ _ hAC,
        {
            apply C21 A B _ hAB (C22 A),
        },
    },
end

end Segment

