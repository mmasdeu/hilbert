import tactic
import .lesson8

noncomputable theory
open_locale classical

open PreHilbertPlane HilbertPlane Triangle

variables {Ω : Type*} [HilbertPlane Ω]
variables {A B C D E F : Ω}

lemma origin_on_ray : A ∈ pts (A=>B) :=
begin
    rw Ray.mem_pts,
    left,
    refl,
end
/- Any point on a ray different from its origin defines the same ray-/
lemma point_on_ray_gives_same_ray : A ≠ E → B ≠ E → E ∈ pts (A=>B) → pts (A=>B) = pts (A=>E) :=
begin
    intros hAE hBE hE,
    unfold pts,
    ext1,
    split,
    {
        dsimp,
        intro h,
        cases h with h0 h1,
        {
            subst h0,
            dsimp,
            exact origin_on_ray,
        },
        {
            dsimp at h1,
            obtain rfl | hAB := em(A = B), finish,
            right,
            dsimp,
            rw Ray.mem_pts at hE,
            dsimp at hE,
            rcases hE with (hE | hE), tauto,
            cases h1,
            cases hE,
            have hco : collinear ({A, B, x, E} : set Ω),
            {
                have : {A, B, x, E} = ({A, x, B} : set Ω).union({A, E, B}),
                {
                    ext,
                    split,
                    {
                        intro h,
                        rcases h with h|h|h|h,
                        {
                            subst h, left, simp,
                        },
                        {
                            subst h, left, simp,
                        },
                        {
                            subst h, left, simp,
                        },
                        {
                            simp at h, subst h, right, simp,
                        },
                    },
                    {
                        intro h,
                        cases h;
                        finish,
                    }
                },
                rw this,
                apply collinear_union {A, x, B} {A, E, B} hAB,
                simpa using h1_left,
                simpa using hE_left,
                all_goals {finish},
            },
            {
                split,
                {
                    simp,
                    apply collinear_subset _ {A, B, x, E} _ hco,
                    intros y hy, finish,
                },
                {
                    sorry
                },
            },
        },
    },
    {
        sorry
    }
end

/- Given a line and a point, there is a point on the other side -/
lemma point_on_other_side_of_line (ℓ : Line Ω) (A : Ω) :
    ¬ A ∈ ℓ → ∃ B : Ω, ¬ B ∈ ℓ ∧ ¬ same_side ℓ A B :=
begin
    intro hA,
    rcases (same_side.at_least_two_classes ℓ) with ⟨X, Y, ⟨hX, hY, H⟩⟩,
    by_cases h1 : same_side ℓ A X,
    {
        use Y,
        split, assumption,
        intro h2,
        have h3 : same_side ℓ X Y,
        {
            rw same_side.symm_iff at h1,
            apply same_side.trans h1 h2,
        },
        exact H h3,
    },
    {
        use X,
        exact ⟨hX, h1⟩,
    }
end

/- (using C4 and C1)
Construct an angle ∟ C' A' B'' on the other side of A'=>C' from B'
that is congruent to ∟ BAC and at the same time A'B''
is congruent to AB.
-/
lemma transport_angle_to_other_ray ( A B C A' B' C' : Ω)
    (h: (▵ A B C).nondegenerate) (h': (▵ A' B' C').nondegenerate) :
    ∃ B'' : Ω, (∟ C' A' B'') ≃ (∟ B A C) ∧ A'⬝B'' ≅ A⬝B ∧ (pts (A=>B) = pts (A'=>B'')) :=
begin
    have hACp : A' ≠ C',
    {
        sorry
    },
    let ℓ := line_through A' C',
    have hApℓ: A' ∈ ℓ := line_through_left,
    have hCpℓ: C' ∈ ℓ := line_through_right,
    have hBpℓ: ¬ B' ∈ ℓ,
    {
        intro H,
        apply h',
        use ℓ, tauto,
    },
    have H := point_on_other_side_of_line ℓ B' hBpℓ,
    rcases H with ⟨E, hEℓ, hBpE⟩,
    have hnc : ¬ collinear_triple E A' C',
    {
        sorry
    },
    have hT2 : (∟ B' A' C').nondegenerate,
    {
        sorry
    },
    -- Transport the angle to the ray A'=>C'.
    have HH := C4 (∟ B' A' C') (A'=>C') E hT2 hnc,
    obtain ⟨ℓ, ⟨Q, ⟨hQ1, hQ2, hQ3, hQ4⟩⟩, huniq⟩ := HH,
    simp only at hQ3,

    sorry
end

lemma segment_union (A B C : Ω) (h : A * B * C) :
pts (A ⬝ C) = (pts (A ⬝ B)).union( pts (B ⬝ C)) :=
begin
    ext,
    split,
    {
        intro h,
        simp only [_root_.mem_pts, Segment.mem_pts] at h,
        rcases h with h|h|h,
        {
            subst h,
            left,
            simp,
        },
        {
            subst h,
            right,
            simp,
        },
        {
            by_cases h1 : A * x * B,
            {
                left,
                simp [h1],
            },
            {
                right,
                simp,
                right, right,
                
                sorry
            }
        }
    },
    {
        intro h,
        rcases h with h|h,
        {
            simp at h ⊢,
            rcases h with h|h|h,
            {tauto},
            {
                subst h,
                tauto,
            },
            {
                right, right,
                
                sorry
            }
        },
        sorry
    }
end

/- Proposition 10.1 (SSS) of Hartshorne
If two triangles have their respective sides equal,
then they are congruent.
-/
theorem triangle_SSS' {A B C A' B' C' : Ω} : 
(▵ A B C).nondegenerate → (▵ A' B' C').nondegenerate →
(A⬝B ≅ A'⬝B') → (A⬝C ≅ A'⬝C') → (B⬝C ≅ B'⬝C') → 
(▵ A B C).is_similar(▵ A' B' C') :=
begin
    intros hT hT' hAB hAC hBC,
    /- (using C4 and C1)
    Construct an angle ∟ C' A' B'' on the other side of A'=>C' from B'
    that is congruent to ∟ BAC and at the same time A'B''
    is congruent to AB.
    -/
    have hACp : A' ≠ C',
    {
        sorry
    },
    let ℓ := line_through A' C',
    have hApℓ: A' ∈ ℓ, exact line_through_left,
    have hCpℓ: C' ∈ ℓ, exact line_through_right,
    have hBpℓ: ¬ B' ∈ ℓ,
    {
        intro h,
        apply hT',
        use ℓ, tauto,
    },

    have H := point_on_other_side_of_line ℓ B' hBpℓ,
    rcases H with ⟨E, hEℓ, hBpE⟩,
    have hnc : ¬ collinear_triple E A' C',
    {
        sorry
    },
    have hT2 : (∟ B' A' C').nondegenerate,
    {
        sorry
    },
    -- Let B₀ be the point defining the angle transported to the ray A'=>C'.
    obtain ⟨B₀,h⟩ := HilbertPlane.C4 (∟ B' A' C') (A'=>C') E hT2 hnc,
    have hBpp : ∃ B'' : Ω, (∟ C' A' B'') ≃ (∟ B A C) ∧ A'⬝B'' ≅ A⬝B,
    {
        sorry
    },

    --repeat {split},
    --repeat {assumption},
    sorry
end

theorem triangle_SSS (T T' : Triangle Ω) : 
(T.A⬝T.B ≅ T'.A⬝T'.B) → (T.A⬝T.C ≅ T'.A⬝T'.C) → (T.B⬝T.C ≅ T'.B⬝T'.C) → T.is_congruent T' :=
begin
    intros hAB hAC hBC,
    rw is_congruent,
    suffices : T.is_similar T', by finish,
    apply triangle_SSS' _ _ hAB hAC hBC;
    sorry
end

lemma similar_of_congruent (T R : Triangle Ω) (h : is_congruent T R) :
is_similar T R :=
begin
	sorry
end
