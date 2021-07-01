import tactic
import .lesson8

noncomputable theory
open_locale classical

open PreHilbertPlane
open HilbertPlane
open HilbertPlane.Triangle

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
            {
                split,
                {
                    sorry
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
    let ℓ := line_through_points A' C',
    have hApℓ: A' ∈ ℓ := line_through_points_left,
    have hCpℓ: C' ∈ ℓ := line_through_points_right,
    have hBpℓ: ¬ B' ∈ ℓ,
    {
        intro H,
        apply h',
        use ℓ, tauto,
    },
    have H := point_on_other_side_of_line ℓ B' hBpℓ,
    rcases H with ⟨E, hEℓ, hBpE⟩,
    have hnc : ¬ collinear E A' C',
    {
        sorry
    },
    have hT2 : (∟ B' A' C').nondegenerate,
    {
        sorry
    },
    -- Let B₀ be the point defining the angle transported to the ray A'=>C'.
    let B₀ := C4 (∟ B' A' C') (A'=>C') E hT2 hnc hACp,

    sorry
end

/- Proposition 10.1 (SSS) of Hartshorne
   If two triangles have their respective sides equal,
   then they are congruent.
-/
theorem triangle_SSS' (A B C A' B' C' : Ω) : 
 (▵ A B C).nondegenerate → (▵ A' B' C').nondegenerate →
    (A⬝B ≅ A'⬝B') → (A⬝C ≅ A'⬝C') → (B⬝C ≅ B'⬝C') → 
    (∟ B A C ≃ ∟ B' A' C') ∧ (∟ A C B ≃ ∟ A' C' B') ∧ (∟ C B A ≃ ∟ C' B' A') :=
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
    let ℓ := line_through_points A' C',
    have hApℓ: A' ∈ ℓ, exact line_through_points_left,
    have hCpℓ: C' ∈ ℓ, exact line_through_points_right,
    have hBpℓ: ¬ B' ∈ ℓ,
    {
        intro h,
        apply hT',
        use ℓ, tauto,
    },

    have H := point_on_other_side_of_line ℓ B' hBpℓ,
    rcases H with ⟨E, hEℓ, hBpE⟩,
    have hnc : ¬ collinear E A' C',
    {
        sorry
    },
    have hT2 : (∟ B' A' C').nondegenerate,
    {
        sorry
    },
    -- Let B₀ be the point defining the angle transported to the ray A'=>C'.
    let B₀ := HilbertPlane.C4 (∟ B' A' C') (A'=>C') E hT2 hnc hACp,
    --have hB₀ := HilbertPlane.C4spec (∟ B' A' C') (A'=>C') E hT2 hnc hACp,
    have hBpp : ∃ B'' : Ω, (∟ C' A' B'') ≃ (∟ B A C) ∧ A'⬝B'' ≅ A⬝B,
    {
        sorry
    },

    --repeat {split},
    --repeat {assumption},
    sorry
end

theorem triangle_SSS (T T' : Triangle Ω) : 
(T.A⬝T.B ≅ T'.A⬝T'.B) → (T.A⬝T.C ≅ T'.A⬝T'.C) → (T.B⬝T.C ≅ T'.B⬝T'.C) → congruent_triangles T T' :=
begin
    intros hAB hAC hBC,
    /- (using C4 and C1)
     Construct an angle ∟ C' A' B'' on the other side of A'=>C' from B'
     that is congruent to ∟ BAC and at the same time A'B''
     is congruent to AB.
    -/
    let AB := T.A⬝T.B,
    have E := HilbertPlane.C4 (∟ T.B T.A T.C) (T'.A=>T'.C),

    unfold congruent_triangles,
    --repeat {split},
    --repeat {assumption},
    sorry
end