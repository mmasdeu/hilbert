import .incidenceplane

noncomputable theory
open_locale classical
open set function

open IncidencePlane


class NeutralPlane (Point : Type*) extends IncidencePlane Point :=
	-- Ruler postulate, divided into 3 statements
	(ruler (ℓ : Line) : Point → ℝ)
	(ruler_dist (P Q : Point) : distance P Q = abs (ruler (line_through P Q) P - ruler (line_through P Q) Q))
	(ruler_bij (ℓ : Line) : set.bij_on (ruler ℓ) (ℓ : set Point) univ)

	-- Plane separation postulate
	(half_planes (ℓ : Line) : set Point × set Point)
	(half_planes_def_1 (ℓ : Line) (Q : Point) : (half_planes ℓ).1 = half_plane ℓ Q ↔ Q ∈ (half_planes ℓ).1)
	(half_planes_def_2 (ℓ : Line) (Q : Point) : (half_planes ℓ).2 = half_plane ℓ Q ↔ Q ∈ (half_planes ℓ).2)
	(convex_half_plane (ℓ : Line) : is_convex (half_planes ℓ).1 ∧ is_convex (half_planes ℓ).2)
	(partition (ℓ : Line) : (half_planes ℓ).1 ∪ (half_planes ℓ).2 ∪ ℓ = univ)
	(disjoint (ℓ : Line): (half_planes ℓ).1 ∩ (half_planes ℓ).2 = ∅)
	(disjoint' (ℓ : Line) : (half_planes ℓ).1 ∩ ℓ = ∅ ∧ (half_planes ℓ).2 ∩ ℓ = ∅)
	(plane_separation (ℓ : Line) (P Q : Point) : P ∈ (half_planes ℓ).1 → Q ∈ (half_planes ℓ).2 →
	pts(P⬝Q) ∩ ℓ ≠ ∅)

	(angle_measure : Angle Point → ℝ) -- angle measure

  -- Protractor postulate
	(angle_nonneg (α : Angle Point) : 0 ≤ angle_measure α)
	(angle_bounded (α : Angle Point) : angle_measure α < 180)
	(angle_well_def (α β: Angle Point) : α ≈ β → angle_measure α = angle_measure β)
	(angle_nondegenerate (α : Angle Point) : α.O => α.A ≈ α.O => α.B ↔ angle_measure α = 0)
	
	-- Angle construction
	(angle_construction {t : ℝ} (h₀ : 0 < t) (h : t < 180) (r : Ray Point) {E : Point}
	(hE : E ∉ (r.line))	: Point)
	(angle_construction_def' {t : ℝ} (h₀ : 0 < t) (h : t < 180) (r : Ray Point) {E : Point}
	(hE : E ∉ (r.line)) : angle_construction h₀ h r hE ∈ half_plane (r.line) E)
	(angle_construction_def {t : ℝ} (h₀ : 0 < t) (h : t < 180) (r : Ray Point) {E : Point}
	(hE : E ∉ (r.line)) : angle_measure (∟ r.target r.origin (angle_construction h₀ h r hE)) = t)
	(angle_construction_unique {t : ℝ} (h₀ : 0 < t) (h : t < 180) (r : Ray Point) {E : Point}
	(hE : E ∉ (r.line))	(B : Point) (hB : B ∈ half_plane (r.line) E):
	angle_measure (∟ r.target r.origin B) = t → r.origin => B ≈ r.origin => angle_construction h₀ h r hE)

	-- Angle addition
	(angle_addition (A B C D : Point) (h : Ray.between (A=>B) (A=>D) (A=>C)) :
	angle_measure (∟B A D) + angle_measure (∟ D A C) = angle_measure (∟ B A C) )

	-- SAS
	(SAS (S T : Triangle Point) (hAB : (S.A⬝S.B) ≅ (T.A⬝T.B)) (hBC : (S.B⬝S.C) ≅ (T.B⬝T.C))
	(hABC : angle_measure (∟ T.A T.B T.C) =  angle_measure (∟ S.A S.B S.C)) : 
	(S.A⬝S.C) ≅ (T.A⬝T.C) ∧ angle_measure (∟ T.B T.C T.A) = angle_measure (∟ S.B S.C S.A)
	∧ angle_measure (∟ T.C T.A T.B) =  angle_measure (∟ S.C S.A S.B))

namespace IncidencePlane
variables {Ω : Type*} [NeutralPlane Ω]

namespace Angle

def m (α : Angle Ω) := NeutralPlane.angle_measure α
@[simp] def congruent (α β : Angle Ω) := α.m = β.m
infix `≅`:100 := congruent

def is_acute (α : Angle Ω) := α.m < 90
def is_obtuse (α : Angle Ω) := 90 < α.m
def is_right (α : Angle Ω) := α.m = 90

@[simp] def linear_pair (α β : Angle Ω) := α.O = β.O ∧ (α.O=>α.B) ≈ (α.O=>β.A) ∧ α.A * α.O * β.B
@[simp] def supplementary (α β : Angle Ω) := α.m + β.m = 180

end Angle

def perpendicular (r s : Line Ω) := ∃ A B C, A ∈ r ∧ A ∈ s ∧ B ∈ r ∧ C ∈ s ∧ (∟ B A C).is_right
infix `⊥`:100 := perpendicular

namespace Triangle

def angles (T : Triangle Ω) := [(∟ T.A T.B T.C).m, (∟ T.B T.C T.A).m, (∟ T.C T.A T.B).m]
@[simp] def congruent (T S : Triangle Ω) := T.sides = S.sides ∧ T.angles = S.angles
infix `≅`:100 := congruent
end Triangle

end IncidencePlane

namespace NeutralPlane
variables {Ω : Type*} [NeutralPlane Ω]

lemma ruler_inj {P Q : Ω} {ℓ : Line Ω} : P ∈ ℓ → Q ∈ ℓ → ruler ℓ P = ruler ℓ Q → P = Q :=
λ hP hQ H, (NeutralPlane.ruler_bij ℓ).inj_on hP hQ H

def ruler_inv (ℓ : Line Ω) : ℝ → Ω := inv_fun_on (ruler ℓ) (ℓ : set Ω)

lemma ruler_compat {ℓ : Line Ω} {P : Ω} (hP : P ∈ ℓ) : ruler_inv ℓ (ruler ℓ P) = P :=
(NeutralPlane.ruler_bij ℓ).inv_on_inv_fun_on.1 hP

lemma ruler_compat' (ℓ : Line Ω) (x : ℝ) : ruler ℓ (ruler_inv ℓ x) = x :=
(surj_on.inv_on_inv_fun_on (NeutralPlane.ruler_bij ℓ).2.2).2 (mem_univ x)

end NeutralPlane
