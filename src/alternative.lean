import tactic
import data.real.basic
import data.set.function

noncomputable theory
open_locale classical
open set function

/--
If P is of some type α, and we can write P ∈ R for objects R of type β, we can construct {P | P ∈ R} as a subset of α.
-- This subset will be called pts R.
Example: since we will have a symbol P ∈ ℓ where P is type Point and ℓ is of type Line, we can write
pts(ℓ) to mean the subset of all Points P such that P ∈ ℓ.
-/
def pts {α β : Type*} [has_mem α β] (S : β) : set α := {x : α | x ∈ S}
@[simp] lemma mem_pts {α β : Type*} [has_mem α β] (x : α) (S : β) : x ∈ pts S ↔ x ∈ S :=  iff.rfl

class subset (Point L : Type*) [has_mem Point L] [has_equiv L]

instance has_coe_to_set (Point : Type*) (L : Type*) [has_mem Point L] [has_equiv L] : has_coe (subset Point L) (set Point) := ⟨
	begin
		intro S,
		exact pts S,
	end
⟩

/--
We define an incidence plane as having the undefined terms `Point` and `Line`,
a function `distance` that takes every two points to a real number, and a predicate
`belongs` that relates points and lines.

There are essentially two axioms: existence of two distinct points, and the incidence postulate.
-/
class IncidencePlane (Point : Type*) :=
	(distance : Point → Point → ℝ)
	(Line : Type*)
  (belongs : Point → Line → Prop)
	
	-- Existence postulate
	(existence : ∃ P Q : Point, P ≠ Q)

	-- Incidence postulate is divided into 4 statements
	(line_through : Point → Point → Line)
	(line_through_left (P Q : Point) : belongs P (line_through P Q))
	(line_through_right (P Q : Point) : belongs Q (line_through P Q))
	(incidence {P Q : Point} {ℓ : Line} : P ≠ Q → belongs P ℓ → belongs Q ℓ → ℓ = line_through P Q)


namespace IncidencePlane
variables {Ω : Type*} [IncidencePlane Ω]

-- From here on, we can use the symbol `∈`
instance : has_mem Ω (Line Ω) := ⟨belongs⟩

-- Here we state that Ω is nonempty (in fact it must have at least two distinct points!)
instance : nonempty Ω := nonempty_of_exists IncidencePlane.existence

-- This allows to think of a line as a set of points automatically
instance : has_coe (Line Ω) (set Ω) := ⟨pts⟩

/--
This is our first lemma: it is a rephrasing of the incidence axiom that
doesn't mention `line_through`
-/ 
lemma equal_lines_of_contain_two_points {A B : Ω}	{r s : Line Ω}
(hAB: A ≠ B)	(hAr: A ∈ r) (hAs: A ∈ s) (hBr: B ∈ r) (hBs: B ∈ s) :	r = s :=
by rw [incidence hAB hAr hBr, incidence hAB hAs hBs]

-- Define collinearity of a set of points to mean that they all lie on some line
def collinear (S : set Ω) : Prop := ∃ (ℓ : Line Ω), ∀ {P : Ω}, P ∈ S → P ∈ ℓ

-- The next lemma allow us to deal with collinearity of sets
meta def extfinish : tactic unit := `[ext, finish]
lemma collinear_of_equal {S T : set Ω} (h : S = T . extfinish) : (collinear S ↔ collinear T) :=
iff_of_eq (congr_arg collinear h)

lemma collinear_subset (S T : set Ω) (hST : S ⊆ T) : collinear T → collinear S :=
begin
	intro h,
	obtain ⟨ℓ, hℓ⟩ := h,
	exact ⟨ℓ, λ P hP, hℓ (hST hP)⟩,
end

lemma collinear_union (S T : set Ω) {P Q : Ω} (h : P ≠ Q) (hS : collinear S) (hT : collinear T)
(hPS : P ∈ S) (hPT : P ∈ T) (hQS : Q ∈ S) (hQT : Q ∈ T) : collinear (S ∪ T) :=
begin
	obtain ⟨u, hu⟩ := hS,
	obtain ⟨v, hv⟩ := hT,
	have huv : u = v := equal_lines_of_contain_two_points h (hu hPS) (hv hPT) (hu hQS) (hv hQT),
	subst huv,
	use u,
	finish,
end

/--
The current axioms allow us to make the following 3 definitions.

-- Say that  B is between A and C if they are collinear and AB + BC = AC. We will write A * B * C.
Note that this means that always A * A * C and A * C * C, in particular.
-- Two lines intersect if they share a point
-- Two lines are parallel if they dont intersect (so a line is never parallel to itself)

-/
def between (A B C : Ω) := collinear ({A, B, C} : set Ω) ∧ distance A B + distance B C = distance A C
notation A `*` B `*` C := IncidencePlane.between A B C

def intersect (r s : Line Ω) : Prop := ∃ A, A ∈ r ∧ A ∈ s

def parallel (r s : Line Ω) : Prop := ¬ intersect r s

/--
Next we introduce the notion of a Segment. A segment is the giving two points, A and B.
We will use the notation A⬝B to denote the segment denoted by A and B. The segment A⬝B consists
of all the points X such that A * X * B.

We will identify A⬝B with B⬝A, using the symbol ≈.
-/


structure Segment (Point : Type*) :=
(A : Point) (B : Point)
infix `⬝`:100 := Segment.mk

-- Declare when P ∈ A⬝B and when A⬝B ≈ B⬝A 
instance : subset Ω (Segment Ω) :=
{ mem := λ P S, S.A * P * S.B,
  equiv :=  λ S T, (S.A = T.A ∧ S.B = T.B) ∨ (S.A = T.B ∧ S.B = T.A)}

namespace Segment

--instance has_coe_to_set : has_coe (Segment Ω) (set Ω) := ⟨pts⟩


@[simp] lemma mem_pts (P : Ω) (S : Segment Ω) :
P ∈ S ↔ (S.A * P * S.B) := iff.rfl

@[simp] def length (S : Segment Ω) := distance S.A S.B


@[simp] def congruent (S T : Segment Ω) := length S = length T

end Segment

structure Ray (Point : Type*):=
	(origin : Point) (target : Point)
notation A `=>` B := Ray.mk A B

namespace Ray

instance : has_equiv (Ray Ω) := ⟨λ S T, S.origin = T.origin ∧ ((S.origin * S.target * T.target) ∨ S.origin * T.target * S.target)⟩
instance : has_mem Ω (Ray Ω) := ⟨λ P r, (r.origin * P * r.target) ∨ (r.origin * r.target * P)⟩

instance has_coe_to_set : has_coe (Ray Ω) (set Ω) := ⟨pts⟩
instance has_coe_to_line : has_coe (Ray Ω) (Line Ω) := ⟨λ r, line_through r.origin r.target⟩

def degenerate (r : Ray Ω) := r.origin = r.target
def opposite (r s : Ray Ω) := r.origin = s.origin ∧ r.target * r.origin * s.target

end Ray

def is_convex (S : set Ω) := ∀ P Q : Ω, P ∈ S → Q ∈ S → pts (P⬝Q) ⊆ S
def same_side (ℓ : Line Ω) (P Q : Ω) := pts (P⬝Q) ∩ ℓ = ∅
def half_plane (ℓ : Line Ω) (P : Ω) := {Q | same_side ℓ P Q}
-- Note : with this definition, the half plane determined by a point in ℓ is the empty set.


structure Angle (Point : Type*) := (A : Point) (O : Point) (B : Point)
notation `∟`:100 := Angle.mk

namespace Angle

def degenerate (α : Angle Ω) := collinear ({α.A, α.O, α.B} : set Ω)
def interior (α : Angle Ω) := half_plane (line_through α.O α.A) α.B ∩ half_plane (line_through α.O α.A) α.A
instance : has_equiv (Angle Ω) :=
⟨λ α β, (((α.O => α.A) ≈ (β.O => β.A)) ∧ ((α.O => α.B) ≈ (β.O => β.B))) ∨ (((α.O => α.A) ≈ (β.O => β.B)) ∧ ((α.O => α.B) ≈ (β.O => β.A)))⟩

end Angle

structure Triangle (Point : Type*) :=
	(A : Point) (B : Point) (C : Point)
notation `▵`:100 := Triangle.mk

namespace Triangle
def vertices (T : Triangle Ω) := [T.A, T.B, T.C]
def degenerate (T: Triangle Ω) := collinear ({T.A, T.B, T.C} : set Ω)
def sides (T : Triangle Ω) := [(T.A⬝T.B).length, (T.B⬝T.C).length, (T.A⬝T.C).length]

instance : has_mem Ω (Triangle Ω) := ⟨λ P T, P ∈ T.A⬝T.B ∨ P ∈ T.B⬝T.C ∨ P ∈ T.A⬝T.C⟩

instance has_coe_to_set : has_coe (Triangle Ω) (set Ω) := ⟨pts⟩

end Triangle


end IncidencePlane


open IncidencePlane


namespace Ray
variables {Ω : Type*} [IncidencePlane Ω]
def between (r s t : Ray Ω) := r.origin = s.origin ∧ s.origin = t.origin ∧ s.target ∈ Angle.interior (∟ r.target r.origin t.target)

end Ray

class BIYSCPlane (Point : Type*) extends IncidencePlane Point :=
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
	(angle_nondegenerate (α : Angle Point) : (α.O => α.A) ≈ (α.O => α.B) ↔ angle_measure α = 0)
	
	-- Angle construction
	(angle_construction {t : ℝ} (h₀ : 0 < t) (h : t < 180) (r : Ray Point) {E : Point}
	(hE : E ∉ (r : Line))	: Point)
	(angle_construction_def' {t : ℝ} (h₀ : 0 < t) (h : t < 180) (r : Ray Point) {E : Point}
	(hE : E ∉ (r : Line)) : angle_construction h₀ h r hE ∈ half_plane (r : Line) E)
	(angle_construction_def {t : ℝ} (h₀ : 0 < t) (h : t < 180) (r : Ray Point) {E : Point}
	(hE : E ∉ (r : Line)) : angle_measure (∟ r.target r.origin (angle_construction h₀ h r hE)) = t)
	(angle_construction_unique {t : ℝ} (h₀ : 0 < t) (h : t < 180) (r : Ray Point) {E : Point}
	(hE : E ∉ (r : Line))	(B : Point) (hB : B ∈ half_plane (r : Line) E):
	angle_measure (∟ r.target r.origin B) = t → (r.origin => B) ≈ (r.origin => angle_construction h₀ h r hE))

	-- Angle addition
	(angle_addition (A B C D : Point) (h : Ray.between (A=>B) (A=>D) (A=>C)) :
	angle_measure (∟B A D) + angle_measure (∟ D A C) = angle_measure (∟ B A C) )

	-- SAS
	(SAS (S T : Triangle Point) (hAB : (S.A⬝S.B).congruent (T.A⬝T.B)) (hBC : (S.B⬝S.C).congruent (T.B⬝T.C))
	(hABC : angle_measure (∟ T.A T.B T.C) =  angle_measure (∟ S.A S.B S.C)) : 
	(S.A⬝S.C).congruent (T.A⬝T.C) ∧ angle_measure (∟ T.B T.C T.A) = angle_measure (∟ S.B S.C S.A)
	∧ angle_measure (∟ T.C T.A T.B) =  angle_measure (∟ S.C S.A S.B))

namespace IncidencePlane
namespace Angle
variables {Ω : Type*} [BIYSCPlane Ω]
open BIYSCPlane
def m (α : Angle Ω) := angle_measure α
end Angle

namespace Triangle
variables {Ω : Type*} [BIYSCPlane Ω]
def angles (T : Triangle Ω) := [(∟ T.A T.B T.C).m, (∟ T.B T.C T.A).m, (∟ T.C T.A T.B).m]
def congruent (T S : Triangle Ω) := T.sides = S.sides ∧ T.angles = S.angles
end Triangle

end IncidencePlane

namespace BIYSCPlane
variables {Ω : Type*} [BIYSCPlane Ω]

lemma ruler_inj {P Q : Ω} {ℓ : Line Ω} : P ∈ ℓ → Q ∈ ℓ → ruler ℓ P = ruler ℓ Q → P = Q :=
λ hP hQ H, (BIYSCPlane.ruler_bij ℓ).inj_on hP hQ H

def ruler_inv (ℓ : Line Ω) : ℝ → Ω := inv_fun_on (ruler ℓ) (ℓ : set Ω)

lemma ruler_compat {ℓ : Line Ω} {P : Ω} (hP : P ∈ ℓ) : ruler_inv ℓ (ruler ℓ P) = P :=
(BIYSCPlane.ruler_bij ℓ).inv_on_inv_fun_on.1 hP

lemma ruler_compat' (ℓ : Line Ω) (x : ℝ) : ruler ℓ (ruler_inv ℓ x) = x :=
(surj_on.inv_on_inv_fun_on (BIYSCPlane.ruler_bij ℓ).2.2).2 (mem_univ x)

end BIYSCPlane

open BIYSCPlane

-- Exercises
variables {Ω : Type*} [BIYSCPlane Ω]

lemma distance_eq (A : Ω) : distance A A = 0 :=
begin
	rw ruler_dist,
	simp only [sub_self, abs_zero],
end

lemma line_through_symm (P Q : Ω) : line_through P Q = line_through Q P :=
begin
	by_cases hPQ : Q = P,
	{
		subst hPQ,
	},
	{
		exact IncidencePlane.incidence hPQ (line_through_right P Q) (line_through_left P Q),
	}
end

lemma distance_symm (A B : Ω) : distance A B = distance B A :=
begin
	rw ruler_dist,
	rw ruler_dist,
	rw line_through_symm,
	rw abs_sub_comm,
end

lemma distance_nonneg (A B : Ω) : 0 ≤ distance A B :=
begin
	rw ruler_dist,
	apply abs_nonneg,
end

lemma distance_nondegenerate (A B : Ω) : distance A B = 0 ↔ A = B :=
begin
	split,
	{
		intro h,
		rw ruler_dist at h,
		set ℓ := line_through A B,
		have h' : ruler ℓ A = ruler ℓ B := eq_of_abs_sub_eq_zero h,
		apply ruler_inj (line_through_left A B) (line_through_right A B) h',
	},
	{
		intro h,
		subst h,
		rw ruler_dist,
		simp only [sub_self, abs_zero],
	}
end

lemma between_swap' (A B C : Ω) : (A * B * C) → (C * B * A) :=
begin
	intro h,
	cases h,
	split,
	{
		rw collinear_of_equal at h_left,
		rw collinear_of_equal,
		finish,
	},
	{
		rw [show distance A C = distance C A, by rw distance_symm] at h_right,
		rw ←h_right,
		rw [show distance C B = distance B C, by rw distance_symm],
		rw [show distance B A = distance A B, by rw distance_symm],
		rw add_comm,
	},
end

lemma between_swap (A B C : Ω) : (A * B * C) ↔ (C * B * A) :=
begin
	split; apply between_swap',
end

@[simp] lemma  between_trivial (A B : Ω) : A * B * B :=
begin
	unfold between,
	split,
	{
		use line_through A B,
		simp,
		exact ⟨line_through_left A B, line_through_right A B⟩
	},
	{
		rw distance_eq,
		exact add_zero (distance A B)
	}
end

@[simp] lemma  between_trivial' (A B : Ω) : A * A * B :=
begin
	rw between_swap,
	exact between_trivial B A,
end

lemma segment_eq (A B : Ω) : pts (A⬝B) = pts (B⬝A) :=
begin
	ext,
	split;
	{
		intro h,
		simp at h ⊢,
		rw between_swap,
		tauto,
	},
end

-- We skip the ruler placement postulate. We'll see whether it's needed or not...

meta def linarith' := `[linarith]
lemma abs_sub_of_le (x y : ℝ) (h: x ≤ y . linarith') : |x - y| = y - x :=
begin
	rw abs_of_nonpos (sub_nonpos.mpr h),
	exact neg_sub x y,
end
lemma abs_sub_of_le' (x y : ℝ) (h: y ≤ x . linarith') : |x - y| = x - y :=
begin
	rw abs_of_nonneg (sub_nonneg.mpr h),
end

lemma ruler_dist' (ℓ : Line Ω) {P Q : Ω} (hP : P ∈ ℓ) (hQ : Q ∈ ℓ) : distance P Q = |ruler ℓ P - ruler ℓ Q| :=
begin
	by_cases P = Q,
	{
		rw [h, distance_eq],
		simp only [sub_self, abs_zero],
	},
	{
		rw [incidence h hP hQ, ruler_dist],
	}
end

lemma between_iff_aux (A B C : Ω) : (A * B * C) → C * B * A :=
begin
	intro h,
	split,
	{
		rw collinear_of_equal,
		exact h.1,
	},
	{
		cases h,
		rw distance_symm C B,
		rw distance_symm B A,
		rw distance_symm C A,
		rw ←h_right,
		ring,
	}
end

lemma between_iff (A B C : Ω) : (A * B * C) ↔ C * B * A :=
begin
	split; apply between_iff_aux,
end


lemma between_ruler_aux {A B C : Ω} (ℓ : Line Ω) (hA : A ∈ ℓ) (hB : B ∈ ℓ) (hC : C ∈ ℓ) :
ruler ℓ A ≤ ruler ℓ B ∧ ruler ℓ B ≤ ruler ℓ C → A * B * C :=
begin
	intro h,
	cases h,
	{
		unfold between,
		rw [ruler_dist' ℓ hA hB, ruler_dist' ℓ hB hC, ruler_dist' ℓ hA hC],
		split,
		{
			use ℓ,
			finish,
		},
		repeat {rw abs_sub_of_le},
		ring,
	},
end

lemma between_ruler (A B C : Ω) (ℓ : Line Ω) (hA : A ∈ ℓ) (hB : B ∈ ℓ) (hC : C ∈ ℓ) :
(A * B * C) ↔ ruler ℓ A ≤ ruler ℓ B ∧ ruler ℓ B ≤ ruler ℓ C ∨ ruler ℓ C ≤ ruler ℓ B ∧ ruler ℓ B ≤ ruler ℓ A :=
begin
	split,
	{
		intro h,
		cases h,
		set α := ruler ℓ,
		by_cases H : α A ≤ α B ∧ α B ≤ α C, tauto,
		right,
		rw [ruler_dist' ℓ hA hB, ruler_dist' ℓ hB hC, ruler_dist' ℓ hA hC] at h_right,
		rw [show ruler ℓ = α, by refl] at h_right,
		replace H : α B < α A ∨ α C < α B,
		{
			push_neg at H,
			by_cases hc : α A ≤ α B,
			{
				specialize H hc,
				right, exact H,
			},
			{
				left,
				linarith,
			}
		},
		cases H,
		{
			split,
			{
				by_contradiction hc,
				replace hc : α B < α C, by linarith,
				rw abs_sub_of_le' at h_right,
				rw abs_sub_of_le at h_right,
				by_cases h1 : α A ≤ α C,
				{
					rw abs_sub_of_le at h_right,
					linarith,
				},
				{
					rw abs_sub_of_le' at h_right,
					linarith,
				}
			},
			exact le_of_lt H,			
		},
		{
			split,
			exact le_of_lt H,
			by_contradiction hc,
			replace hc : α A < α B, by linarith,
			rw abs_sub_of_le at h_right,
			rw abs_sub_of_le' at h_right,
			by_cases h1 : α A ≤ α C,
			{
				rw abs_sub_of_le at h_right,
				linarith,
			},
			{
				rw abs_sub_of_le' at h_right,
				linarith,
			}
		}
	},
	{
		intro h,
		cases h,
		{
			apply between_ruler_aux ℓ; assumption,
		},
		{
			rw between_iff,
			apply between_ruler_aux ℓ; assumption,
		}
	}
end

def is_midpoint (P Q M : Ω) := (P * M * Q) ∧ distance P M = distance M Q

lemma midpoint_exists_unique (P Q : Ω) : ∃! M, is_midpoint P Q M :=
begin
	sorry
end

lemma point_construction (r : Ray Ω) (h : ¬ r.degenerate) (d : ℝ) (hd : 0 ≤ d) : 
∃! Q, Q ∈ pts r ∧ distance r.origin Q = d :=
begin
	sorry
end

lemma pasch {T : Triangle Ω} {ℓ : Line Ω} (hT : ¬ T.degenerate) (hℓ : pts ℓ ∩ T.vertices.to_finset ∩ ℓ = ∅)
(h : (pts ℓ ∩ T.A⬝T.B).nonempty) : (pts ℓ ∩ T.B⬝T.C).nonempty ∨ (pts ℓ ∩ T.A⬝T.C).nonempty :=
begin
	sorry
end

lemma isosceles_triangle (T : Triangle Ω) (h : (T.A⬝T.B).congruent (T.A⬝T.C)) :
(∟ T.A T.B T.C).m = (∟ T.A T.C T.B).m :=
begin
	set S1 := ▵ T.B T.A T.C,
	set S2 := ▵ T.C T.A T.B,
	simp at h,
	have h1 : (T.B⬝T.A).congruent (T.C⬝T.A),
	{
		simp,
		rw distance_symm,
		rw h,
		exact distance_symm T.A T.C,
	},
	have h2 : (T.A⬝T.C).congruent (T.A⬝T.B),
	{
		simp,
		rw distance_symm,
		rw h,
		exact distance_symm T.C T.A,
	},
	have h3 : (∟ T.C T.A T.B).m = (∟ T.B T.A T.C).m,
	{
		apply angle_well_def,
		unfold has_equiv.equiv,
		simp,
	},
	have := (BIYSCPlane.SAS S1 S2 h1 h2 h3).2,
	simpa using this.1,
end

lemma ray_theorem {ℓ : Line Ω} {A B C : Ω} (hA : A ∈ ℓ) (hB : B ∉ ℓ) (hC : C ∈ pts(A=>B)) (hAC : C ≠ A) :
same_side ℓ B C :=
begin
	sorry
end

lemma between_iff_ray_between {A B C D : Ω} (h : ¬ collinear ({A, B, C} : set Ω)) (hD : D ∈ line_through B C)
: (B * D * C) ↔ Ray.between (A=>B) (A=>D) (A=>C)  :=
begin
	sorry
end

lemma same_side.trans (ℓ : Line Ω) {A B C : Ω} : same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
	sorry
end