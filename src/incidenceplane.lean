import tactic
import data.real.basic
import data.set.function

noncomputable theory
open_locale classical
open set function

@[protect_proj]
class subset (A : Type*) (B : out_param $ Type*) :=
(mem : B → A → Prop)

namespace subset
-- The following allows us to use the symbol `∈`
instance {A : Type*} {B : Type*} [subset A B] : has_mem B A := ⟨subset.mem⟩

-- This says that two "subset"s are equivalent (written `≈`, type with \approx) when
-- they have the same points.
instance {A : Type*} {B : Type*} [subset A B] : has_equiv A := ⟨λ X Y, ∀ t, t ∈ X ↔ t ∈ Y⟩
@[simp] lemma equiv_iff {A : Type*} {B : Type*} [subset A B] (X Y : A) : X ≈ Y ↔ ∀ t, t ∈ X ↔ t ∈ Y := iff.rfl

-- A "subset" can always be considered as an actual subset, in Lean this is `set B`
instance {A : Type*} {B : Type*} [subset A B] : has_coe_t A (set B) := ⟨λ x p, p ∈ x⟩

@[simp] lemma mem_pts  {A : Type*} {B : Type*} [subset A B] (a : A) (P : B) : P ∈ (a : set B) ↔ P ∈ a
:= iff.rfl

end subset

@[simp] def pts {A : Type*} {B : Type*} [subset A B] : A → set B := λ a, {x : B | x ∈ a}


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
	(infix `∈`:100 := belongs)
	-- Existence postulate
	(existence : ∃ P Q : Point, P ≠ Q)

	-- Incidence postulate is divided into 4 statements
	(line_through : Point → Point → Line)
	(line_through_left (P Q : Point) : P ∈ (line_through P Q))
	(line_through_right (P Q : Point) : Q ∈ (line_through P Q))
	(incidence {P Q : Point} {ℓ : Line} : P ≠ Q → P ∈  ℓ → Q ∈ ℓ → ℓ = line_through P Q)


namespace IncidencePlane
variables {Ω : Type*} [IncidencePlane Ω]

-- From here on, we can use the symbol `∈` for Lines
instance : subset (Line Ω) Ω := {mem := belongs}

-- Here we state that Ω is nonempty (in fact it must have at least two distinct points!)
instance : nonempty Ω := nonempty_of_exists IncidencePlane.existence

/--
This lemma is a rephrasing of the incidence axiom that
doesn't mention `line_through`
-/ 
lemma equal_lines_of_contain_two_points {A B : Ω}	{r s : Line Ω}
(hAB: A ≠ B)	(hAr: A ∈ r) (hAs: A ∈ s) (hBr: B ∈ r) (hBs: B ∈ s) :	r = s :=
by rw [incidence hAB hAr hBr, incidence hAB hAs hBs]

-- Define collinearity of a set of points to mean that they all lie on some line
def collinear (S : set Ω) : Prop := ∃ (ℓ : Line Ω), ∀ {P : Ω}, P ∈ S → P ∈ ℓ

-- The next lemmas allow us to deal with collinearity of sets
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
	use u,
	have huv : u = v := equal_lines_of_contain_two_points h (hu hPS) (hv hPT) (hu hQS) (hv hQT),
	simp [←huv] at hv,
	finish,
end

/--
Say that  B is between A and C if they are collinear and AB + BC = AC. We will write A * B * C.
Note that this means that always A * A * C and A * C * C, in particular.
-/
def between (A B C : Ω) := collinear ({A, B, C} : set Ω) ∧ distance A B + distance B C = distance A C
notation A `*` B `*` C := IncidencePlane.between A B C

/--
Two lines intersect if they share a point
-/
def intersect (r s : Line Ω) : Prop := ∃ A, A ∈ r ∧ A ∈ s

/--
Two lines are parallel if they dont intersect (so a line is never parallel to itself)
-/
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

namespace Segment

-- Declare when P ∈ A⬝B
instance : subset (Segment Ω) Ω := { mem := λ P S, S.A * P * S.B }
@[simp] lemma mem_pts (S : Segment Ω) (P : Ω) : P ∈ S ↔ (S.A * P * S.B) := iff.rfl


/--
The length of a segment is defined to be the distance between its two endpoints
If S if a segment, we can use this definition writing `S.length`
-/
@[simp] def length (S : Segment Ω) := distance S.A S.B

/--
Two segments are said to be congruent (written ≅) if they have the same length
-/
@[simp] def congruent (S T : Segment Ω) := length S = length T
infix `≅`:100 := congruent

end Segment

/--
A set of points is convex if given two points P and Q in the set, the segment P⬝Q is contained in the set
-/
def is_convex (S : set Ω) := ∀ P Q : Ω, P ∈ S → Q ∈ S → pts (P⬝Q) ⊆ S

/--
Two points P and Q lie on the same side of a line ℓ if the segment P⬝Q doesn't intersect ℓ
-/
def same_side (ℓ : Line Ω) (P Q : Ω) :=  pts (P⬝Q) ∩ ℓ = ∅

/--
The half-plane determined by a line ℓ and a point P consists of all the points lying on the same side of P
Note : with this definition, the half plane determined by a point in ℓ is the empty set.
-/
def half_plane (ℓ : Line Ω) (P : Ω) := {Q | same_side ℓ P Q}

/--
Sometimes we will want to consider the closed half plane: all the points lying on the same
side of P, together with the line ℓ
-/
def closed_half_plane (ℓ : Line Ω) ( P : Ω) := (half_plane ℓ P) ∪ ℓ

structure Ray (Point : Type*):=
	(origin : Point) (target : Point)
infix `=>`:100 := Ray.mk

namespace Ray

instance : subset (Ray Ω) Ω := {mem := λ P r, (r.origin * P * r.target) ∨ (r.origin * r.target * P)}
@[simp] lemma mem_pts (r : Ray Ω) (P : Ω) : P ∈ r ↔ (r.origin * P * r.target) ∨ (r.origin * r.target * P) := iff.rfl
/--
The line determined by a ray
-/
def line (r : Ray Ω) : Line Ω := line_through r.origin r.target

/--
A ray is degenerate if its origin and target are the same
-/
@[simp] def degenerate (r : Ray Ω) := r.origin = r.target

/--
We say that non-degenerate rays r and s are `opposite` if they have the same origin, which is between the two targets
-/
def opposite (r s : Ray Ω) := ¬ r.degenerate ∧ ¬ s.degenerate ∧ r.origin = s.origin ∧ r.target * r.origin * s.target

end Ray


/-
ANGLES
-/


structure Angle (Point : Type*) := (A : Point) (O : Point) (B : Point)
notation `∟`:100 := Angle.mk

namespace Angle

def degenerate (α : Angle Ω) := collinear ({α.A, α.O, α.B} : set Ω)
def interior (α : Angle Ω) := closed_half_plane (line_through α.O α.A) α.B ∩ closed_half_plane (line_through α.O α.A) α.A
instance : has_equiv (Angle Ω) :=
⟨λ α β, ((α.O => α.A ≈ β.O => β.A) ∧ (α.O => α.B ≈ β.O => β.B)) ∨ ((α.O => α.A ≈ β.O => β.B) ∧ (α.O => α.B ≈ β.O => β.A))⟩


end Angle

structure Triangle (Point : Type*) :=
	(A : Point) (B : Point) (C : Point)
notation `▵`:100 := Triangle.mk

namespace Triangle

def degenerate (T: Triangle Ω) := collinear ({T.A, T.B, T.C} : set Ω)
def vertices (T : Triangle Ω) := [T.A, T.B, T.C]
def sides (T : Triangle Ω) := [(T.A⬝T.B).length, (T.B⬝T.C).length, (T.A⬝T.C).length]

instance : subset (Triangle Ω) Ω := {mem := λ P T, P ∈ T.A⬝T.B ∨ P ∈ T.B⬝T.C ∨ P ∈ T.A⬝T.C}

end Triangle

namespace Ray
def between (r s t : Ray Ω) := r.origin = s.origin ∧ s.origin = t.origin ∧ s.target ∈ Angle.interior (∟ r.target r.origin t.target)

end Ray


end IncidencePlane