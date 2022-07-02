import tactic

noncomputable theory
open_locale classical

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

notation p `xor` q := (p ∧ ¬ q) ∨ (q ∧ ¬ p)
def xor3 (p q r : Prop) : Prop := (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨ (¬ p ∧ ¬ q ∧ r)

class PreHilbertPlane (Point : Type*) :=
	(Line : Type*)
  (belongs : Point → Line → Prop)
	(between : Point → Point → Point → Prop)

  (notation A `∈` ℓ := belongs A ℓ)

	-- I1: there is a unique line passing through two distinct points.
	(I1 {A B : Point} (h : A ≠ B) : ∃! (ℓ : Line) , A ∈ ℓ ∧ B ∈ ℓ)

	-- I2: any line contains at least two points.
	(I2 (ℓ : Line) : ∃ A B : Point, A ≠ B ∧ A ∈ ℓ ∧ B ∈ ℓ)

	-- I3: there exists 3 non-collinear points.
	(I3 : ∃ A B C : Point, (A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ (∀ ℓ : Line, (A ∈ ℓ ∧ B ∈ ℓ) → (¬ (C ∈ ℓ) ))))

namespace PreHilbertPlane
variables {Ω : Type*} [PreHilbertPlane Ω]

-- From here on, we can use the symbol `∈` for Lines
instance : subset (Line Ω) Ω := {mem := belongs}

notation A `*` B `*` C := PreHilbertPlane.between A B C

def collinear_triple (A B C : Ω) : Prop := ∃ {ℓ : Line Ω}, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ
@[simp] lemma collinear_triple_iff {A B C : Ω} :
	collinear_triple A B C ↔ ∃ ℓ : Line Ω, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ := iff.rfl

def collinear (S : set Ω) : Prop := ∃ {ℓ : Line Ω}, ∀ {P}, P ∈ S → P ∈ ℓ

@[simp]
lemma collinear_def (A B C : Ω) : collinear_triple A B C ↔ collinear ({A, B, C} : set Ω) :=
begin
	split;
	{
		intro h,
		obtain ⟨ℓ, hℓ⟩ := h,
		use ℓ,
		finish,
	},
end

def intersect (r s : Line Ω) : Prop := ∃ A, A ∈ r ∧ A ∈ s

def parallel (r s : Line Ω) : Prop := (r = s) ∨ (¬ intersect r s)
notation r `||` s := parallel r s

end PreHilbertPlane

open PreHilbertPlane

/--
Next we introduce the notion of a Segment. A segment is the giving two points, A and B.
We will use the notation A⬝B to denote the segment denoted by A and B. The segment A⬝B consists
of all the points X such that A * X * B, together with A and B.
-/
structure Segment (Point : Type*) :=
	(A : Point) (B : Point)

infix `⬝`:100 := Segment.mk

namespace Segment

variables {Ω : Type*} [PreHilbertPlane Ω]

-- Declare when P ∈ A⬝B
instance : subset (Segment Ω) Ω := { mem := λ P S, P = S.A ∨ P = S.B ∨ S.A * P * S.B}
@[simp] lemma mem_pts (S : Segment Ω) (P : Ω) : P ∈ S ↔ P = S.A ∨ P = S.B ∨ S.A * P * S.B := iff.rfl

end Segment

structure Ray (Point : Type*):=
	(origin : Point) (target : Point)
notation A `=>` B := Ray.mk A B

namespace Ray
variables {Ω : Type*} [PreHilbertPlane Ω]

instance : subset (Ray Ω) Ω := { mem := λ P r, P = r.origin ∨ (collinear_triple r.origin P r.target ∧ ¬ r.origin ∈ pts (P⬝r.target)) }

def nondegenerate (r : Ray Ω) := r.origin ≠ r.target

end Ray

structure Angle (Point : Type*) :=
	(A : Point) (x : Point)	(B : Point)
notation `∟`:100 := Angle.mk

namespace Angle
variables {Ω : Type*} [PreHilbertPlane Ω]

def nondegenerate (a : Angle Ω) := ¬ collinear_triple a.A a.x a.B

end Angle

namespace HilbertPlane
variables {Ω : Type*} [PreHilbertPlane Ω]
variables {A B : Ω}
variables {r s : Line Ω}

lemma I11 (h: A ≠ B) : ∃ (ℓ : Line Ω), A ∈ ℓ ∧ B ∈ ℓ := exists_of_exists_unique (I1 h)

lemma I12 (h: A ≠ B) (hAr: A ∈ r) (hBr : B ∈ r) (hAs : A ∈ s) (hBs : B ∈ s) : r = s :=
begin
    apply (unique_of_exists_unique (I1 h));
    tauto,
end

lemma there_are_two_points : ∃ A B : Ω, (A ≠ B) :=
begin
    rcases I3 with ⟨A, ⟨B, ⟨C, ⟨h1, h2⟩⟩⟩⟩,
    use [A, B],
		exact _inst_1,
end

def line_through_aux (A B : Ω) : {ℓ : Line Ω // A ∈ ℓ ∧ B ∈ ℓ} :=
begin
    apply classical.indefinite_description,
    by_cases h : A = B,
    {
        subst h,
        have h1 : ∃ C D : Ω, C ≠ D := there_are_two_points,
        obtain ⟨C, D, hC⟩ := h1,
        by_cases h1 : A = C,
        {
            subst h1,
            obtain ⟨ℓ, hAℓ, _⟩ := I11 hC,
            exact ⟨ℓ, hAℓ, hAℓ⟩,
        },
        {
            obtain ⟨ℓ, hAℓ, _⟩ := I11 h1,
            exact ⟨ℓ, hAℓ, hAℓ⟩,
        },
    },
    exact I11 h,
end

def same_side  (ℓ : Line Ω) (A B: Ω) := (A ∈ ℓ ∧ B ∈ ℓ) ∨ ( pts (A⬝B) ∩ ℓ = ∅)
def line_through (A B : Ω) : Line Ω := (line_through_aux A B).1

end HilbertPlane

open HilbertPlane

class HilbertPlane (Point : Type*) extends PreHilbertPlane Point :=
	/- Betweenness is symmetric -/
	(B11 {A B C : Point} : (A * B * C) → (C * B * A))
	/- If A * B * C then the three points are distinct and collinear. -/
	(B12 {A B C : Point} : (A * B * C) → (A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ collinear_triple A B C))
	/- Given two distinct points A, B, there is a third point C such that A * B * C.-/
	(B2 {A B : Point} (h: A ≠ B) : ∃ C, A * B * C)
	/- Given 3 distinct collinear points A B C, exactly one of them is between the other two.-/
	(B3 {A B C : Point} (h: collinear_triple A B C) :
		xor3 (A * B * C) ( B * A * C ) (A * C * B))

	(B4 {A B C D : Point} {ℓ : Line} -- Pasch
		(hnc: ¬ collinear_triple A B C)
		(hnAl: ¬ (A ∈ ℓ)) (hnBl: ¬ B ∈ ℓ) (hnCl: ¬ C ∈ ℓ)
		(hDl: D ∈ ℓ) (hADB: A * D * B) :
    (∃ E ,  E ∈ ℓ ∧ (A * E * C)) xor (∃ E, E ∈ ℓ ∧ (B * E * C)))

	(seg_cong : Segment Point → Segment Point → Prop)
	(notation X `≅`:50 Y := seg_cong X Y)
	(ang_cong : Angle Point → Angle Point → Prop)
	(notation X `≃`:50 Y := ang_cong X Y)
	
	/- Given a segment AB and a ray C->D, there is a unique point E on C->D such that
		AB ≅ CE. -/
	(C1 (S : Segment Point) (r : Ray Point) : 
		∃! E, (E ∈ pts r) ∧ ((S.A⬝S.B) ≅ (r.origin⬝E)))
	/- Congruence of segments is reverse-transitive -/
	(C21 (S T U): (S ≅ T) → (S ≅ U) → (T ≅ U))
	/- Congruence of segments is reflexive.
	Note that this together with C21 implies symmetry of congruence. -/
	(C22 (S) : S ≅ S)
	/- Congruence of segments respects the notion of sum of segments -/
	(C3 (A B C D E F) : (A * B * C) → (D * E * F) →
		((A⬝B) ≅ (D⬝E)) → ((B⬝C) ≅ (E⬝F)) → ((A⬝C) ≅ (D⬝F)))
	/- Given a nondegenerate angle α, a segment AB, and a point s,
	construct a point E on the same side as s, such that ∟EAB ≃ α. -/
	(C4 (α : Angle Point) (S : Ray Point) (s : Point)
		(hα : α.nondegenerate) (hs : ¬ collinear_triple s S.origin S.target) :
		∃! ℓ : Line, ∃ E : Point, E ∈ ℓ ∧ S.origin ∈ ℓ ∧ (∟ E S.origin S.target ≃ α)
		∧ same_side (line_through S.origin S.target) E s)
	/- Congruence of angles is reverse-transitive.-/
	(C5 (α β γ : Angle Point) : α ≃ β → α ≃ γ → β ≃ γ)
	/- Given triangles T and T', if they have two sides and their middle angle
	congruent, then the third sides and the other two angles are also congruent.-/
	(C6 (A B C A' B' C') : (A⬝B ≅ A'⬝B') → (A⬝C ≅ A'⬝C') → (∟ B A C ≃ ∟ B' A' C') →
		(B⬝C ≅ B'⬝C') ∧ (∟ A B C ≃ ∟ A' B' C') ∧ (∟ A C B ≃ ∟ A' C' B'))

class EuclideanPlane (Point : Type*) extends HilbertPlane Point :=
	(parallel_postulate {ℓ r s : Line} :
		(intersect r s) → (r || ℓ) → (s || ℓ) → (r = s))

namespace HilbertPlane

notation X `≅`:50 Y:50 := HilbertPlane.seg_cong X Y
notation X `≅`:50 Y:50 := HilbertPlane.ang_cong X Y

end HilbertPlane

structure Triangle (Point : Type*) :=
	(A : Point) (B : Point)	(C : Point)
notation `▵`:100 := Triangle.mk

namespace Triangle
variables {Ω : Type*} [HilbertPlane Ω]

instance : subset (Triangle Ω) Ω :=
{mem := λ P T, P ∈ T.A⬝T.B ∨ P ∈ T.B⬝T.C ∨ P ∈ T.A⬝T.C}

def nondegenerate (T : Triangle Ω) := ¬ collinear_triple T.A T.B T.C

def is_similar (T R : Triangle Ω) : Prop :=
	(∟ T.B T.A T.C ≅ ∟ R.B R.A R.C)
∧ (∟ T.A T.C T.B ≅ ∟ R.A R.C R.B)
∧ (∟ T.C T.B T.A ≅ ∟ R.C R.B R.A)

def is_congruent (T R : Triangle Ω) : Prop :=
	is_similar T R ∧ (T.A⬝T.B ≅ R.A⬝R.B) ∧ (T.A⬝T.C ≅ R.A⬝R.C) ∧ (T.B⬝T.C ≅ R.B⬝R.C)


end Triangle