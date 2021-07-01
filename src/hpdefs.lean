import tactic

noncomputable theory
open_locale classical

def pts {α β : Type*} [has_mem α β] (S : β) : set α := {x : α | x ∈ S}

@[simp] lemma mem_pts {α β : Type*} [has_mem α β] (x : α) (S : β) : x ∈ pts S ↔ x ∈ S :=  iff.rfl

notation p `xor` q := (p ∧ ¬ q) ∨ (q ∧ ¬ p)
def xor3 (p q r : Prop) : Prop := (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨ (¬ p ∧ ¬ q ∧ r)

class PreHilbertPlane (Point : Type*) :=
	(Line : Type*)
  (belongs : Point → Line → Prop)
	(between : Point → Point → Point → Prop)

  (notation A `∈` ℓ := belongs A ℓ)

	-- I1: there is a unique line passing through two distinct points.
	(I1' {A B : Point} (h : A ≠ B) : ∃! (ℓ : Line) , A ∈ ℓ ∧ B ∈ ℓ)

	-- I2: any line contains at least two points.
	(I2' (ℓ : Line) : ∃ A B : Point, A ≠ B ∧ A ∈ ℓ ∧ B ∈ ℓ)

	-- I3: there exists 3 non-collinear points.
	(I3' : ∃ A B C : Point, (A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ (∀ ℓ : Line, (A ∈ ℓ ∧ B ∈ ℓ) → (¬ (C ∈ ℓ) ))))

namespace PreHilbertPlane
variables {Ω : Type*} [PreHilbertPlane Ω]

instance : has_mem Ω (Line Ω) := ⟨belongs⟩

instance Line.has_coe : has_coe (Line Ω) (set Ω) := ⟨pts⟩
@[simp] lemma mem_coe_to_mem (p : Ω) (ℓ : Line Ω) : p ∈ (ℓ : set Ω) ↔ p ∈ ℓ := iff.rfl

def points_between (A B : Ω) : set Ω := {P : Ω | between A P B}
notation A `*` B `*` C := PreHilbertPlane.between A B C

-- Put the axioms in terms of this has_mem
lemma I1 {A B : Ω} (h : A ≠ B) : ∃! (ℓ : Line Ω), ( A ∈ ℓ ) ∧ ( B ∈ ℓ ) := I1' h
lemma I2 (ℓ : Line Ω) : ∃ A B : Ω, A ≠ B ∧ A ∈ ℓ ∧ B ∈ ℓ := I2' ℓ
lemma I3 : ∃ A B C : Ω, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ ∀ ℓ : Line Ω, A ∈ ℓ ∧ B ∈ ℓ → ¬ C ∈ ℓ := I3'


def collinear (A B C : Ω) := ∃ (ℓ : Line Ω), A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ
@[simp] lemma collinear_iff {A B C : Ω} :
	collinear A B C ↔ ∃ ℓ : Line Ω, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ := iff.rfl

def intersect (r s : Line Ω) := ∃ A, A ∈ r ∧ A ∈ s

def parallel (r s : Line Ω) := (r = s) ∨ (¬ intersect r s)
notation r `||` s := parallel r s

end PreHilbertPlane

open PreHilbertPlane

/-- A segment is created by giving two points. -/
structure Segment (Point : Type*) :=
	(A : Point) (B : Point)
notation A `⬝`:100 B := Segment.mk A B

namespace Segment
variables {Ω : Type*} [PreHilbertPlane Ω]

/--
When thought of as a set, it is the the set consisting of the endpoints
and all the points between them
-/
instance : has_mem Ω (Segment Ω) :=
⟨λ P S, P = S.A ∨ P = S.B ∨ S.A * P * S.B⟩

instance has_coe_to_set : has_coe (Segment Ω) (set Ω) := ⟨pts⟩
@[simp] lemma mem_coe_to_mem_pts (P : Ω) (S : Segment Ω) :
	P ∈ (S : set Ω) ↔ (P = S.A ∨ P = S.B ∨ S.A * P * S.B) := iff.rfl

@[simp] lemma mem_pts (P : Ω) (S : Segment Ω) :
	P ∈ S ↔ (P = S.A ∨ P = S.B ∨ S.A * P * S.B) := iff.rfl

end Segment


structure Ray (Point : Type*):=
	(origin : Point) (target : Point)
notation A `=>` B := Ray.mk A B

namespace Ray
variables {Ω : Type*} [PreHilbertPlane Ω]

instance : has_mem Ω (Ray Ω) :=
⟨λ P r, P = r.origin ∨ (collinear r.origin P r.target ∧ ¬ r.origin ∈ pts (P⬝r.target))⟩

instance has_coe_to_set : has_coe (Ray Ω) (set Ω) := ⟨pts⟩
@[simp] lemma mem_coe_to_mem_pts (P : Ω) (r : Ray Ω) :
	P ∈ (r : set Ω) ↔
	P = r.origin ∨ (collinear r.origin P r.target ∧ ¬ r.origin ∈ pts (P⬝r.target)) := iff.rfl
@[simp] lemma mem_pts (P : Ω) (r : Ray Ω) :
	P ∈ pts r ↔ P = r.origin ∨ (collinear r.origin P r.target ∧ ¬ r.origin ∈ pts (P⬝r.target)) := iff.rfl

end Ray

structure Angle (Point : Type*) :=
	(A : Point) (x : Point)	(B : Point)
notation `∟`:100 := Angle.mk

namespace Angle
variables {Ω : Type*} [PreHilbertPlane Ω]

def nondegenerate (a : Angle Ω) := ¬ collinear a.A a.x a.B

instance : has_mem Ω (Angle Ω) :=
⟨λ P a, P ∈ pts (a.x=>a.A) ∨ P ∈ pts (a.x=>a.B)⟩

instance has_coe_to_set : has_coe (Angle Ω) (set Ω) := ⟨pts⟩
@[simp] lemma mem_coe_to_mem_pts (P : Ω) (a : Angle Ω) :
	P ∈ (a : set Ω) ↔
	P ∈ pts (a.x=>a.A) ∨ P ∈ pts (a.x=>a.B) := iff.rfl

@[simp] lemma mem_pts (P : Ω) (a : Angle Ω) :
	P ∈ a ↔
	P ∈ pts (a.x=>a.A) ∨ P ∈ pts (a.x=>a.B) := iff.rfl

end Angle

class HilbertPlane (Point : Type*) extends PreHilbertPlane Point :=
	/- Betweenness is symmetric -/
	(B11 {A B C : Point} : (A * B * C) → (C * B * A))
	/- If A * B * C then the three points are distinct and collinear. -/
	(B12 {A B C : Point} : (A * B * C) → (A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ collinear A B C))
	/- Given two distinct points A, B, there is a third point C such that A * B * C.-/
	(B2 {A B : Point} (h: A ≠ B) : ∃ C, A * B * C)
	/- Given 3 distinct collinear points A B C, exactly one of them is between the other two.-/
	(B3 {A B C : Point} (h: collinear A B C) :
		xor3 (A * B * C) ( B * A * C ) (A * C * B))

	(B4 {A B C D : Point} {ℓ : Line} -- Pasch
		(hnc: ¬ collinear A B C)
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
		(hα : α.nondegenerate) (hs : ¬ collinear s S.origin S.target)
		(hr : S.origin ≠ S.target) :  ∃! E : Point,
		(∟ E S.origin S.target ≃ α) ∧ 
		 ∀ x, (E * x * s) → ∀ (ℓ : Line), S.origin ∈ ℓ ∧ S.target ∈ ℓ 
		 → ¬ x ∈ ℓ)
	/- Congruence of angles is reverse-transitive.-/
	(C5 (α β γ : Angle Point) : α ≃ β → α ≃ γ → β ≃ γ)
	/- Given triangles T and T', if they have two sides and their middle angle
	   congruent, then the third sides and the other two angles are also congruent.-/
	(C6 (A B C A' B' C') : (A⬝B ≅ A'⬝B') → (A⬝C ≅ A'⬝C') → (∟ B A C ≃ ∟ B' A' C') →
		(B⬝C ≅ B'⬝C') ∧ (∟ A B C ≃ ∟ A' B' C') ∧ (∟ A C B ≃ ∟ A' C' B'))

class EuclideanPlane (Point : Type*) extends HilbertPlane Point :=
	(parallel_postulate {ℓ r s : Line} :
		(intersect r s) ∧ (r || ℓ) ∧ (s || ℓ) → (r = s))

namespace HilbertPlane

notation X `≅`:50 Y:50 := HilbertPlane.seg_cong X Y
notation X `≃`:50 Y:50 := HilbertPlane.ang_cong X Y

structure Triangle (Point : Type*) :=
	(A : Point) (B : Point)	(C : Point)
notation `▵`:100 := Triangle.mk

namespace Triangle
variables {Ω : Type*} [HilbertPlane Ω]

def nondegenerate (T : Triangle Ω) := ¬ collinear T.A T.B T.C

def similar_triangles (T R : Triangle Ω) :=
	(∟ T.B T.A T.C ≃ ∟ R.B R.A R.C)
∧ (∟ T.A T.C T.B ≃ ∟ R.A R.C R.B)
∧ (∟ T.C T.B T.A ≃ ∟ R.C R.B R.A)

def congruent_triangles (T R : Triangle Ω) :=
	similar_triangles T R ∧
	(T.A⬝T.B ≅ R.A⬝R.B) ∧ (T.A⬝T.C ≅ R.A⬝R.C) ∧ (T.B⬝T.C ≅ R.B⬝R.C)

instance : has_mem Ω (Triangle Ω) :=
⟨λ P T, P ∈ pts (T.A⬝T.B) ∨ P ∈ pts (T.B⬝T.C) ∨ P ∈ pts (T.A⬝T.C)⟩

instance has_coe_to_set : has_coe (Triangle Ω) (set Ω) := ⟨pts⟩
@[simp] lemma mem_coe_to_mem_pts (P : Ω) (T : Triangle Ω) :
	P ∈ (T : set Ω) ↔
	P ∈ pts (T.A⬝T.B) ∨ P ∈ pts (T.B⬝T.C) ∨ P ∈ pts (T.A⬝T.C) := iff.rfl

@[simp] lemma mem_pts (P : Ω) (T : Triangle Ω) :
	P ∈ T ↔
	P ∈ pts (T.A⬝T.B) ∨ P ∈ pts (T.B⬝T.C) ∨ P ∈ pts (T.A⬝T.C) := iff.rfl

end Triangle

end HilbertPlane