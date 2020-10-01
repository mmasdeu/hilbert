import tactic

noncomputable theory
open_locale classical

namespace hilbertplane

notation p `xor` q := (p ∧ ¬ q) ∨ (q ∧ ¬ p)

class HilbertPlane :=
	(Point : Type)
	(Line : Type)

    (belongs : Point → Line → Prop)
    (notation A `∈` ℓ := belongs A ℓ)
    (notation A `∉` ℓ := ¬ belongs A ℓ)
	(I1 {A B : Point} (h : A ≠ B) : ∃! ℓ, ( A ∈ ℓ ) ∧ ( B ∈ ℓ ))
	(I2 (ℓ : Line) : ∃ A B : Point, A ≠ B ∧ A ∈ ℓ ∧ B ∈ ℓ)
	(I3 : ∃ A B C : Point, (A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ (∀ ℓ : Line, (A ∈ ℓ ∧ B ∈ ℓ) → (¬ (C ∈ ℓ) ))))

	(between : Point → Point → Point → Prop)
	(notation A `*` B `*` C := between A B C)
	
	(collinear : Point → Point → Point → Prop)
	(collinear_def : ∀ A B C, collinear A B C ↔ ∃ ℓ : Line, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ)

	(B11 {A B C} : (A * B * C) → (C * B * A))
	(B12 {A B C} : (A * B * C) → (A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ collinear A B C))
	(B2 {A B} : ∃ C, A * B * C)
	(B3 {A B C ℓ}
		(hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
		(hAl : A ∈ ℓ) (hBl : B ∈ ℓ) (hCl : C ∈ ℓ) :
		((A * B * C) ∧ ¬( B * A * C ) ∧ ¬ (A * C * B)) ∨ 
		(¬ (A * B * C) ∧ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
		(¬ (A * B * C) ∧ ¬( B * A * C ) ∧ (A * C * B)))

	(B4 {A B C D ℓ} -- Pasch
		(hnc: ¬ collinear A B C)
		(hnAl: ¬ (A ∈ ℓ)) (hnBl: ¬ B ∈ ℓ) (hnCl: ¬ C ∈ ℓ)
		(hDl: D ∈ ℓ) (hADB: A * D * B) :
            (∃ E ,  E ∈ ℓ ∧ (A * E * C)) xor (∃ E, E ∈ ℓ ∧ (B * E * C)))

	(intersect : Line → Line → Prop)
	(intersect_def {r s : Line} : (intersect r s ↔ ∃ A : Point, A ∈ r ∧ A ∈ s))

	(parallel : Line → Line → Prop)
	(parallel_def {r s} : parallel r s ↔  (r = s) ∨ (¬ (intersect r s)))
	(notation r `||` s := parallel r s)

	(parallel_postulate {A ℓ r s} :
		A ∈ r ∧ A ∈ s ∧ r || ℓ ∧ s || ℓ → r = s)

	(line_segment : Point → Point → set Point)
	(line_segment_def {A B} : line_segment A B = ({A} ∪ {B} ∪ {C | A * C * B}))
	(notation A `#` B := line_segment A B)
	(triangle : Point → Point → Point → set Point)
	(triangle_def {A B C}  (h: ¬ collinear A B C) : triangle A B C = (A#B) ∪ (A#C) ∪ (B#C))

notation A `*` B `*` C := HilbertPlane.between A B C
notation A `#` B := HilbertPlane.line_segment A B
notation r `||` s := HilbertPlane.parallel  r s
notation A `∈` ℓ := HilbertPlane.belongs A ℓ
notation A `∉` ℓ := ¬ HilbertPlane.belongs A ℓ

variables {Ω : HilbertPlane}
@[simp] lemma collinear_iff {A B C : Ω.Point} :
	HilbertPlane.collinear A B C ↔ ∃ ℓ : Ω.Line, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ :=
begin
	rw HilbertPlane.collinear_def,
end

@[simp] lemma intersect_iff {r s : Ω.Line} : HilbertPlane.intersect r s ↔ ∃ A : Ω.Point, A ∈ r ∧ A ∈ s :=
begin
	rw HilbertPlane.intersect_def,
end

def line_to_set : Ω.Line → set Ω.Point := λ ℓ , { P : Ω.Point | P ∈ ℓ}

instance line_to_set_coe (Ω : HilbertPlane) :
  has_coe (Ω.Line) (set Ω.Point) := ⟨line_to_set⟩


end hilbertplane