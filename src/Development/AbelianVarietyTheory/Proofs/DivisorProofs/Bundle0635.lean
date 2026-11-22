import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0629
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0614
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0616

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCoboundaryOfDegreeTwoImageCoboundaryAl
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

private theorem mn_ne (s : Finset κ) (h : s.Nonempty) : mn (ne s h) = s.min' h := rfl

private theorem min'_eq_of {s : Finset κ} (h : s.Nonempty) {m : κ} (hm : m ∈ s) (hle : ∀ x ∈ s, m ≤ x) :
    s.min' h = m :=
  le_antisymm (Finset.min'_le _ _ hm) (Finset.le_min' _ _ _ hle)

private theorem max'_eq_of {s : Finset κ} (h : s.Nonempty) {m : κ} (hm : m ∈ s) (hle : ∀ x ∈ s, x ≤ m) :
    s.max' h = m :=
  le_antisymm (Finset.max'_le _ _ _ hle) (Finset.le_max' _ _ hm)

private theorem mp_homOf_eq {p : ℕ} (y : CC F p) (s t : {s : Finset κ // s.card = p + 1}) (e : s.1 = t.1)
    (h : s.1 ⊆ t.1) :
    mp F (homOf (a := ne s.1 (card_nonempty s)) (b := ne t.1 (card_nonempty t)) h) (y s) = y t := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨t, ht⟩ := t
  simp only at e
  subst e
  exact mp_id F _ _

private theorem e2_of_not (y : CC F 2) {a b d : (NE κ)ᵒᵖ} (φ : a ⟶ b) (ψ : b ⟶ d)
    (h : ¬ (mn d < mn b ∧ mn b < mn a)) : e2 F y a b d φ ψ = 0 := by
  simp [e2, h]

private theorem e2_of_lt (y : CC F 2) (t : {s : Finset κ // s.card = 2 + 1}) {a b : (NE κ)ᵒᵖ} (φ : a ⟶ b)
    (ψ : b ⟶ ne t.1 (card_nonempty t)) (h₁ : mn (ne t.1 (card_nonempty t)) < mn b) (h₂ : mn b < mn a) :
    e2 F y a b _ φ ψ = - y t := by
  simp only [e2, LinearMap.pi_apply, dif_pos (And.intro h₁ h₂), LinearMap.neg_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
  congr 1
  exact mp_homOf_eq F y ⟨_, card_three h₁ h₂⟩ t
    (Finset.eq_of_subset_of_card_le (triple_subset φ ψ) (by rw [t.2, card_three h₁ h₂]))
    (triple_subset φ ψ)

private theorem f_single (f : C1 F) {m x : κ} (e : m = x) {T : (NE κ)ᵒᵖ}
    (φ : ne {m} (Finset.singleton_nonempty m) ⟶ T) (hx : ({x} : Finset κ) ⊆ sub T) :
    f _ T φ = f (ne {x} (Finset.singleton_nonempty x)) T (homOf hx) := by
  subst e; rfl

def cechOfPosetOne (f : C1 F) : CC F 1 := fun P =>
  f (ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P))
      (homOf (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _))) -
    f (ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P))
      (homOf (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _)))

variable {F}

private theorem restrict_of_d1 {y : CC F 2} {f : C1 F} (hf : e2 F y = d1 F f) {a P T : (NE κ)ᵒᵖ}
    (φ : a ⟶ P) (ψ : P ⟶ T) :
    mp F ψ (f a P φ) = f a T (φ ≫ ψ) - f P T ψ + e2 F y a P T φ ψ := by
  have := congrFun (congrFun (congrFun (congrFun (congrFun hf a) P) T) φ) ψ
  rw [d1_apply] at this
  rw [this]; abel

theorem restrict_cechOfPosetOne {y : CC F 2} {f : C1 F} (hf : e2 F y = d1 F f)
    (P : {s : Finset κ // s.card = 1 + 1}) (T : (NE κ)ᵒᵖ) (h : P.1 ⊆ sub T) :
    mp F (homOf (a := ne P.1 (card_nonempty P)) (b := T) h) (cechOfPosetOne F f P) =
      f (ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _)) T
        (homOf (b := ne P.1 (card_nonempty P)) (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _)) ≫ homOf h) -
      f (ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _)) T
        (homOf (b := ne P.1 (card_nonempty P)) (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _)) ≫ homOf h) +
      e2 F y (ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P)) T
        (homOf (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _))) (homOf h) -
      e2 F y (ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P)) T
        (homOf (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _))) (homOf h) := by
  simp only [cechOfPosetOne, map_sub]
  rw [restrict_of_d1 hf, restrict_of_d1 hf]
  abel

private theorem e2_min_single (y : CC F 2) (P : {s : Finset κ // s.card = 1 + 1}) (T : (NE κ)ᵒᵖ)
    (φ : ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _) ⟶ ne P.1 (card_nonempty P))
    (ψ : ne P.1 (card_nonempty P) ⟶ T) :
    e2 F y _ _ T φ ψ = 0 :=
  e2_of_not F y φ ψ (fun h => (lt_irrefl _) (h.2.trans_eq (Finset.min'_singleton _).symm))

private theorem e2_max_single_of_le (y : CC F 2) (P : {s : Finset κ // s.card = 1 + 1}) (T : (NE κ)ᵒᵖ)
    (φ : ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _) ⟶ ne P.1 (card_nonempty P))
    (ψ : ne P.1 (card_nonempty P) ⟶ T) (h : ¬ mn T < P.1.min' (card_nonempty P)) :
    e2 F y _ _ T φ ψ = 0 :=
  e2_of_not F y φ ψ (fun h' => h h'.1)

private theorem e2_max_single_of_lt (y : CC F 2) (P : {s : Finset κ // s.card = 1 + 1})
    (t : {s : Finset κ // s.card = 2 + 1})
    (φ : ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _) ⟶ ne P.1 (card_nonempty P))
    (ψ : ne P.1 (card_nonempty P) ⟶ ne t.1 (card_nonempty t))
    (h : mn (ne t.1 (card_nonempty t)) < P.1.min' (card_nonempty P)) :
    e2 F y _ _ _ φ ψ = - y t :=
  e2_of_lt F y t φ ψ h (by
    rw [mn_ne, mn_ne, Finset.min'_singleton]
    exact Finset.min'_lt_max'_of_card _ (by rw [P.2]; omega))

theorem delta_cechOfPosetOne_of_eq {y : CC F 2} {f : C1 F} (hf : e2 F y = d1 F f)
    (t : {s : Finset κ // s.card = 2 + 1}) {i j k : κ} (hij : i < j) (hjk : j < k)
    (ht : t.1 = {i, j, k}) : δ F 1 (cechOfPosetOne F f) t = y t := by
  have hik := hij.trans hjk
  have hi : i ∈ t.1 := by rw [ht]; simp
  have hj : j ∈ t.1 := by rw [ht]; simp
  have hk : k ∈ t.1 := by rw [ht]; simp
  have huniv : (Finset.univ : Finset t.1) = {⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩} := by
    ext ⟨x, hx⟩
    have hx' := hx
    rw [ht] at hx'
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
    simpa using hx'
  rw [δ_apply, huniv, Finset.sum_insert (by simp [hij.ne, hik.ne]), Finset.sum_insert (by simp [hjk.ne]),
    Finset.sum_singleton]
  erw [restrict_cechOfPosetOne hf, restrict_cechOfPosetOne hf, restrict_cechOfPosetOne hf]
  all_goals first | exact Finset.erase_subset _ _ | skip
  have hle : ∀ x ∈ t.1, i ≤ x := by
    intro x hx
    rw [ht] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    exacts [le_rfl, hij.le, hik.le]
  have tmin : mn (ne t.1 (card_nonempty t)) = i := min'_eq_of _ hi hle
  have mem3 : ∀ {x z : κ}, z ∈ t.1.erase x ↔ z ≠ x ∧ (z = i ∨ z = j ∨ z = k) := by
    intro x z; rw [ht]; simp
  have iMin : ∀ h, (Cube.eraseIdx t ⟨i, hi⟩).1.min' h = j := fun h =>
    min'_eq_of h (mem3.2 ⟨hij.ne', by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [absurd rfl hne, le_rfl, hjk.le])
  have iMax : ∀ h, (Cube.eraseIdx t ⟨i, hi⟩).1.max' h = k := fun h =>
    max'_eq_of h (mem3.2 ⟨hik.ne', by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [absurd rfl hne, hjk.le, le_rfl])
  have jMin : ∀ h, (Cube.eraseIdx t ⟨j, hj⟩).1.min' h = i := fun h =>
    min'_eq_of h (mem3.2 ⟨hij.ne, by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [le_rfl, absurd rfl hne, hik.le])
  have jMax : ∀ h, (Cube.eraseIdx t ⟨j, hj⟩).1.max' h = k := fun h =>
    max'_eq_of h (mem3.2 ⟨hjk.ne', by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [hik.le, absurd rfl hne, le_rfl])
  have kMin : ∀ h, (Cube.eraseIdx t ⟨k, hk⟩).1.min' h = i := fun h =>
    min'_eq_of h (mem3.2 ⟨hik.ne, by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [le_rfl, hij.le, absurd rfl hne])
  have kMax : ∀ h, (Cube.eraseIdx t ⟨k, hk⟩).1.max' h = j := fun h =>
    max'_eq_of h (mem3.2 ⟨hjk.ne, by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [hij.le, le_rfl, absurd rfl hne])
  have hiT : ({i} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t)) := Finset.singleton_subset_iff.2 hi
  have hjT : ({j} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t)) := Finset.singleton_subset_iff.2 hj
  have hkT : ({k} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t)) := Finset.singleton_subset_iff.2 hk
  have lI : mn (ne t.1 (card_nonempty t)) <
      (Cube.eraseIdx t ⟨i, hi⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨i, hi⟩)) := by
    rw [tmin, iMin]; exact hij
  have lJ : ¬ mn (ne t.1 (card_nonempty t)) <
      (Cube.eraseIdx t ⟨j, hj⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨j, hj⟩)) := by
    rw [tmin, jMin]; exact lt_irrefl _
  have lK : ¬ mn (ne t.1 (card_nonempty t)) <
      (Cube.eraseIdx t ⟨k, hk⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨k, hk⟩)) := by
    rw [tmin, kMin]; exact lt_irrefl _
  have sI : cubeSign t.1 i = 1 := cubeSign_eq_one_of_forall_le hle
  have sJ : cubeSign t.1 j = -1 := by
    rw [cubeSign, ht, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp [hij, hjk.not_gt, lt_irrefl]
  have sK : cubeSign t.1 k = 1 := by
    rw [cubeSign, ht, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp [hik, hjk, lt_irrefl, Finset.card_pair hij.ne]
  erw [e2_min_single y (Cube.eraseIdx t ⟨i, hi⟩) (ne t.1 (card_nonempty t)),
    e2_min_single y (Cube.eraseIdx t ⟨j, hj⟩) (ne t.1 (card_nonempty t)),
    e2_min_single y (Cube.eraseIdx t ⟨k, hk⟩) (ne t.1 (card_nonempty t)),
    e2_max_single_of_lt y (Cube.eraseIdx t ⟨i, hi⟩) t _ _ lI,
    e2_max_single_of_le y (Cube.eraseIdx t ⟨j, hj⟩) _ _ _ lJ,
    e2_max_single_of_le y (Cube.eraseIdx t ⟨k, hk⟩) _ _ _ lK,
    f_single F f (iMin _) _ hjT, f_single F f (iMax _) _ hkT,
    f_single F f (jMin _) _ hiT, f_single F f (jMax _) _ hkT,
    f_single F f (kMin _) _ hiT, f_single F f (kMax _) _ hjT]
  erw [sI, sJ, sK]
  simp only [one_smul, neg_smul, sub_zero, add_zero, sub_neg_eq_add]
  abel

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem exists_cech_coboundary_of_degreeTwo_image_coboundary : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (y : CC F 2), δ F 2 y = 0 → ∀ f : C1 F, e2 F y = d1 F f →
      ∃ c : CC F 1, δ F 1 c = y := by
  intro κ _ R _ F y _ f hf
  refine ⟨cechOfPosetOne F f, funext fun (t : {s : Finset κ // s.card = 2 + 1}) => ?_⟩
  obtain ⟨a, b, d, hab, had, hbd, ht⟩ := Finset.card_eq_three.1 t.2
  rcases lt_or_gt_of_ne hab with h₁ | h₁ <;> rcases lt_or_gt_of_ne had with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hbd with h₃ | h₃
  all_goals first
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : a < b) (by assumption : b < d)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : a < d) (by assumption : d < b)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : b < a) (by assumption : a < d)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : b < d) (by assumption : d < a)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : d < a) (by assumption : a < b)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : d < b) (by assumption : b < a)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact (lt_irrefl _ ((h₁.trans h₃).trans h₂)).elim
    | exact (lt_irrefl _ ((h₁.trans h₂).trans h₃)).elim

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleCohomologousPosetOneCocycle
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset.CechPosetH1Surjective

open GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq {a b : (NE κ)ᵒᵖ} (φ ψ : a ⟶ b) : φ = ψ :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

noncomputable def V (f : Z1 F) (b : (NE κ)ᵒᵖ) (x : κ) : F.obj b :=
  if hx : x ∈ sub b then
    f.1 (ne {x} (Finset.singleton_nonempty x)) b
      (homOf (show ({x} : Finset κ) ⊆ sub b from Finset.singleton_subset_iff.2 hx))
  else 0

variable {F}

theorem V_res (f : Z1 F) {a b : (NE κ)ᵒᵖ} (φ : a ⟶ b) {x : κ} (hx : x ∈ sub a) :
    mp F φ (V F f a x) = V F f b x - f.1 a b φ := by
  unfold V
  rw [dif_pos hx, dif_pos (sub_subset φ hx)]
  have e := Z1.comp f (homOf (a := ne {x} (Finset.singleton_nonempty x)) (b := a)
    (Finset.singleton_subset_iff.2 hx)) φ
  rw [hom_eq (_ ≫ φ) (homOf (a := ne {x} (Finset.singleton_nonempty x)) (b := b)
    (Finset.singleton_subset_iff.2 (sub_subset φ hx)))] at e
  rw [e]
  ring

noncomputable def zc (f : Z1 F) : CC F 1 := fun t =>
  V F f (ne t.1 (card_nonempty t)) (t.1.min' (card_nonempty t)) -
    V F f (ne t.1 (card_nonempty t)) (t.1.max' (card_nonempty t))

theorem zc_res (f : Z1 F) (s : {s : Finset κ // s.card = 1 + 1}) (b : (NE κ)ᵒᵖ)
    (h : sub (ne s.1 (card_nonempty s)) ⊆ sub b) :
    mp F (homOf h) (zc f s) = V F f b (s.1.min' (card_nonempty s)) - V F f b (s.1.max' (card_nonempty s)) := by
  unfold zc
  rw [map_sub, V_res f (homOf h) (x := s.1.min' (card_nonempty s)) (Finset.min'_mem _ _),
    V_res f (homOf h) (x := s.1.max' (card_nonempty s)) (Finset.max'_mem _ _)]
  ring

theorem pair_min_max {s : Finset κ} {x y : κ} (hs : s = {x, y}) (h : x < y) (hne : s.Nonempty) :
    s.min' hne = x ∧ s.max' hne = y := by
  subst hs
  constructor
  · exact le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by
      intro z hz; simp at hz; rcases hz with rfl | rfl
      · exact le_rfl
      · exact h.le))
  · exact le_antisymm (Finset.max'_le _ _ _ (by
      intro z hz; simp at hz; rcases hz with rfl | rfl
      · exact h.le
      · exact le_rfl)) (Finset.le_max' _ _ (by simp))

theorem exists_triple {s : Finset κ} (h : s.card = 3) : ∃ a b c, a < b ∧ b < c ∧ s = {a, b, c} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 h
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  all_goals first
    | exact absurd (h1.trans h3) (not_lt.2 h2.le)
    | exact absurd (h2.trans h3) (not_lt.2 h1.le)
    | exact absurd (h1.trans h2) (not_lt.2 h3.le)
    | exact absurd (h3.trans h1) (not_lt.2 h2.le)
    | exact absurd (h2.trans h1) (not_lt.2 h3.le)
    | exact absurd (h3.trans h2) (not_lt.2 h1.le)
    | (refine ⟨x, y, z, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨x, z, y, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨y, x, z, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨y, z, x, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨z, x, y, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨z, y, x, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)

end GlobalTheory.CechPoset.CechPosetH1Surjective

namespace GlobalTheory.CechPoset.CechPosetH1Surjective
open GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem erase3 {a b c : κ} (hab : a < b) (hbc : b < c) :
    ({a, b, c} : Finset κ).erase a = {b, c} ∧ ({a, b, c} : Finset κ).erase b = {a, c} ∧
      ({a, b, c} : Finset κ).erase c = {a, b} := by
  have hac := hab.trans hbc
  refine ⟨?_, ?_, ?_⟩ <;> ext w <;> simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] <;>
    constructor
  all_goals first
    | (rintro ⟨hw, h | h | h⟩ <;> first | exact absurd h hw | (subst h; simp))
    | (rintro (h | h) <;> subst h <;> simp [hab.ne, hab.ne', hbc.ne, hbc.ne', hac.ne, hac.ne'])

theorem sign3 {a b c : κ} (hab : a < b) (hbc : b < c) :
    GlobalTheory.cubeSign ({a, b, c} : Finset κ) a = 1 ∧ GlobalTheory.cubeSign ({a, b, c} : Finset κ) b = -1 ∧
      GlobalTheory.cubeSign ({a, b, c} : Finset κ) c = 1 := by
  have hac := hab.trans hbc
  refine ⟨?_, ?_, ?_⟩ <;> simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, hab, hbc, hac,
    not_lt.2 hab.le, not_lt.2 hbc.le, not_lt.2 hac.le, Finset.card_pair hab.ne]

theorem part2 (f : Z1 F) : f.1 - e1 F (zc f) = d0 F (fun a => V F f a (mn a)) := by
  funext a b φ
  simp only [Pi.sub_apply, amitsur_d0_apply]
  rw [V_res f φ (mn_mem a)]
  by_cases h : mn b < mn a
  · have e : e1 F (zc f) a b φ = -(mp F (homOf (a := ne {mn b, mn a} (Finset.insert_nonempty _ _)) (b := b)
        (pair_subset φ)) (zc f ⟨{mn b, mn a}, Finset.card_pair h.ne⟩)) := by
      simp [e1, h]
    have z := zc_res f ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ b (pair_subset φ)
    obtain ⟨h1, h2⟩ := pair_min_max (s := ({mn b, mn a} : Finset κ)) rfl h (Finset.insert_nonempty _ _)
    rw [h1, h2] at z
    rw [e]
    linear_combination z
  · have e : e1 F (zc f) a b φ = 0 := by simp [e1, h]
    have e' : mn b = mn a := le_antisymm (mn_le_of_hom φ) (not_lt.1 h)
    rw [e, e']
    ring

end GlobalTheory.CechPoset.CechPosetH1Surjective

namespace GlobalTheory.CechPoset.CechPosetH1Surjective
open GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

def term3 {M : Type} [AddCommGroup M] (W : κ → M) (a b c x : κ) : M :=
  GlobalTheory.cubeSign ({a, b, c} : Finset κ) x • (if x = a then W b - W c else if x = b then W a - W c else W a - W b)

theorem sum3 {M : Type} [AddCommGroup M] (W : κ → M) {a b c : κ} (hab : a < b) (hbc : b < c) :
    ∑ x ∈ ({a, b, c} : Finset κ), term3 W a b c x = 0 := by
  have hac := hab.trans hbc
  rw [Finset.sum_insert (by simp [hab.ne, hac.ne]), Finset.sum_insert (by simp [hbc.ne]),
    Finset.sum_singleton]
  obtain ⟨s1, s2, s3⟩ := sign3 hab hbc
  simp only [term3, if_pos rfl, if_neg hab.ne', if_neg hac.ne', if_neg hbc.ne', s1, s2, s3, one_smul, neg_smul]
  norm_num

theorem part1 (f : Z1 F) : δ F 1 (zc f) = 0 := by
  funext t
  rw [δ_apply]
  obtain ⟨s, hs⟩ := t
  obtain ⟨a, b, c, hab, hbc, rfl⟩ := exists_triple (s := s) (by rw [hs])
  have hac := hab.trans hbc
  obtain ⟨e1', e2', e3'⟩ := erase3 hab hbc
  refine (Finset.sum_congr rfl
    (g := fun i : ({a, b, c} : Finset κ) => term3 (V F f (ne {a, b, c} (card_nonempty ⟨_, hs⟩))) a b c i.1)
    fun i _ => ?_).trans ?_
  · have z := zc_res f (GlobalTheory.Cube.eraseIdx ⟨{a, b, c}, hs⟩ i) (ne _ (card_nonempty ⟨_, hs⟩))
      (Finset.erase_subset i.1 _)
    rw [z]
    obtain ⟨x, hx⟩ := i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{x, b, c}, hs⟩ ⟨x, by simp⟩).1) e1' hbc
        (card_nonempty _)
      rw [h1, h2, term3, if_pos rfl]
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{a, x, c}, hs⟩ ⟨x, by simp⟩).1) e2' hac
        (card_nonempty _)
      rw [h1, h2, term3, if_neg hab.ne', if_pos rfl]
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{a, b, x}, hs⟩ ⟨x, by simp⟩).1) e3' hab
        (card_nonempty _)
      rw [h1, h2, term3, if_neg hac.ne', if_neg hbc.ne']
  · refine (Finset.sum_coe_sort ({a, b, c} : Finset κ)
      (term3 (V F f (ne {a, b, c} (card_nonempty ⟨_, hs⟩))) a b c)).trans ?_
    exact sum3 _ hab hbc

end GlobalTheory.CechPoset.CechPosetH1Surjective

open GlobalTheory.CechPoset.CechPosetH1Surjective in

theorem GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (f : Z1 F),
    ∃ z : CC F 1, δ F 1 z = 0 ∧ ∃ g : C0 F, f.1 - e1 F z = d0 F g :=
  fun F f => ⟨zc f, part1 f, fun a => V F f a (mn a), part2 f⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeIntersectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_intersection : ∀ (H Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ H) (i₂ : Z₂ ⟶ H), IsClosedImmersion i₁ → IsClosedImmersion i₂ → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ (∃ z, z ≫ i₁ = h) ∧ ∃ z, z ≫ i₂ = h := by
  first | (exact @GlobalTheory.closedSubscheme_inter_exists) | (exact GlobalTheory.closedSubscheme_inter_exists) | (intros; apply GlobalTheory.closedSubscheme_inter_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCohomologyDerivativeRelationOfFrameStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cohomologyDerivativeRelation_of_frame : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → ∀ x : GlobalTheory.CatCoh.H1 F, ∃ (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w := by
  first | exact @GlobalTheory.AbCoh.dRel_of_frame_exists | exact GlobalTheory.AbCoh.dRel_of_frame_exists | (intros; apply GlobalTheory.AbCoh.dRel_of_frame_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePrimePowerRoots
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_prime_power_roots : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharZero k], ∃ ζ : ℕ → kˣ, (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) ∧ ∀ r, ζ (r + 1) ^ p = ζ r := by
  first | (exact @GlobalTheory.exists_compatible_primitive_prime_pow_roots) | (exact GlobalTheory.exists_compatible_primitive_prime_pow_roots) | (intros; apply GlobalTheory.exists_compatible_primitive_prime_pow_roots  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSimilitudeLevelTowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_similitude_level_tower : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (W : ℕ → Q → Q → kˣ) (ζ : ℕ → kˣ), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ r, ζ (r + 1) ^ p = ζ r) → (∀ r (a b : Q), a ^ (p ^ (r + 1)) = 1 → b ^ (p ^ (r + 1)) = 1 → W r (a ^ p) (b ^ p) = W (r + 1) a b ^ p) → (∀ r, ∃ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) ∧ ∀ x y, W r (f x) (f y) = ζ r ^ D.EF x y) → ∃ ev : ℕ → D.La → Q, (∀ r, ((∀ x y, ev r (x + y) = ev r x * ev r y) ∧ (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) ∧ ∀ x y, W r (ev r x) (ev r y) = ζ r ^ D.EF x y) ∧ ∀ r x, ev (r + 1) x ^ p = ev r x := by
  first | (exact @GlobalTheory.TowerLev.exists_compatible) | (exact GlobalTheory.TowerLev.exists_compatible) | (intros; apply GlobalTheory.TowerLev.exists_compatible  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjIdempotentModPrimePowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_idempotent_mod_prime_pow : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℕ), ∃ ε u v : 𝓞 D.F, ε + D.bar ε = 1 + (p : 𝓞 D.F) ^ r * u ∧ ε * D.bar ε = (p : 𝓞 D.F) ^ r * v := by
  first | (exact @GlobalTheory.UPel.HT.SplitIdem.exists_conj_idem) | (exact GlobalTheory.UPel.HT.SplitIdem.exists_conj_idem) | (intros; apply GlobalTheory.UPel.HT.SplitIdem.exists_conj_idem  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullSymplecticLevelStructureOfTateIsoStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullSymplecticLevelStructure_of_tateIso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    {z : kˣ}, IsPrimitiveRoot z l.M' → z ^ (l.M' / l.A) = I.ζ l.A →
    ∃ ev : D.La → Q, IsSympLevel D act e l.M' z ev ∧ Induces l (I.ev l.A) (I.ev l.M) ev := by
  first | exact @GlobalTheory.FullLevel.exists_sympLevel_of_tate | exact GlobalTheory.FullLevel.exists_sympLevel_of_tate | (intros; apply GlobalTheory.FullLevel.exists_sympLevel_of_tate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitRatioGenericLineBundleIsosStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_unit_ratio_generic_lineBundle_isos : ∀ (X Y : Scheme.{0}) (β : Y ⟶ X) (P M : LB X) (N : LB Y), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull β) N) (w₁ : LB.Iso (P.pull β) N) (v : LB.Iso P M), w.IsGen → w₁.IsGen → v.IsGen → ∃ u : Γ(Y, ⊤)ˣ, ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ β ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (P.pull β).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.rs _ (le_top : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ ⊤) (u : Γ(Y, ⊤)) * (β.appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (M.pull β).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  first | exact @GlobalTheory.GenIsoRatio.ratio | exact GlobalTheory.GenIsoRatio.ratio | (intros; apply GlobalTheory.GenIsoRatio.ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeBaseChangeHomOfGrpPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_groupScheme_baseChange_hom_of_grpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G A : Over S) [GrpObj G] [GrpObj A] (G' A' : Over S') [GrpObj G'] [GrpObj A'] (φG : G'.left ⟶ G.left) (φA : A'.left ⟶ A.left) (p : G ⟶ A), IsGrpPullback G' G f φG → IsGrpPullback A' A f φA → IsMonHom p → ∃ p' : G' ⟶ A', IsMonHom p' ∧ p'.left ≫ φA = φG ≫ p.left := by
  first | (exact @GlobalTheory.GrpBC.exists_baseChange_hom) | (exact GlobalTheory.GrpBC.exists_baseChange_hom) | (intros; apply GlobalTheory.GrpBC.exists_baseChange_hom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutDataStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pushout_data_on_basis : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ → (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₁.app U).hom)) → (∀ U : Y₂.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₂.app U).hom)) → ∃ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ ∧ IsClosedImmersion j₂ ∧ Surjective j₁ ∧ Surjective j₂ ∧ ∃ 𝒱 : Set Y.Opens, TopologicalSpace.Opens.IsBasis 𝒱 ∧ ∀ V ∈ 𝒱, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  first | exact @GlobalTheory.FerrandPush.exists_pushout_data | exact GlobalTheory.FerrandPush.exists_pushout_data | (intros; apply GlobalTheory.FerrandPush.exists_pushout_data <;> assumption)
end

