import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
import ReciprocityTheory.DualLattices.Bundle0018
import ReciprocityTheory.DualLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionEndomorphismWeightBoundStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_action_endomorphism_weight_bound : GlobalTheory.LeviCut.AdjBdd := by
  first | exact @GlobalTheory.LeviCut.adjBdd_holds | exact GlobalTheory.LeviCut.adjBdd_holds | (intros; apply GlobalTheory.LeviCut.adjBdd_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingToOrderedCechDegreeTwoMemCocyclesTwo
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

def triVal (c : CC F 2) (X : (NE κ)ᵒᵖ) (s : Finset κ) : F.obj X :=
  if h : s.card = 2 + 1 ∧ s ⊆ sub X then
    mp F (homOf (a := ne s (card_nonempty ⟨s, h.1⟩)) (b := X) h.2) (c ⟨s, h.1⟩)
  else 0

variable {F}

theorem hom_eq {a b : (NE κ)ᵒᵖ} (f g : a ⟶ b) : f = g := Subsingleton.elim _ _

theorem triVal_eq (c : CC F 2) (X : (NE κ)ᵒᵖ) {s : Finset κ} (hs : s.card = 2 + 1) (h : s ⊆ sub X) :
    mp F (homOf (a := ne s (card_nonempty ⟨s, hs⟩)) (b := X) h) (c ⟨s, hs⟩) = triVal F c X s := by
  unfold triVal; rw [dif_pos ⟨hs, h⟩]

theorem triVal_map (c : CC F 2) {X Y : (NE κ)ᵒᵖ} (f : X ⟶ Y) {s : Finset κ} (h : s ⊆ sub X) :
    mp F f (triVal F c X s) = triVal F c Y s := by
  unfold triVal
  by_cases hs : s.card = 2 + 1
  · rw [dif_pos ⟨hs, h⟩, dif_pos ⟨hs, h.trans (sub_subset f)⟩, ← mp_comp]
    congr 1
  · rw [dif_neg (fun h' => hs h'.1), dif_neg (fun h' => hs h'.1), map_zero]

theorem alternatingToOrderedCechDegreeTwo_apply_triple (c : CC F 2) {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    e2 F c a b d f g = if mn d < mn b ∧ mn b < mn a then -triVal F c d {mn d, mn b, mn a} else 0 := by
  unfold e2
  simp only [LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [← triVal_eq c d (card_three h.1 h.2) (triple_subset f g)]
    rfl
  · rfl

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem triVal_eq' (c : CC F 2) {X : (NE κ)ᵒᵖ} (s : {s : Finset κ // s.card = 2 + 1})
    (f : ne s.1 (card_nonempty s) ⟶ X) : mp F f (c s) = triVal F c X s.1 := by
  obtain ⟨s, hs⟩ := s
  rw [← triVal_eq c X hs (sub_subset f), hom_eq f (homOf (sub_subset f))]

theorem triVal_rel (c : CC F 2) (hc : δ F 2 c = 0) (X : (NE κ)ᵒᵖ) {w x y z : κ}
    (h1 : w < x) (h2 : x < y) (h3 : y < z) (hs : ({w, x, y, z} : Finset κ) ⊆ sub X) :
    triVal F c X {x, y, z} - triVal F c X {w, y, z} + triVal F c X {w, x, z} - triVal F c X {w, x, y} = 0 := by
  have ht : ({w, x, y, z} : Finset κ).card = 2 + 1 + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [h1.ne, (h1.trans h2).ne, (h1.trans (h2.trans h3)).ne]),
      Finset.card_insert_of_notMem (by simp [h2.ne, (h2.trans h3).ne]), Finset.card_pair h3.ne]
  have e := congrArg (mp F (homOf (a := ne _ (card_nonempty ⟨_, ht⟩)) (b := X) hs))
    (congrFun hc ⟨_, ht⟩)
  rw [δ_apply, map_sum, Pi.zero_apply, map_zero] at e
  have e' : ∑ i ∈ ({w, x, y, z} : Finset κ), GlobalTheory.cubeSign ({w, x, y, z} : Finset κ) i •
      triVal F c X (({w, x, y, z} : Finset κ).erase i) = 0 := by
    rw [← e, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← mp_comp, triVal_eq']
  rw [Finset.sum_insert (by simp [h1.ne, (h1.trans h2).ne, (h1.trans (h2.trans h3)).ne]),
    Finset.sum_insert (by simp [h2.ne, (h2.trans h3).ne]), Finset.sum_pair h3.ne] at e'
  have hwx := h1.ne; have hwy := (h1.trans h2).ne; have hwz := (h1.trans (h2.trans h3)).ne
  have hxy := h2.ne; have hxz := (h2.trans h3).ne; have hyz := h3.ne
  simp only [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h1, h2, h3, h1.trans h2,
    h1.trans (h2.trans h3), h2.trans h3, lt_irrefl, not_lt_of_gt, if_true, if_false] at e'
  simp only [Finset.insert_empty, Finset.card_empty, Finset.card_singleton,
    Finset.card_pair hwx, Finset.card_insert_of_notMem (show w ∉ ({x, y} : Finset κ) by simp [hwx, hwy]),
    Finset.card_pair hxy] at e'
  rw [Finset.erase_insert (by simp [hwx, hwy, hwz]),
    Finset.erase_insert_of_ne hwx, Finset.erase_insert (by simp [hxy, hxz]),
    Finset.erase_insert_of_ne hwy, Finset.erase_insert_of_ne hxy,
    Finset.erase_insert (by simp [hyz]),
    Finset.erase_insert_of_ne hwz, Finset.erase_insert_of_ne hxz,
    Finset.erase_insert_of_ne hyz, Finset.erase_singleton] at e'
  norm_num at e'
  linear_combination e'

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem alternatingToOrderedCechDegreeTwo_map_apply (c : CC F 2) {a b d g : (NE κ)ᵒᵖ} (f : a ⟶ b) (f' : b ⟶ d) (f'' : d ⟶ g) :
    mp F f'' (e2 F c a b d f f') =
      if mn d < mn b ∧ mn b < mn a then -triVal F c g {mn d, mn b, mn a} else 0 := by
  rw [alternatingToOrderedCechDegreeTwo_apply_triple]
  split_ifs
  · rw [map_neg, triVal_map c f'' (triple_subset f f')]
  · exact map_zero _

theorem e2_mem_Z2_of_delta_eq_zero (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 2) (hc : δ F 2 c = 0) :
    e2 F c ∈ Z2 F := by
  intro a b d g φ ψ χ
  have hab := mn_le_of_hom φ; have hbd := mn_le_of_hom ψ; have hdg := mn_le_of_hom χ
  have hs : ({mn g, mn d, mn b, mn a} : Finset κ) ⊆ sub g := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mn_mem g
    · exact sub_subset χ (mn_mem d)
    · exact sub_subset (ψ ≫ χ) (mn_mem b)
    · exact sub_subset (φ ≫ ψ ≫ χ) (mn_mem a)
  have hrel : mn g < mn d → mn d < mn b → mn b < mn a →
      triVal F c g {mn d, mn b, mn a} - triVal F c g {mn g, mn b, mn a} +
        triVal F c g {mn g, mn d, mn a} - triVal F c g {mn g, mn d, mn b} = 0 :=
    fun h1 h2 h3 => triVal_rel c hc g h1 h2 h3 hs
  rw [alternatingToOrderedCechDegreeTwo_map_apply, alternatingToOrderedCechDegreeTwo_apply_triple, alternatingToOrderedCechDegreeTwo_apply_triple, alternatingToOrderedCechDegreeTwo_apply_triple]
  generalize mn a = xa at *
  generalize mn b = xb at *
  generalize mn d = xd at *
  generalize mn g = xg at *
  rcases hdg.lt_or_eq with h1 | rfl <;> rcases hbd.lt_or_eq with h2 | rfl <;>
    rcases hab.lt_or_eq with h3 | rfl <;>
    simp_all [lt_irrefl, not_lt_of_ge, le_of_lt]
  rw [if_pos (h2.trans h3), if_pos (h1.trans h2)]
  linear_combination -hrel
end GlobalTheory.CechPoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchFactorMulPSeriesEqIntegralStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archFactor_mul_pSeries_eq_integral_alt : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (F : NumberField.RingOfIntegers K → ℂ) (C : ℝ), (∀ α, ‖F α‖ ≤ C) → (∀ (u : (NumberField.RingOfIntegers K)ˣ) (α : NumberField.RingOfIntegers K), F ((u : NumberField.RingOfIntegers K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : NumberField.RingOfIntegers K) * α : NumberField.RingOfIntegers K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∀ p : (I → ℝ) → ℝ, Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) → ∀ s : ℂ, 1 < s.re → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s = 2 ^ Fintype.card I * ∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral | exact GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral | (intros; apply GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLocalFiniteLengthAndSocleElementStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem : ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R], (∃ n : ℕ, Module.length R R = n) ∧ (¬ IsField R → ∃ t : R, t ≠ 0 ∧ (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) ∧ Module.length (R ⧸ Ideal.span {t}) (R ⧸ Ideal.span {t}) < Module.length R R) := by
  first | exact @GlobalTheory.artinianLocal_finiteLength_and_socle_element | exact GlobalTheory.artinianLocal_finiteLength_and_socle_element | (intros; apply GlobalTheory.artinianLocal_finiteLength_and_socle_element <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechBijectiveOfAffine
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_bijective {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') (V : X'.Opens) : Function.Bijective (trivCoord φ s' V) :=
  (GlobalTheory.AbLaw.SecOn.chart (LB.isLB_pull (LB.isLB_triv X) φ) (i0 φ)
    (by rw [triv_pull_U]; exact le_top)).bijective

theorem Φ_bijective_of_affine : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (h : IsPullback φ s' s (spMap (algebraMap R R'))) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), (∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) → ∀ p : ℕ, Function.Bijective (Φ h.w D hD' p) := by
  intro R R' _ _ _ X X' s s' φ h κ _ _ D hD' hD p
  have hB := GlobalTheory.AbLaw.secTermBaseChange_bijective (M := LB.triv X) (D := D) (LB.isLB_triv X) h (p + 1)
    fun t ht => hD t (Finset.card_pos.1 (by omega))
  exact (Function.Bijective.piMap fun t => trivCoord_bijective φ s' _).comp hB

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechDifferentialComm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_restrict {X X' : Scheme.{0}} {R' : Type} [CommRing R'] (φ : X' ⟶ X) (s' : X' ⟶ Sp R')
    {V W : X'.Opens} (h : W ≤ V) (x : GlobalTheory.AbLaw.SecOnR s' ((LB.triv X).pull φ) V) :
    trivCoord φ s' W (GlobalTheory.AbLaw.SecOnR.restrict s' _ h x) = Sec.res s' h (trivCoord φ s' V x) := by
  simp only [trivCoord, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.AbLaw.SecOnR.coord_restrict]
  change (X'.presheaf.map _ ≫ X'.presheaf.map _).hom _ = (X'.presheaf.map _ ≫ X'.presheaf.map _).hom _
  rw [← Functor.map_comp, ← Functor.map_comp]; rfl

theorem Φ_apply {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R}
    {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ]
    (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (q : ℕ)
    (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X q)
    (t : {s : Finset κ // s.card = q + 1}) :
    Φ w D hD' q x t = trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (q + 1) x t) :=
  rfl

theorem trivCoord_d {R' : Type} [CommRing R'] {X X' : Scheme.{0}} {s' : X' ⟶ Sp R'} (φ : X' ⟶ X) {κ : Type}
    [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i))
    (p : ℕ) (y : GlobalTheory.Cube.Term (GlobalTheory.AbLaw.secCube s' ((LB.triv X).pull φ) fun i => φ ⁻¹ᵁ D i) (p + 1))
    (t : {s : Finset κ // s.card = p + 1 + 1}) :
    trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (GlobalTheory.Cube.d _ (p + 1) y t) =
      δ (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p (fun u => trivCoord φ s' (⨅ i ∈ u.1, φ ⁻¹ᵁ D i) (y u)) t := by
  refine (congrArg (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) (GlobalTheory.Cube.d_apply _ (p + 1) y t)).trans ?_
  refine ((map_sum (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) _ _)).trans ?_
  refine Eq.trans ?_ (δ_apply (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p _ t).symm
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (map_zsmul (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) _ _).trans ?_
  congr 1
  exact trivCoord_restrict φ s' _ _

theorem Φ_dB : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p), Φ w D hD' (p + 1) (dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x) = δ _ p (Φ w D hD' p x) := by
  intro R R' _ _ _ X X' s s' φ w κ _ D hD' p x
  have e1 : dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x =
      (GlobalTheory.Cube.d (GlobalTheory.AbLaw.secCube s (LB.triv X) D) (p + 1)).baseChange R' x := by
    simp only [dB, GlobalTheory.AbLaw.cechLB_d]; rfl
  have e2 := GlobalTheory.AbLaw.d_secTermBaseChange (LB.triv X) D w (p + 1) x
  funext t
  refine (Φ_apply w D hD' (p + 1) _ t).trans ?_
  refine (congrArg (fun z => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)
    (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (p + 1 + 1) z t)) e1).trans ?_
  refine (congrArg (fun z => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (z t)) e2.symm).trans ?_
  exact trivCoord_d φ D hD' p _ t

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechOneTmul
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset

theorem Φ_one_tmul : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), Φ w D hD' 0 ((1 : R') ⊗ₜ[R] one s D) = fun _ => 1 := by
  intro R R' _ _ _ X X' s s' φ w κ _ D hD'
  funext t
  have key : GlobalTheory.AbLaw.SecOnR.coord (f := s') (M := (LB.triv X).pull φ) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w 1 ((1 : R') ⊗ₜ[R] one s D) t) (i0 φ) = 1 := by
    erw [GlobalTheory.AbLaw.secTermBaseChange_tmul, one_smul]
    refine (GlobalTheory.AbLaw.SecOn.coord_pullLE (M := LB.triv X) φ (GlobalTheory.AbLaw.preimage_biInf D φ t.1).ge ((GlobalTheory.AbLaw.secOnTrivEquiv _).symm 1) (i0 φ)).trans ?_
    have hc : GlobalTheory.LB.coord ((GlobalTheory.AbLaw.secOnTrivEquiv (X := X) (⨅ i ∈ t.1, D i)).symm 1) PUnit.unit = 1 := by
      refine (GlobalTheory.AbLaw.SecOn.coord_chart_symm (M := Out.Inh.trivLB X) (Out.Inh.trivLB_isLB X) PUnit.unit PUnit.unit le_top (1 : Γ(X, ⨅ i ∈ t.1, D i))).trans ?_
      rw [map_one]
      exact (_root_.one_mul _).trans (map_one _)
    exact (congrArg _ hc).trans (map_one _)
  change Sec.res s' _ (GlobalTheory.AbLaw.SecOnR.coord (f := s') (M := (LB.triv X).pull φ) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w 1 ((1 : R') ⊗ₜ[R] one s D) t) (i0 φ)) = 1
  rw [key]
  exact (Sec.res s' _).map_one

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechPullbackComm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_pull_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {g' : R →+* R'} {g'' : R →+* R''}
    {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X}
    (w' : φ ≫ s = s' ≫ spMap g') (w'' : φ' ≫ s = s'' ≫ spMap g'') (ψ : X'' ⟶ X') (h : ψ ≫ φ = φ')
    (V : X.Opens) (V' : X'.Opens) (V'' : X''.Opens) (e' : V' ≤ φ ⁻¹ᵁ V) (e'' : V'' ≤ φ' ⁻¹ᵁ V) (e : V'' ≤ ψ ⁻¹ᵁ V')
    (x : GlobalTheory.AbLaw.SecOnR s (LB.triv X) V) :
    trivCoord φ' s'' V'' (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w'' V V'' e'' x) =
      (ψ.appLE V' V'' e).hom (trivCoord φ s' V' (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w' V V' e' x)) := by
  subst h
  have k : ∀ {Y : Scheme.{0}} {S : Type} [CommRing S] {g : R →+* S} (t : Y ⟶ Sp S) (π : Y ⟶ X)
      (w : π ≫ s = t ≫ spMap g) (O : Y.Opens) (eO : O ≤ π ⁻¹ᵁ V) (e2 : O ≤ π ⁻¹ᵁ (V ⊓ (LB.triv X).U PUnit.unit)),
      trivCoord π t O (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w V O eO x) =
        (π.appLE _ O e2).hom (x.coord PUnit.unit) := by
    intro Y S _ g t π w O eO e2
    have := GlobalTheory.AbLaw.SecOn.coord_pullLE π eO ((GlobalTheory.AbLaw.SecOnR.of s (LB.triv X) V).symm x) (i0 π)
    refine (congrArg (Sec.res t (le_inf le_rfl (by rw [triv_pull_U]; exact le_top))) this).trans ?_
    exact GlobalTheory.LB.resG_appLE π _ _ _
  have e2 : V' ≤ φ ⁻¹ᵁ (V ⊓ (LB.triv X).U PUnit.unit) := fun y hy => ⟨e' hy, trivial⟩
  rw [k s' φ w' V' e' e2, k s'' (ψ ≫ φ) w'' V'' e'' (fun y hy => e2 (e hy))]
  exact (congrArg (fun q => q.hom (x.coord PUnit.unit)) (Scheme.Hom.appLE_comp_appLE ψ φ _ V' V'' e2 e)).symm

theorem Φ_ext_eq_pullCoef : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R'] [Algebra R R''] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X} (w' : φ ≫ s = s' ≫ spMap (algebraMap R R')) (w'' : φ' ≫ s = s'' ≫ spMap (algebraMap R R'')) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X') (wψ : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' → ∀ {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ' ⁻¹ᵁ D i)) (hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i)) (p : ℕ) (z : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p) (t : {s : Finset κ // s.card = p + 1}), Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ z) t = (pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)) (Φ w' D hD' p z t) := by
  intro R R' R'' _ _ _ _ _ X X' X'' s s' s'' φ φ' w' w'' α ψ wψ h κ _ D hD' hD'' hle p z t
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
    exact (map_zero ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)))).symm
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    exact (congrArg₂ (· + ·) hx hy).trans (map_add ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) _ _).symm
  | tmul r x =>
    have a1 : Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ (r ⊗ₜ x)) t = trivCoord φ' s'' _ (α r • GlobalTheory.AbLaw.secCubePull (LB.triv X) D w'' t.1 (x t)) := rfl
    have a2 : Φ w' D hD' p (r ⊗ₜ x) t = trivCoord φ s' _ (r • GlobalTheory.AbLaw.secCubePull (LB.triv X) D w' t.1 (x t)) := rfl
    refine a1.trans (Eq.trans ?_ (congrArg ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) a2).symm)
    refine ((trivCoord φ' s'' _).map_smul _ _).trans ?_
    refine Eq.trans ?_ (congrArg ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) ((trivCoord φ s' _).map_smul _ _)).symm
    refine Eq.trans ?_ ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).smul (ne t.1 (card_nonempty t)) r _).symm
    exact congrArg (α r • ·) (trivCoord_pull_comp w' w'' ψ h _ _ _ _ _ (pr _ hD' _ hD'' hle (ne t.1 (card_nonempty t)).unop).2 (x t))

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaIntegralDenominatorBoundStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_integral_denominator_bound : GlobalTheory.LeviCut.BetaDen := by
  first | exact @GlobalTheory.LeviCut.betaDen | exact GlobalTheory.LeviCut.betaDen | (intros; apply GlobalTheory.LeviCut.betaDen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigMatConjTransposeMul
section
open Classical

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.MinorFrame.FockRowSub

variable {ι : Type} [Fintype ι] {a d : ℕ}

def rowEquiv (ι : Type) [Fintype ι] (d : ℕ) : Fin d × ι ≃ Fin (Fintype.card (Fin d × ι)) :=
  Fintype.equivFin _

def varFlat (ι : Type) [Fintype ι] (d a : ℕ) : Var ι d a → Fin (Fintype.card (Fin d × ι)) × Fin a :=
  fun y => (rowEquiv ι d (y.2.1, y.1), y.2.2)

theorem varFlat_injective : Function.Injective (varFlat ι d a) := by
  intro y z h
  simp only [varFlat, Prod.mk.injEq] at h
  have h1 := (rowEquiv ι d).injective h.1
  simp only [Prod.mk.injEq] at h1
  exact Prod.ext h1.2 (Prod.ext h1.1 h.2)

def bigMat (κ : ι → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (Fintype.card (Fin d × ι))) (Fin (Fintype.card (Fin d × ι))) ℂ :=
  (blockDiagonal κ).submatrix (rowEquiv ι d).symm (rowEquiv ι d).symm

theorem rename_rowSub (κ : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    rename (varFlat ι d a) (rowSub κ P) = ReciprocityTheory.PGsh.rowSubst (bigMat κ) (rename (varFlat ι d a) P) := by
  have key : (rename (varFlat ι d a)).comp (rowSub κ) =
      (ReciprocityTheory.PGsh.rowSubst (bigMat κ)).comp (rename (varFlat ι d a)) := by
    refine MvPolynomial.algHom_ext fun y => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rowSub, aeval_X, rename_X, ReciprocityTheory.PGsh.rowSubst_X,
      ← (rowEquiv ι d).sum_comp, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single y.1]
    · simp only [map_sum, map_mul, rename_C, rename_X, bigMat, submatrix_apply, varFlat, Equiv.symm_apply_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [blockDiagonal_apply_eq]
    · intro τ _ hτ
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [bigMat, varFlat, blockDiagonal_apply_ne _ _ _ hτ]
    · simp
  exact congrArg (fun f => f P) key

theorem bigMat_conjTranspose_mul (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    (bigMat fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ))ᴴ * bigMat (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  rw [bigMat, conjTranspose_submatrix, submatrix_mul_equiv, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  have h : ∀ τ, (κ τ : Matrix (Fin d) (Fin d) ℂ)ᴴ * (κ τ : Matrix (Fin d) (Fin d) ℂ) = 1 := fun τ => by
    have := (κ τ).2
    rw [Matrix.mem_unitaryGroup_iff'] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  simp only [h]
  rw [show (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) = (1 : ι → Matrix (Fin d) (Fin d) ℂ) from rfl,
    blockDiagonal_one, submatrix_one_equiv]

theorem fockS_eq_fischer {ν : ℕ} {κ : Type} (f g : MvPolynomial (Fin ν × κ) ℂ) :
    Formalism.L2.DIV.fockS f g = ReciprocityTheory.PGsh.fischer g f := by
  rw [Formalism.L2.DIV.fockS_eq_sum f g (g.support ∪ f.support) Finset.subset_union_right, ReciprocityTheory.PGsh.fischer]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Formalism.L2.DIV.mfact, Finsupp.prod, RCLike.star_def]
  ring

end GlobalTheory.MinorFrame.FockRowSub

namespace GlobalTheory.MinorFrame

open FockRowSub

theorem fockS_rowSub_unitary {ι : Type} [Fintype ι] (a d : ℕ) (κ : ι → Matrix.unitaryGroup (Fin d) ℂ)
    (P Q : Pol ι d a) :
    Formalism.L2.DIV.fockS (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P)
      (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  rw [← GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename varFlat_injective, rename_rowSub, rename_rowSub, fockS_eq_fischer,
    ReciprocityTheory.PGsh.fischer_rowSubst, ReciprocityTheory.PGsh.rowSubst_mul, bigMat_conjTranspose_mul, ReciprocityTheory.PGsh.rowSubst_one,
    ← fockS_eq_fischer, GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename varFlat_injective]

end GlobalTheory.MinorFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfSplitInjectiveFgProjectiveConstantRanStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank : ∀ (R : Type) [CommRing R] (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ), FP R M n → FP R N n → ∀ (f : M →ₗ[R] N) (r : N →ₗ[R] M), (∀ x, r (f x) = x) → Function.Bijective f := by
  first | exact @GlobalTheory.AbCoh.bijective_of_split_of_FP | exact GlobalTheory.AbCoh.bijective_of_split_of_FP | (intros; apply GlobalTheory.AbCoh.bijective_of_split_of_FP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualConvPowPrimePowApplyPow
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

theorem convPow_prime_apply_pow_prime (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p) (a ^ p) = χ (mulBy R (G.A n) p a) ^ p := by
  rw [← frobTwistDual_verschiebung h (G := G) n χ, ← relFrob_app_frobProj h (G := G) n a]
  have e : (verschiebung h G).app n ((relFrob h G).app n ((frobProj h G).app n a)) =
      mulBy R _ p ((frobProj h G).app n a) := by
    rw [← prime_smul_id_app]
    exact (congrArg (fun f => Hom.app f n ((frobProj h G).app n a)) (verschiebung_comp_relFrob h G))
  rw [e, ← SemiBialgHom.map_mulBy, frobTwistDual_frobProj]

theorem convPow_primePow_apply_pow (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r := by
  induction r generalizing a with
  | zero =>
    simp only [pow_zero, pow_one]
    rw [mulBy, pow_one]
    rfl
  | succ r ih =>
    rw [pow_succ, pow_mul, pow_mul, convPow_prime_apply_pow_prime p R h G n, map_pow, ih,
      mulBy_mulBy, ← pow_mul, mul_comm (p ^ r) p, ← pow_succ']

end PDivGroup

end GlobalTheory
end

