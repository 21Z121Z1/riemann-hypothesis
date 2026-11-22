import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0641
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevIffIsEtLevOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev.PullPt

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S T : Scheme.{0}} {s : S ⟶ Sp R} {t : T ⟶ S} {s₁ : T ⟶ Sp R} {o : Obj b N s} {o₁ : Obj b N s₁}

def ptOver (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) : Over.mk (U.hom ≫ t) ⟶ o.A :=
  Over.homMk (g.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w g]
    rfl)

@[simp] theorem ptOver_left (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) :
    (ptOver m g).left = g.left ≫ m.φ := rfl

theorem ptOver_injective (m : ObjMap o₁ o t) {U : Over T} : Function.Injective (ptOver m (U := U)) := by
  intro g h e
  have e' : g.left ≫ m.φ = h.left ≫ m.φ := by
    rw [← ptOver_left m g, ← ptOver_left m h, e]
  ext
  exact m.cart.1.hom_ext e' (by rw [Over.w g, Over.w h])

theorem ptOver_surjective (m : ObjMap o₁ o t) {U : Over T} : Function.Surjective (ptOver m (U := U)) := by
  intro g₀
  refine ⟨Over.homMk (m.cart.1.lift g₀.left U.hom (by rw [Over.w g₀]; rfl)) (m.cart.1.lift_snd _ _ _), ?_⟩
  ext
  simp [ptOver, m.cart.1.lift_fst]

theorem ptOver_mul (m : ObjMap o₁ o t) {U : Over T} (g h : U ⟶ o₁.A) :
    ptOver m (g * h) = ptOver m g * ptOver m h := by
  ext
  exact (m.cart.2 U g h (ptOver m g) (ptOver m h) rfl rfl).symm

theorem ptOver_one (m : ObjMap o₁ o t) {U : Over T} : ptOver m (1 : U ⟶ o₁.A) = 1 := by
  have h := ptOver_mul m (1 : U ⟶ o₁.A) 1
  rw [_root_.mul_one] at h
  exact (mul_eq_left.mp h.symm)

theorem ptOver_eq_one (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) : ptOver m g = 1 ↔ g = 1 := by
  rw [← ptOver_one m]
  exact (ptOver_injective m).eq_iff

theorem ptOver_act (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) (c : D.O) :
    ptOver m (g ≫ o₁.act.act c) = ptOver m g ≫ o.act.act c := by
  ext
  simp [ptOver, m.act]

theorem ptOf_eq (m : ObjMap o₁ o t) (g : 𝟙_ (Over T) ⟶ o₁.A) :
    (Over.homMk (𝟙 T) (by simp) : Over.mk ((𝟙_ (Over T)).hom ≫ t) ⟶ Over.mk t) ≫ ptOf m g = ptOver m g := by
  ext
  simp [ptOf, ptOver]

theorem ptOf_injective (m : ObjMap o₁ o t) : Function.Injective (ptOf m) := by
  intro g h e
  apply ptOver_injective m
  rw [← ptOf_eq, ← ptOf_eq, e]

theorem ptOf_mul (m : ObjMap o₁ o t) (g h : 𝟙_ (Over T) ⟶ o₁.A) :
    ptOf m (g * h) = ptOf m g * ptOf m h := by
  have e := ptOf_eq m (g * h)
  rw [ptOver_mul, ← ptOf_eq, ← ptOf_eq, ← comp_mul] at e
  ext
  have e' := congrArg CommaMorphism.left e
  simpa using e'

theorem ptOf_one (m : ObjMap o₁ o t) : ptOf m (1 : 𝟙_ (Over T) ⟶ o₁.A) = 1 := by
  have h := ptOf_mul m (1 : 𝟙_ (Over T) ⟶ o₁.A) 1
  rw [_root_.mul_one] at h
  exact (mul_eq_left.mp h.symm)

theorem ptOf_act (m : ObjMap o₁ o t) (g : 𝟙_ (Over T) ⟶ o₁.A) (c : D.O) :
    ptOf m (g ≫ o₁.act.act c) = ptOf m g ≫ o.act.act c := by
  ext
  simp [ptOf, m.act]

theorem homMk_ptOf (m : ObjMap o₁ o t) {k : Type} [Field k] (x : Sp k ⟶ T) (g : 𝟙_ (Over T) ⟶ o₁.A) :
    (Over.homMk x rfl : Over.mk (x ≫ (Over.mk t).hom) ⟶ Over.mk t) ≫ ptOf m g =
      ptOver m (toUnit (Over.mk x) ≫ g) := by
  ext
  simp [ptOf, ptOver]

end GlobalTheory.UPel.HT.EtLev.PullPt

namespace GlobalTheory.UPel.HT.EtLev

open PullPt

theorem isEtLev_iff_isEtLevOver : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S T : Scheme.{0}) (s : S ⟶ Sp R) (t : T ⟶ S) (s₁ : T ⟶ Sp R) (o : Obj b N s) (o₁ : Obj b N s₁)
    (m : ObjMap o₁ o t) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (l : D.La → (𝟙_ (Over T) ⟶ o₁.A)),
    IsEtLev o₁ w0 r l ↔ IsEtLevOver o w0 r (T := Over.mk t) (fun y => ptOf m (l y)) := by
  intro p _ D R _ b N S T s t s₁ o o₁ m w0 r l
  have hadd : (∀ x y, l (x + y) = l x * l y) ↔ (∀ x y, ptOf m (l (x + y)) = ptOf m (l x) * ptOf m (l y)) := by
    refine forall₂_congr fun x y => ?_
    rw [← ptOf_mul, (ptOf_injective m).eq_iff]
  have hlin : (∀ (c : D.O) x, l (c • x) = l x ≫ o₁.act.act c) ↔
      (∀ (c : D.O) x, ptOf m (l (c • x)) = ptOf m (l x) ≫ o.act.act c) := by
    refine forall₂_congr fun c x => ?_
    rw [← ptOf_act, (ptOf_injective m).eq_iff]
  have hker : (∀ x ∈ wSub D w0 r, l x = 1) ↔ (∀ x ∈ wSub D w0 r, ptOf m (l x) = 1) := by
    refine forall₂_congr fun x _ => ?_
    rw [← ptOf_one m, (ptOf_injective m).eq_iff]
  have hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T),
      ((∀ y, toUnit (Over.mk x) ≫ l y = 1 → y ∈ wSub D w0 r) ∧
        ∀ g : Over.mk x ⟶ o₁.A, (∀ c ∈ w0 ^ r, g ≫ o₁.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
          ∃ y, toUnit (Over.mk x) ≫ l y = g) ↔
      ((∀ y, (Over.homMk x rfl : Over.mk (x ≫ (Over.mk t).hom) ⟶ Over.mk t) ≫ ptOf m (l y) = 1 → y ∈ wSub D w0 r) ∧
        ∀ g : Over.mk (x ≫ (Over.mk t).hom) ⟶ o.A,
          (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
          ∃ y, (Over.homMk x rfl : Over.mk (x ≫ (Over.mk t).hom) ⟶ Over.mk t) ≫ ptOf m (l y) = g) := by
    intro k _ _ x
    simp only [homMk_ptOf]
    refine and_congr (forall_congr' fun y => by rw [ptOver_eq_one]) ?_
    constructor
    · intro h g₀ hg₀
      obtain ⟨g, rfl⟩ := ptOver_surjective m (U := Over.mk x) g₀
      obtain ⟨y, hy⟩ := h g (fun c hc => by rw [← ptOver_eq_one m, ptOver_act]; exact hg₀ c hc)
      exact ⟨y, by rw [hy]⟩
    · intro h g hg
      obtain ⟨y, hy⟩ := h (ptOver m g) (fun c hc => by rw [← ptOver_act, ptOver_eq_one]; exact hg c hc)
      exact ⟨y, ptOver_injective m hy⟩
  unfold IsEtLev IsEtLevOver
  rw [hadd, hlin, hker]
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun x => hgeom k x)))

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesSectionQuotients
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

section QuotEtale

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {B : La} {t0 : ι → Y → ℂ} {t : Fin n → ι → Y → ℂ}

end QuotEtale

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] in
private lemma sec_eq_transition_mul {A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La} {B : La} {s : ι → Y → ℂ}
    (hs : A.IsSec B s) {i j : ι} {y : Y} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : s i y = A.g B i j y * s j y := by
  have h := hs
  unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSec _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSecOn at h
  exact h.2 i j y (Set.mem_univ y) hi hj

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.etale_zmap_main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (U : Set Y),
    A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → IsOpen U →
    (∀ y ∈ U, t0 (A.pick y) y ≠ 0 ∧ A.IsCoordAt t0 t y) → _root_.GlobalTheory.OTY.Etale A U (A.zmap t0 t) := by
  intro n Y _ _ _ _ _ ι La _ A B t0 t U h0 ht hU hcoord
  have hne : ∀ i, ∀ y ∈ U, y ∈ (A.chart i).source → t0 i y ≠ 0 := by
    intro i y hy hi
    rw [sec_eq_transition_mul h0 hi (A.mem_pick y)]
    exact mul_ne_zero (A.g_ne B i _ y hi (A.mem_pick y)) (hcoord y hy).1
  have hz : ∀ i, ∀ y ∈ U, y ∈ (A.chart i).source →
      A.zmap t0 t y = A.zLoc t0 t i (A.chart i y) := by
    intro i y hy hi
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zmap _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc
    rw [(A.chart i).left_inv hi]
    congr 1
    funext k
    rw [sec_eq_transition_mul (ht k) hi (A.mem_pick y),
      sec_eq_transition_mul h0 hi (A.mem_pick y)]
    exact (mul_div_mul_left _ _ (A.g_ne B i _ y hi (A.mem_pick y))).symm
  have hloc : ∀ i, DifferentiableOn ℂ (A.zLoc t0 t i)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
    intro i
    apply (differentiableOn_piLp (𝕜 := ℂ) 2).2
    intro k
    have hk := ht k
    have h0' := h0
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSec _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSecOn at hk h0'
    have hsub : (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ⊆
        (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ := fun v hv => ⟨hv.1, Set.mem_univ _⟩
    have hnum : DifferentiableOn ℂ (fun v => t k i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (hk.1 i).mono hsub
    have hden : DifferentiableOn ℂ (fun v => t0 i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (h0'.1 i).mono hsub
    have hdiv : DifferentiableOn ℂ
        (fun v => t k i ((A.chart i).symm v) / t0 i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
      simp only [div_eq_mul_inv]
      exact hnum.mul (hden.inv fun v hv => hne i _ hv.2 ((A.chart i).map_target hv.1))
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc
    exact hdiv
  refine ⟨hU, ?_, ?_⟩
  · intro i
    refine (hloc i).congr ?_
    intro v hv
    simp only [Function.comp_apply]
    rw [hz i _ hv.2 ((A.chart i).map_target hv.1), (A.chart i).right_inv hv.1]
  · intro i y hy hi
    unfold _root_.GlobalTheory.OTY.jdet _root_.GlobalTheory.OTY.jz
    set j := A.pick y with hj_def
    have hj : y ∈ (A.chart j).source := A.mem_pick y
    have hV : (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ (A.chart j).source) ∈
        𝓝 (A.chart i y) := by
      refine ((A.chart i).isOpen_inter_preimage_symm (hU.inter (A.chart j).open_source)).mem_nhds ?_
      refine ⟨(A.chart i).map_source hi, ?_⟩
      simp only [Set.mem_preimage, (A.chart i).left_inv hi]
      exact ⟨hy, hj⟩
    have heq : A.zmap t0 t ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)]
        A.zLoc t0 t j ∘ ((A.chart j) ∘ (A.chart i).symm) := by
      filter_upwards [hV] with v hv
      simp only [Function.comp_apply]
      exact hz j _ hv.2.1 hv.2.2
    rw [heq.fderiv_eq]
    have hT : DifferentiableAt ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) := by
      refine (A.holo_trans i j).differentiableAt ?_
      have ho : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source) :=
        (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
      refine ho.mem_nhds ?_
      refine ⟨(A.chart i).map_source hi, ?_⟩
      simp only [Set.mem_preimage, (A.chart i).left_inv hi]
      exact hj
    have hTy : ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
      simp only [Function.comp_apply, (A.chart i).left_inv hi]
    have hL : DifferentiableAt ℂ (A.zLoc t0 t j) (((A.chart j) ∘ (A.chart i).symm) (A.chart i y)) := by
      rw [hTy]
      refine (hloc j).differentiableAt ?_
      refine ((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ?_
      refine ⟨(A.chart j).map_source hj, ?_⟩
      simp only [Set.mem_preimage, (A.chart j).left_inv hj]
      exact hy
    rw [fderiv_comp _ hL hT, hTy]
    have hdet : LinearMap.det (((fderiv ℂ (A.zLoc t0 t j) (A.chart j y)).comp
        (fderiv ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y)) : _root_.ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) :
          _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) =
        LinearMap.det (fderiv ℂ (A.zLoc t0 t j) (A.chart j y) : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) *
          LinearMap.det (fderiv ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) :
            _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) :=
      LinearMap.det_comp _ _
    rw [ContinuousLinearMap.det, hdet]
    refine mul_ne_zero ?_ ?_
    · have hc := (hcoord y hy).2
      unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsCoordAt at hc
      exact hc
    · have hk := A.g_kap i j y hi hj
      have hg := A.g_ne A.kap i j y hi hj
      rw [hk] at hg
      exact hg

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionIntegralJ
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.WpInt

theorem isIntegral_int_of_closure (y : ℂ)
    (hy : IsIntegral (integralClosure ℤ ℂ).toSubring y) : IsIntegral ℤ y := by
  set R : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  haveI : Algebra.IsIntegral ℤ R := ⟨fun r => by
    have h : IsIntegral ℤ (r : ℂ) := r.2
    exact (isIntegral_algHom_iff (R.subtype.toIntAlgHom) Subtype.coe_injective).mp h⟩
  exact isIntegral_trans (R := ℤ) (A := R) y hy

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ →
    ∀ x : Fin 2 → ZMod N, IsIntegral ℤ (12 * (N : ℂ) ^ 2 * wp N x τ / ω ^ 2) ∧
      IsIntegral ℤ ((N : ℂ) ^ 3 * wpd N x τ / ω ^ 3) := by
  intro N _ τ ω hj hω x
  set R : Subring ℂ := (integralClosure ℤ ℂ).toSubring with hR
  have hjR : IsIntegral R (jT τ) := hj.tower_top
  have hbij : ActBij (vact N) := (GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).1.actBij
  have hfam := GlobalTheory.T.weierstrassP_torsion_isModularFamily N
  have halg := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure (Fin 2 → ZMod N) (vact N)
  have hlin := GlobalTheory.T.hasQExpansionOfLevel_linear_operations N
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNx : ∀ y : Fin 2 → ZMod N, N • y = 0 := fun y => by
    funext i; simp [nsmul_eq_mul]
  constructor
  · have hF : IsFam (vact N) ((2 : ℕ) : ℤ) (fun y t => (12 * (N : ℂ) ^ 2) * wp N y t) :=
      halg.2.2.1 2 _ (wp N) hfam.1
    have hQ : ∀ y, QAll (· ∈ R) N ((fun y t => (12 * (N : ℂ) ^ 2) * wp N y t) y) := fun y =>
      ⟨fun k => 12 * (N : ℂ) ^ 2 * cP N y k, hlin.2.2.1 _ _ _ (GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N y),
        fun k => (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N y k hN (hNx y)).2.2.1⟩
    have h := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow _ (vact N) 2 N _ R τ ω hN hbij hF hQ hjR hω x
    exact isIntegral_int_of_closure _ h
  · have hF : IsFam (vact N) ((3 : ℕ) : ℤ) (fun y t => ((N : ℂ) ^ 3) * wpd N y t) :=
      halg.2.2.1 3 _ (wpd N) hfam.2
    have hQ : ∀ y, QAll (· ∈ R) N ((fun y t => ((N : ℂ) ^ 3) * wpd N y t) y) := fun y =>
      ⟨fun k => (N : ℂ) ^ 3 * cD N y k, hlin.2.2.1 _ _ _ (GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N y),
        fun k => (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N y k hN (hNx y)).2.1⟩
    have h := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow _ (vact N) 3 N _ R τ ω hN hbij hF hQ hjR hω x
    exact isIntegral_int_of_closure _ h

end GlobalTheory.WpInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentDualFrobeniusOfBlock
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.DualFrobNilMat

theorem mulVec_transpose_inv_blk_apply {B : Type} [CommRing B] (σ : B →+* B) (p : ℕ) {d k : ℕ}
    (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B) (w : Fin d ⊕ Fin k → B) (r : Fin d ⊕ Fin k) :
    ((U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j)) r =
      (∑ j : Fin d, U⁻¹ (Sum.inl j) r * σ (w (Sum.inl j))) +
      (p : B) * ∑ j : Fin k, U⁻¹ (Sum.inr j) r * σ (w (Sum.inr j)) := by
  have hU : ∀ r s, U.transpose⁻¹ r s = U⁻¹ s r := fun r s => by
    rw [← Matrix.transpose_nonsing_inv]; rfl
  simp only [Matrix.mulVec, dotProduct, blk, Matrix.mul_diagonal, hU, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_one, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem isNil_of_block : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O) (σ : B →+* B) (p : ℕ) (m : Ideal O), θ (p : B) ∈ m → m ≠ ⊤ → (∀ b, ∃ c, σ b - b ^ p = p * c) → ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B) (c : Fin d → Fin d → B), (∀ a j, ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b) → (∃ N : ℕ, ∀ w : Fin d → O ⧸ m, (fun w : Fin d → O ⧸ m => fun a => ∑ j, Ideal.Quotient.mk m (θ (c a j)) * w j ^ p)^[N] w = 0) → IsNil θ σ (U.transpose⁻¹ * blk d k 1 (p : B)) := by
  intro B O _ _ θ σ p m hp hm hσ d k U c hc hS
  obtain ⟨N, hN⟩ := hS
  set ρ : B →+* O ⧸ m := (Ideal.Quotient.mk m).comp θ with hρ
  have hρp : ρ (p : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hp
  have hρσ : ∀ b, ρ (σ b) = ρ b ^ p := by
    intro b
    obtain ⟨e, he⟩ := hσ b
    have h := congrArg ρ he
    rw [map_sub, map_mul, map_pow, hρp, zero_mul, sub_eq_zero] at h
    exact h
  have hp0 : p ≠ 0 := by
    rintro rfl
    apply hm
    obtain ⟨e, he⟩ := hσ 0
    simp only [map_zero, pow_zero, zero_sub, Nat.cast_zero, zero_mul, neg_eq_zero] at he
    have h1 : (1 : O) = 0 := by rw [← map_one θ, he, map_zero]
    rw [Ideal.eq_top_iff_one, h1]
    exact m.zero_mem
  have hT : ∀ (w : Fin d ⊕ Fin k → B) r,
      ρ (((U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j)) r) =
        ∑ j, ρ (U⁻¹ (Sum.inl j) r) * ρ (w (Sum.inl j)) ^ p := by
    intro w r
    rw [mulVec_transpose_inv_blk_apply, map_add, map_mul, hρp, zero_mul, add_zero, map_sum]
    simp only [map_mul, hρσ]
  have hinl : ∀ a j, ρ (U⁻¹ (Sum.inl j) (Sum.inl a)) = ρ (c a j) := by
    intro a j
    obtain ⟨e, he⟩ := hc a j
    have h := congrArg ρ he
    rw [map_sub, map_mul, hρp, zero_mul, sub_eq_zero] at h
    exact h.symm
  have hiter : ∀ (t : ℕ) (v : Fin d ⊕ Fin k → B),
      (fun a => ρ (((fun w : Fin d ⊕ Fin k → B =>
        (U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j))^[t] v) (Sum.inl a))) =
      (fun w : Fin d → O ⧸ m => fun a => ∑ j, Ideal.Quotient.mk m (θ (c a j)) * w j ^ p)^[t]
        (fun a => ρ (v (Sum.inl a))) := by
    intro t
    induction t with
    | zero => intro v; rfl
    | succ t ih =>
      intro v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      funext a
      rw [hT]
      exact Finset.sum_congr rfl fun j _ => by rw [hinl]; rfl
  refine ⟨N + 1, fun v r hu => hm ?_⟩
  rw [Function.iterate_succ_apply'] at hu
  have h0 : ρ (((U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ
      (((fun w : Fin d ⊕ Fin k → B =>
        (U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j))^[N] v) j)) r) = 0 := by
    rw [hT]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h := congrFun (hiter N v) j
    rw [hN] at h
    simp only [Pi.zero_apply] at h
    rw [h, zero_pow hp0, mul_zero]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.Quotient.eq_zero_iff_mem.1 h0) hu

end GlobalTheory.DualFrobNilMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfMemSmallCover
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
private theorem isNilpotent_of_mem_of_isNilDP {B : Type} [CommRing B]
    {J : Ideal B} (δ : DividedPowers J) (hδ : _root_.GlobalTheory.Cris.IsNilDP δ) {x : B} (hx : x ∈ J) :
    IsNilpotent x := by
  obtain ⟨N, hN⟩ := hδ
  refine ⟨N, ?_⟩
  have h := hN [(N, x)] (by simpa using hx) (by simp)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [← δ.factorial_mul_dpow_eq_pow hx, h, mul_zero]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in

theorem _root_.GlobalTheory.Cris.exists_finite_small_cover (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (K : Type) (U : K → X.Opens) (hU : ⨆ i, U i = ⊤)
    (T : _root_.GlobalTheory.Cris.Thick κ s) : ∃ (n : ℕ) (b : Fin n → T.B),
      Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : _root_.GlobalTheory.Cris.Thick κ s) (u : T ⟶ S),
        IsUnit (u.φ (b i)) → _root_.GlobalTheory.Cris.IsSmall κ s U S := by
  classical
  let G : Set T.B₀ := {f | ∃ k, ∀ p : PrimeSpectrum T.B₀,
    f ∉ p.asIdeal → T.x.base p ∈ U k}
  have hG : Ideal.span G = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    let p : PrimeSpectrum T.B₀ := ⟨m, hm.isPrime⟩
    have hp : T.x.base p ∈ (⨆ i, U i : X.Opens) := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := (TopologicalSpace.Opens.mem_iSup).1 hp
    obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (a := p) (u := (fun q : PrimeSpectrum T.B₀ ↦ T.x.base q) ⁻¹' (U k))
        hk ((U k).isOpen.preimage T.x.continuous)
    exact hpf (hle (Ideal.subset_span ⟨k, fun q hq ↦ hsub hq⟩))
  obtain ⟨t, htG, htspan⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  let e := t.equivFin
  have hlift : ∀ i : Fin t.card, ∃ y, T.π y = (e.symm i : T.B₀) :=
    fun i ↦ T.surj _
  choose b hb using hlift
  refine ⟨t.card, b, ?_, ?_⟩
  · have hmap : Ideal.map T.π (Ideal.span (Set.range b)) = ⊤ := by
      rw [Ideal.map_span, ← htspan]
      congr 1
      ext f
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        rw [hb]
        exact (e.symm i).2
      · intro hf
        exact ⟨b (e ⟨f, hf⟩), ⟨_, rfl⟩, by rw [hb, Equiv.symm_apply_apply]⟩
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective _ T.surj).1
      (hmap ▸ Submodule.mem_top : (1 : T.B₀) ∈ _)
    have hJ : 1 - y ∈ T.J := by
      rw [← T.ker, map_sub, map_one, hy1, sub_self]
    have hunit : IsUnit y := by
      have := (isNilpotent_of_mem_of_isNilDP _ T.nil hJ).isUnit_one_sub
      simpa using this
    exact Ideal.eq_top_of_isUnit_mem _ hy hunit
  · intro i S u hu
    obtain ⟨k, hk⟩ := htG (e.symm i).2
    refine ⟨k, fun q _ ↦ ?_⟩
    show S.x.base q ∈ U k
    rw [← u.pt, Scheme.Hom.comp_apply]
    apply hk
    intro hq
    have h1 : u.φ₀ (e.symm i : T.B₀) ∈ q.asIdeal := hq
    rw [← hb, u.comm] at h1
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (hu.map S.π))

end GlobalTheory.Cris
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingObstructionBocksteinAddStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftingObstructionBockstein_add : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (x x' : HO1 s') (z z' : HO2 s₀), Bock h h₀ t x z → Bock h h₀ t x' z' → Bock h h₀ t (x + x') (z + z') := by
  first | exact @GlobalTheory.AbCoh.Bock_add | exact GlobalTheory.AbCoh.Bock_add | (intros; apply GlobalTheory.AbCoh.Bock_add <;> assumption)
end

