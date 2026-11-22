import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0637
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnion
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.UnionHInv

variable {A : Type} [CommRing A] {ι : Type} [Preorder ι] (S : ι → Subalgebra ℤ A) (hS : Monotone S)

noncomputable def diag : ι ⥤ CommRingCat.{0} where
  obj i := CommRingCat.of (S i)
  map {i j} h := CommRingCat.ofHom (Subalgebra.inclusion (hS (leOfHom h))).toRingHom
  map_id i := by ext x; rfl
  map_comp f g := by ext x; rfl

noncomputable def cocone : Cocone (diag S hS) where
  pt := CommRingCat.of A
  ι := { app := fun i => CommRingCat.ofHom (S i).val.toRingHom
         naturality := fun i j h => by ext x; rfl }

theorem cocone_isColimit [IsDirected ι (· ≤ ·)] [Nonempty ι] (hcov : ∀ a, ∃ i, a ∈ S i) :
    Nonempty (IsColimit (cocone S hS)) := by
  haveI : ReflectsColimitsOfShape ι (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change A at x
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · intro i j xi xj h
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, homOfLE hik, homOfLE hjk, ?_⟩
    apply Subtype.ext
    exact h

end GlobalTheory.UnionHInv

open GlobalTheory.UnionHInv in

theorem GlobalTheory.EtC.hInv_of_directed_union : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (S : ι → Subalgebra ℤ A), Monotone S → (∀ a, ∃ i, a ∈ S i) → (∀ i, IsUnit (q : S i)) → (∀ i, HInv q (S i)) → HInv q A := by
  intro q _ A _ ι _ _ _ S hS hcov hu hH
  obtain ⟨hc⟩ := cocone_isColimit S hS hcov
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_filtered_colimit q ι (diag S hS) (cocone S hS) hc hu hH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationTensorLiftsIffProjectionsStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeFiltration_tensor_lifts_iff_projections : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : B₀.left ⟶ Y.left)
    (wi : i ≫ X.hom = A₀.hom ≫ spMap π) (wj : j ≫ Y.hom = B₀.hom ≫ spMap π)
    (e : Sp R ⟶ X.left) (e' : Sp R ⟶ Y.left), e ≫ X.hom = 𝟙 _ → e' ≫ Y.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ B₀).left ≫ j = spMap π ≫ e' →
    ∀ (l : (A₀ ⊗ B₀).left ⟶ (X ⊗ Y).left), l ≫ (fst X Y).left = (fst A₀ B₀).left ≫ i → l ≫ (snd X Y).left = (snd A₀ B₀).left ≫ j →
    ∀ (wl : l ≫ (X ⊗ Y).hom = (A₀ ⊗ B₀).hom ≫ spMap π) (d : Crys κ (spMap π) (A₀ ⊗ B₀)),
    d ∈ schemeFil κ (A₀ ⊗ B₀) (X ⊗ Y) l wl ↔
      push κ (spMap π) (fst A₀ B₀) d ∈ schemeFil κ A₀ X i wi ∧ push κ (spMap π) (snd A₀ B₀) d ∈ schemeFil κ B₀ Y j wj := by
  first | exact @GlobalTheory.SqLift.ProdFil.schemeFil_tensor_iff | exact GlobalTheory.SqLift.ProdFil.schemeFil_tensor_iff | (intros; apply GlobalTheory.SqLift.ProdFil.schemeFil_tensor_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoloEtaleIffCharts
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.holo_etale_iff_charts : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ u : Y → ℂ, (Holo n (fun y : U => z y) (fun y : U => u y) ↔ ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) := by
  intro n Y _ _ _ _ _ ι La _ A U z hz u
  have h := GlobalTheory.T.etale_holomorphic_iff_chart_holomorphic n Y ι La A U z hz Set.univ u isOpen_univ
  simp only [Set.preimage_univ, Set.inter_univ] at h
  exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCocycleAdditiveLawReductionCoboundaryStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_cocycle_additiveLaw_reduction_coboundary : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d N : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) k), 2 ≤ N → IsCoc (addLaw k d) c → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ c = 0) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ Red p (cob1 (addLaw (Fr p k) d) h) c := by
  first | exact @GlobalTheory.LazardHomog.homogCoc_red_cob | exact GlobalTheory.LazardHomog.homogCoc_red_cob | (intros; apply GlobalTheory.LazardHomog.homogCoc_red_cob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2ExteriorSquareIso
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Wedge

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem update_pair_vector_zero (a b x : M) : Function.update ![a, b] 0 x = ![x, b] := by
  funext i; fin_cases i <;> simp

theorem update_pair_vector_one (a b x : M) : Function.update ![a, b] 1 x = ![a, x] := by
  funext i; fin_cases i <;> simp

def ιTwo : M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun a b ↦ exteriorPower.ιMulti R 2 ![a, b])
    (fun a a' b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_add ![a, b] 0 a a'
      simpa only [update_pair_vector_zero] using h)
    (fun r a b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_smul ![a, b] 0 r a
      simpa only [update_pair_vector_zero] using h)
    (fun a b b' ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_add ![a, b] 1 b b'
      simpa only [update_pair_vector_one] using h)
    (fun r a b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_smul ![a, b] 1 r b
      simpa only [update_pair_vector_one] using h)

theorem ιTwo_apply (a b : M) : ιTwo a b = exteriorPower.ιMulti R 2 ![a, b] := by
  rw [ιTwo, LinearMap.mk₂_apply]

theorem ιTwo_self (a : M) : ιTwo (R := R) a a = 0 := by
  rw [ιTwo_apply]
  exact (exteriorPower.ιMulti R 2 (M := M)).map_eq_zero_of_eq ![a, a] (i := 0) (j := 1) rfl (by decide)

theorem ιTwo_swap (a b : M) : ιTwo (R := R) b a = -ιTwo a b := by
  have h := ιTwo_self (R := R) (a + b)
  simp only [map_add, LinearMap.add_apply, ιTwo_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem sum_sum_ιTwo_of_symm {n : ℕ} (x : Fin n → M) (c : Fin n → Fin n → R)
    (hc : ∀ a b, c a b = c b a) : ∑ a, ∑ b, c a b • ιTwo (R := R) (x a) (x b) = 0 := by
  rw [← Finset.sum_product' (s := Finset.univ) (t := Finset.univ)
    (f := fun a b ↦ c a b • ιTwo (R := R) (x a) (x b))]
  refine Finset.sum_involution (fun p _ ↦ p.swap) (fun p _ ↦ ?_) (fun p _ hp ↦ ?_)
    (fun p _ ↦ by simp) (fun p _ ↦ Prod.swap_swap p)
  · simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hc p.2 p.1, ιTwo_swap (x p.1), smul_neg, add_neg_cancel]
  · intro he
    apply hp
    have : p.1 = p.2 := (Prod.ext_iff.1 he).2
    simp only [this, ιTwo_self, smul_zero]

end Wedge

section Forget

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def fnZZ2 : cechDeRhamTotalCocyclesTwo F →ₗ[R] Z2 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def hypercohomologyTwoToAlgebraCohomology : Hyp2 F →ₗ[R] CatCoh.H2 F :=
  Submodule.mapQ _ _ (fnZZ2 F) (by rintro _ ⟨e, rfl⟩; exact ⟨e.1, rfl⟩)

theorem hypercohomologyTwo_cup_forget_forms (a b : Hyp1 F) : hypercohomologyTwoToAlgebraCohomology F (cupHyp F a b) = cup F (toO F a) (toO F b) := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rfl

def cupProductWedge (halt : ∀ a, cupHyp F a a = 0) : Hyp1 F [⋀^Fin 2]→ₗ[R] Hyp2 F where
  toFun v := cupHyp F (v 0) (v 1)
  map_update_add' v i a b := by fin_cases i <;> simp
  map_update_smul' v i r a := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all

def cupWedge (halt : ∀ a, cupHyp F a a = 0) : ⋀[R]^2 (Hyp1 F) →ₗ[R] Hyp2 F :=
  exteriorPower.alternatingMapLinearEquiv (cupProductWedge F halt)

theorem cupWedge_ιTwo (halt : ∀ a, cupHyp F a a = 0) (a b : Hyp1 F) :
    cupWedge F halt (ιTwo a b) = cupHyp F a b := by
  rw [ιTwo_apply, cupWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem exact_clAll_toO (hc : Closed1 F = ⊤) : Function.Exact (clAll F hc) (toO F) := by
  intro y
  constructor
  · intro hy
    have h : y ∈ Fil1 F := hy
    rw [Fil1_eq_range] at h
    obtain ⟨ω, rfl⟩ := h
    exact ⟨ω.1, rfl⟩
  · rintro ⟨w, rfl⟩
    have h : clAll F hc w ∈ Fil1 F := by
      rw [Fil1_eq_range]; exact ⟨_, rfl⟩
    exact h

end Forget

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem exists_wedge_hyp_equiv : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) → WedgeO F →
    (∀ a, cupHyp F a a = 0) → ∃ e : ⋀[R]^2 (Hyp1 F) ≃ₗ[R] Hyp2 F,
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHyp F a b := by
  intro R _ C _ F hF h0 hc hs hw halt
  let e₀ := cupWedge F halt
  have e₀_ι : ∀ a b, e₀ (ιTwo a b) = cupHyp F a b := cupWedge_ιTwo F halt
  have hsurj : Function.Surjective e₀ := by
    intro z
    obtain ⟨n, a, b, rfl⟩ := GlobalTheory.T.hyper_h2_generated_by_cups R C F hF h0 hc hs hw z
    exact ⟨∑ k, ιTwo (a k) (b k), by simp only [map_sum, e₀_ι]⟩
  have hex := exact_clAll_toO F hc
  have hinj : Function.Injective e₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    obtain ⟨ew, hew⟩ := hw

    have hcomm : ew.toLinearMap ∘ₗ exteriorPower.map 2 (toO F) = hypercohomologyTwoToAlgebraCohomology F ∘ₗ e₀ := by
      refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
      have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
      have hv' : (toO F) ∘ v = ![toO F (v 0), toO F (v 1)] := by funext i; fin_cases i <;> rfl
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe, exteriorPower.map_apply_ιMulti, hv', hew]
      rw [hv, ← ιTwo_apply, e₀_ι, hypercohomologyTwo_cup_forget_forms]
      rfl
    have h1 : exteriorPower.map 2 (toO F) t = 0 := by
      apply ew.injective
      have := LinearMap.congr_fun hcomm t
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
      rw [this, ht, map_zero, map_zero]
    obtain ⟨m, a, w, rfl⟩ := GlobalTheory.T.exists_sum_ιMulti_of_exteriorSquare_map_eq_zero R (Glob1 F) (Hyp1 F) (CatCoh.H1 F) (clAll F hc) (toO F) hs hex t h1
    simp only [← ιTwo_apply] at ht ⊢
    have hsum : ∑ k, cupHyp F (a k) (clAll F hc (w k)) = 0 := by
      simpa only [map_sum, e₀_ι] using ht
    obtain ⟨N, ⟨Φ⟩⟩ := hF
    obtain ⟨l, -, hl⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 N Φ
    let x : Fin N → Hyp1 F := fun i ↦ clAll F hc (Φ.w i)
    have hcl : ∀ v : Glob1 F, clAll F hc v = ∑ i, l i v • x i := by
      intro v
      conv_lhs => rw [hl v]
      simp only [map_sum, map_smul, x]

    let Mi : Fin N → Hyp1 F := fun i ↦ ∑ k, l i (w k) • a k
    have ht1 : ∑ k, ιTwo (R := R) (a k) (clAll F hc (w k)) = ∑ i, ιTwo (Mi i) (x i) := by
      simp only [hcl, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Mi]
      exact Finset.sum_comm
    have hM0 : ∀ i, toO F (Mi i) = 0 := by
      intro i
      have := GlobalTheory.T.sum_cup_oneForms_zero_imp_coordinates_zero R C F ⟨N, ⟨Φ⟩⟩ h0 hc hs m a w hsum (l i)
      simpa only [Mi, map_sum, map_smul] using this
    have hMu : ∀ i, ∃ u, clAll F hc u = Mi i := fun i ↦ (hex (Mi i)).1 (hM0 i)
    choose u hu using hMu
    rw [ht1]
    simp only [← hu]
    have hcup : ∑ i, cupHyp F (clAll F hc (u i)) (clAll F hc (Φ.w i)) = 0 := by
      rw [← ht, ht1]
      simp only [← hu, map_sum, e₀_ι, x]
    have hw2 := (GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge R C F hc hs N u Φ.w).1 hcup
    have hsym := (GlobalTheory.T.sumWedgeGlobalOneForms_eq_zero_iff R C F ⟨N, ⟨Φ⟩⟩ h0 N u Φ.w).1 hw2
    let c : Fin N → Fin N → R := fun p q ↦ ∑ i, l p (u i) * l q (Φ.w i)
    have hc' : ∀ p q, c p q = c q p := by
      intro p q
      have := hsym (l p) (l q)
      rw [Finset.sum_sub_distrib, sub_eq_zero] at this
      simp only [c]
      rw [this]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    have step : ∀ i, ιTwo (R := R) (clAll F hc (u i)) (x i) =
        ∑ p, ∑ q, (l p (u i) * l q (Φ.w i)) • ιTwo (R := R) (x p) (x q) := by
      intro i
      rw [hcl (u i)]
      conv_lhs => rw [show x i = ∑ q, l q (Φ.w i) • x q from hcl (Φ.w i)]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by rw [mul_comm]
    have hexp : ∑ i, ιTwo (R := R) (clAll F hc (u i)) (x i) = ∑ p, ∑ q, c p q • ιTwo (R := R) (x p) (x q) := by
      simp only [step]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      simp only [c, Finset.sum_smul]
    rw [hexp]
    exact sum_sum_ιTwo_of_symm x c hc'
  refine ⟨LinearEquiv.ofBijective e₀ ⟨hinj, hsurj⟩, fun a b ↦ ?_⟩
  have := e₀_ι a b
  rw [ιTwo_apply] at this
  exact this

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerFockOmegaActionAdjointLines
section
noncomputable section
namespace GlobalTheory.FockAdjLines
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem Jm_eq_diagonal (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem inner_omAct_adj : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι → ∀ (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P Q : Pol p q r s), inner ℂ (ι (omAct p q r s Z P)) (ι Q) = inner ℂ (ι P) (ι (omAct p q r s (Matrix.kroneckerMap (· * ·) (Jm p q) (Jm r s) * Z.conjTranspose * Matrix.kroneckerMap (· * ·) (Jm p q) (Jm r s)) Q)) := by
  intro p q r s H _ _ ι hι Z P Q
  refine GlobalTheory.FockAdj.inner_omAct hι _ _ ?_ P Q
  rintro ⟨a, c⟩ ⟨b, d⟩
  rw [Jm_eq_diagonal, Jm_eq_diagonal, Matrix.kroneckerMap_diagonal_diagonal _ (by simp) (by simp),
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;>
    simp [linePos]

end GlobalTheory.FockAdjLines
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IotaCompTrans
section
noncomputable section

namespace GlobalTheory.AbHomDesc

variable {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)

def iota (hI : RingHom.ker π = I) (S : Subring R) : S ⧸ I.comap S.subtype →+* R₀ :=
  Ideal.Quotient.lift _ (π.comp S.subtype) fun x hx => by
    have h : (x : R) ∈ I := hx
    rw [← hI] at h
    exact h

theorem iota_comp_mk (hI : RingHom.ker π = I) (S : Subring R) :
    (iota I π hI S).comp (Ideal.Quotient.mk _) = π.comp S.subtype := rfl

theorem iota_injective (hI : RingHom.ker π = I) (S : Subring R) : Function.Injective (iota I π hI S) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change (x : R) ∈ I
  rw [← hI]
  exact ha

def trans {S S' : Subring R} (h : S ≤ S') : S ⧸ I.comap S.subtype →+* S' ⧸ I.comap S'.subtype :=
  Ideal.quotientMap _ (Subring.inclusion h) fun x hx => hx

theorem iota_comp_trans (hI : RingHom.ker π = I) {S S' : Subring R} (h : S ≤ S') :
    (iota I π hI S').comp (trans I h) = iota I π hI S := by
  ext x
  rfl

theorem trans_comp_mk {S S' : Subring R} (h : S ≤ S') :
    (trans I h).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (Subring.inclusion h) := rfl

end GlobalTheory.AbHomDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteRingOfModule
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvP

theorem isAdicComplete_ring_of_module {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (p : ℕ) [h : IsAdicComplete (Ideal.span {(p : O)}) A] :
    IsAdicComplete (Ideal.span {(p : A)}) A := by
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(p : A)} ^ n • ⊤ : Submodule A A) ↔
      x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O A) := by
    intro n x
    rw [GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists, GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]
    simp [Algebra.smul_def]
  exact
    { haus' := fun x hx => IsHausdorff.haus h.toIsHausdorff x fun n =>
        SModEq.sub_mem.2 ((key n _).1 (SModEq.sub_mem.1 (hx n)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn =>
          SModEq.sub_mem.2 ((key _ _).1 (SModEq.sub_mem.1 (hf hmn)))
        exact ⟨L, fun n => SModEq.sub_mem.2 ((key _ _).2 (SModEq.sub_mem.1 (hL n)))⟩ }

theorem constantCoeff_nmul {O : Type} [CommRing O] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ j, constantCoeff (μ j) = 0) :
    ∀ (k : ℕ) (j : Fin d), constantCoeff (nmul μ k j) = 0 := by
  intro k
  induction k with
  | zero => intro j; rfl
  | succ k ihk =>
    intro j
    have hsucc : nmul μ (k + 1) j =
        subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (μ j) := by
      simp only [nmul, Function.iterate_succ_apply']
      rfl
    rw [hsucc]
    refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_ (hμ j) <;>
    · rintro (l | l)
      · simpa using ihk l
      · simp

theorem ev_subst_nmul_p : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), c.ev (n + 1) (subst (nmul c.μ p) s) = G.mulP n (c.ev n s) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c n s
  haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A (n + 1)) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  haveI : IsAdicComplete (Ideal.span {(p : G.A (n + 1))}) (G.A (n + 1)) :=
    isAdicComplete_ring_of_module (O := O) p
  have hT := (GlobalTheory.CEval.continuous_eval p O (G.A (n + 1)) (Fin d) (c.x (n + 1)) (c.nil (n + 1))).2
    (c.ev (n + 1)) (c.isEval (n + 1))
  let E' : MvPowerSeries (Fin d) O →ₐ[O] G.A (n + 1) :=
    (G.mulP n : G.A n →ₐ[O] G.A (n + 1)).comp (c.ev n)
  have hu : ∀ j, constantCoeff (nmul c.μ p j) = 0 :=
    constantCoeff_nmul c.μ (fun j => c.isLaw.const j) p
  have hE' : IsEval p (fun j => c.ev (n + 1) (nmul c.μ p j)) E' := by
    constructor
    · intro j
      show G.mulP n (c.ev n (X j)) = c.ev (n + 1) (nmul c.μ p j)
      rw [(c.isEval n).1 j, GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c (n + 1) p j, ← c.res n j, mulP_res]
    · intro m
      obtain ⟨N, hN⟩ := (c.isEval n).2 m
      refine ⟨N, fun f hf => ?_⟩
      have := map_dvd (G.mulP n : G.A n →ₐ[O] G.A (n + 1)) (hN f hf)
      rwa [map_pow, map_natCast] at this
  exact hT.1 (Fin d) (nmul c.μ p) E' hu hE' s

end GlobalTheory.EvP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacterHarishChandraProductCuspidalGLOfRegulStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card F) p.1 p.2) → ∀ n, n = deg L → IsChar ℂ ℂ (J θ L n) := by
  first | (exact @GlobalTheory.Shin.isChar_J_of_reg) | (exact GlobalTheory.Shin.isChar_J_of_reg) | (intros; apply GlobalTheory.Shin.isChar_J_of_reg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackCompSpreadToSubringStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_isGrpPullback_comp_of_subring_le : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → IsGrpPullback e.A d₀.A (spMap R₀.subtype) j → IsGrpPullback e.A u.A (spMap R₀.subtype ≫ h₀) (j ≫ ψ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ₁ : A₁.left ⟶ d₀.A.left), IsGrpPullback A₁ d₀.A (spMap (Subring.inclusion hle)) φ₁ → IsGrpPullback A₁ u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) := by
  first | exact @GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring | exact GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring | (intros; apply GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFlatPullbackReductionStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_flat_pullback_reduction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X Y : Over (Sp R)) (X₀ Y₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left) (j : Y₀.left ⟶ Y.left),
    IsPullback i X₀.hom X.hom (spMap π) → IsPullback j Y₀.hom Y.hom (spMap π) → Flat X.hom →
    ∀ (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀), i ≫ f.left = f₀.left ≫ j → IsIso f₀ → IsIso f := by
  first | exact @GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction | exact GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction | (intros; apply GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassVanishesFinitelyGeneratedSubalgebraStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_class_vanishes_finitely_generated_subalgebra : ∀ (q : ℕ) (A S : Type) [CommRing A] [CommRing S] [Algebra A S], IsUnit (q : A) → ∀ (n i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) n i), pull _ (spMap (laurentMap (algebraMap A S))) _ _ x = 0 → ∃ t : Finset S, pull _ (spMap (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S))))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.GmStep.KillColim.kill_colim) | (exact GlobalTheory.EtC.GmStep.KillColim.kill_colim) | (intros; apply GlobalTheory.EtC.GmStep.KillColim.kill_colim  <;> assumption)
end

