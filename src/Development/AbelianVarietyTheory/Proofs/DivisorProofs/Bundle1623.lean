import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1590
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveBaseChangeTwoDistinctPointsOfFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_baseChange_two_distinct_points_of_field : ∀ (R F : Type) [CommRing R] [Field F] (ψ : R →+* F) (X : Over (Sp R)) (P₁ : Polynomial R) (u₁ : Sp (Localization.Away P₁) ⟶ X.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ X.hom = spMap (algebraMap R (Localization.Away P₁)) → IsUnit (ψ P₁.leadingCoeff) → spMap ψ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap ψ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ → ∃ (P' : Polynomial F) (_ : P' ≠ 0) (u' : Sp (Localization.Away P') ⟶ ((Over.pullback (spMap ψ)).obj X).left) (a' b' : Localization.Away P' →ₐ[F] F), u' ≫ ((Over.pullback (spMap ψ)).obj X).hom = spMap (algebraMap F (Localization.Away P')) ∧ spMap a'.toRingHom ≫ u' ≠ spMap b'.toRingHom ≫ u' := by
  first | exact @GlobalTheory.curve_baseChange_two_points | exact GlobalTheory.curve_baseChange_two_points | (intros; apply GlobalTheory.curve_baseChange_two_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRealFamilyArchimedeanLinearStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxCoords_real_family_archimedean_linear : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ] (e : Formalism.IndefR.Datum.WO S T ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∃ P Q : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F), ∀ t, e (L t) = (fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i)) 0, fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i)) 0) := by
  first | exact @GlobalTheory.RealDirCoord.darboux_real_coords | exact GlobalTheory.RealDirCoord.darboux_real_coords | (intros; apply GlobalTheory.RealDirCoord.darboux_real_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAngleFormReEqStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_angleForm_re_eq : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E), ContDiffAt ℝ 2 a z → ContDiffAt ℝ 2 a' z → ContDiffAt ℝ 2 q z → 0 < a z → 0 < a' z → (dbar (angleForm n a a' q ξ) z ξ).re = (n + 1) * (‖q z‖ ^ 2 / (a z * a' z)) ^ n * ((‖del q z ξ - q z * del (fun x => (Real.log (a' x) : ℂ)) z ξ‖ ^ 2 - ‖dbar q z ξ - q z * dbar (fun x => (Real.log (a x) : ℂ)) z ξ‖ ^ 2) / (a z * a' z)) + (‖q z‖ ^ 2 / (a z * a' z)) ^ (n + 1) * ((leviForm (fun x => Real.log (a x)) z ξ ξ).re - (leviForm (fun x => Real.log (a' x)) z ξ ξ).re) := by
  first | exact @GlobalTheory.CurveDens.re_dbar_angleForm | exact GlobalTheory.CurveDens.re_dbar_angleForm | (intros; apply GlobalTheory.CurveDens.re_dbar_angleForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCompHolomorphicStatement
section
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_comp_holomorphic : ∀ {n m : ℕ} {φ : V n → V m} {c : V m → ℂ} {v : V n}, DifferentiableAt ℂ φ v → DifferentiableAt ℝ c (φ v) → ∑ a, GlobalTheory.dbar (fun x => c (φ x)) v (coordVec a) • dzb a = pull (fderiv ℂ φ v) (∑ b, GlobalTheory.dbar c (φ v) (coordVec b) • dzb b) := by
  first | exact @GlobalTheory.CxForm.sum_dbar_comp_smul_dzb | exact GlobalTheory.CxForm.sum_dbar_comp_smul_dzb | (intros; apply GlobalTheory.CxForm.sum_dbar_comp_smul_dzb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDensityOfTransitionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_density_of_transition : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → IsDens (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) := by
  first | exact @GlobalTheory.CurveDens.isDens_re_dbar_coeff | exact GlobalTheory.CurveDens.isDens_re_dbar_coeff | (intros; apply GlobalTheory.CurveDens.isDens_re_dbar_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSumLeibnizStatement
section
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_sum_leibniz : ∀ {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}, (∀ i, DifferentiableAt ℝ (c i) v) → (∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) → dbarAt (fun x => ∑ i, c i x • F i x) v = ∑ i, ((∑ a, GlobalTheory.dbar (c i) v (coordVec a) • dzb a) * F i v + c i v • dbarAt (F i) v) := by
  first | exact @GlobalTheory.CxForm.dbarAt_sum_smul | exact GlobalTheory.CxForm.dbarAt_sum_smul | (intros; apply GlobalTheory.CxForm.dbarAt_sum_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqOfLocalEq
section
set_option autoImplicit false

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm.DdcGerm

theorem repr_eventuallyEq {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) (S : Finset (Fin (n + n))) :
    (fun x => (bas n).repr (α x) S) =ᶠ[𝓝 v] fun x => (bas n).repr (β x) S :=
  h.mono fun x hx => by simp only [hx]

theorem delAt_germ {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : delAt α v = delAt β v := by
  simp only [delAt, coefwise]
  refine Finset.sum_congr rfl fun a _ => congrArg _ (Finset.sum_congr rfl fun S _ => ?_)
  rw [del_congr (repr_eventuallyEq h S)]

theorem dbarAt_germ {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : dbarAt α v = dbarAt β v := by
  simp only [dbarAt, coefwise]
  refine Finset.sum_congr rfl fun a _ => congrArg _ (Finset.sum_congr rfl fun S _ => ?_)
  rw [dbar_congr (repr_eventuallyEq h S)]

theorem loc_dbar_of_mem {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (α : A.Fld) (i : A.ι) {v : V n}
    (hv : v ∈ (A.e i).target) : A.loc (A.dbar α) i v = dbarAt (A.loc α i) v := by
  rw [HolAtlas.loc, dif_pos hv]
  exact congrArg (dbarAt (A.loc α i)) ((A.e i).right_inv hv)

theorem ddc_eq_of_eventuallyEq : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (α : A.Fld) (x : A.Pt)
    (f : V n → Alt n), A.loc α x.1.1 =ᶠ[𝓝 x.crd] f → A.ddc α x = kappa • delAt (dbarAt f) x.crd := by
  intro M _ n A α x f h
  have ht : (A.e x.1.1).target ∈ 𝓝 x.crd := (A.e x.1.1).open_target.mem_nhds ((A.e x.1.1).map_source x.2)
  have key : A.loc (A.dbar α) x.1.1 =ᶠ[𝓝 x.crd] dbarAt f := by
    filter_upwards [ht, h.eventuallyEq_nhds] with v hv hv'
    rw [loc_dbar_of_mem A α _ hv, dbarAt_germ hv']
  change kappa • delAt (A.loc (A.dbar α) x.1.1) x.crd = _
  rw [delAt_germ key]

end GlobalTheory.SecForm.DdcGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcOfValuesEq
section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecForm.DdcValues

variable {n : ℕ}

theorem coefwise_del_sum {ι : Type} [Fintype ι] {g : ι → V n → ℂ} (w : ι → Alt n) {β : V n → Alt n} {v : V n}
    (hg : ∀ i, DifferentiableAt ℝ (g i) v) (hβ : ∀ᶠ x in 𝓝 v, β x = ∑ i, g i x • w i) (ξ : V n) :
    coefwise (fun f => del f v ξ) β = ∑ i, del (g i) v ξ • w i := by
  have h (S) : del (fun x => (bas n).repr (β x) S) v ξ = ∑ i, del (g i) v ξ * (bas n).repr (w i) S := by
    have e : (fun x => (bas n).repr (β x) S) =ᶠ[𝓝 v] fun x => ∑ i, (bas n).repr (w i) S • g i x :=
      hβ.mono fun x hx => by simp [hx, Finsupp.finsetSum_apply, mul_comm]
    rw [del_congr e, del_sum (A := fun i x => (bas n).repr (w i) S • g i x) (fun i _ => (hg i).const_smul ((bas n).repr (w i) S)), ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [del_const_smul _ (hg i)]
    simp [mul_comm]
  simp only [coefwise, h, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_smul, ← Finset.smul_sum, Module.Basis.sum_repr]

theorem coefwise_dbar_sum {ι : Type} [Fintype ι] {g : ι → V n → ℂ} (w : ι → Alt n) {v : V n}
    (hg : ∀ i, DifferentiableAt ℝ (g i) v) (ξ : V n) :
    coefwise (fun f => dbar f v ξ) (fun x => ∑ i, g i x • w i) = ∑ i, dbar (g i) v ξ • w i := by
  have h (S) : dbar (fun x => (bas n).repr (∑ i, g i x • w i) S) v ξ =
      ∑ i, dbar (g i) v ξ * (bas n).repr (w i) S := by
    have e : (fun x => (bas n).repr (∑ i, g i x • w i) S) = fun x => ∑ i, (bas n).repr (w i) S • g i x :=
      funext fun x => by simp [Finsupp.finsetSum_apply, mul_comm]
    rw [e, dbar_sum (A := fun i x => (bas n).repr (w i) S • g i x) (fun i _ => (hg i).const_smul ((bas n).repr (w i) S)), ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dbar_const_smul _ (hg i)]
    simp [mul_comm]
  simp only [coefwise, h, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_smul, ← Finset.smul_sum, Module.Basis.sum_repr]

theorem sym_mul_sym_swap (a b c d : Fin n) : sym (a, b) * sym (c, d) = -(sym (a, d) * sym (c, b)) := by
  apply Subtype.ext
  change dz a * dzb b * (dz c * dzb d) = -(dz a * dzb d * (dz c * dzb b))
  have h₁ : dzb b * (dz c * dzb d) = dz c * dzb d * dzb b :=
    Subalgebra.mem_center_iff.1 (sym (c, d)).2 _
  have h₂ : dzb d * (dz c * dzb b) = dz c * dzb b * dzb d :=
    Subalgebra.mem_center_iff.1 (sym (c, b)).2 _
  have h₃ : dzb d * dzb b = -(dzb b * dzb d) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  rw [mul_assoc, mul_assoc, h₁, h₂, mul_assoc, mul_assoc, h₃]
  simp only [mul_neg]

theorem sum_four (D : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, (D a b c d + D c d a b - D a d c b - D c b a d) • (sym (a, b) * sym (c, d)) =
      (4 : ℂ) • ∑ a, ∑ b, ∑ c, ∑ d, D a b c d • (sym (a, b) * sym (c, d)) := by
  have P (F : Fin n → Fin n → Fin n → Fin n → Ev n) : ∑ a, ∑ b, ∑ c, ∑ d, F a b c d =
      ∑ p : Fin n × Fin n × Fin n × Fin n, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  rw [P, P]
  simp only [sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  set T := ∑ p : Fin n × Fin n × Fin n × Fin n,
    D p.1 p.2.1 p.2.2.1 p.2.2.2 • (sym (p.1, p.2.1) * sym (p.2.2.1, p.2.2.2)) with hT
  have h₂ : ∑ p : Fin n × Fin n × Fin n × Fin n,
      D p.2.2.1 p.2.2.2 p.1 p.2.1 • (sym (p.1, p.2.1) * sym (p.2.2.1, p.2.2.2)) = T :=
    Fintype.sum_equiv ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => by simp [mul_comm]
  have h₃ : ∑ p : Fin n × Fin n × Fin n × Fin n,
      D p.1 p.2.2.2 p.2.2.1 p.2.1 • (sym (p.1, p.2.1) * sym (p.2.2.1, p.2.2.2)) = -T := by
    rw [hT, ← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv ⟨fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1), fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => by rw [sym_mul_sym_swap, smul_neg]; rfl
  have h₄ : ∑ p : Fin n × Fin n × Fin n × Fin n,
      D p.2.2.1 p.2.1 p.1 p.2.2.2 • (sym (p.1, p.2.1) * sym (p.2.2.1, p.2.2.2)) = -T := by
    rw [hT, ← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv ⟨fun p => (p.2.2.1, p.2.1, p.1, p.2.2.2), fun p => (p.2.2.1, p.2.1, p.1, p.2.2.2),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => by rw [sym_mul_sym_swap, smul_neg, mul_comm]; rfl
  rw [h₂, h₃, h₄]
  module

end GlobalTheory.SecForm.DdcValues

namespace GlobalTheory.SecForm

open DdcValues

theorem ddc_ofValues {n : ℕ} (α : V n → V n → V n → ℂ) (v : V n)
    (h : ∀ a b, ContDiffAt ℝ 2 (fun x => α x (coordVec a) (coordVec b)) v) :
    kappa • delAt (dbarAt fun x => (ofValues (α x) : Alt n)) v = (ofValuesTwo (ddcForm α v) : Alt n) := by
  set f : Fin n × Fin n → V n → ℂ := fun p x => α x (coordVec p.1) (coordVec p.2) with hf
  have e₀ : (fun x => (ofValues (α x) : Alt n)) = fun x => ∑ p, f p x • (sym p : Alt n) := by
    funext x
    simp only [ofValues, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, Fintype.sum_prod_type, hf]
  have hev : ∀ᶠ x in 𝓝 v, ∀ p, DifferentiableAt ℝ (f p) x :=
    eventually_all.2 fun p => ((h p.1 p.2).eventually (by simp)).mono fun x hx => hx.differentiableAt (by simp)
  have e₁ : ∀ᶠ x in 𝓝 v, dbarAt (fun x => (ofValues (α x) : Alt n)) x =
      ∑ q : Fin n × Fin n × Fin n, dbar (f q.2) x (coordVec q.1) • (dzb q.1 * sym q.2) := by
    filter_upwards [hev] with x hx
    rw [e₀, dbarAt, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coefwise_dbar_sum _ hx, Finset.mul_sum]
    simp only [mul_smul_comm]
  have hd (q : Fin n × Fin n × Fin n) : DifferentiableAt ℝ (fun x => dbar (f q.2) x (coordVec q.1)) v := by
    have h1 := (h q.2.1 q.2.2).fderiv_right (m := 1) (by norm_num)
    simp only [dbar_apply]
    exact (((h1.clm_apply contDiffAt_const).add
      ((h1.clm_apply contDiffAt_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)).differentiableAt one_ne_zero
  have e₂ : delAt (dbarAt fun x => (ofValues (α x) : Alt n)) v =
      ((∑ a, ∑ b, ∑ c, ∑ d, ddbar (f (c, d)) v (coordVec a) (coordVec b) • (sym (a, b) * sym (c, d)) : Ev n) :
        Alt n) := by
    simp only [delAt, coefwise_del_sum _ hd e₁, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul,
      Subalgebra.coe_mul, Fintype.sum_prod_type, Finset.mul_sum, mul_smul_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    rw [ddbar_eq_del_dbar (h c d), ← mul_assoc]
    rfl
  rw [e₂, ← Subalgebra.coe_smul]
  congr 1
  have := sum_four fun a b c d => ddbar (f (c, d)) v (coordVec a) (coordVec b)
  simp only [ofValuesTwo, ddcForm, mul_smul, ← Finset.smul_sum]
  erw [this]
  module

end GlobalTheory.SecForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

variable {n : ℕ}

def dOne (f : V n → ℂ) (v : V n) : Alt n := ∑ a, del f v (coordVec a) • dz a

theorem delAt_eq_sum_dOne (β : V n → Alt n) (u : V n) :
    delAt β u = ∑ T, dOne (fun x => (bas n).repr (β x) T) u * bas n T := by
  simp only [delAt, coefwise, dOne, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  exact Finset.sum_comm

theorem delAt_congr {F G : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] G) : delAt F v = delAt G v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => congrArg _ (Finset.sum_congr rfl fun S _ => ?_)
  have e : del (fun x => (bas n).repr (F x) S) v = del (fun x => (bas n).repr (G x) S) v :=
    del_congr (h.fun_comp fun y => (bas n).repr y S)
  simp only [e]

end GlobalTheory.CxForm.DelForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelMulOfDelEqZero
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.CxForm.DelClosed

theorem del_mul_of_del_eq_zero : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n)
    (α β : A.Fld), A.IsForm α → A.IsForm β → A.del β = 0 → A.del (α * β) = A.del α * β := by
  intro M _ n A α β hα hβ hdβ
  funext x
  have hl : A.loc (α * β) x.1.1 = fun v => A.loc α x.1.1 v * A.loc β x.1.1 v :=
    funext (FormMul.loc_mul A α β _)
  obtain ⟨y, hy⟩ := FormMul.delAt_mul (FormMul.differentiableAt_coef hα x) (FormMul.differentiableAt_coef hβ x)
  have h2 : delAt (A.loc β x.1.1) x.crd = 0 := congrFun hdβ x
  show delAt (A.loc (α * β) x.1.1) x.crd = delAt (A.loc α x.1.1) x.crd * β x
  rw [hl, hy, h2, mul_zero, add_zero, HolAtlas.loc_crd]

end GlobalTheory.CxForm.DelClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTApply
section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.DblTargetDelta

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}

def topR (x : WOF F E nS (nT + nT)) : WOF F E nS nT := x.submatrix (finSumFinEquiv ∘ Sum.inl) id

def botR (x : WOF F E nS (nT + nT)) : WOF F E nS nT := x.submatrix (finSumFinEquiv ∘ Sum.inr) id

def deltaT (f₁ f₂ : WOF F E nS nT → ℂ) : WOF F E nS (nT + nT) → ℂ :=
  fun x => f₁ (topR x) * conj (f₂ (-botR x))

theorem deltaT_apply (f₁ f₂ : WOF F E nS nT → ℂ) (x : WOF F E nS (nT + nT)) :
    deltaT f₁ f₂ x = f₁ (topR x) * conj (f₂ (-botR x)) := rfl

end GlobalTheory.DblTargetDelta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMRealLineFiniteInvariantStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deriv_heisenbergCM_real_line_finite_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ u : Formalism.IndefR.DatumF.WOF F E nS nT, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) f = f →
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) (fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0) = fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  first | exact @GlobalTheory.HeisDerivCM.heisOF_deriv_fix | exact GlobalTheory.HeisDerivCM.heisOF_deriv_fix | (intros; apply GlobalTheory.HeisDerivCM.heisOF_deriv_fix <;> assumption)
end

