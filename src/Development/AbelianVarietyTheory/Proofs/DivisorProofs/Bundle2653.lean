import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLin
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObstructionPullbackEqZeroOfNaturalLift
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem obstructionPullback_eq_zero_of_naturalLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (C'' : Type) [Category.{0} C''] (F'' : C'' ⥤ CommAlgCat.{0} R₀) (L'' : Pre I π F'') (m : CoefMap (RingHom.id R₀) F' F'') (u : ∀ T : C'', L'.B (m.G.obj T) →ₐ[R] L''.B T) (v : ∀ T : C'', L.B (n.G.obj (m.G.obj T)) →ₐ[R] L''.B T), L.IsLift L' n l → L'.IsLift L'' m u → L'.IsNat L'' m u → (∀ T b, L''.p T (v T b) = m.α T (n.α _ (L.p _ b))) → (∀ (T T' : C'') (a : T ⟶ T') b, L''.ρ a (v T b) = v T' (L.ρ (n.G.map (m.G.map a)) b)) → ∀ (w : Glob1 F) (c : GlobalTheory.CatCoh.H1 (ext R₁ F')), L.IsOb1 L' n l α w c → (extMap R₁ m).pull1 c = 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C' _ F' L L' n l C'' _ F'' L'' m u v hl hu hun hvp hvn w c hc
  obtain ⟨κ, σ', z, hκ, hσ', rfl, hz⟩ := hc
  choose σ'' hσ'' using fun T : C'' ↦ GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T)
    (L''.semi T) (L''.surj T) (L''.ker T)

  have hdiff : ∀ (T : C'') (b : L.B (n.G.obj (m.G.obj T))),
      (u T).comp (l (m.G.obj T)) b - v T b ∈ I.map (algebraMap R (L''.B T)) := fun T b ↦ by
    refine (L''.ker T _).1 ?_
    rw [map_sub, sub_eq_zero]
    exact (hu T _).trans ((congrArg (m.α T) (hl _ b)).trans (hvp T b).symm)
  choose th hth using fun T : C'' ↦ ((theta_classify R R₀ (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T)))
    (L''.B T) I hI π hπ (L.p _) (L.semi _) (L.surj _) (L.ker _) ((u T).comp (l (m.G.obj T)))).1 (v T) (hdiff T)).exists

  have key : ∀ (T T' : C'') (a : T ⟶ T'),
      L''.ρ a (th T (w.1 (n.G.obj (m.G.obj T)))) =
        u T' (κ _ _ (m.G.map a) (w.1 (n.G.obj (m.G.obj T)))) + th T' (w.1 (n.G.obj (m.G.obj T'))) := by
    intro T T' a
    have h1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L'.B (m.G.obj T')) (L''.B T') _ _ _ (hκ _ _ (m.G.map a))).1 (u T')
    have h2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T'))) (F.obj (n.G.obj (m.G.obj T'))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L''.B T') (L''.B T') _ _ _ (hth T')).2 (L.ρ (n.G.map (m.G.map a)))
      (mp F (n.G.map (m.G.map a))) (fun x ↦ L.nat _ x)
    rw [AlgHom.comp_assoc] at h2
    have h3 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk _ _ (L.p (n.G.obj (m.G.obj T))) (L.semi _) (L.surj _) (L.ker _)
      (L''.B T') _ _ _ _ _ h1).2.1 h2
    have h4 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L''.B T) (L''.B T') _ _ _ (hth T)).1 (L''.ρ a)
    have e1 : (L''.ρ a).comp ((u T).comp (l (m.G.obj T))) =
        (u T').comp ((L'.ρ (m.G.map a)).comp (l (m.G.obj T))) := AlgHom.ext fun b ↦ hun a _
    have e2 : (L''.ρ a).comp (v T) = (v T').comp (L.ρ (n.G.map (m.G.map a))) := AlgHom.ext fun b ↦ hvn T T' a b
    rw [e1, e2] at h4
    have h5 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk _ _ (L.p (n.G.obj (m.G.obj T))) (L.semi _) (L.surj _) (L.ker _)
      (L''.B T') _ _ ((v T').comp (L.ρ (n.G.map (m.G.map a)))) _ _ h4).2.2 |>.1 <| h3
    have h6 := DFunLike.congr_fun h5 (w.1 (n.G.obj (m.G.obj T)))
    rw [w.2 (n.G.map (m.G.map a))]
    exact h6
  choose g hgK hg using fun T : C'' ↦ (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T)
    (L''.semi T) (L''.surj T) (L''.ker T) (σ'' T) (hσ'' T)).2.2.2 (-(th T (w.1 (n.G.obj (m.G.obj T)))))
    (neg_mem ((hth T).mem _))
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
  refine ⟨g, ?_⟩
  funext T T' a
  have sg := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T) (L''.semi T) (L''.surj T)
    (L''.ker T) (L''.B T') (F''.obj T') (L''.p T') (L''.semi T') (L''.surj T') (L''.ker T') (L''.ρ a) (mp F'' a)
    (fun b ↦ L''.nat a b) (σ'' T) (σ'' T') (hσ'' T) (hσ'' T')
  have su := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L'.B (m.G.obj T')) (F'.obj (m.G.obj T')) (L'.p _) (L'.semi _)
    (L'.surj _) (L'.ker _) (L''.B T') (F''.obj T') (L''.p T') (L''.semi T') (L''.surj T') (L''.ker T') (u T')
    (coefHom m T') (fun b ↦ hu T' b) (σ' _) (σ'' T') (hσ' _) (hσ'' T')
  haveI : Algebra.Smooth R (L''.B T') := L''.smooth T'
  change g T' - extHom R₁ (mp F'' a) (g T) = extHom R₁ (coefHom m T') (z.1 _ _ (m.G.map a))
  refine sub_eq_zero.1 (GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L''.B T') (F''.obj T') (L''.p T') (L''.semi T')
    (L''.surj T') (L''.ker T') (σ'' T') (hσ'' T') _ ?_ ?_)
  · have k1 := hgK T'
    have k2 := sg.2 _ (hgK T)
    have k3 := su.2 _ (hz _ _ (m.G.map a)).1
    unfold Aug.KerQ at k1 k2 k3 ⊢
    rw [map_sub, map_sub, k1, k2, k3, sub_zero, sub_zero]
  · rw [map_sub, map_sub, hg T', ← sg.1, hg T, ← su.1, (hz _ _ _).2, map_neg, key T T' a]
    abel

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOverStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ord_functionField_pullback_primeDivisor_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g := by
  first | exact @GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective | exact GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective | (intros; apply GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderActionMatrixEigenvalues
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
noncomputable section

namespace GlobalTheory.CommonEigField

open Module

theorem finrank_common_eig_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} {O : Type}
    (A : O → Matrix (Fin n) (Fin n) K) (m0 : O → K) :
    finrank K (⨅ a, LinearMap.ker (Matrix.toLin' (A a) - m0 a • LinearMap.id) : Submodule K (Fin n → K)) =
      finrank L (⨅ a, LinearMap.ker (Matrix.toLin' ((A a).map f) - f (m0 a) • LinearMap.id) :
        Submodule L (Fin n → L)) := by
  letI := f.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 f.injective
  refine ReciprocityTheory.ChartRestriction.G.Chart.finrank_eig_bc (V := K) (k := L) (fun a => Matrix.toLin' (A a))
    (fun a => Matrix.toLin' ((A a).map f)) (fun a c => ?_) m0
  funext i
  simp only [Matrix.toLin'_apply, Function.comp_apply]
  exact (RingHom.map_mulVec f (A a) c i).symm

theorem finrank_eigK_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {n : ℕ}
    (ρ : orderC c →+* Module.End R (Fin n → R)) (σ : E →+* K) :
    finrank K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      finrank K (⨅ a : orderC c, LinearMap.ker (Matrix.toLin' ((LinearMap.toMatrix' (ρ a)).map (algebraMap R K))
        - σ a • LinearMap.id) : Submodule K (Fin n → K)) := by
  classical
  let e := TensorProduct.piScalarRight R K K (Fin n)
  have hint : ∀ (a : orderC c) (y : K ⊗[R] (Fin n → R)),
      e ((ρ a).baseChange K y) = Matrix.toLin' ((LinearMap.toMatrix' (ρ a)).map (algebraMap R K)) (e y) := by
    intro a y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x v =>
      funext i
      simp only [LinearMap.baseChange_tmul, e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
        Matrix.toLin'_apply]
      rw [← LinearMap.toMatrix'_mulVec (ρ a) v]
      simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Matrix.map_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, _root_.mul_assoc]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hmap : Submodule.map (e : K ⊗[R] (Fin n → R) →ₗ[K] (Fin n → K)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      ⨅ a : orderC c, LinearMap.ker (Matrix.toLin' ((LinearMap.toMatrix' (ρ a)).map (algebraMap R K))
        - σ a • LinearMap.id) := by
    ext x
    rw [Submodule.mem_map_equiv]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [← e.injective.eq_iff, hint, LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply]
  rw [← e.finrank_map_eq, hmap]

theorem finrank_common_eig_basis {L : Type} [Field L] {W : Type*} [AddCommGroup W] [Module L W] {n : ℕ}
    (B : Module.Basis (Fin n) L W) {O : Type} (T : O → Module.End L W) (C : O → Matrix (Fin n) (Fin n) L)
    (hT : ∀ a i, T a (B i) = ∑ k, C a k i • B k) (m0 : O → L) :
    finrank L (⨅ a, Module.End.eigenspace (T a) (m0 a) : Submodule L W) =
      finrank L (⨅ a, LinearMap.ker (Matrix.toLin' (C a) - m0 a • LinearMap.id) : Submodule L (Fin n → L)) := by
  classical
  let e := B.equivFun
  have hint : ∀ a (w : W), e (T a w) = Matrix.toLin' (C a) (e w) := by
    intro a
    have h : T a = (e.symm.toLinearMap ∘ₗ Matrix.toLin' (C a)) ∘ₗ e.toLinearMap := by
      refine B.ext fun i => ?_
      rw [hT]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Module.Basis.equivFun_apply,
        Module.Basis.repr_self, Finsupp.single_eq_pi_single, Matrix.toLin'_apply, Matrix.mulVec_single_one,
        Module.Basis.equivFun_symm_apply, Matrix.col_apply]
    intro w
    rw [h]
    simp
  have hmap : Submodule.map (e : W →ₗ[L] (Fin n → L)) (⨅ a, Module.End.eigenspace (T a) (m0 a)) =
      ⨅ a, LinearMap.ker (Matrix.toLin' (C a) - m0 a • LinearMap.id) := by
    ext x
    rw [Submodule.mem_map_equiv]
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [← e.injective.eq_iff, hint, LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply]
  rw [← e.finrank_map_eq, hmap]

end GlobalTheory.CommonEigField

namespace GlobalTheory

open Module

theorem finrank_eigK_eq_finrank_eig_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E))
    (R : Subring ℂ) (n : ℕ)
    (ρ : orderC c →+* Module.End R (Fin n → R)) (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (B : Module.Basis (Fin n) ℂ W) (T : orderC c → Module.End ℂ W),
    (∀ a i, T a (B i) = ∑ k, ((ρ a (Pi.single i 1) k : R) : ℂ) • B k) →
    ∀ σ : E →+* FractionRing R, Module.finrank (FractionRing R) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      Module.finrank ℂ (⨅ a : orderC c, Module.End.eigenspace (T a) (j (σ a)) : Submodule ℂ W) := by
  intro E _ _ _ c R n ρ j hj W _ _ B T hT σ
  rw [CommonEigField.finrank_eigK_eq, CommonEigField.finrank_common_eig_map j,
    CommonEigField.finrank_common_eig_basis B T
      (fun a => ((LinearMap.toMatrix' (ρ a)).map (algebraMap R (FractionRing R))).map j) ?_]
  intro a i
  rw [hT]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.map_apply, LinearMap.toMatrix'_apply, hj]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginLocalRingNoetherianFreeUnitSectionConormal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin
variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

theorem constO_eq_strMap : constO G = (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.strMap G).hom := by
  ext r
  rw [GlobalTheory.HodgeTateCompare.strMap_eq]
  have h1 : (StructureSheaf.toStalk R (G.hom (origin G))).hom r =
      ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (G.hom (origin G)) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [Scheme.ΓSpecIso_inv]
    exact (congrArg (fun q => q.hom r) (StructureSheaf.toOpen_germ (R := R) ⊤ (G.hom (origin G)) trivial)).symm
  have h2 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.germ_stalkMap G.hom ⊤ (origin G) trivial)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  change _ = (G.hom.stalkMap (origin G)).hom ((StructureSheaf.toStalk R (G.hom (origin G))).hom r)
  rw [h1, h2]
  simp [constO, Scheme.Hom.appLE]
  first
    | (erw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]; done)
    | (erw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]; rfl)
    | (rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]; rfl)
    | (simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]; rfl)

theorem free_finite_cotangent_of_eq [Smooth G.hom] (φ : R →+* G.left.presheaf.stalk (origin G))
    (hφ : φ = (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.strMap G).hom) :
    letI : Algebra R (G.left.presheaf.stalk (origin G)) := φ.toAlgebra
    Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent := by
  subst hφ
  obtain ⟨h1, h2⟩ := GlobalTheory.HodgeTateCompare.finite_projective_of_smooth (G := G)
  change Module.Free R (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G) ∧ Module.Finite R (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G)
  exact ⟨Module.free_of_flat_of_isLocalRing, h1⟩

end GlobalTheory.CoordsOrigin

theorem GlobalTheory.CoordsOrigin.noetherian_free_cotangent : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Sp R)) [GrpObj G], Smooth G.hom → IsNoetherianRing (G.left.presheaf.stalk (origin G)) ∧
      (letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra;
        Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent) := by
  intro R _ _ _ G _ hs
  haveI := hs
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  exact ⟨inferInstance, GlobalTheory.CoordsOrigin.free_finite_cotangent_of_eq G _ (GlobalTheory.CoordsOrigin.constO_eq_strMap G)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSpecBaseChangeMapEqOfFieldExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory

theorem baseChange_map_eq_of_fieldExtension : ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f g : V ⟶ W), (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map g → (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map g := by
  intro R k Ω _ _ _ _ _ _ _ V W f g h
  have hu : Spec.map (CommRingCat.ofHom (algebraMap R Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h1 : pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ f.left =
      pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ g.left := by
    have := congrArg (fun φ => φ.left ≫ pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) h
    simp only [Over.pullback_map_left] at this
    erw [pullback.lift_fst, pullback.lift_fst] at this
    exact this
  set s := Spec.map (CommRingCat.ofHom (algebraMap R k)) with hs
  set t := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with ht
  rw [hu] at h1
  have f₁ : Flat t := by
    rw [ht, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField k) _
  have f₂ : Surjective t :=
    ⟨fun y => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have : Epi (pullback.fst (pullback.snd V.hom s) t) := Flat.epi_of_flat_of_surjective _
  have key : pullback.fst V.hom s ≫ f.left = pullback.fst V.hom s ≫ g.left := by
    rw [← cancel_epi (pullback.fst (pullback.snd V.hom s) t)]
    have hc : (pullback.fst (pullback.snd V.hom s) t ≫ pullback.fst V.hom s) ≫ V.hom =
        pullback.snd (pullback.snd V.hom s) t ≫ t ≫ s := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
    have he := pullback.lift_fst _ _ hc
    rw [← Category.assoc, ← Category.assoc, ← he, Category.assoc, Category.assoc, h1]
  apply Over.OverMorphism.ext
  simp only [Over.pullback_map_left]
  apply pullback.hom_ext
  · erw [pullback.lift_fst, pullback.lift_fst]
    exact key
  · erw [pullback.lift_snd, pullback.lift_snd]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicValNonneg
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD)

namespace GlobalTheory.JetIntegral

section Size

variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem l_pos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos

theorem sz_mul {r r' : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r' y) : Sz l lam (r + r') (x * y) := by
  obtain ⟨hx, h1⟩ := hx
  obtain ⟨hy, h2⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have e : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [e, map_mul, norm_mul, Real.rpow_add l_pos]
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg l_pos.le _)

theorem sz_one : Sz l lam 0 (1 : ℂ) := by
  refine ⟨one_mem _, ?_⟩
  have e : (⟨1, one_mem _⟩ : algebraicClosure ℚ ℂ) = 1 := rfl
  rw [e, map_one, norm_one, Real.rpow_zero]

theorem sz_pow {r : ℝ} {x : ℂ} (hx : Sz l lam r x) (n : ℕ) : Sz l lam ((n : ℝ) * r) (x ^ n) := by
  induction n with
  | zero => simpa using (sz_one (lam := lam))
  | succ n ih =>
    have h := sz_mul ih hx
    rw [pow_succ]
    convert h using 1
    push_cast; ring

theorem sz_prod {ι : Type} (s : Finset ι) (r : ι → ℝ) (f : ι → ℂ) (h : ∀ i ∈ s, Sz l lam (r i) (f i)) :
    Sz l lam (∑ i ∈ s, r i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (sz_one (lam := lam))
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact sz_mul (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sz_inv_l_pow (n : ℕ) : Sz l lam (n : ℝ) (((l : ℂ) ^ n)⁻¹) := by
  have hmem : ((l : ℂ) ^ n)⁻¹ ∈ algebraicClosure ℚ ℂ :=
    inv_mem (pow_mem (natCast_mem _ l) n)
  refine ⟨hmem, ?_⟩
  have e : (⟨((l : ℂ) ^ n)⁻¹, hmem⟩ : algebraicClosure ℚ ℂ) = ((l : algebraicClosure ℚ ℂ) ^ n)⁻¹ := by
    apply Subtype.ext; simp
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h1 := PadicComplex.norm_extends' l (l : ℚ_[l])
    rw [Padic.norm_p] at h1
    simpa using h1
  rw [e, map_inv₀, map_pow, map_natCast, norm_inv, norm_pow, hl, inv_pow, inv_inv, Real.rpow_natCast]

theorem sz_sign (ε : ℤˣ) : Sz l lam 0 (((ε : ℤ) : ℂ)⁻¹) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using (sz_one (lam := lam))
  · have hmem : (-1 : ℂ) ∈ algebraicClosure ℚ ℂ := neg_mem (one_mem _)
    have e : (⟨-1, hmem⟩ : algebraicClosure ℚ ℂ) = -1 := rfl
    refine ⟨by simpa using hmem, ?_⟩
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, inv_neg, inv_one]
    rw [e, map_neg, map_one, norm_neg, norm_one, Real.rpow_zero]

end Size

theorem expand_id {I : Type} [Fintype I] (D x m C e : ℂ) (a b A : I → ℂ) (κ : I → ℕ) (k : ℕ)
    (hm : m ≠ 0) (he : e ≠ 0) (ha : ∀ i, a i ≠ 0) (hA : ∀ i, A i ≠ 0)
    (h : C ^ k * x = m * D * ∏ i, (e * A i) ^ κ i) :
    D * ∏ i, ((b i / a i) ^ κ i / a i ^ k) = x * m⁻¹ * (C / ∏ i, a i) ^ k * ∏ i, (e⁻¹ * (b i / (a i * A i))) ^ κ i := by
  have h3 : ∏ i, (e⁻¹ * (b i / (a i * A i))) ^ κ i = (∏ i, (b i / a i) ^ κ i) / ∏ i, (e * A i) ^ κ i := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← div_pow]
    congr 1
    field_simp [ha i, hA i, he]
  have h1 : ∏ i, ((b i / a i) ^ κ i / a i ^ k) = (∏ i, (b i / a i) ^ κ i) / ∏ i, a i ^ k := by
    rw [Finset.prod_div_distrib]
  have h2 : (C / ∏ i, a i) ^ k = C ^ k / ∏ i, a i ^ k := by rw [div_pow, Finset.prod_pow]
  have hP2 : ∏ i, a i ^ k ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (ha i)
  have hP3 : ∏ i, (e * A i) ^ κ i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (mul_ne_zero he (hA i))
  rw [h1, h2, h3]
  generalize ∏ i, (b i / a i) ^ κ i = P1 at *
  generalize ∏ i, a i ^ k = P2 at *
  generalize ∏ i, (e * A i) ^ κ i = P3 at *
  field_simp
  linear_combination (-P1) * h

end GlobalTheory.JetIntegral

namespace GlobalTheory.JetIntegral

theorem padicVal_nonneg {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (z : ClassGroup (OF E) → ℚ)
    (C : ClassGroup (OF E)) :
    0 ≤ padicValRat l ((l : ℚ) ^ cE_vp l z * (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))) := by
  have hl : (l : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  by_cases hq : z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E) = 0
  · rw [hq, mul_zero, padicValRat.zero]
  rw [padicValRat.mul (pow_ne_zero _ hl) hq, padicValRat.pow, padicValRat.self (Fact.out : l.Prime).one_lt, mul_one]
  have h1 : (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat ≤ cE_vp l z :=
    Finset.le_sup (f := fun C => (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat)
      (Finset.mem_univ C)
  have h2 := Int.self_le_toNat (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)))
  have h3 : ((-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat : ℤ) ≤ (cE_vp l z : ℤ) := by
    exact_mod_cast h1
  omega

theorem jetInt : EisRule → JetCore → ModelInt → JetInt := by
  intro hEis hJet hMod
  intro E _ _ _ _ I _ d φ s hFD hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy _ lam Ω hΩ
  classical
  obtain ⟨𝔠, R, hloc, X₀, δ₀, N, T, a, b, hR0, hRq, hAdm, hOver, hab, hC⟩ :=
    hMod E I d φ s hFD hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy lam Ω hΩ
  refine ⟨a, b, fun i => ⟨(hab i).1, (hab i).2.1, (hab i).2.2.2.1, (hab i).2.2.2.2.1⟩, ?_⟩
  intro g κ u hg hu
  obtain ⟨-, -, hUn, -, -, -, hCM, -⟩ := hFD
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := GlobalTheory.LatAlgebraic.two_le_finrank hUn
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  set m : ℂ := (l : ℂ) ^ cE_vp l z with hmdef
  have hm0 : m ≠ 0 := pow_ne_zero _ hl0
  have hmR : m ∈ R := by
    have h := hRq ((l : ℚ) ^ cE_vp l z) (by
      rw [padicValRat.pow, padicValRat.self hl.one_lt]; positivity)
    simpa [hmdef] using h
  have hmz : ∀ C, m * ((z C / 2 ^ Module.finrank ℚ (FR E) : ℚ) : ℂ) ∈ R := by
    intro C
    have h := hRq _ (padicVal_nonneg l z C)
    convert h using 1
    push_cast [hmdef]
    ring
  obtain ⟨r, hr⟩ := hEis E hf2 𝔠 s hs z hz R m hmR hmz
  obtain ⟨ε, hε⟩ := hJet
  obtain ⟨x, hx⟩ := hε E I 𝔠 hf2 R s r hs R X₀ δ₀ N hAdm κ
  have hxe := hx R.subtype (fun a => rfl) φ (condQ 𝔣 Q) y m hCM hc0 (hr I φ (condQ 𝔣 Q) y hCM hc0) T hOver g u hg hu
  have hε0 : ((ε : ℤ) : ℂ) ≠ 0 := by exact_mod_cast ε.ne_zero
  rw [expand_id (iterD u g 0) (R.subtype x) m T.C ((ε : ℤ) : ℂ) a b T.A κ (2 * s) hm0 hε0 (fun i => (hab i).1)
    (fun i => (hab i).2.2.1) hxe]
  have hx0 : Sz l lam 0 (R.subtype x) := hR0 _ x.2
  have hmi : Sz l lam (cE_vp l z : ℝ) m⁻¹ := sz_inv_l_pow _
  have hCp := sz_pow hC (2 * s)
  have hP := sz_prod Finset.univ (fun i => (κ i : ℝ) * (0 + c_vp 𝔣 l)) _
    (fun i _ => sz_pow (sz_mul (sz_sign ε) (hab i).2.2.2.2.2) (κ i))
  have htot := sz_mul (sz_mul (sz_mul hx0 hmi) hCp) hP
  convert htot using 1
  push_cast
  rw [← Finset.sum_mul]
  ring

end GlobalTheory.JetIntegral
end
end

