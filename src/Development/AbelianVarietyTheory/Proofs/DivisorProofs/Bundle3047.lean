import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2993
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2977
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0495
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3041
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpFormEqZeroOfTangent
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LieInjField

open GlobalTheory.CechDR in

theorem cmpForm_surjective (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) : Function.Surjective (cmpForm (A.hom ≫ 𝟙 (Sp R))) := by
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.smooth; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hcmp := (cechDeRham_comparison_bijective_cup_smooth hC R A.left _ hsm hsep hqc).1
  have hcl : Function.Injective (clForm (A.hom ≫ 𝟙 (Sp R))) := (hH R A g hab hdim).2.2.2.2.1.2.1
  intro ω
  obtain ⟨c, hc⟩ := hcmp.2 (clForm _ ω)
  have hF : clForm _ ω ∈ CechHodgeFiltration (A.hom ≫ 𝟙 (Sp R)) := by rw [cechHodgeFiltration_eq_range]; exact ⟨ω, rfl⟩
  have h1 : c ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := by
    change toH1O _ c = 0
    apply GlobalTheory.T.structure_sheaf_comparison_injective R A.left _
    rw [← structureSheaf_comparison_comm, map_zero, hc]
    exact hF
  rw [hodgeFiltration_eq_range] at h1
  obtain ⟨f, rfl⟩ := h1
  rw [comparison_formClass] at hc
  exact ⟨f, hcl hc⟩

theorem cmpForm_eq_zero_of_tangent (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] (g : ℕ) (hab : IsAbelianScheme B)
    (hdim : SmoothOfRelativeDimension g B.hom) (f : Form (B.hom ≫ 𝟙 (Sp K)))
    (hf : ∀ v : epsR K ⟶ B, IsTangent v → tanVal v f = 0) :
    GlobalTheory.CechDR.cmpForm (B.hom ≫ 𝟙 (Sp K)) f = 0 := by
  haveI := hab.comm
  have hsm : Smooth B.hom := hab.smooth
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_lieBasis_smooth_commGroupScheme_field K B g hdim
  refine GlobalTheory.T.cmpForm_eq_zero_of_pullback_vanishing K B hsm f fun L _ σ ↦ ?_
  letI : GrpObj ((Over.pullback (spMap σ)).obj B) := Functor.grpObjObj
  have hG := isGrpPullback_pullback B (spMap σ)
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hG
  haveI := hab'.comm
  have hdim' : SmoothOfRelativeDimension g ((Over.pullback (spMap σ)).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hG.1 hdim
  have m : IsMor (dp0 K) (B.hom ≫ 𝟙 (Sp K)) (dp0 L) (((Over.pullback (spMap σ)).obj B).hom ≫ 𝟙 (Sp L)) σ
      (Limits.pullback.fst B.hom (spMap σ)) := IsMor.of_dividedPowersZeroIdeal _ (by simpa using hG.1.w)
  refine ⟨_, _, m, hG.1, fun u ↦ ?_⟩
  let c : epsR L ⟶ (Over.pullback (spMap σ)).obj B := GlobalTheory.GrpTangent.epsScale 0 ≫ u
  have hc : tanVal c (m.pullForm f) = 0 := by
    rw [tanVal_epsScale, zero_mul]
  have ht : IsTangent (c⁻¹ * u) := by
    rw [GlobalTheory.GrpTangent.isTangent_iff, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      GlobalTheory.GrpTangent.epsZero_epsScale, inv_mul_cancel]
  have e : u = c * (c⁻¹ * u) := (mul_inv_cancel_left c u).symm
  rw [e, GlobalTheory.T.crystallineForm_tangentValue_mul_abelianScheme hC hH L _ g hab' hdim', hc, zero_add]
  exact GlobalTheory.T.pullbackForm_vanishes_tangents_of_lieBasis K B hsm g y hy f (fun i ↦ hf _ (hy.1 i)) L σ _ _ hG m _ ht

def lieVal (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] :
    Serre.Lie (Serre.intAct B) →ₗ[K] Module.Dual K (Form (B.hom ≫ 𝟙 (Sp K))) where
  toFun v := tanVal v.hom
  map_add' v w := LinearMap.ext fun f ↦ tanVal_mul v.isTangent w.isTangent f
  map_smul' r v := LinearMap.ext fun f ↦ tanVal_epsScale r v.hom f

theorem lieVal_apply (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B]
    (v : Serre.Lie (Serre.intAct B)) : lieVal K B v = tanVal v.hom := rfl

theorem eq_of_tanVal_eq : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ v w : epsR K ⟶ B, IsTangent v → IsTangent w → (∀ f : Form (B.hom ≫ 𝟙 (Sp K)), tanVal v f = tanVal w f) → v = w := by
  intro hC hH K _ B _ g hab hdim v w hv hw h
  haveI := hab.comm
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_lieBasis_smooth_commGroupScheme_field K B g hdim
  let b := Serre.Lie.basis (Serre.intAct B) hy
  haveI := Module.Finite.of_basis b
  have hL : Module.finrank K (Serre.Lie (Serre.intAct B)) = g := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have htop : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) = ⊤ := (hH K B g hab hdim).2.2.2.2.1.1
  obtain ⟨hfin, -, hrk⟩ : Module.Finite K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) ∧
      Module.Projective K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) ∧
      ∀ p : PrimeSpectrum K, Module.rankAtStalk (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) p = g :=
    (hH K B g hab hdim).2.2.1
  have hG : Module.finrank K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) = g := by
    have h' := hrk (IsLocalRing.closedPoint K)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at h'
  let eC : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) ≃ₗ[K] GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K)) := LinearEquiv.ofTop _ htop
  haveI : Module.Finite K (GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K))) := Module.Finite.equiv eC.symm
  have hC' : Module.finrank K (GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K))) = g := by rw [eC.finrank_eq, hG]
  let c := GlobalTheory.CechDR.cmpForm (B.hom ≫ 𝟙 (Sp K))
  have hcs : Function.Surjective c := cmpForm_surjective hC hH K B g hab hdim
  let P := lieVal K B
  have hker : LinearMap.ker c ≤ LinearMap.ker P.flip := fun f hf ↦
    LinearMap.ext fun u ↦ GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero K B u.hom f hf
  let T : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) →ₗ[K] Module.Dual K (Serre.Lie (Serre.intAct B)) :=
    (LinearMap.ker c).liftQ P.flip hker ∘ₗ (c.quotKerEquivOfSurjective hcs).symm.toLinearMap
  have hT : ∀ f, T (c f) = P.flip f := fun f ↦ by
    have : (c.quotKerEquivOfSurjective hcs).symm (c f) = Submodule.Quotient.mk f :=
      (c.quotKerEquivOfSurjective hcs).symm_apply_eq.2 rfl
    change (LinearMap.ker c).liftQ P.flip hker ((c.quotKerEquivOfSurjective hcs).symm (c f)) = _
    rw [this]; rfl
  have hTi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro ω hω
    obtain ⟨f, rfl⟩ := hcs ω
    rw [LinearMap.mem_ker, hT] at hω
    exact cmpForm_eq_zero_of_tangent hC hH K B g hab hdim f fun v hv ↦
      LinearMap.congr_fun hω (Serre.Lie.mk (Serre.intAct B) v hv)
  have hTs : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Subspace.dual_finrank_eq, hL, hC'])).1 hTi
  let V := Serre.Lie.mk (Serre.intAct B) v hv
  let W := Serre.Lie.mk (Serre.intAct B) w hw
  have hsurj : Function.Surjective (T ∘ₗ c) := hTs.comp hcs
  have key : ∀ φ : Module.Dual K (Serre.Lie (Serre.intAct B)), φ V = φ W := fun φ ↦ by
    obtain ⟨f, rfl⟩ := hsurj φ
    rw [LinearMap.comp_apply, hT]
    exact h f
  have hVW : V - W = 0 :=
    (Module.forall_dual_apply_eq_zero_iff K (V - W)).1 fun φ ↦ by rw [map_sub, key φ, sub_self]
  exact congrArg Serre.Lie.hom (sub_eq_zero.1 hVW)

end GlobalTheory.LieInjField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.DimCoheight

theorem trdeg_eq_of_isFractionRing (R A K : Type) [CommRing R] [Nontrivial R] [CommRing A] [IsDomain A]
    [Field K] [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K] [FaithfulSMul R A]
    [IsFractionRing A K] : Algebra.trdeg R K = Algebra.trdeg R A := by
  have _ : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A K)
  have _ : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  rw [← trdeg_add_eq R A (A := K), trdeg_eq_zero (R := A) (A := K), add_zero]

theorem exists_ringKrullDim_affine_eq (Y : Scheme.{0}) [IsIntegral Y]
    (hft : ∀ U : Y.Opens, IsAffineOpen U → Algebra.FiniteType ℤ Γ(Y, U)) :
    ∃ c : WithBot ℕ∞, ∀ U : Y.Opens, IsAffineOpen U → Nonempty U → ringKrullDim Γ(Y, U) = c := by
  by_cases h0 : CharZero Y.functionField
  · refine ⟨((Cardinal.toENat (Algebra.trdeg ℤ Y.functionField) + 1 : ℕ∞) : WithBot ℕ∞),
      fun U hU _ => ?_⟩
    have := hft U hU
    have := functionField_isFractionRing_of_isAffineOpen Y U hU
    have hK := IsFractionRing.injective Γ(Y, U) Y.functionField
    have : CharZero Γ(Y, U) := ⟨fun a b h => by
      have := congrArg (algebraMap Γ(Y, U) Y.functionField) h
      simpa using this⟩
    have hinj : Function.Injective (algebraMap ℤ Γ(Y, U)) := RingHom.injective_int _
    have : FaithfulSMul ℤ Γ(Y, U) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    rw [IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one _ hinj,
      ← trdeg_eq_of_isFractionRing ℤ Γ(Y, U) Y.functionField]
  · obtain ⟨p, hp⟩ := CharP.exists Y.functionField
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact h0 (CharP.charP_to_charZero _)
    have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero Y.functionField p).resolve_right hp0⟩
    letI : Algebra (ZMod p) Y.functionField := ZMod.algebra _ p
    refine ⟨((Algebra.trdeg (ZMod p) Y.functionField).toENat : WithBot ℕ∞), fun U hU _ => ?_⟩
    have := hft U hU
    have := functionField_isFractionRing_of_isAffineOpen Y U hU
    have hK := IsFractionRing.injective Γ(Y, U) Y.functionField
    have : CharP Γ(Y, U) p := (algebraMap Γ(Y, U) Y.functionField).charP hK p
    letI : Algebra (ZMod p) Γ(Y, U) := ZMod.algebra _ p
    have : IsScalarTower (ZMod p) Γ(Y, U) Y.functionField := IsScalarTower.of_algebraMap_eq
      fun x => congrArg (· x) (RingHom.ext_zmod (algebraMap (ZMod p) Y.functionField)
        ((algebraMap Γ(Y, U) Y.functionField).comp (algebraMap (ZMod p) Γ(Y, U))))
    have : Algebra.FiniteType (ZMod p) Γ(Y, U) :=
      Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) Γ(Y, U)
    exact GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing (ZMod p) Y.functionField

end GlobalTheory.DimCoheight

namespace GlobalTheory.DimCoheight

theorem finiteType_of_isAmb {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} (hq : IsAmb q)
    (U : Y.Opens) (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(Y, U) := by
  have := hq.finite
  have : IsProper q := CommonModel.isProper_of_isProjOver hq.isProjOver
  have : LocallyOfFiniteType (spMap (Int.castRingHom k)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hl : LocallyOfFiniteType (Spec.map (Spec.preimage (hU.fromSpec ≫ q ≫ spMap (Int.castRingHom k)))) := by
    rw [Spec.map_preimage]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hl
  have e : (Spec.preimage (hU.fromSpec ≫ q ≫ spMap (Int.castRingHom k))).hom = algebraMap ℤ Γ(Y, U) :=
    RingHom.ext_int _ _
  rw [e] at hl
  exact RingHom.finiteType_algebraMap.mp hl

theorem coheight_add_eq : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k),
    IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → ∀ (z : Y) (e : ℕ), HasDim z e →
    Order.coheight z + (e : ℕ∞) = d := by
  intro k _ Y _ q hq d hd z e hz
  have hft := finiteType_of_isAmb hq
  obtain ⟨c, hc⟩ := exists_ringKrullDim_affine_eq Y hft

  have hdc : (d : WithBot ℕ∞) ≤ c := by
    rw [← hd]
    refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    have hU : IsAffineOpen U := hU
    refine ⟨(U : Set Y), U.isOpen, hyU, ?_⟩
    have hne : Nonempty U := ⟨⟨y, hyU⟩⟩
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).le.trans (hc U hU hne).le

  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hne : Nonempty U := ⟨⟨z, hzU⟩⟩
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(Y, U), hU.fromSpec P = z := by
    have : z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hzU
    exact this
  have := hft U hU
  have hcA := hc U hU hne

  obtain ⟨M, hM, hMd⟩ : ∃ M : Ideal Γ(Y, U), M.IsMaximal ∧ (d : WithBot ℕ∞) ≤ M.height := by
    rcases Nat.eq_zero_or_eq_succ_pred d with h | h
    · obtain ⟨M, hM⟩ := Ideal.exists_maximal Γ(Y, U)
      exact ⟨M, hM, by rw [h]; exact_mod_cast bot_le⟩
    · by_contra hne
      push_neg at hne
      have : ringKrullDim Γ(Y, U) ≤ ((d.pred : ℕ) : WithBot ℕ∞) := by
        refine (ringKrullDim_le_iff_isMaximal_height_le _).2 fun m hm => ?_
        have h1 := hne m hm
        rw [h] at h1
        have h2 : m.height < ((d.pred + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
        exact_mod_cast Order.le_of_lt_add_one (by exact_mod_cast h2)
      have h3 := hdc.trans (hcA.symm.le.trans this)
      rw [h] at h3
      have : d.pred + 1 ≤ d.pred := by exact_mod_cast h3
      omega
  have h2 := FinTypeIntCatenary.height_maximal_le Γ(Y, U) P.asIdeal M

  let x : Spec Γ(Y, U) := P
  have eS := (asIso (hU.fromSpec.stalkMap x) ≪≫ Spec.stalkIso Γ(Y, U) x).commRingCatIsoToRingEquiv
  have hPh : (P.asIdeal.height : WithBot ℕ∞) = Order.coheight z := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (Localization.AtPrime P.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv eS, ← ringKrullDim_stalk_eq_coheight]
    rw [← hP]

  have h3 : ringKrullDim (Γ(Y, U) ⧸ P.asIdeal) ≤ e := by
    rw [← topologicalKrullDim_range_inter_closure_eq (B := Γ(Y, U)) hU.fromSpec P, hP, ← hz]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  have hge : (d : WithBot ℕ∞) ≤ (Order.coheight z : WithBot ℕ∞) + (e : WithBot ℕ∞) := by
    rw [← hPh]
    exact hMd.trans (h2.trans (add_le_add le_rfl h3))

  have hle : topologicalKrullDim (closure ({z} : Set Y)) + Order.coheight z ≤ topologicalKrullDim Y := by
    haveI : QuasiSober (closure ({z} : Set Y)) := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
    exact DimCodim.dim_add_le_of_le_coheight continuous_subtype_val Subtype.val_injective _
      fun w => Order.coheight_anti (specializes_iff_mem_closure.2 w.2)
  rw [hz, hd] at hle
  have a1 : (e : ℕ∞) + Order.coheight z ≤ d := by exact_mod_cast hle
  have a2 : (d : ℕ∞) ≤ Order.coheight z + e := by exact_mod_cast hge
  rw [add_comm] at a1
  exact le_antisymm a1 a2

end GlobalTheory.DimCoheight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDiagonalMumfordBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagWeil

theorem diag_psum (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (I : Finset (Fin 2)) :
    lift (𝟙 A) (𝟙 A) ≫ psum A (x2 A) I = psum A ![𝟙 A, 𝟙 A] I := by
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl <;>
    simp [psum, padd, pzero, x2, List.finRange_succ]

theorem lbIso_lam_diag (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB) :
    LBIso ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) (cubeLB A ![𝟙 A, 𝟙 A] M) := by
  refine GlobalTheory.PrimNorm.lbIso_nested hM _ _ _ _ _ _ ?_
  simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [← Over.comp_left, diag_psum]

end GlobalTheory.DiagWeil

open GlobalTheory.TorusRM.DiagFrame in

theorem GlobalTheory.DiagWeil.weilIs_diag_lam : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (N : LB A.left), N.IsLB → LBIso N (cubeLB A ![𝟙 A, 𝟙 A] M) → Out.RelAmple A N → ∀ (k : ℕ) (a b : Fin g → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((2 * (hermForm Hm a b).im : ℝ)) : ℂ) / k) → Out.WeilIs A N k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  intro A _ _ g hA _ M u Hm χ hM hF N hN hNc hamp k a b c hk ha hb hc
  have : IsProper A.hom := hA.proper
  have hL : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB (LB.isLB_linComb hM _ _) _
  have hcube : (cubeLB A ![𝟙 A, 𝟙 A] M).IsLB := LB.isLB_linComb hM _ _
  have hLN : LBIso ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) N :=
    LBIso.trans hL hcube hN (GlobalTheory.DiagWeil.lbIso_lam_diag A hM) hNc.symm
  have hampL : Out.RelAmple A ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GlobalTheory.AmpleApprox.relAmple_of_lbIso_self hN hL hLN hamp
  have hF' := isFactorAH_diagUnif u hF
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hampL g (diagUnif u) _ _ hF'.1 hF'.2.1 hF'.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hF' hpos
  have hc' : (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (((a ⬝ᵥ ((2 : ℂ) • Hm).mulVec (star b)).im : ℝ) : ℂ) / k) := by
    rw [hc]
    congr 4
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_im]
    simp [hermForm]
  have hw := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm A hA _ hL g (diagUnif u) _ _ hAH k a b c hk ha hb hc'
  rw [diagUnif_ex] at hw
  exact GlobalTheory.PELFamily.weilIs_of_lbIso GlobalTheory.globalFns_holds hA hN hL
    (LBIso.trans hN hL (pull_isLB hL _) hLN.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hL)) hw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOfMumfordBundleIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two.WeilCmp

variable {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S)

theorem cubN_cmp {T : Over S} (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂]
    [IsMonHom g₂] {U : Type} [CommGroup U] (v : (T ⟶ P₀.A) → (T ⟶ P₀.A) → U)
    {θ₁ : (T ⟶ P₁.A) → (T ⟶ P₁.A) → (T ⟶ P₁.A) → U} {θ₂ : (T ⟶ P₂.A) → (T ⟶ P₂.A) → (T ⟶ P₂.A) → U}
    (h₁ : IsCub θ₁) (h₂ : IsCub θ₂)
    (a₁ : ∀ x x' y, v (x * x') y * θ₁ (x ≫ f₁) (x' ≫ f₁) (y ≫ g₁) =
      θ₂ (x ≫ f₂) (x' ≫ f₂) (y ≫ g₂) * (v x y * v x' y))
    (a₂ : ∀ x y y', v x (y * y') * θ₁ (x ≫ f₁) (y ≫ g₁) (y' ≫ g₁) =
      θ₂ (x ≫ f₂) (y ≫ g₂) (y' ≫ g₂) * (v x y * v x y'))
    {k : ℕ} {x y : T ⟶ P₀.A} (hx : x ^ k = 1) (hy : y ^ k = 1) :
    cubN θ₁ k 1 (x ≫ f₁) (y ≫ g₁) = cubN θ₂ k 1 (x ≫ f₂) (y ≫ g₂) * v x y ^ k ∧
      cubN θ₁ k 1 (y ≫ g₁) (x ≫ f₁) = cubN θ₂ k 1 (y ≫ g₂) (x ≫ f₂) * v x y ^ k := by
  have first : ∀ n : ℕ, v (x ^ n) y * cubN θ₁ n 1 (x ≫ f₁) (y ≫ g₁) =
      v 1 y * (cubN θ₂ n 1 (x ≫ f₂) (y ≫ g₂) * v x y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have a := a₁ (x ^ n) x y
      rw [MonObj.pow_comp, MonObj.pow_comp] at a
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a' ih' ⊢
      linear_combination (norm := abel) a' + ih'
  have second : ∀ n : ℕ, v x (y ^ n) * cubN θ₁ n 1 (y ≫ g₁) (x ≫ f₁) =
      v x 1 * (cubN θ₂ n 1 (y ≫ g₂) (x ≫ f₂) * v x y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have a := a₂ x (y ^ n) y
      rw [MonObj.pow_comp, MonObj.pow_comp, h₁.s01 (x ≫ f₁), h₁.s12 _ (x ≫ f₁), h₂.s01 (x ≫ f₂),
        h₂.s12 _ (x ≫ f₂)] at a
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a' ih' ⊢
      linear_combination (norm := abel) a' + ih'
  have a := first k
  have b := second k
  rw [hx] at a
  rw [hy] at b
  exact ⟨mul_left_cancel a, mul_left_cancel b⟩

theorem isRatio_cmp (hG : GlobalFnsSt) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A)
    (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂]
    {r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))} {hr₁ : r₁.IsGen} (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩)
    {r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))} {hr₂ : r₂.IsGen} (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩)
    (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)) (hu : u.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1)
    {T : Over S} {k : ℕ} {x y : T ⟶ P₀.A} (hx : x ^ k = 1) (hy : y ^ k = 1) {e : Γ(T.left, ⊤)ˣ}
    (he : WeilCube.IsRatio c₁ k (x ≫ f₁) (y ≫ g₁) e) : WeilCube.IsRatio c₂ k (x ≫ f₂) (y ≫ g₂) e := by
  intro T' ρ z J₂ hJ₂
  obtain ⟨J₁, hJ₁, -⟩ := exists_good P₁.L P₁.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim)
    (fun a => a.elim)
  obtain ⟨J, hJ, e₁, e₂⟩ := exists_good_join P₁.isLB P₂.isLB hJ₁ hJ₂
  have hx' : (ρ ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have hy' : (ρ ≫ y) ^ k = 1 := by rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  have q₁ : Good P₁.L z (rl J) := (isPart_inl P₁.L P₂.L).good hJ
  have q₂ : Good P₂.L z (rr J) := (isPart_inr P₁.L P₂.L).good hJ
  obtain ⟨a, b⟩ := cubN_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ (fun a b => val u (lift a b).left z J) (isCub_cubV c₁ q₁)
    (isCub_cubV c₂ q₂) (fun x x' y => GlobalTheory.T.weilComparisonGenerator_additive_first_variable hG S P₀ P₁ P₂ f₁ g₁ f₂ g₂ _ _ c₁ _ _ c₂ u hu hn T' z J hJ x x' y)
    (fun x y y' => GlobalTheory.T.weilComparisonGenerator_additive_second_variable hG S P₀ P₁ P₂ f₁ g₁ f₂ g₂ _ _ c₁ _ _ c₂ u hu hn T' z J hJ x y y') hx' hy'
  rw [e₁, e₂] at a b
  simp only [Category.assoc] at a b
  have h := he T' ρ z J₁ hJ₁
  rw [a, b, ← _root_.mul_assoc] at h
  exact mul_right_cancel h

end GlobalTheory.Mum.Two.WeilCmp

open GlobalTheory.Mum.Two.WeilCmp in

theorem GlobalTheory.Mum.Two.weilIs_iff_of_lbIso : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A), IsMonHom f₁ → IsMonHom g₁ → IsMonHom f₂ → IsMonHom g₂ → LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L) (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L) → ∀ (F : Type) [Field F] (p : Sp F ⟶ S) (k : ℕ) (x y : Over.mk p ⟶ P₀.A), x ^ k = 1 → y ^ k = 1 → ∀ c, WeilIs P₁.A P₁.L k (x ≫ f₁) (y ≫ g₁) c ↔ WeilIs P₂.A P₂.L k (x ≫ f₂) (y ≫ g₂) c := by
  intro S _ P₀ P₁ P₂ f₁ g₁ f₂ g₂ _ _ _ _ hw F _ p k x y hx hy c
  have hL := GlobalTheory.allSixLaws.1
  haveI : Nonempty P₁.A.left := ⟨(x ≫ f₁).left (⊥ : PrimeSpectrum F)⟩
  haveI : Nonempty P₂.A.left := ⟨(x ≫ f₂).left (⊥ : PrimeSpectrum F)⟩
  obtain ⟨r₁, hr₁, ⟨c₁⟩⟩ := PolAV_exists_cubical hL.cube P₁
  obtain ⟨r₂, hr₂, ⟨c₂⟩⟩ := PolAV_exists_cubical hL.cube P₂
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.exists_weilComparisonGenerator_of_lambdaBundleIso S P₀ P₁ P₂ f₁ g₁ f₂ g₂ hw
  obtain ⟨u, hu, hn⟩ := GlobalTheory.T.exists_weilComparisonGenerator_normalised_zeroSection S P₀ P₁ P₂ f₁ g₁ f₂ g₂ u₀ hu₀
  have hx₁ : (x ≫ f₁) ^ k = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hy₁ : (y ≫ g₁) ^ k = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hx₂ : (x ≫ f₂) ^ k = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hy₂ : (y ≫ g₂) ^ k = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  obtain ⟨e₀, he₀⟩ := WeilCube.exists_isRatio c₁ k (x ≫ f₁) (y ≫ g₁) hx₁ hy₁
  have he₂ := isRatio_cmp P₀ P₁ P₂ hL.globalFns f₁ g₁ f₂ g₂ c₁ c₂ u hu hn hx hy he₀
  exact (WeilCube.weilIs_iff c₁ hL.globalFns P₁.isAb hx₁ hy₁ he₀ c).trans
    (WeilCube.weilIs_iff c₂ hL.globalFns P₂.isAb hx₂ hy₂ he₂ c).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCurvatureMatrixEvenFormsEqZeroStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_curvatureMatrixEvenForms_eq_zero : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => (curvEv G x i j : Alt n)) v = 0 := by
  first | exact @GlobalTheory.ChernCalc.CurvClosed.dbarAt_curvEv | exact GlobalTheory.ChernCalc.CurvClosed.dbarAt_curvEv | (intros; apply GlobalTheory.ChernCalc.CurvClosed.dbarAt_curvEv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarOperatorLocalCalculusComplexFormsStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_operator_local_calculus_complex_forms : ∀ (n : ℕ) (v : V n), (∀ α β : V n → Alt n, α =ᶠ[𝓝 v] β → dbarAt α v = dbarAt β v) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α j x) S) v) → dbarAt (fun x => ∑ j ∈ s, α j x) v = ∑ j ∈ s, dbarAt (α j) v) ∧ (∀ (c : ℂ) (α : V n → Alt n), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v) → dbarAt (fun x => c • α x) v = c • dbarAt α v) ∧ (∀ γ : Alt n, dbarAt (fun _ => γ) v = 0) ∧ (∀ (w : V n → Ev n) (β : V n → Alt n), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr ((w x : Alt n)) S) v) → (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (β x) S) v) → dbarAt (fun x => (w x : Alt n) * β x) v = dbarAt (fun x => (w x : Alt n)) v * β v + (w v : Alt n) * dbarAt β v) := by
  first | exact @GlobalTheory.CxForm.dbarAt_local_calculus | exact GlobalTheory.CxForm.dbarAt_local_calculus | (intros; apply GlobalTheory.CxForm.dbarAt_local_calculus <;> assumption)
end

