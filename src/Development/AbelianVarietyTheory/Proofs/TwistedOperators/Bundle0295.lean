import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0270
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTsumOfFactor
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0360
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalTranslateFlagUnipotentHeightLeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_translate_flagUnipotent_height_le : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C := by
  first | exact @GlobalTheory.FlagHeight.exists_rat_translate_height_le | exact GlobalTheory.FlagHeight.exists_rat_translate_height_le | (intros; apply GlobalTheory.FlagHeight.exists_rat_translate_height_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.ParGL

theorem exists_isSatVecGL_bound : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V), IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ (KGL w n) → (∀ h ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, heckeVec ρ (KGL w n) h x = c • x) → ∃ B, IsSatVecGL w ρ x B ∧ ∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  intro E _ _ w n V _ _ ρ hun x hx0 hxf hs
  have hK : IsCommensurated (KGL w n) := Formalism.UG.Final.GLintComm E w n
  obtain ⟨U, hU, hxU, hirr, hunU, hline⟩ :=
    GlobalTheory.T.spherical_eigenvector_generates_irreducible_subrepresentation ρ (KGL w n) (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1 hK hun x hx0 hxf hs
  set π := GlobalTheory.PRep.sub ρ U hU with hπ
  let x' : U := ⟨x, hxU⟩
  have hx'0 : x' ≠ 0 := fun e => hx0 (congrArg Subtype.val e)
  have hx'f : x' ∈ fixed π (KGL w n) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hxf k hk)
  have hsub : ∀ g (y : U), U.subtype (π g y) = ρ g (U.subtype y) := fun _ _ => rfl
  have heig : ∀ h ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, ∀ y ∈ fixed π (KGL w n), heckeVec π (KGL w n) h y = c • y := by
    intro h hh
    obtain ⟨c, hc⟩ := hs h hh
    have e1 : heckeVec π (KGL w n) h x' = c • x' := Subtype.val_injective (by
      have := map_heckeVec hK hh U.subtype hsub (x := x')
      exact this.trans hc)
    refine ⟨c, fun y hy => ?_⟩
    obtain ⟨a, rfl⟩ := hline y hy
    have := map_heckeVec hK hh (ρ := π) (ρ' := π) (a • LinearMap.id) (fun g y => by simp) (x := x')
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at this
    rw [← this, e1, smul_comm]
  obtain ⟨B, hB⟩ := GlobalTheory.LFun.ExSatGL.exists_hasSatGL E w n U π
    ((Submodule.ne_bot_iff _).2 ⟨x', hx'f, hx'0⟩) heig
  have hx' : IsSatVecGL w π x' B := hB.2 x' hx'f hx'0
  have hup := GlobalTheory.T.norm_satake_le_of_unitary_spherical_GL GlobalTheory.SatakeBound.satakeTrivialBound E w n _ π B hirr hunU hB
  refine ⟨B, hx'.map U.subtype hsub hx0, fun β hβ => ⟨hup β hβ, ?_⟩⟩
  have hst := GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w n _ π x' B hunU hx'
  have h1 : β⁻¹ ∈ B.map star := hst ▸ Multiset.mem_map_of_mem _ hβ
  obtain ⟨β', hβ', e⟩ := Multiset.mem_map.1 h1
  have h2 : ‖((β⁻¹ : ℂˣ) : ℂ)‖ = ‖(β' : ℂ)‖ := by
    rw [← e]
    simp
  rw [h2]
  exact hup β' hβ'

end GlobalTheory.FinZeta.ParGL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarInnerProductFormulaUnitCoefficient
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace

open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.UnitCoefIP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem exists_scalar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ ev : Pl D.host.E → List ℤ → ℂ, ∃ C : ℂ, ∀ y₁ ∈ GlobalTheory.LiftLower.partH R i σ ev, ∀ (y₂ : (R.HW i σ).H) (w : c.W), ‖w‖ = 1 →
    GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e y₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e y₂ fun ρ => v ρ)) = C * inner ℂ y₁ y₂ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _hirr _hS hI hFo hZ hδ i σ s m μ' η' ω B f₀ f c io H hd hν _hy _hH v hv ev
  have hC := hd.1
  obtain ⟨⟨μ, 𝓧⟩, hμ⟩ := hd.2.2.2.2.2.2.2.1.1.2.norm.1
  obtain ⟨⟨Fr, hFr⟩, hFr2⟩ := (hC.models.νW i).1.2.2 R.θ hC.models.inf
  obtain ⟨mR, hmR⟩ := (hFr2 Fr hFr).1
  choose δ _hδpos hδ' using hδ i σ
  have hδv : ∀ ρ, ∫ b, ‖⟪((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
      (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ) = δ ρ :=
    fun ρ => (hδ' ρ Fr hFr (mR ρ) (hmR ρ) (v ρ) (hv ρ)).2
  have hW := GlobalTheory.LiftScalarL.inner_HW R hC.models.HW i σ
  set N : ℝ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) with hN
  have hN0 : (N : ℂ) ≠ 0 := by
    have : 0 < N := Finset.prod_pos fun ρ _ => by
      have := one_le_dimK i σ ρ
      positivity
    exact_mod_cast this.ne'
  by_cases h0 : typePart R i σ A.μ0 R.triv ev = ⊥
  · refine ⟨0, fun y₁ hy₁ y₂ w _ => ?_⟩
    have e1 : y₁ = 0 := by
      rw [← GlobalTheory.LiftLower.typePart_base hC.lev, h0] at hy₁
      exact (Submodule.mem_bot ℂ).1 hy₁
    subst e1
    simp [l2, Lift.pet, upLift, petW]
  · obtain ⟨Bf, -, -, -, hK⟩ := hZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd μ 𝓧 hμ ev h0
    refine ⟨(((R.νV i A.μ0) (R.fdV i A.μ0)).toReal : ℂ) * (Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * (∏ ρ, (δ ρ : ℂ)) *
      ((Nat.card R.triv.H : ℂ) * (Datum.nrm2 μ 𝓧 f : ℂ) *
        (GlobalTheory.LFun.LSD D (finS R A.μ0) Bf μ' ((1 + (D.R.t : ℂ)) / 2) / (dOff D (finS R A.μ0) : ℂ)))) / N,
      fun y₁ hy₁ y₂ w hw => ?_⟩
    have hm : ∀ x, (R.HW i σ).e x ∈ R.Wall i σ := HMod_mem (hC.models.HW i σ)
    have hw' : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
    have hy' : y₁ ∈ typePart R i σ A.μ0 R.triv ev := by
      rw [GlobalTheory.LiftLower.typePart_base hC.lev]; exact hy₁
    have hK1 := hK _ (Submodule.mem_comap.1 hy') _ (hm y₂)
    have hIP := isMultiplicityInner_of_model (R.HW i σ) hW y₁ y₂
    have key := GlobalTheory.LiftScalarL.l2_upwardLift R hI hFo hd hν hμ hFr hmR (hm y₁) (hm y₂) hIP _ hK1 v δ hδv w hw'
    refine key.trans ?_
    rw [hW y₁ y₂]
    field_simp

end GlobalTheory.UnitCoefIP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionIsotropicRestrictionNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerResNonzero

variable {D : D7}

theorem exists_right_inv {V : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hC : LinearIndependent D.host.E C.transpose) :
    ∃ N : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * N = 1 := by
  set P := adj D C * V.gram with hP
  have hinj : Function.Injective (Matrix.toLin' Pᵀ) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    rw [Matrix.toLin'_apply] at ha
    rw [Matrix.mulVec_transpose, hP, ← Matrix.vecMul_vecMul] at ha
    have hG := GlobalTheory.LatVac.gram_det_isUnit V
    have h1 : a ᵥ* adj D C = 0 := by
      have := congrArg (fun v => v ᵥ* V.gram⁻¹) ha
      simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at this
      rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one] at this
    have h2 : C *ᵥ star a = 0 := by
      have e : a ᵥ* adj D C = star (C *ᵥ star a) := by
        rw [Matrix.star_mulVec, star_star]; rfl
      rw [e] at h1
      exact star_eq_zero.1 h1
    have h3 : star a = 0 := by
      funext j
      refine Fintype.linearIndependent_iff.1 hC (star a) ?_ j
      funext i
      have := congrFun h2 i
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply, Pi.zero_apply] at this ⊢
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact star_eq_zero.1 h3
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Pᵀ) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(LinearMap.toMatrix' g)ᵀ, ?_⟩
  have e : LinearMap.toMatrix' g * Pᵀ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have := congrArg Matrix.transpose e
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem lattice_ratMx (D : D7) (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) ∧ LocallyCompactSpace (Mx D m n) ∧
    SecondCountableTopology (Mx D m n) ∧ T2Space (Mx D m n) ∧ DiscreteTopology (ratMx D m n) ∧
    ∃ K : Set (Mx D m n), IsCompact K ∧ ∀ x : Mx D m n, ∃ γ ∈ ratMx D m n, γ + x ∈ K :=
  GlobalTheory.AdelicMatrixLattice.lattice D (Examples₂.posSpace Examples₂.star_isIntegral m) (Examples₂.posSpace Examples₂.star_isIntegral n)

theorem isoPart_add' {V W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y y' : Mx D W.rank r) :
    isoPart V W C (y + y') = isoPart V W C y + isoPart V W C y' :=
  Matrix.add_mul _ _ _

theorem isoPart_zero' {V W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    isoPart V W C (0 : Mx D W.rank r) = 0 := Matrix.zero_mul _

theorem midPart_zero' {V V' W : HSp D} (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    midPart V V' W B (0 : WO V' W) = 0 := Matrix.zero_mul _

theorem isoPart_mem_iff {V W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hC : LinearIndependent D.host.E C.transpose) (y : Mx D W.rank r) :
    isoPart V W C y ∈ ratL W V ↔ y ∈ ratMx D W.rank r := by
  constructor
  · rintro ⟨Q, hQ⟩
    obtain ⟨N, hN⟩ := exists_right_inv (V := V) hC
    refine ⟨Q * N, ?_⟩
    change (Q * N).map (incA D) = y
    have hQ' : Q.map (incA D) = y * (adj D C * V.gram).map (incA D) := hQ
    rw [Matrix.map_mul, hQ', Matrix.mul_assoc, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.mul_one]
  · rintro ⟨γ₀, rfl⟩
    exact ⟨γ₀ * (adj D C * V.gram), by
      show (γ₀ * (adj D C * V.gram)).map (incA D) = _
      rw [Matrix.map_mul]; rfl⟩

theorem exists_res_ne_zero : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → (∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x') → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ f, IsThetaFunO ψ V W f ∧ res V V' W C B μ 𝓨 f ≠ 0 := by
  intro D V V' W r C B hs hF ψ hψ μ 𝓨 h
  obtain ⟨f₀, hf₀, hne₀⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ V W
  obtain ⟨x₀, hx₀⟩ : ∃ x, f₀ x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne₀ (funext hc)
  have hf₁ : IsThetaFunO ψ V W (heisO ψ V W x₀ f₀) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ x₀
  have h0 : heisO ψ V W x₀ f₀ 0 ≠ 0 := by
    simp only [heisO, zero_add, GlobalTheory.FinTranslate.symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]
    exact hx₀

  have hiso : ∀ y y' : Mx D W.rank r, symplOH V W (isoPart V W C y) (isoPart V W C y') = 0 := fun y y' => by
    have := hF y y' 0 0
    rwa [midPart_zero', add_zero, add_zero, GlobalTheory.FinTranslate.symplOH_zero_left] at this

  have hc : ∀ (g : WO V W → ℂ), IsThetaFunO ψ V W g → ∀ a ∈ ratL W V, ∀ z,
      heisO ψ V W a g z = ψ (symplO V W z a) * g z := by
    intro g hg a ha z
    have := GlobalTheory.ThetaCoefficient.char_mul_heisO hg ha 0 z
    simp only [heisO, GlobalTheory.FinTranslate.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one, one_mul] at this
    exact this.symm
  refine by_contra fun hall => ?_
  push_neg at hall
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_ratMx D W.rank r
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hcont : Continuous (isoPart V W C : Mx D W.rank r → WO V W) := continuous_id.matrix_mul continuous_const
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (Mx D W.rank r) (ratMx D W.rank r) K hK hKc
    (ratL W V) (fun a y => ψ (symplO V W (isoPart V W C y) a))
    (fun a => by
      simp only [GlobalTheory.ThetaCoefficient.symplO_eq]
      exact hψ.1.1.comp (((GlobalTheory.FinTranslate.continuous_symplOH V W _).comp hcont).add
        ((GlobalTheory.FinTranslate.continuous_symplOH V W _).comp hcont)))
    (fun a x y => by
      simp only [isoPart_add', GlobalTheory.ThetaCoefficient.symplO_eq, GlobalTheory.FinTranslate.symplOH_add_left,
        ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun a b x => by
      show ψ (symplO V W (isoPart V W C x) (a + b)) = _
      simp only [GlobalTheory.ThetaCoefficient.symplO_eq, GlobalTheory.FinTranslate.symplOH_add_right, ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun x => by
      show ψ (symplO V W (isoPart V W C x) 0) = 1
      rw [GlobalTheory.ThetaCoefficient.symplO_eq, GlobalTheory.FinTranslate.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun a x => hψ.1.2.1 _)
    (fun y => by
      rw [← isoPart_mem_iff hs.frame.2.1 y, ← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W]
      exact Subtype.forall)
    μ 𝓨 h.1 h.2.1 (fun y => heisO ψ V W x₀ f₀ (isoPart V W C y)) (hf₁.cont.comp hcont)
    (fun γ hγ y => by
      obtain ⟨γ₀, hγ₀⟩ := (isoPart_mem_iff (V := V) hs.frame.2.1 γ).2 hγ
      have e := hf₁.quasi γ₀ (isoPart V W C y)
      change ratW W V γ₀ = isoPart V W C γ at hγ₀
      rw [hγ₀, hiso, neg_zero, AddChar.map_zero_eq_one, one_mul] at e
      simp only [isoPart_add']
      exact e)
    (fun a => by
      have e := congrFun (hall _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₁ (a : WO V W))) 0
      simp only [res, midPart_zero', add_zero, Pi.zero_apply] at e
      rw [← e]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hc _ hf₁ a a.2 _).symm))
  have := congrFun key 0
  simp only [isoPart_zero', Pi.zero_apply] at this
  exact h0 this

end GlobalTheory.TowerResNonzero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitMemSpanStaircaseIdealProductsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_mem_span_staircaseIdeal_products : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (ρ : ℕ) (p : Fin (2 * ρ + 2 - 1)) (q : Fin (2 * ρ + 1 - 1)), p.1 + q.1 = 2 * ρ → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ ((u : D.host.F) : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c} := by
  first | exact @GlobalTheory.StairUnit.exists_unit_mem_span | exact GlobalTheory.StairUnit.exists_unit_mem_span | (intros; apply GlobalTheory.StairUnit.exists_unit_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryImage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH
open scoped TensorProduct InnerProductSpace Classical Kronecker
open GlobalTheory.Chain.IoLift

noncomputable section

namespace GlobalTheory.Chain.IoLift.UImg

variable {p q : ℕ}

def sumAct (M : GKMod p q) (Y : Type) : Mat p q →ₗ[ℂ] Module.End ℂ (Y →₀ M.V) where
  toFun X := Finsupp.mapRange.linearMap (M.act X)
  map_add' X X' := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    simp
  map_smul' c X := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    simp

theorem sumAct_apply (M : GKMod p q) (Y : Type) (X : Mat p q) (v : Y →₀ M.V) (y : Y) :
    sumAct M Y X v y = M.act X (v y) := by
  simp [sumAct]

theorem sumAct_single (M : GKMod p q) (Y : Type) (X : Mat p q) (y : Y) (x : M.V) :
    sumAct M Y X (Finsupp.single y x) = Finsupp.single y (M.act X x) := by
  simp [sumAct]

def sumMod (M : GKMod p q) (Y : Type) : GKMod p q where
  V := Y →₀ M.V
  act := sumAct M Y
  lie X X' := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    rw [sumAct_apply, M.lie X X']
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Finsupp.sub_apply, sumAct_apply]
  kfin v := by
    induction v using Finsupp.induction_linear with
    | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun X _ w hw => by
        rw [Submodule.mem_bot] at hw ⊢; rw [hw, map_zero]⟩
    | add f g hf hg =>
      obtain ⟨W, hW, hf, hK⟩ := hf
      obtain ⟨W', hW', hg, hK'⟩ := hg
      refine ⟨W ⊔ W', inferInstance, Submodule.add_mem_sup hf hg, fun X hX w hw => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
      rw [map_add]
      exact Submodule.add_mem_sup (hK X hX a ha) (hK' X hX b hb)
    | single y x =>
      obtain ⟨W, hW, hx, hK⟩ := M.kfin x
      refine ⟨W.map (Finsupp.lsingle y), inferInstance, Submodule.mem_map_of_mem hx, ?_⟩
      rintro X hX _ ⟨w, hw, rfl⟩
      rw [Finsupp.lsingle_apply, sumAct_single]
      exact Submodule.mem_map_of_mem (f := Finsupp.lsingle y) (hK X hX w hw)
  wts v := by
    induction v using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add f g hf hg => exact Submodule.add_mem _ hf hg
    | single y x =>
      have h : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
          (⨆ μ : Ix p q → ℚ, wtSub (sumAct M Y) μ).comap (Finsupp.lsingle y) := by
        refine iSup_le fun μ x hx => ?_
        rw [Submodule.mem_comap]
        refine Submodule.mem_iSup_of_mem μ ?_
        simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
        intro a
        rw [Finsupp.lsingle_apply, sumAct_single, Finsupp.smul_single, ← Finsupp.single_sub, hx a,
          Finsupp.single_zero]
      exact h (M.wts x)

def fockMod (p q r s : ℕ) : GKMod p q where
  V := Pol p q r s
  act := fockAct1 p q r s
  lie X X' := by
    have h : ∀ U : Mat p q, fockAct1 p q r s U = omAct p q r s (U ⊗ₖ (1 : Mat r s)) := fun _ => rfl
    rw [map_sub]
    simp only [h]
    rw [← GlobalTheory.FockLie.omAct_lie, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, map_sub]
  kfin P := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).1
  wts P := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).2

theorem exists_unitary_image (M : GKMod p q) (Y Z : Type) [AddCommGroup Y] [Module ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] (B : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z)
    (hB : ∀ (X : Mat p q) P P' y y',
      ⟪B (M.act X P) y, B P' y'⟫_ℂ = ⟪B P y, B (M.act (adjZ X) P') y'⟫_ℂ) :
    ∃ (A : UGKMod p q) (j : A.M.V →ₗ[ℂ] Z) (B' : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V),
      Function.Injective j ∧ (∀ P y, j (B' P y) = B P y) ∧
        Submodule.span ℂ {x | ∃ P y, B' P y = x} = ⊤ ∧
        ∀ X P y, B' (M.act X P) y = A.M.act X (B' P y) := by
  let E : (Y →₀ M.V) →ₗ[ℂ] Z := Finsupp.lsum ℂ fun y => B.flip y
  have hE1 : ∀ y P, E (Finsupp.single y P) = B P y := fun y P => by
    simp [E]
  have hE : ∀ X (x x' : Y →₀ M.V), ⟪E (sumAct M Y X x), E x'⟫_ℂ =
      ⟪E x, E (sumAct M Y (adjZ X) x')⟫_ℂ := by
    intro X x x'
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, inner_add_left, hf, hg]
    | single y P =>
      induction x' using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [map_add, inner_add_right, hf, hg]
      | single y' P' => simp only [sumAct_single, hE1, hB]
  obtain ⟨A, f, j, hf, hj, hjf, hact⟩ :=
    GlobalTheory.GKQuot.exists_unitary_quotient p q (sumMod M Y) Z E hE
  let g : (Y →₀ M.V) →ₗ[ℂ] A.M.V := f
  have hjg : ∀ y P, j (g (Finsupp.single y P)) = B P y := fun y P => (hjf _).trans (hE1 y P)
  let B' : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P y => g (Finsupp.single y P))
      (fun P P' y => by rw [Finsupp.single_add, map_add])
      (fun c P y => by rw [← Finsupp.smul_single, map_smul, RingHom.id_apply])
      (fun P y y' => hj (by rw [map_add, hjg, hjg, hjg, map_add]))
      (fun c P y => hj (by rw [map_smul, hjg, hjg, map_smulₛₗ]))
  have hB' : ∀ P y, B' P y = g (Finsupp.single y P) := fun _ _ => rfl
  refine ⟨A, j, B', hj, fun P y => hjg y P, ?_, fun X P y => ?_⟩
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨v, rfl⟩ : ∃ v, g v = x := hf x
    induction v using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | single y P => exact Submodule.subset_span ⟨P, y, rfl⟩
  · rw [hB', hB', ← sumAct_single]
    exact hact X _

theorem unitaryImage : ∀ p q r s : ℕ, UnitaryImage p q r s :=
  fun p q r s Y Z _ _ _ _ B hB => exists_unitary_image (fockMod p q r s) Y Z B hB

end GlobalTheory.Chain.IoLift.UImg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitriangularStabilizerOfPrincipalMoveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move : ∀ {D : D7} (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) (Q : GlobalTheory.FinPl.Pl D → Prop) (g k : GA D W) (u : UX D ρ), g ∈ grpAt W Q → k ∈ grpAt W Q → MxOff Q (mt W k ⬝ x - mt W g⁻¹ ⬝ (x ⬝ u.1.1)) → ∃ r ∈ Rgrp W x, r ∈ grpAt W Q ∧ g = r * k⁻¹ := by
  first | exact @GlobalTheory.PrincipalMove.exists_move | exact GlobalTheory.PrincipalMove.exists_move | (intros; apply GlobalTheory.PrincipalMove.exists_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtendRestrictionFinitePointsEqStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_restriction_finitePoints_eq : ∀ {D : D7} {V : HSp D} (c : CoefA V), c.Is → ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (Ψ : GA D V → c.W), (∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h, Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) → ∀ h : GA D V, c.ext (fun u => Ψ (GlobalTheory.AdelicScalar.finLift V u)) h = Ψ h := by
  first | exact @GlobalTheory.AdelicRestrict.ext_restrict | exact GlobalTheory.AdelicRestrict.ext_restrict | (intros; apply GlobalTheory.AdelicRestrict.ext_restrict <;> assumption)
end

