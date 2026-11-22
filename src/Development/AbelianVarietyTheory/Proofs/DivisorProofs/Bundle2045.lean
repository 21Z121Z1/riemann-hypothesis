import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0011
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCF
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSixth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleConstantsEqOfSameLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotSameRig

open GlobalTheory.Grid

variable {D : D7}

theorem heisO_smul {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (ζ : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (ζ • g) = ζ • heisO ψ S T w g := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem thetaAt_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ}
    {f₀ Φ f f' : WO S T → ℂ} (ζ : ℂ) (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h' : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (ζ • f₀) Φ f') : f' = ζ • f := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c (ζ • f₀) (ζ • Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.trans Φ hΦ x hx, heisO_smul]
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.modul Φ hΦ y hy, heisO_smul]
      vac := by rw [LinearMap.smul_apply, hT.vac] }
  rw [h'.2 _ hT', hall Tm hT, LinearMap.smul_apply]

theorem isVacO_fixSig {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) :
    IsVacO ψ θ (Formalism.L2.Fam.ThC.fixSig S) (Formalism.L2.Fam.ThC.fixSig T) sS sT LS LT f :=
  ⟨h.1, h.2.inf, ⟨h.2.theta.quasi, h.2.theta.level, h.2.theta.cont, h.2.theta.smooth⟩, h.2.lat, h.2.fock, h.2.norm⟩

theorem setIntegral_eq_mul {V : HSp D} (ν₁ ν₂ : Measure (GA D V)) (fd₁ fd₂ : Set (GA D V)) (h₁ : ν₁.IsHaarMeasure)
    (h₂ : ν₂.IsHaarMeasure) (hfd₁ : IsFundamentalDomain (GQ V) fd₁ ν₁) (hfd₂ : IsFundamentalDomain (GQ V) fd₂ ν₂) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) →
      (IntegrableOn f fd₁ ν₁ ↔ IntegrableOn f fd₂ ν₂) ∧ ∫ g in fd₁, f g ∂ν₁ = c * ∫ g in fd₂, f g ∂ν₂ := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hc := Measure.isMulLeftInvariant_eq_smul ν₁ ν₂
  set c₀ : NNReal := Measure.haarScalarFactor ν₁ ν₂ with hc₀
  have hpos : 0 < c₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure ν₁ ν₂
  have hc0 : (c₀ : ENNReal) ≠ 0 := by exact_mod_cast hpos.ne'
  have hctop : (c₀ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsm : (c₀ • ν₂ : Measure (GA D V)) = (c₀ : ENNReal) • ν₂ := rfl
  have hfd₂' : IsFundamentalDomain (GQ V) fd₂ ν₁ := hfd₂.mono (by rw [hc, hsm]; exact Measure.smul_absolutelyContinuous)
  refine ⟨(c₀ : ℂ), by exact_mod_cast hpos.ne', fun f hf => ?_⟩
  have hf' : ∀ (g : GQ V) (x : GA D V), f (g • x) = f x := fun g x => hf g g.2 x
  constructor
  · rw [hfd₁.integrableOn_iff hfd₂' hf', hc, hsm, IntegrableOn, Measure.restrict_smul, integrable_smul_measure hc0 hctop]
    rfl
  · rw [hfd₁.setIntegral_eq hfd₂' hf', hc, hsm, Measure.restrict_smul, integral_smul_measure]
    simp [Complex.real_smul]

set_option maxHeartbeats 1000000 in

theorem const_of_sameRig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    X.rA = Y.rA → X.rA' = Y.rA' → X.rW = Y.rW → ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  intro D T L sc G W i j A A' WW X Y hX hY hA hA' hW c hc

  have hvX := hX.is.isVac
  have hvY := hY.is.isVac
  rw [← hA, ← hW] at hvY
  have hvX' := hX.is.isVac'
  have hvY' := hY.is.isVac'
  rw [← hA', ← hW] at hvY'
  have hψ : IsStdChar D W.ψ (-1) := hvX.1
  have hθ : IsInfFam W.θ := hvX.2.inf
  have hcS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1
  have hcT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hX.is.rigW.2.2 τ).1
  have hcS' : ∀ τ, IsCartanInv (gramAt D A' τ) (X.rA'.s τ) := fun τ => (hX.is.rigA'.2.2 τ).1
  obtain ⟨ζ, hζ1, hζ⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hψ hθ (Formalism.L2.Fam.ThC.fixSig (neg A))
    (Formalism.L2.Fam.ThC.fixSig WW) (fun τ => -X.rA.s τ) X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _)
    hcS hcT X.rA.Λ X.rW.Λ (GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1) hX.is.rigW.1 X.vac Y.vac (isVacO_fixSig hvX)
    (isVacO_fixSig hvY)
  obtain ⟨ζ', hζ1', hζ'⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hψ hθ (Formalism.L2.Fam.ThC.fixSig A')
    (Formalism.L2.Fam.ThC.fixSig WW) X.rA'.s X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _)
    hcS' hcT X.rA'.Λ X.rW.Λ hX.is.rigA'.1 hX.is.rigW.1 X.vac' Y.vac' (isVacO_fixSig hvX') (isVacO_fixSig hvY')
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1
  have hζ0' : ζ' ≠ 0 := fun h => by rw [h, norm_zero] at hζ1'; exact zero_ne_one hζ1'

  have he : ∀ t, Y.e t = X.e t := fun t => GlobalTheory.BaseKernelUniq.idemSum_unique A (hY.is.idem t) (hX.is.idem t)
  have hid : ∀ t, Y.ideal (locPl G) t = X.ideal (locPl G) t := fun t => by
    unfold Tri.ideal
    exact Finset.prod_congr rfl fun w hw => by rw [(hY.is.expo t w hw).unique (hX.is.expo t w hw)]

  have hf : ∀ t, Y.f t = ζ • X.f t := fun t => by
    have h2 := hY.is.fst t
    rw [← hA, ← hW, he t, hid t, hζ] at h2
    exact thetaAt_smul (S := neg A) ζ (hX.is.fst t) h2
  have hf' : ∀ t, Y.f' t = ζ' • X.f' t := fun t => by
    have h2 := hY.is.snd t
    rw [← hA', ← hW, he t, hid t, hζ'] at h2
    exact thetaAt_smul ζ' (hX.is.snd t) h2

  have thX : ∀ t, IsThetaFunO W.ψ (neg A) WW (X.f t) := fun t =>
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ (hX.is.fst t) hvX.2.theta
  have thX' : ∀ t, IsThetaFunO W.ψ A' WW (X.f' t) := fun t =>
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ (hX.is.snd t) hvX'.2.theta

  have hk : ∀ t P h g, Y.ker W.ψ W.θ t P h g = ζ * X.ker W.ψ W.θ t P h g := by
    intro t P h g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) hψ hθ (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
      (thX t) P
    have hWX : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
    have hWY : IsWeilDatumO W.ψ (neg A) WW _ _ ((Y.ω t).toSgn true) := hY.is.weil t
    have hu := GlobalTheory.WeilUniq.weilDatum_unique D W.ψ hψ (neg A) WW _ _ _ _ hWY hWX ((ofSgn true A).symm g, h) _ hF
    unfold Tri.ker
    rw [← hA, ← hW, hf t, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul]
    show ((Y.ω t).toSgn true) ((ofSgn true A).symm g, h) (ζ • _) 0 =
      ζ * ((X.ω t).toSgn true) ((ofSgn true A).symm g, h) _ 0
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hu]
  have hk' : ∀ t P h g, Y.ker' W.ψ W.θ t P h g = ζ' * X.ker' W.ψ W.θ t P h g := by
    intro t P h g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := A') hψ hθ X.rA'.s X.rA'.B X.rW.s X.rW.B (thX' t) P
    have hWX : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
    have hWY : IsWeilDatumO W.ψ A' WW _ _ (Y.ω' t) := hY.is.weil' t
    have hu := GlobalTheory.WeilUniq.weilDatum_unique D W.ψ hψ A' WW _ _ _ _ hWY hWX (g, h) _ hF
    unfold Tri.ker'
    rw [← hA', ← hW, hf' t, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul]
    show (Y.ω' t) (g, h) (ζ' • _) 0 = ζ' * (X.ω' t) (g, h) _ 0
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hu]

  have inv : ∀ t P h, ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t P h (γ * g) = X.ker W.ψ W.θ t P h g := by
    intro t P h γ hγ g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) hψ hθ (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
      (thX t) P
    have hWX : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
    have e1 : (((ofSgn true A).symm (γ * g), h) : GA D (neg A) × GA D WW) =
        ((ofSgn true A).symm γ, 1) * ((ofSgn true A).symm g, h) := by simp
    show ((X.ω t).toSgn true) ((ofSgn true A).symm (γ * g), h) _ 0 = ((X.ω t).toSgn true) ((ofSgn true A).symm g, h) _ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hWX.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hWX.om_pres _ _ hF)
  have inv' : ∀ t P h, ∀ γ ∈ GQ A', ∀ g, X.ker' W.ψ W.θ t P h (γ * g) = X.ker' W.ψ W.θ t P h g := by
    intro t P h γ hγ g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := A') hψ hθ X.rA'.s X.rA'.B X.rW.s X.rW.B (thX' t) P
    have hWX : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
    have e1 : ((γ * g, h) : GA D A' × GA D WW) = (γ, 1) * (g, h) := by simp
    show (X.ω' t) (γ * g, h) _ 0 = (X.ω' t) (g, h) _ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hWX.om_aut _ hγ 1 (one_mem _) _ (hWX.om_pres _ _ hF)

  obtain ⟨r, hr0, hr⟩ := setIntegral_eq_mul X.m Y.m X.fd Y.fd hX.is.meas.1 hY.is.meas.1 hX.is.meas.2 hY.is.meas.2
  obtain ⟨r', hr0', hr'⟩ := setIntegral_eq_mul X.m' Y.m' X.fd' Y.fd' hX.is.meas'.1 hY.is.meas'.1 hX.is.meas'.2
    hY.is.meas'.2
  have hYk : ∀ t P h, Y.ker W.ψ W.θ t P h = fun g => ζ * X.ker W.ψ W.θ t P h g := fun t P h => funext (hk t P h)
  have hYk' : ∀ t P h, Y.ker' W.ψ W.θ t P h = fun g => ζ' * X.ker' W.ψ W.θ t P h g := fun t P h => funext (hk' t P h)
  have hI : ∀ t P h, X.I W.ψ W.θ t P h = r * ζ⁻¹ * Y.I W.ψ W.θ t P h := fun t P h => by
    rw [Tri.I, Tri.I, hYk, integral_const_mul, (hr _ (inv t P h)).2]
    field_simp
  have hI' : ∀ t P h, X.I' W.ψ W.θ t P h = r' * ζ'⁻¹ * Y.I' W.ψ W.θ t P h := fun t P h => by
    rw [Tri.I', Tri.I', hYk', integral_const_mul, (hr' _ (inv' t P h)).2]
    field_simp
  have hint : ∀ t P h, IntegrableOn (Y.ker W.ψ W.θ t P h) Y.fd Y.m → IntegrableOn (X.ker W.ψ W.θ t P h) X.fd X.m :=
    fun t P h hi => by
      rw [hYk, IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.2 hζ0)] at hi
      exact (hr _ (inv t P h)).1.2 hi
  have hint' : ∀ t P h, IntegrableOn (Y.ker' W.ψ W.θ t P h) Y.fd' Y.m' →
      IntegrableOn (X.ker' W.ψ W.θ t P h) X.fd' X.m' := fun t P h hi => by
    rw [hYk', IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.2 hζ0')] at hi
    exact (hr' _ (inv' t P h)).1.2 hi

  set κ : ℂ := r * ζ⁻¹ * (r' * ζ'⁻¹)⁻¹ with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact mul_ne_zero (mul_ne_zero hr0 (inv_ne_zero hζ0)) (inv_ne_zero (mul_ne_zero hr0' (inv_ne_zero hζ0')))
  obtain ⟨⟨t₁, h₁⟩, P, P', H⟩ := hc
  have hX1 : X.IsConst W.ψ W.θ fun t => κ * c t := by
    refine ⟨⟨t₁, mul_ne_zero hκ0 h₁⟩, P, P', fun t => ⟨fun h => ⟨hint t P h ((H t).1 h).1, hint' t P' h ((H t).1 h).2⟩,
      ?_, fun h => ?_⟩⟩
    · obtain ⟨h, hh⟩ := (H t).2.1
      refine ⟨h, ?_⟩
      rw [hI']
      exact mul_ne_zero (mul_ne_zero hr0' (inv_ne_zero hζ0')) hh
    · have e := (H t).2.2 h
      have e' : Y.I' W.ψ W.θ t P' h = (r' * ζ'⁻¹)⁻¹ * X.I' W.ψ W.θ t P' h := by
        rw [hI', ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hr0' (inv_ne_zero hζ0')), one_mul]
      rw [hI, e, e', hκ]
      ring
  have := GlobalTheory.BotTransfer.isConst_smul hX1 (inv_ne_zero hκ0)
  simpa only [← mul_assoc, inv_mul_cancel₀ hκ0, one_mul] using this

end GlobalTheory.BotSameRig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegrandIntegrableOfCoefficientConstComStatement
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingIntegrand_integrable_of_coefficient_const_compact : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  IsSelfDualC X.A (stdLat X.A) → (∀ x, x ∈ intG D P.a ↔ X.ιA x ∈ openOff X.A (stdLat X.A) ∅) →
  ∀ (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), GlobalTheory.Doubling.IsMaj X.A a →
  ∀ (Sf : Finset (FinPl D)) (Φ : WO X.A X.B → ℂ) (c : ℂ),
    (∀ x ∈ intG D P.a, ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = c) →
    (∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = 0) →
    (∀ s : ℂ, IntegrableOn (integrand X.om X.m ν 𝓕 (stdLat X.A) a Φ Φ (fun _ => 1) (fun _ => 1) s) (openOff X.A (stdLat X.A) Sf) X.m) ∧
      ∫ g in openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g ∂X.m = c := by
  first | exact @GlobalTheory.RatioConst.integral_const_coef | exact GlobalTheory.RatioConst.integral_const_coef | (intros; apply GlobalTheory.RatioConst.integral_const_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLastAddGaps
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CompHS
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

open Classical in

def headWt (τ : Psi H) (k : ℕ) : AllWt.Weight Dw := fun τ' i => if τ' = τ ∧ (i : ℕ) ≤ k then 1 else 0

open Classical in

def tailWt (τ : Psi H) (k : ℕ) : AllWt.Weight Dw := fun τ' i => if τ' = τ ∧ k < (i : ℕ) then -1 else 0

open Classical in

def unitWt (τ : Psi H) (a : ℤ) : AllWt.Weight Dw := fun τ' _ => if τ' = τ then a else 0

theorem eq_last_add_gaps {N : ℕ} (v : Fin N → ℤ) (hN : 0 < N) (i : Fin N) :
    v i = v ⟨N - 1, by omega⟩ + ∑ k ∈ Finset.range (N - 1), if (i : ℕ) ≤ k then gap v k else 0 := by
  have h := ofGaps_gap v ⟨N - 1, by omega⟩ i
  simp only [ofGaps] at h
  have hi : (i : ℕ) ≤ N - 1 := by omega
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have e : (Finset.range (N - 1)).filter (fun k => (i : ℕ) ≤ k) = Finset.Ico (i : ℕ) (N - 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [e, Finset.sum_Ico_eq_sub _ hi]
  linarith

open Classical in

def piece (Dw : Datum H) (τ : Psi H) (k : ℕ) : AllWt.Weight Dw :=
  if k + 1 < Dw.p + Dw.q then (if k < Dw.p then headWt τ k else tailWt τ k) else 0

open Classical in
theorem piece_apply (τ τ' : Psi H) (k : ℕ) (i : Fin (Dw.p + Dw.q)) : piece Dw τ k τ' i =
    if τ' = τ then (if k + 1 < Dw.p + Dw.q then (if k < Dw.p then (if (i : ℕ) ≤ k then 1 else 0)
      else (if k < (i : ℕ) then -1 else 0)) else 0) else 0 := by
  unfold piece headWt tailWt
  by_cases h : τ' = τ <;> split_ifs <;> simp_all

open Classical in
theorem unitWt_apply (τ τ' : Psi H) (a : ℤ) (i : Fin (Dw.p + Dw.q)) :
    unitWt τ a τ' i = if τ' = τ then a else 0 := rfl

open Classical in
theorem decomp (la : AllWt.Weight Dw) (hla : GapGe 0 la) (hN : 0 < Dw.p + Dw.q) :
    let cτ : Psi H → ℤ := fun τ => la τ ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ) k else 0
    la = ∑ x ∈ (Finset.univ ×ˢ Finset.range (Dw.p + Dw.q - 1)).disjSum (Finset.univ : Finset (Psi H × Bool)),
      (Sum.elim (fun y : Psi H × ℕ => (gap (la y.1) y.2).toNat)
        (fun y : Psi H × Bool => if y.2 then (cτ y.1).toNat else (-cτ y.1).toNat) x) •
      (Sum.elim (fun y : Psi H × ℕ => piece Dw y.1 y.2)
        (fun y : Psi H × Bool => unitWt y.1 (if y.2 then 1 else -1)) x) := by
  intro cτ
  classical
  funext τ' i
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_disjSum, Finset.sum_product, Finset.univ_product_univ.symm,
    Finset.sum_product]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, piece_apply, unitWt_apply, Fintype.sum_bool,
    mul_ite, mul_zero, if_true, if_false]
  rw [Finset.sum_eq_single (s := Finset.univ) τ' (fun x _ hx => by simp [Ne.symm hx]) (by simp),
    Finset.sum_eq_single (s := Finset.univ) τ' (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp only [if_true, nsmul_eq_mul, Bool.false_eq_true, if_false, mul_one]
  have hv := eq_last_add_gaps (la τ') hN i
  have hterm : ∀ y ∈ Finset.range (Dw.p + Dw.q - 1), (if (i : ℕ) ≤ y then gap (la τ') y else 0) =
      ((gap (la τ') y).toNat : ℤ) * (if y + 1 < Dw.p + Dw.q then (if y < Dw.p then (if (i : ℕ) ≤ y then 1 else 0)
        else (if y < (i : ℕ) then -1 else 0)) else 0) + (if Dw.p ≤ y then gap (la τ') y else 0) := by
    intro y hy
    have hy' : y + 1 < Dw.p + Dw.q := by simp only [Finset.mem_range] at hy; omega
    have hg : 0 ≤ gap (la τ') y := hla τ' y hy'
    rw [Int.toNat_of_nonneg hg, if_pos hy']
    split_ifs <;> first | omega | simp <;> omega
  have hc := Int.toNat_sub_toNat_neg (cτ τ')
  have hcdef : cτ τ' = la τ' ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ') k else 0 := rfl
  rw [hv, Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  linarith

end GlobalTheory.NefWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTwoNotMem
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PairVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

structure GoodPlace {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W) (χX : Chr F E) (v : Pl F) :
    Prop where

  inertOrSplit : (∃ w, Formalism.UG.IsInertAt F E v w) ∨ Nonempty (E →ₐ[F] Fv F v)

  two : (2 : 𝓞 F) ∉ v.asIdeal

  psi : PsiUnr B.ψ v

  vac : M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

  lat : ∀ l, l ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v) ↔
    ∀ i, l.1 i ∈ v.adicCompletionIntegers F ∧ l.2 i ∈ v.adicCompletionIntegers F

  unr : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χX w

theorem eventually_two_not_mem : ∀ (F : Type) [Field F] [NumberField F], ∀ᶠ v : Pl F in Filter.cofinite, (2 : 𝓞 F) ∉ v.asIdeal := by
  intro F _ _
  have h0 : (Ideal.span {(2 : 𝓞 F)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact two_ne_zero
  have hf := Ideal.finite_factors h0
  refine hf.subset ?_
  intro v hv
  have hv' : (2 : 𝓞 F) ∈ v.asIdeal := by simpa using hv
  exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv')

end GlobalTheory.PairVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintaniStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bump_shintani_alt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) ∧ ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) ∧ ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit F (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w) := by
  first
  | exact @GlobalTheory.JSW.BumpShintani.exists_bump_shintani
  | exact GlobalTheory.JSW.BumpShintani.exists_bump_shintani
  | (intros; apply GlobalTheory.JSW.BumpShintani.exists_bump_shintani <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedData
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (x : O.Cl' t → VsV D i O.c'.F), ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f := by
  intro hci D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i Tp tup O hO t x
  have hj := inR i
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨-, -, -, -, hr, -, hr1, -, -, -, hDom, -, hLast⟩ := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T R F κ v₀ hR hT i _ rfl
    (T.dict ((i : ℕ) + 1) T.toCore.σ₀ 1).1
  obtain ⟨hι, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT.laws _ hj _ hσ (Wc D i) O.hV (rank_Wc i)
  obtain ⟨c0, ⟨m, hm, hc0⟩, hv⟩ := hO.cxi
  obtain ⟨hxi, n, hn, hxn⟩ := GlobalTheory.ClassSumRule.xi_laws hR.lev (hO.tuple t).xi
  obtain ⟨hd, hA, -⟩ := hO.cov t
  have hpq := hr ▸ hr1
  have hN : 0 < m * n := Nat.mul_pos hm hn
  have hcN : c0 ^ (m * n) = 1 := by rw [pow_mul, hc0, one_pow]
  have hxN : ∀ h : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) h)) ^ (m * n) = 1 := fun h => by
    rw [mul_comm, pow_mul, hxn, one_pow]
  obtain ⟨_, _, _, hfam⟩ := hR.fam.tie
  obtain ⟨ψ, hψ, hw⟩ := GlobalTheory.ClassSumRule.exists_char hR.lev (O.dδ t) hd hι (hr.symm.trans (rank_Wc i).symm) hpq
    (hO.tuple t).half (fun P hP z => by
      obtain ⟨a, ha⟩ := GlobalTheory.RationalValues.xiR_mem R hR.lev hR.fam.pl_onto hR.fam.muVal hfam.ok i (tup t) P hP z
      rw [← ha, ← hO.lift.field]
      exact (O.jL a).2) (hO.tuple t).xi (hO.tuple t).phi
  obtain ⟨f, hf, hcls, -⟩ := GlobalTheory.ClsVal.exists_cusp_isThClsD_unique hci _ _ _ _ _ O.c' _ (O.dδ t) _
    (unfBC O.hle (T.U ((i : ℕ) + 1))) hr1
    (fun σ hσ => GlobalTheory.OneMapAll.isUnf_unfExt O.hle σ (fun _ => rfl) (hT.laws.unf _ hj (σ.comp (incF T.Q.c O.c' O.hle)) hσ))
    hT.laws.pins.2.1.2 (fun _ => hO.cov t)
    (GlobalTheory.OneMapTuples.unitC_of_cXiAt D _ _ _ _ _ _ _ _ (O.dδ t) (rank_Wc i) _ hι hpq _ hx₀ hd hA _ _ hN hxN _ _ c0 hcN (hv t))
    ψ (GlobalTheory.ClassSumRule.psiTie_of_values _ (O.dδ t) (rank_Wc i) _ hι hpq _ hx₀ hd hA _ _ hN hxN hxi _ _ c0 hcN (hv t) ψ hψ)
    _ (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.bad t) (O.vol t) (O.ep t) _ O.io (wtA (κ i)) hDom hLast
    (fun k => hw _ (hO.w t k)) (hO.reps t).1 (by
      obtain ⟨-, _, h⟩ := hO.io
      exact h.2.2.1.le) x
  exact ⟨f, hf, hcls⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramesFockMapPolynomialLieActionsStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frames_fockMap_polynomial_lie_actions : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) , IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W), IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → M.IsWeil ψ χX χW om → ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) → (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) → ∃ (P Q R S : InfinitePlace F → ℕ) (A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c c' : InfinitePlace F → ℂ), FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C ∧ Function.Injective Φ ∧ LinearMap.range Φ = M.Pol ψ τ ∧ ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c ∧ ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c' := by
  first | exact @GlobalTheory.HoweD.FockData.exists_fock_data | exact GlobalTheory.HoweD.FockData.exists_fock_data | (intros; apply GlobalTheory.HoweD.FockData.exists_fock_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFiniteDimFinitePartsWeilOperatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_finiteDim_finiteParts_weilOperators : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ p0, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ,
        om p Φ = ∑ i, GlobalTheory.WeilM.pureA D.host.F (f i) (g i) := by
  first | exact @GlobalTheory.WeilCont.exists_local_finite_parts | exact GlobalTheory.WeilCont.exists_local_finite_parts | (intros; apply GlobalTheory.WeilCont.exists_local_finite_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedDataAllTuplesOfBaseTupleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedData_allTuples_of_baseTuple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) , R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → R.thP_vP → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧ O'.lev = (O i).lev := by
  first | exact @GlobalTheory.PinnedTuples.exists_pins_of_base | exact GlobalTheory.PinnedTuples.exists_pins_of_base | (intros; apply GlobalTheory.PinnedTuples.exists_pins_of_base <;> assumption)
end

