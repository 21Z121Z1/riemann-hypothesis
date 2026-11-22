import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0359
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviLogModulusVector
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0330
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0366
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsParabolicIsotropicFlagStabilizerSplitPlaceStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParabolic_isotropicFlag_stabilizer_split_place : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (𝔉 : IsoFlag V), GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.IsParabRad (parAt 𝔉 s)
      ((NLoc 𝔉 v).map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) := by
  first | exact @GlobalTheory.SplitFlag.isParabRad_parAt | exact GlobalTheory.SplitFlag.isParabRad_parAt | (intros; apply GlobalTheory.SplitFlag.isParabRad_parAt <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPureTensorBaseVectorAndLocalFactorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPureTensor_base_vector_and_local_factor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun _ => f₀) f₀ ∧ ∀ (q : Place D) (x : Place D → WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT q (x q) → (∀ p, p ≠ q → x p = f₀) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x (x q) := by
  first | exact @GlobalTheory.LocalPure.isPure_base_and_local | exact GlobalTheory.LocalPure.isPure_base_and_local | (intros; apply GlobalTheory.LocalPure.isPure_base_and_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRestrictedFiniteTensorFamilyTypeIdempotentsStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → U.u ∉ T.S → ∀ A, IsFinFamily D.sp.cm.sig V.gram (frameLat V) (fam T U μf A) := by
  first | exact @GlobalTheory.TrIdem.isFinFamily_fam | exact GlobalTheory.TrIdem.isFinFamily_fam | (intros; apply GlobalTheory.TrIdem.isFinFamily_fam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumCompGroupSwappingSymplecticEquiv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SwapWeil

variable {D : D7}

theorem symplOH_of {A B C E : HSp D} (e : WO A B → WO C E) (h : ∀ x y, symplO C E (e x) (e y) = symplO A B x y)
    (x y : WO A B) : symplOH C E (e x) (e y) = symplOH A B x y := by
  simp only [symplOH, h]

theorem theta_pull {ψ : AddChar (AF D.host.F) ℂ} {A B C E : HSp D} (e : WO A B ≃ₗ[AE D] WO C E) (hc : Continuous e)
    (hrat : ∀ x, x ∈ ratL B A → e x ∈ ratL E C) (hs : ∀ x y, symplO C E (e x) (e y) = symplO A B x y)
    (hinf : ∀ x : WO A B, x.map (infPart D) = 0 → (e x).map (infPart D) = 0)
    (hfin : ∀ x : WO A B, x.map (finPart D) = 0 → (e x).map (finPart D) = 0)
    {f : WO C E → ℂ} (hf : IsThetaFunO ψ C E f) : IsThetaFunO ψ A B (fun w => f (e w)) where
  quasi γ w := by
    obtain ⟨γ', hγ'⟩ := hrat (ratW B A γ) ⟨γ, rfl⟩
    have e1 : e (ratW B A γ) = ratW E C γ' := hγ'.symm
    show f (e (ratW B A γ + w)) = _
    rw [map_add, e1, hf.quasi, ← e1, symplOH_of (⇑e) hs]
  level := by
    obtain ⟨U, hU, k⟩ := hf.level
    refine ⟨U.comap (e : WO A B →+ WO C E), hU.preimage hc, fun u hu h0 => ?_⟩
    funext w
    have := congrFun (k (e u) hu (hinf u h0)) (e w)
    simp only [heisO] at this ⊢
    rw [map_add, ← symplOH_of (⇑e) hs]
    exact this
  cont := hf.cont.comp hc
  smooth k L hL h0 w := by
    have := hf.smooth k ((e : WO A B →+ WO C E).comp L) (hc.comp hL) (fun t => hfin _ (h0 t)) (e w)
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.coe_coe, map_add] using this

theorem isDetAt_inv {e : AE D} (he : e * e = e) {V V₂ : HSp D} {g : GA D V} {k : GA D V₂} {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) (hk : (mt V₂ k).det = (mt V g⁻¹).det) : IsDetAt e V₂ k x⁻¹ := by
  unfold IsDetAt at hx
  have hd : (mt V g⁻¹).det * (mt V g).det = 1 := by
    have hm : mt V g⁻¹ * mt V g = 1 := by simp [Formalism.L2.Theta.mt]
    rw [← Matrix.det_mul, hm, Matrix.det_one]
  show ((x⁻¹ : (AE D)ˣ) : AE D) = e * (mt V₂ k).det + (1 - e)
  rw [hk]
  apply Units.inv_eq_of_mul_eq_one_left
  rw [hx]
  linear_combination e * hd + ((mt V g⁻¹).det * (mt V g).det - (mt V g⁻¹).det - (mt V g).det + 1) * he

def swapOm {S T S' T' : HSp D} (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T) (φ' : GA D T' →* GA D S)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ) where
  toFun p :=
    { toFun := fun F w => om (φ' p.2, φ p.1) (fun x => F (L.symm x)) (L w)
      map_add' := fun F G => by
        funext w
        have e : (fun x => (F + G) (L.symm x)) = (fun x => F (L.symm x)) + fun x => G (L.symm x) := rfl
        show om _ (fun x => (F + G) _) _ = om _ (fun x => F _) _ + om _ (fun x => G _) _
        rw [e, map_add]; rfl
      map_smul' := fun c F => by
        funext w
        have e : (fun x => (c • F) (L.symm x)) = c • fun x => F (L.symm x) := rfl
        show om _ (fun x => (c • F) _) _ = c • om _ (fun x => F _) _
        rw [e, map_smul]; rfl }
  map_one' := by
    refine LinearMap.ext fun F => funext fun w => ?_
    have e : ((φ' (1 : GA D S' × GA D T').2, φ (1 : GA D S' × GA D T').1) : GA D S × GA D T) = 1 := by
      simp
    simp only [LinearMap.coe_mk, AddHom.coe_mk, e, map_one, Module.End.one_apply, LinearEquiv.symm_apply_apply]
  map_mul' p q := by
    refine LinearMap.ext fun F => funext fun w => ?_
    have e : ((φ' (p * q).2, φ (p * q).1) : GA D S × GA D T) = (φ' p.2, φ p.1) * (φ' q.2, φ q.1) := by
      simp
    simp only [LinearMap.coe_mk, AddHom.coe_mk, e, map_mul, Module.End.mul_apply, LinearEquiv.apply_symm_apply]

theorem swapOm_apply {S T S' T' : HSp D} (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T)
    (φ' : GA D T' →* GA D S) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S') (h : GA D T')
    (F : WO S' T' → ℂ) : swapOm L φ φ' om (g, h) F = fun w => om (φ' h, φ g) (fun x => F (L.symm x)) (L w) :=
  rfl

end GlobalTheory.SwapWeil

set_option maxHeartbeats 1600000 in
open GlobalTheory.SwapWeil in

theorem GlobalTheory.SwapWeil.isWeilDatumO_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T S' T' : HSp D), S'.rank = T.rank → T'.rank = S.rank →
    ∀ (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T) (φ' : GA D T' →* GA D S),
    Continuous L → Continuous L.symm → (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') →
    (∀ x y, symplO S T (L x) (L y) = symplO S' T' x y) →
    (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) → (∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0) →
    Continuous φ → Continuous φ' → (∀ γ ∈ GQ S', φ γ ∈ GQ T) → (∀ γ ∈ GQ T', φ' γ ∈ GQ S) →
    (∀ g h x, L (actO S' T' g h x) = actO S T (φ' h) (φ g) (L x)) →
    (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) → (∀ e h, SuppAt e T' h → SuppAt e S (φ' h)) →
    (∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det) → (∀ h, (Formalism.L2.Theta.mt S (φ' h)).det = (Formalism.L2.Theta.mt T' h⁻¹).det) →
    ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω →
      ∃ ω' : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ), IsWeilDatumO ψ S' T' χT χS ω' ∧
        ∀ g h (f : WO S T → ℂ), ω' (g, h) (fun u => f (L u)) = fun u => ω (φ' h, φ g) f (L u) := by
  intro D ψ S T S' T' hST hTS L φ φ' hLc hLsc hrat hs hinf hfin hφ hφ' hGQ hGQ' hact hsupp hsupp' hdet hdet' χS χT om H
  have hs' : ∀ x y, symplO S' T' (L.symm x) (L.symm y) = symplO S T x y := fun x y => by
    rw [← hs, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have thL : ∀ G : WO S T → ℂ, IsThetaFunO ψ S T G → IsThetaFunO ψ S' T' (fun w => G (L w)) := fun G hG =>
    theta_pull L hLc (fun x hx => (hrat x).2 hx) hs (fun x hx => (hinf x).2 hx) (fun x hx => (hfin x).2 hx) hG
  have thLs : ∀ F : WO S' T' → ℂ, IsThetaFunO ψ S' T' F → IsThetaFunO ψ S T (fun x => F (L.symm x)) := fun F hF =>
    theta_pull L.symm hLsc (fun x hx => (hrat (L.symm x)).1 (by rwa [LinearEquiv.apply_symm_apply])) hs'
      (fun x hx => (hinf (L.symm x)).1 (by rwa [LinearEquiv.apply_symm_apply]))
      (fun x hx => (hfin (L.symm x)).1 (by rwa [LinearEquiv.apply_symm_apply])) hF
  have hratS : ∀ x, L.symm.toAddEquiv x ∈ ratL T' S' ↔ x ∈ ratL T S := fun x => by
    show L.symm x ∈ ratL T' S' ↔ x ∈ ratL T S
    rw [← hrat, LinearEquiv.apply_symm_apply]
  refine ⟨swapOm L φ φ' om, ⟨H.std, H.hecT, H.hecS, by rw [hST]; exact H.resT, by rw [hTS]; exact H.resS,
    fun p F hF => ?_, fun g h w₀ F hF => ?_, fun γ hγ γ' hγ' F hF => ?_, fun F hF w => ?_,
    fun μ 𝓕 hμ h𝓕 p F hF => ?_, fun e he g h hg hh x y hx hy => ?_⟩, fun g h f => ?_⟩
  · obtain ⟨g, h⟩ := p
    exact thL _ (H.om_pres _ _ (thLs F hF))
  · have e1 : (fun x => heisO ψ S' T' w₀ F (L.symm x)) = heisO ψ S T (L w₀) (fun x => F (L.symm x)) := by
      funext x
      simp only [heisO]
      rw [← symplOH_of (⇑L) hs (L.symm x) w₀, LinearEquiv.apply_symm_apply, map_add, LinearEquiv.symm_apply_apply]
    funext w
    show om (φ' h, φ g) (fun x => heisO ψ S' T' w₀ F (L.symm x)) (L w) =
      heisO ψ S' T' (actO S' T' g h w₀) (swapOm L φ φ' om (g, h) F) w
    rw [e1, H.om_heis _ _ _ _ (thLs F hF), ← hact]
    simp only [heisO, swapOm_apply, map_add, symplOH_of (⇑L) hs]
  · show om (φ' γ', φ γ) (fun x => F (L.symm x)) (L 0) = F 0
    rw [L.map_zero, H.om_aut _ (hGQ' γ' hγ') _ (hGQ γ hγ) _ (thLs F hF)]
    exact congrArg F L.symm.map_zero
  · exact (H.om_cont _ (thLs F hF) (L w)).comp ((hφ'.comp continuous_snd).prodMk (hφ.comp continuous_fst))
  · haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : BorelSpace (WO S' T') := ⟨rfl⟩
    obtain ⟨ν, hν, h𝓖, hu⟩ := GlobalTheory.WeilSrc.haar_pull L.symm.toAddEquiv hLsc hLc (ratL T S) (ratL T' S') hratS μ 𝓕 hμ h𝓕
    have e1 := hu fun w => ‖swapOm L φ φ' om p F w‖ₑ ^ 2
    have e2 := hu fun w => ‖F w‖ₑ ^ 2
    have e3 : ∀ x, swapOm L φ φ' om p F (L.symm.toAddEquiv x) = om (φ' p.2, φ p.1) (fun x => F (L.symm x)) x :=
      fun x => by
        show om _ _ (L (L.symm x)) = _
        rw [LinearEquiv.apply_symm_apply]
    simp only [e3] at e1
    rw [← e1, ← e2]
    exact H.om_unit ν _ hν h𝓖 _ _ (thLs F hF)
  · obtain ⟨r, hr, Hs⟩ := H.om_split e he (φ' h) (φ g) (hsupp' e h hh) (hsupp e g hg) y⁻¹ x⁻¹
      (isDetAt_inv he.1 hy (hdet' h)) (isDetAt_inv he.1 hx (hdet g))
    refine ⟨r, hr, fun ℓ hℓ F hF => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.funLeft ℂ ℂ L
    have hinv : ∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ G, IsThetaFunO ψ S T G →
        ℓ' (heisO ψ S T u G) = ℓ' G := by
      intro u hu G hG
      show ℓ (fun w => heisO ψ S T u G (L w)) = ℓ (fun w => G (L w))
      have e1 : (fun w => heisO ψ S T u G (L w)) = heisO ψ S' T' (L.symm u) (fun w => G (L w)) := by
        funext w
        simp only [heisO]
        rw [← symplOH_of (⇑L) hs w (L.symm u), map_add, LinearEquiv.apply_symm_apply]
      rw [e1]
      refine hℓ _ ?_ _ (thL G hG)
      have hu' : cA D e • u = u := by
        ext i j
        exact hu i j
      intro i j
      have k := congrArg (fun M : WO S' T' => M i j) (congrArg L.symm hu')
      simpa only [LinearEquiv.map_smul, Matrix.smul_apply, smul_eq_mul] using k
    have main := Hs ℓ' hinv _ (thLs F hF)
    have e1 : ℓ' (fun x => F (L.symm x)) = ℓ F := by
      show ℓ (fun w => F (L.symm (L w))) = ℓ F
      simp only [LinearEquiv.symm_apply_apply]
    have hfac : splitFacO χS χT y⁻¹ x⁻¹ = splitFacO χT χS x y := by
      unfold splitFacO
      rw [map_inv, map_inv, inv_inv, mul_comm]
    rw [e1, hfac] at main
    exact main
  · funext u
    show om _ (fun x => f (L (L.symm x))) _ = _
    simp only [LinearEquiv.apply_symm_apply]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeReductionEqOneOfCompletionCongruence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevRedTriv

open Formalism.L2.DIV

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem coord_mem_idS {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (PP : Pl E) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (PP.asIdeal • Λ)) (i : Fin n) :
    ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
      (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ z) i := by
  set B : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 with hB
  revert i
  refine Submodule.span_induction
    (p := fun z _ => ∀ i, ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (B *ᵥ z) i)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.smul_induction_on
      (p := fun x => ∀ i, ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
        (B *ᵥ fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) i) hx ?_ ?_
    · intro p hp l hl i
      have hlm : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        Submodule.subset_span ⟨l, hl, rfl⟩
      have ht := (hβ _).1 hlm i
      refine ⟨oToS F E p * ⟨_, ht⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp), ?_⟩
      have e : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((p • l) i)) =
          ((oToS F E p : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) •
            (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) := by
        funext k
        rw [Pi.smul_apply, Pi.smul_apply, oToS_coe, smul_eq_mul]
        show ((p : E) * l k) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) =
          (algebraMap (𝓞 E) E p) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) * ((l k) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F))
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Subring.coe_mul]
    · intro x₁ x₂ h₁ h₂ i
      obtain ⟨s₁, hs₁, e₁⟩ := h₁ i
      obtain ⟨s₂, hs₂, e₂⟩ := h₂ i
      refine ⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, ?_⟩
      have e : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((x₁ + x₂) i)) =
          (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x₁ i)) +
            (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x₂ i)) := by
        funext k; simp
      rw [e, Matrix.mulVec_add, Pi.add_apply, Subring.coe_add, e₁, e₂]
  · intro i
    exact ⟨0, Ideal.zero_mem _, by simp⟩
  · intro a c _ _ ha hc i
    obtain ⟨s₁, hs₁, e₁⟩ := ha i
    obtain ⟨s₂, hs₂, e₂⟩ := hc i
    exact ⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, by rw [Matrix.mulVec_add, Pi.add_apply, Subring.coe_add, e₁, e₂]⟩
  · intro c a _ ha i
    obtain ⟨s, hs, e⟩ := ha i
    refine ⟨c * s, Ideal.mul_mem_left _ _ hs, ?_⟩
    have : c • a = ((c : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) • a := rfl
    rw [this, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Subring.coe_mul, e]

theorem coe_sub_one_apply (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (i j : Fin n) :
    (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = ((intGL F E n y).1 - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem conj_sub_one {R : Type} [CommRing R] {m : ℕ} (β : GL (Fin m) R) (X Y : Matrix (Fin m) (Fin m) R)
    (h : X = β.1 * Y * (β⁻¹).1) : Y - 1 = (β⁻¹).1 * (X - 1) * β.1 := by
  subst h
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem map_smul_sub {A B : Type} [CommRing A] [CommRing B] {m : ℕ} (f : A →+* B) (c : A) (c' : B) (hc : f c = c')
    (M : Matrix (Fin m) (Fin m) A) (u : Fin m → A) (w : Fin m → B) (hu : ⇑f ∘ u = w) :
    (fun i => f ((c • (M *ᵥ u - u)) i)) = c' • ((M.map f - 1) *ᵥ w) := by
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hc, Pi.sub_apply, map_sub,
    RingHom.map_mulVec, hu, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← hu]
  rfl

theorem col_entry {R : Type} [CommRing R] {m : ℕ} (β : GL (Fin m) R) (X Y : Matrix (Fin m) (Fin m) R)
    (e2 : Y - 1 = (β⁻¹).1 * (X - 1) * β.1) (c : R) (i j : Fin m) :
    ((β⁻¹).1 *ᵥ (c • ((X - 1) *ᵥ (β.1 *ᵥ Pi.single j 1)))) i = c * (Y - 1) i j := by
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← e2,
    Matrix.mulVec_single_one]
  rfl

theorem redFn_eq_one_of_cols {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (PP : Pl E) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ St β) (b : 𝓞 E)
    (hb : b ∉ PP.asIdeal)
    (h : ∀ j, ((oToS F E b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) •
      ((x.1 - 1) *ᵥ (β.1 *ᵥ Pi.single j 1)) ∈ Formalism.L2.Herm.hatL (F := F) (PP.asIdeal • Λ)) :
    redFn β PP x = 1 := by
  obtain ⟨y, rfl⟩ := hx
  have e2 : (intGL F E n y).1 - 1 = (β⁻¹).1 * ((frGL β y).1 - 1) * β.1 := conj_sub_one β _ _ rfl
  have hprime : PP.asIdeal.IsPrime := PP.isPrime
  have hb0 : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hb
  rw [redFn_frGL]
  apply Units.ext
  ext i j
  obtain ⟨s, hs, es⟩ := coord_mem_idS hβ PP (h j) i
  rw [col_entry β _ _ e2] at es
  have es' : s = oToS F E b * (y.1 - 1) i j := by
    apply Subtype.ext
    rw [Subring.coe_mul, coe_sub_one_apply, es]
  have e6 : resS F PP ((y.1 - 1) i j) = 0 := by
    have h0 : resS F PP s = 0 := by
      rw [GlobalTheory.GeoActCompare.resS_eq_resI, GlobalTheory.GeoActCompare.resI_eq_zero_iff]; exact hs
    rw [es', map_mul, resS_oToS] at h0
    exact (mul_eq_zero.1 h0).resolve_left hb0
  show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at e6
  rw [e6, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end General

section Adelic

set_option maxHeartbeats 1000000 in

theorem col_cong (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D))
    (hβ : Formalism.L2.DIV.IsFrame β L) (k : GA D V) (PP : Formalism.L2.DIV.Pl D.host.E) (b : 𝓞 D.host.E)
    (h : ∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (fmt V k *ᵥ u - u) ∈ hatV (PP.asIdeal • L))
    (w : Fin V.rank → Lev.EAf D) (hw : w ∈ Formalism.L2.Herm.hatL (F := D.host.F) L) :
    ((oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) •
      (((Lev.finE V k).1 - 1) *ᵥ w) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (PP.asIdeal • L) := by
  have eX : (Lev.finE V k).1 = (fmt V k).map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := rfl
  rw [eX]
  choose u hu using fun i => (GlobalTheory.LevSplit.swp_bij (F := D.host.F) (E := D.host.E)).2 (w i)
  have hu' : (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (u i)) = w := funext hu
  have hc : ⇑(GlobalTheory.LevSplit.swp D.host.F D.host.E) ∘ u = w := funext hu
  have hum : u ∈ hatV L := (GlobalTheory.LevSplit.latHat_iff L u).2 (by rw [hu']; exact hw)
  have h1 := (GlobalTheory.LevSplit.latHat_iff (PP.asIdeal • L) _).1 (h u hum)
  have eb : GlobalTheory.LevSplit.swp D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) =
      ((oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) := by
    rw [GlobalTheory.LevSplit.swp_tmul, oToS_coe]
  rw [map_smul_sub (GlobalTheory.LevSplit.swp D.host.F D.host.E) _ _ eb (fmt V k) u w hc] at h1
  exact h1

theorem redFn_eq_one_of_cong (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D))
    (hβ : Formalism.L2.DIV.IsFrame β L) (k : GA D V) (hk : Lev.finE V k ∈ Formalism.L2.DIV.St β)
    (PP : Formalism.L2.DIV.Pl D.host.E) (b : 𝓞 D.host.E) (hb : b ∉ PP.asIdeal)
    (h : ∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (fmt V k *ᵥ u - u) ∈ hatV (PP.asIdeal • L)) :
    Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 :=
  redFn_eq_one_of_cols hβ PP _ hk b hb fun j =>
    col_cong D V L β hβ k PP b h _ (GlobalTheory.ChainOnto.LStab.col_mem_hatL hβ j)

end Adelic

end GlobalTheory.LevRedTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelModelsOfFunctorialityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_models_of_functoriality : GlobalTheory.FunPr.Hypotheses₂ → RowModels := by
  first | exact @GlobalTheory.SepRows.rowModels_of_functoriality | exact GlobalTheory.SepRows.rowModels_of_functoriality | (intros; apply GlobalTheory.SepRows.rowModels_of_functoriality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelTowerRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows.RowRapidPf

theorem multT_le_empty {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) :
    MultT θ M J χ ≤ MultT θ M ∅ 1 :=
  Submodule.map_mono (Submodule.span_mono fun _ h =>
    ⟨h.aut, h.cusp, fun _ _ hk => absurd hk (Set.notMem_empty _), h.equiv, h.cont⟩)

theorem rowRapid : GlobalTheory.FunPr.Hypotheses₂ → RowTower → RowRapid := by
  intro hP hT D hq hs T L μ0 hL sc hc G W M hM M₀ hM₀ t ht w
  have ht' : t ∈ MultT W.θ M₀ ∅ 1 := multT_le_empty W.θ M₀ _ _ ht
  have key : ∀ ρ Φ n (h : n ≤ D.R.m),
      PathConv W M (rowPath T 0 n) (rowFam 0 n fun i => W.datum ρ Φ (Fin.castLE h i)) (t w) ∧
        RapidDec (G.V (.grid n 0)) (part W M ρ Φ (t w) n h) := by
    intro ρ Φ n h
    obtain ⟨S, MB, -, -, vec, hv⟩ := hT D hq hs T L μ0 hL sc hc G W M hM M₀ hM₀ n h
    obtain ⟨F', hF', hF⟩ := hv t ht' Φ
    obtain ⟨hcv, heq⟩ := hF ρ w
    refine ⟨hcv, ?_⟩
    rw [heq]
    exact (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ S MB W.θ W.θ_is ∅ 1 F' hF' (vec ρ w)).2.2
  exact ⟨fun ρ Φ n h => (key ρ Φ n h).2, fun ρ Φ => (key ρ Φ D.R.m le_rfl).1⟩

end GlobalTheory.SepRows.RowRapidPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviLogModulusVectorStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_log_modulus_vector : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (P : Finset (SV (wittIndex V))), IsPar P → ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∃ h : A0 (wittIndex V), ∀ u, vec u ∈ aP P → inner ℝ (vec u) h = - logDelta Φ u m := by
  first | exact @GlobalTheory.LeviVec.exists_levi_vec | exact GlobalTheory.LeviVec.exists_levi_vec | (intros; apply GlobalTheory.LeviVec.exists_levi_vec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusCharacterProductEqAbsDetStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_character_product_eq_abs_det : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (j : Fin (wittIndex V)) (p : PA Φ.flag0), ∏ i ∈ Finset.Iic j, absChi Φ i p = absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) := by
  first | exact @GlobalTheory.LeviShift.prod_absChi_Iic | exact GlobalTheory.LeviShift.prod_absChi_Iic | (intros; apply GlobalTheory.LeviShift.prod_absChi_Iic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionComplementTranslatesLocallyConstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRestriction_complement_translates_locallyConstant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ e, IsSplitIdem D e → ∀ f, IsThetaFunO ψ V W f → ∃ (L : AddSubgroup (halfMx (cA D e) W.rank r)) (Kc : Set (halfMx (cA D e) W.rank r)), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ IsCompact Kc ∧ (∀ t, t ∉ Kc → res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f) = 0) ∧ ∀ t, ∀ l ∈ L, heisO ψ V W (restEmb V W K (t + l : halfMx (cA D e) W.rank r)) f = heisO ψ V W (restEmb V W K t) f := by
  first | exact @GlobalTheory.HalfSupport.supp_locConst | exact GlobalTheory.HalfSupport.supp_locConst | (intros; apply GlobalTheory.HalfSupport.supp_locConst <;> assumption)
end

