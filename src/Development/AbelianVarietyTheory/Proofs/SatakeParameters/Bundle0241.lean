import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAllPlaces
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.ThLoc.AllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem tPull_comp (γ₁ γ₂ : Matrix (Fin N) (Fin N) D.host.E) (γ₁' γ₂' : Matrix (Fin N') (Fin N') D.host.E)
    (z : TaylorLogMetric.VC D N N') :
    Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ₂ γ₂' (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ₁ γ₁' z) =
      Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ₁ * γ₂) (γ₁' * γ₂') z := by
  funext τ
  show (Matrix.conjTranspose (γ₂'.map (TaylorLogMetric.embT D τ)) *
      (Matrix.conjTranspose (γ₁'.map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * γ₁.map (TaylorLogMetric.embT D τ)) *
      γ₂.map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) =
    (Matrix.conjTranspose ((γ₁' * γ₂').map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * (γ₁ * γ₂).map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem tPull_one (z : TaylorLogMetric.VC D N N') :
    Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (1 : Matrix (Fin N) (Fin N) D.host.E)
      (1 : Matrix (Fin N') (Fin N') D.host.E) z = z := by
  funext τ
  show (Matrix.conjTranspose ((1 : Matrix (Fin N') (Fin N') D.host.E).map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) *
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) = z τ
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]
  rfl

theorem smulLat_star_smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (hγ : star γ * γ = 1)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) :
    SDLat.smulLat (star γ) (SDLat.smulLat γ M) = M := by
  unfold SDLat.smulLat
  rw [← Submodule.map_comp]
  have h : ((Matrix.toLin' (star γ)).restrictScalars (𝓞 D.host.E)).comp ((Matrix.toLin' γ).restrictScalars (𝓞 D.host.E)) =
      LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    show Matrix.toLin' (star γ) (Matrix.toLin' γ x) = x
    rw [← Matrix.toLin'_mul_apply, hγ, Matrix.toLin'_one, LinearMap.id_apply]
  rw [h, Submodule.map_id]

theorem mem_La_smulLat_iff (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (x : TaylorLogMetric.VC D N N') :
    x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M') ↔
      Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M M' := by
  have h1 : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := Matrix.mem_unitaryGroup_iff'.mp γ.2
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Matrix.mem_unitaryGroup_iff'.mp γ'.2
  have h2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have h2' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ'.2
  constructor
  · intro hx
    exact Formalism.L2.KerInert.ie_La_pull cc δ _ _ h1' M M' hx
  · intro hx
    have h3 : star (star (γ' : Matrix (Fin N') (Fin N') D.host.E)) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 := by
      rw [star_star]; exact h2'
    have h := Formalism.L2.KerInert.ie_La_pull cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E))
      (star (γ' : Matrix (Fin N') (Fin N') D.host.E)) h3 (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')
    rw [smulLat_star_smulLat _ h1, smulLat_star_smulLat _ h1'] at h
    have h4 := h hx
    rw [AddSubgroup.mem_comap] at h4
    have e : Formalism.L2.KerInert.ieTPullHom cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E))
        (star (γ' : Matrix (Fin N') (Fin N') D.host.E))
        (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
          (γ' : Matrix (Fin N') (Fin N') D.host.E) x) = x := by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ x) = x
      rw [tPull_comp, h2, h2', tPull_one]
    rw [e] at h4
    exact h4

end GlobalTheory.ThLoc.AllPlaces

namespace GlobalTheory.ThLoc.AllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem formV_eq_Hf (u v : TaylorLogMetric.VC D N N') :
    formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' u v = TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) u v := rfl

def tPullLin (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun := Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ γ'
  map_add' := Formalism.L2.KerInert.ie_tPull_add cc δ γ γ'
  map_smul' := Formalism.L2.KerInert.ie_tPull_smul cc δ γ γ'

def tPullEquiv (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (γ' : Matrix.unitaryGroup (Fin N') D.host.E) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' :=
  LinearEquiv.ofLinearMap (tPullLin cc δ (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E))
    (tPullLin cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E)) (star (γ' : Matrix (Fin N') (Fin N') D.host.E)))
    (LinearMap.ext fun z => by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ z) = z
      rw [tPull_comp, Matrix.mem_unitaryGroup_iff'.mp γ.2, Matrix.mem_unitaryGroup_iff'.mp γ'.2, tPull_one])
    (LinearMap.ext fun z => by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ z) = z
      rw [tPull_comp, Matrix.mem_unitaryGroup_iff.mp γ.2, Matrix.mem_unitaryGroup_iff.mp γ'.2, tPull_one])

end GlobalTheory.ThLoc.AllPlaces

open GlobalTheory.ThLoc.AllPlaces in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem GlobalTheory.ThLoc.latAt_all : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L') (fun z => B.eNat χ N N' L L' (s.flatV N N' z)) p ι := by
  intro D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L L' hA p _ ι
  have hp : p.Prime := Fact.out
  have hCM : PI.UG.IsCMUnram D.host.E := D.sp.cm.cmUnram
  obtain ⟨hN, hN', hL, hL'⟩ := hA
  obtain ⟨γ, M, hM, hEq, hLM⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N L hL
  obtain ⟨γ', M', hM', hEq', hLM'⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N' L' hL'
  have hAM : TaylorLogMetric.admitted D N N' M M' := ⟨hN, hN', hM, hM'⟩
  have hAL : TaylorLogMetric.admitted D N N' L L' := ⟨hN, hN', hL, hL'⟩
  have hStd := GlobalTheory.T.normalisedThetaFamily_normalised_at_standardPrime D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' M M' hAM p ι hEq hEq'

  let φ : (DVar X.Tau N N' → ℂ) ≃ₗ[ℂ] (DVar X.Tau N N' → ℂ) :=
    (s.flatV N N').trans ((tPullEquiv cc δ γ γ').trans (s.flatV N N').symm)
  have hφ : ∀ z, s.flatV N N' (φ z) = Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
      (γ' : Matrix (Fin N') (Fin N') D.host.E) (s.flatV N N' z) := fun z => by
    show s.flatV N N' ((s.flatV N N').symm (tPullEquiv cc δ γ γ' (s.flatV N N' z))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hI : IsIsom (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))
      (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) (φ : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] _) := by
    intro x y
    show matH _ (φ x) (φ y) = _
    rw [KS.Lat.form_flat s, KS.Lat.form_flat s, hφ, hφ, formV_eq_Hf, formV_eq_Hf,
      Formalism.L2.KerInert.PullbackComparison.Hf_tPull cc δ _ _ (Matrix.mem_unitaryGroup_iff.mp γ.2) (Matrix.mem_unitaryGroup_iff.mp γ'.2)]
  have hloc := GlobalTheory.T.localNormalisation_transport_isometry a₀ b₀ D.host.d ha hd lam hlam (DVar X.Tau N N') _ (s.laF B.tor M M')
    (fun z => B.eNat χ N N' M M' (s.flatV N N' z)) p ι φ hI hStd.locNorm
  have hΛ : (s.laF B.tor M M').comap (φ : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] _).toAddMonoidHom = s.laF B.tor L L' := by
    ext x
    show s.flatV N N' (φ x) ∈ TaylorLogMetric.La D B.tor M M' ↔ s.flatV N N' x ∈ TaylorLogMetric.La D B.tor L L'
    rw [hφ, hLM, hLM']
    exact (mem_La_smulLat_iff γ γ' M M' _).symm
  have hθ : (fun z => B.eNat χ N N' M M' (s.flatV N N' (φ z))) = fun z => B.eNat χ N N' L L' (s.flatV N N' z) := by
    funext z
    rw [hφ, hLM, hLM']
    have h := (Formalism.L2.PairingIndexBounds.Eq.SqG.eulerProduct_eq_of_curve_ideal B hcc hδ χ hχ).1 N N' ⟨M, hM⟩ ⟨M', hM'⟩ hN hN' γ γ'
    exact congrFun h (s.flatV N N' z)
  rw [hΛ] at hloc
  simp only [hθ] at hloc
  exact ⟨hcm, KS.Lat.selfDual_laF s B hcc hδ hAL, fun x hx => KS.Lat.theta_laF s B (KS.Lat.odd_of_cmOK hcm) hx,
    KS.Lat.eNat_laF s B hcc hδ χ hAL, hloc⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PairReadPf

theorem exists_splitPlace_w (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  have hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun _ =>
    D.host.φ₀.injective (by
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])
  obtain ⟨x0, hx0, hx0'⟩ := hw
  have hc0 : IsCMField.ringOfIntegersComplexConj D.host.E x0 ∉ w.asIdeal :=
    hx0' _ (by rw [hstar, IsCMField.coe_ringOfIntegersComplexConj])
  obtain ⟨s, hs⟩ := GlobalTheory.SplitConjPlace.exists_splitPlace w x0 hx0 hc0
  have hsw : s.w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [s.w_under, hs]; rfl
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE w s.w hsw with h | h
  · exact ⟨s, h⟩
  · refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
    rw [GlobalTheory.SplitConjPlace.mem_conj_w, h, GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO]

theorem exists_ne_of_mem_iSup {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Sort*} (p : ι → Submodule ℂ M)
    (ℓ : M →+ ℂ) {x : M} (hx : x ∈ ⨆ i, p i) (h : ℓ x ≠ 0) : ∃ i, ∃ y ∈ p i, ℓ y ≠ 0 := by
  by_contra H
  push_neg at H
  exact h (Submodule.iSup_induction p (motive := fun z => ℓ z = 0) hx (fun i y hy => H i y hy) (map_zero ℓ)
    (fun a b ha hb => by rw [map_add, ha, hb, add_zero]))

theorem exists_ne_of_mem_iSup_sub {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Sort*} (A : Submodule ℂ M)
    (p : ι → Submodule ℂ M) (hpA : ∀ i, p i ≤ A) (ℓ : A →+ ℂ) (x : A) (hx : (x : M) ∈ ⨆ i, p i)
    (h : ℓ x ≠ 0) : ∃ i, ∃ y : A, (y : M) ∈ p i ∧ ℓ y ≠ 0 := by
  by_contra H
  push_neg at H
  obtain ⟨_, hk⟩ := Submodule.iSup_induction p (motive := fun z => ∃ hz : z ∈ A, ℓ ⟨z, hz⟩ = 0) hx
    (fun i y hy => ⟨hpA i hy, H i ⟨y, hpA i hy⟩ hy⟩) ⟨A.zero_mem, by exact map_zero ℓ⟩
    (fun a b ⟨ha, ea⟩ ⟨hb, eb⟩ => ⟨A.add_mem ha hb, by
        have e : (⟨a + b, A.add_mem ha hb⟩ : A) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [e, map_add, ea, eb, add_zero]⟩)
  exact h hk

def precompₛ {V C : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup C] [Module ℂ C] (T : V →ₗ[ℂ] C) :
    (C →ₗ⋆[ℂ] ℂ) →ₗ[ℂ] (V →ₗ⋆[ℂ] ℂ) where
  toFun f := f.comp T
  map_add' f g := by ext; rfl
  map_smul' a f := by ext; rfl

end GlobalTheory.PairReadPf

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.PairReadPf in
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod in

theorem GlobalTheory.NPin.pairRead_of_join : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Join P → ∀ S : Reading P.T, IsTrue P S → RowUnit S → PairRead S := by
  intro hBZ hL D P J S hT hRU i w hw σ Q hPairs
  obtain ⟨s, rfl⟩ := exists_splitPlace_w D w hw
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp only; omega⟩
  obtain ⟨f, hf, F, hF, hne⟩ := hPairs
  have hFmem : (P.M.loc i).real F ∈ NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ := by
    have : (P.M.loc i).real F ∈ LinearMap.range (P.M.loc i).real := LinearMap.mem_range_self _ _
    rw [(P.M.loc i).real_range] at this
    exact this.1
  let X := J.rowM i
  let Θ := J.th i j hj
  let Fp : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) := ⟨_, hFmem⟩
  let yp : ↥X.C := ⟨X.φ f, X.φ_mem f⟩
  have h0 : Θ.Λ Θ.φ₀ Fp yp ≠ 0 := by
    rw [← Θ.read F f Fp rfl]
    intro h
    apply hne
    show inner ℂ F (LinearMap.adjoint (D.what₂.thetaP (D.nd.mu i) (D.nd.j i)) f) = 0
    rw [LinearMap.adjoint_inner_right, ← inner_conj_symm, h, map_zero]

  have hμc := hT.mu i s.w hw j hj
  have hηc := hT.eta i s.w hw
  have hloc := Θ.loc s _ _ hμc hηc
  let ℓ0 : Θ.Ω →+ ℂ := AddMonoidHom.mk' (fun φ => Θ.Λ φ Fp yp) (by intro a b; simp)
  obtain ⟨ι, φ1, hφ1, hℓ1⟩ := exists_ne_of_mem_iSup _ ℓ0 hloc h0
  obtain ⟨hLin, φ2, ⟨Φ0, rfl⟩, hℓ2⟩ := exists_ne_of_mem_iSup _ ℓ0 hφ1 hℓ1
  obtain ⟨c, hc, hci, hιeq⟩ := hLin

  have hFiso : (Fp : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) ∈
      NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have := hF
    rw [P.H.av.typeV] at this
    exact this
  have hspan := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _
    (hT.rep i s hw Q) c hc hci
  let ℓF : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →+ ℂ :=
    AddMonoidHom.mk' (fun F' => Θ.Λ (ι Φ0) F' yp) (by intro a b; simp)
  obtain ⟨T1, F1, hF1, hℓF1⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF Fp (hspan hFiso) hℓ2
  obtain ⟨hT1, F2, ⟨a0, ha0⟩, hℓF2⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF F1 hF1 hℓF1

  have hσne : D.what₂.isot (D.nd.j i) σ ≠ ⊥ := by
    intro hb
    rw [hb, Submodule.mem_bot] at hf
    subst hf
    exact hne (by simp)
  have hyI : (yp : X.A) ∈ Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (P.rep σ) := (X.isot σ f).1 hf
  unfold Formalism.IndefR.principalLevelFrame.isotIn at hyI
  let ℓy : ↥X.C →+ ℂ := (Θ.Λ (ι Φ0) F2).toAddMonoidHom
  obtain ⟨Φe, y1, hy1, hℓy1⟩ := exists_ne_of_mem_iSup_sub X.C _
    (fun Φe => iSup_le fun h => h.2) ℓy yp hyI hℓF2
  obtain ⟨hΦe, y2, ⟨f2, hf2⟩, hℓy2⟩ := exists_ne_of_mem_iSup_sub X.C _
    (fun h => h.2) ℓy y1 hy1 hℓy1
  have hΦC : ∀ g : ↥(P.rep σ).S, Φe g ∈ X.C := fun g => hΦe.2 (LinearMap.mem_range_self _ _)
  have hspan2 := GlobalTheory.T.finiteType_spanned_by_splitPlace_localComponent D.host.E D.R.r (P.rep σ) s _ (hT.row i s hw σ hσne) c hc hci
  let ℓ2 : ↥(P.rep σ).S →+ ℂ :=
    AddMonoidHom.mk' (fun g => Θ.Λ (ι Φ0) F2 ⟨Φe g, hΦC g⟩) (by
      intro a b
      have e : (⟨Φe (a + b), hΦC (a + b)⟩ : ↥X.C) = ⟨Φe a, hΦC a⟩ + ⟨Φe b, hΦC b⟩ := by
        apply Subtype.ext; simp
      show Θ.Λ (ι Φ0) F2 ⟨Φe (a + b), hΦC (a + b)⟩ = Θ.Λ (ι Φ0) F2 ⟨Φe a, hΦC a⟩ + Θ.Λ (ι Φ0) F2 ⟨Φe b, hΦC b⟩
      rw [e, map_add])
  have hℓ2f2 : ℓ2 f2 ≠ 0 := by
    have e : (⟨Φe f2, hΦC f2⟩ : ↥X.C) = y2 := Subtype.ext hf2
    show Θ.Λ (ι Φ0) F2 ⟨Φe f2, hΦC f2⟩ ≠ 0
    rw [e]; exact hℓy2
  obtain ⟨T2, g1, hg1, hℓg1⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 f2 (hspan2 f2.2) hℓ2f2
  obtain ⟨hT2, g2, ⟨c0, hc0⟩, hℓg2⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 g1 hg1 hℓg1

  let T' : ((S i s.w hw).rep Q).V →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) :=
    T1.codRestrict _ hT1.1
  let T'' : ((S i s.w hw).row σ).V →ₗ[ℂ] ↥X.C :=
    (Φe ∘ₗ T2.codRestrict _ hT2.1).codRestrict X.C (fun v => hΦC _)
  have hT'eq : ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a,
      ((T' (((S i s.w hw).rep Q).π (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) :
        ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) =
        NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) :=
    fun x hx a => hT1.2 x hx a
  have hT''eq : ∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a,
      ((T'' (((S i s.w hw).row σ).π (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) =
        X.ρ x (T'' a) := by
    intro x hx a
    have e : (⟨T2 (((S i s.w hw).row σ).π (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a),
        hT2.1 _⟩ : ↥(P.rep σ).S) =
        ⟨NG.rt D.host.E D.R.r x (T2 a), (P.rep σ).stable x _ (hT2.1 a)⟩ := Subtype.ext (hT2.2 x hx a)
    show Φe ⟨_, _⟩ = X.ρ x (Φe ⟨T2 a, hT2.1 a⟩)
    rw [e]
    exact hΦe.1 x ⟨T2 a, hT2.1 a⟩
  let b := ((Θ.Λ ∘ₗ ι).compl₂ T').compr₂ (precompₛ T'')
  have hb0 : b Φ0 a0 c0 ≠ 0 := by
    have e1 : T' a0 = F2 := Subtype.ext ha0
    have e2 : T'' c0 = ⟨Φe g2, hΦC g2⟩ := by
      apply Subtype.ext
      show Φe ⟨T2 c0, hT2.1 c0⟩ = Φe g2
      congr 1
      exact Subtype.ext hc0
    show Θ.Λ (ι Φ0) (T' a0) (T'' c0) ≠ 0
    rw [e1, e2]
    exact hℓg2
  refine GlobalTheory.T.thetaPairing_of_invariant_trilinear_form _ D.R.r (D.R.r + D.R.t) _ _ (S i s.w hw).mu ((S i s.w hw).row σ).π
    (twist ((S i s.w hw).rep Q).π (detChar (Fin (D.R.r + D.R.t)) (S i s.w hw).eta))
    ((hBZ _).1 (Fin D.R.r) _ _ ((S i s.w hw).row σ).smooth ((S i s.w hw).row σ).irr)
    (hRU i s.w hw σ hσne) (S i s.w hw).mu_ok.1 b (fun h => hb0 (by rw [h]; rfl)) ?_
  intro g h Φ Φ' hΦ a c'
  exact GlobalTheory.T.thetaTrilinearForm_localGroup_invariant D P.M i P.rep X _ _ Θ s (S i s.w hw).mu (S i s.w hw).eta ι c hιeq _ _
    ((S i s.w hw).rep Q).π ((S i s.w hw).row σ).π T' hT'eq T'' hT''eq g h Φ Φ' hΦ a c'

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatUOfFixed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSph

theorem satU_of_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v → NG.SatAt { a with S := S, irrS := hS } Dv α → ∀ U : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ f ∈ S, (∀ κ ∈ U, NG.rt L n κ f = f) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f := by
  intro L _ _ _ n a S hS v w Dv α _ hsat U hU f hfS hfU h hh
  obtain ⟨f₀, hf₀S, hf₀0, U', hf₀U', hU', hH⟩ := hsat
  have hf₀S' : f₀ ∈ S := hf₀S
  have hK : ∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
    fun κ hκ _ => ⟨GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv κ, GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv κ hκ _⟩
  have hUmax : ∀ κ : GAf L n, TrivOutside {v} κ → (κ ∈ Umax L n ↔ κ ∈ Umax L n) := fun _ _ => Iff.rfl
  let ρ : GAf L n →* Module.End ℂ (GAf L n → a.W) :=
    { toFun := fun g => NG.rt L n g
      map_one' := LinearMap.ext fun φ => funext fun x => by
        show φ (x * 1) = φ x
        rw [mul_one]
      map_mul' := fun g g' => LinearMap.ext fun φ => funext fun x => by
        show φ (x * (g * g')) = φ (x * g * g')
        rw [mul_assoc] }
  have hρ : ∀ g φ, ρ g φ = NG.rt L n g φ := fun _ _ => rfl
  have hf₀K : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f₀ = f₀ :=
    fun κ hκ ht => hf₀U' κ ((hU' κ ht).2 hκ)
  have hfK : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f :=
    fun κ hκ ht => hfU κ ((hU κ ht).2 hκ)
  have hrtc : ∀ (φ : GAf L n → a.W) (x b : GAf L n), TrivOutside {v} x → TrivOutside {v}ᶜ b →
      NG.rt L n x (NG.rt L n b φ) = NG.rt L n b (NG.rt L n x φ) := by
    intro φ x b hx hb
    funext y
    show φ (y * x * b) = φ (y * b * x)
    rw [mul_assoc, mul_assoc, (GlobalTheory.InertSph.commute_of_trivOutside v x b hx hb).eq]
  have hrtm : ∀ (φ : GAf L n → a.W) (x b : GAf L n),
      NG.rt L n x (NG.rt L n b φ) = NG.rt L n (x * b) φ := by
    intro φ x b
    funext y
    show φ (y * x * b) = φ (y * (x * b))
    rw [mul_assoc]

  have hloc := fun x (hx : TrivOutside {v} x) => GlobalTheory.T.inertDoubleCosetOperator_eq_inertHeckeOperator L n v w Dv (GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv) (GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv)
    (GlobalTheory.T.exists_trivOutside_inertDatum_local_eq L n v w Dv) (GlobalTheory.T.inertDatum_local_injective_on_trivOutside L n v w Dv) x hx
  choose! R ha hR hha hA using hloc
  have hχ : ∀ x, TrivOutside {v} x → ∑ γ ∈ R x, NG.rt L n γ f₀ =
      Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) (ha x) α • f₀ := by
    intro x hx
    rw [hA x hx a.W f₀ hf₀K, GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK (Umax L n) U' hUmax hU' a.W (ha x) (hha x hx).1 f₀ hf₀K]
    exact hH _ (hha x hx)

  let W' : Submodule ℂ (GAf L n → a.W) :=
    Submodule.span ℂ (Set.range fun b : {b : GAf L n // TrivOutside {v}ᶜ b} => NG.rt L n (b : GAf L n) f₀)
  have hgen : ∀ b : GAf L n, TrivOutside {v}ᶜ b → NG.rt L n b f₀ ∈ W' :=
    fun b hb => Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
  have hW : W' ≤ GlobalTheory.SphScalar.fixS ρ S (GlobalTheory.InertSph.Kv L n v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨b, hb⟩, rfl⟩
    refine ⟨hS.1.stable b f₀ hf₀S', fun k hk => ?_⟩
    rw [hρ, hrtc f₀ k b hk.2 hb, hf₀K k hk.1 hk.2]
  have hf₀W : f₀ ∈ W' := by
    have := hgen 1 (GlobalTheory.InertSph.trivOutside_one _)
    have e : NG.rt L n (1 : GAf L n) f₀ = f₀ := funext fun y => by
      show f₀ (y * 1) = f₀ y
      rw [mul_one]
    rwa [e] at this
  have hW0 : W' ≠ ⊥ := by
    intro h0
    apply hf₀0
    have := hf₀W
    rw [h0] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hWb : ∀ b ∈ {b : GAf L n | TrivOutside {v}ᶜ b}, ∀ x ∈ W', ρ b x ∈ W' := by
    intro b hb x hx
    have hle : W' ≤ W'.comap (ρ b) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨b', hb'⟩, rfl⟩
      show ρ b (NG.rt L n b' f₀) ∈ W'
      rw [hρ, hrtm]
      exact hgen _ (GlobalTheory.SatInd.CosetFin.trivOutside_mul hb hb')
    exact hle hx
  have hWR : ∀ x ∈ {x : GAf L n | TrivOutside {v} x}, ∀ y ∈ W', ∑ γ ∈ R x, ρ γ y ∈ W' := by
    intro x hx y hy
    have hγ : ∀ γ ∈ R x, TrivOutside {v} γ := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (hR x hx).1 γ hγ
      exact GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 hx) hk₂.2
    have hle : W' ≤ W'.comap (∑ γ ∈ R x, ρ γ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨b, hb⟩, rfl⟩
      show (∑ γ ∈ R x, ρ γ) (NG.rt L n b f₀) ∈ W'
      rw [LinearMap.sum_apply]
      have e : ∑ γ ∈ R x, ρ γ (NG.rt L n b f₀) = NG.rt L n b (∑ γ ∈ R x, NG.rt L n γ f₀) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun γ hγ' => hrtc f₀ γ b (hγ γ hγ') hb
      rw [e, hχ x hx, map_smul]
      exact W'.smul_mem _ (hgen b hb)
    have := hle hy
    rwa [Submodule.mem_comap, LinearMap.sum_apply] at this
  have hdec : ∀ g : GAf L n, ∃ x ∈ {x : GAf L n | TrivOutside {v} x}, ∃ b ∈ {b : GAf L n | TrivOutside {v}ᶜ b},
      g = x * b := by
    intro g
    obtain ⟨x, b, hx, hb, e⟩ := GlobalTheory.T.finiteAdelicUnitary_eq_mul_trivOutside_place_and_at_place L n v g
    exact ⟨x, hx, b, hb, e⟩
  have hirr : ∀ S' : Submodule ℂ (GAf L n → a.W), S' ≤ S → (∀ g, ∀ x ∈ S', ρ g x ∈ S') → S' = ⊥ ∨ S' = S :=
    fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, fun g x hx => hst g x hx⟩ hle
  have heq := GlobalTheory.SphScalar.fixS_simple ρ S (fun g x hx => hS.1.stable g x hx) hirr (GlobalTheory.InertSph.Kv L n v)
    {x : GAf L n | TrivOutside {v} x} {b : GAf L n | TrivOutside {v}ᶜ b} hdec R (fun x hx => hR x hx)
    W' hW hW0 hWR hWb
  have hfW : f ∈ W' := by
    rw [heq]
    exact ⟨hfS, fun k hk => hfK k hk.1 hk.2⟩

  obtain ⟨C, cf, xs, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv U h
    (GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv
      (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
      (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU h hh)
  set c := Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α with hc
  let T : Module.End ℂ (GAf L n → a.W) := ∑ d ∈ C, cf d • NG.rt L n (xs d)
  have hT : ∀ φ, heckeFunI L n U Dv h φ = T φ := by
    intro φ
    rw [hC a.W φ, LinearMap.sum_apply]
    rfl
  let E : Module.End ℂ (GAf L n → a.W) := T - c • (1 : Module.End ℂ (GAf L n → a.W))
  have hE : ∀ φ, E φ = T φ - c • φ := fun φ => rfl
  have hker : W' ≤ LinearMap.ker E := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨b, hb⟩, rfl⟩
    show E (NG.rt L n b f₀) = 0
    rw [hE, ← hT,
      GlobalTheory.InertSph.heckeFunI_rt U Dv h f₀ b hb,
      GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK U U' hU hU' a.W h hh.1 f₀ hf₀K, hH h hh, map_smul, sub_self]
  have := hker hfW
  rw [LinearMap.mem_ker, hE, sub_eq_zero] at this
  rw [hT]
  exact this

end GlobalTheory.InertSph
end
end

