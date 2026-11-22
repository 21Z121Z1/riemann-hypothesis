import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0336
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0344
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0360
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0415
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0429

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeValuesKilledByLoweringPart
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift.LowerKill

open GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate

theorem entry_eq_zero {n : ℕ} {ε : Fin n → Bool} {κ : Matrix (Fin n) (Fin n) ℂ}
    (h : κ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ) {a b : Fin n} (hab : ε a ≠ ε b) : κ a b = 0 := by
  have e := congrFun (congrFun h a) b
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at e
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at hab e
  · simp only [Bool.false_eq_true, if_false, if_true] at e
    linear_combination (1 / 2 : ℂ) * e
  · simp only [Bool.false_eq_true, if_false, if_true] at e
    linear_combination (-1 / 2 : ℂ) * e

theorem block_conj {n : ℕ} {ε : Fin n → Bool} {κ κ' Y : Matrix (Fin n) (Fin n) ℂ}
    (h : κ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ) (h' : κ' * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ')
    (hY : ∀ a b, ¬ (ε a = false ∧ ε b = true) → Y a b = 0) (a b : Fin n) (hab : ¬ (ε a = false ∧ ε b = true)) :
    (κ' * Y * κ) a b = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : ε d = ε b
  · rw [mul_apply, Finset.sum_eq_zero fun c _ => ?_, zero_mul]
    by_cases hc : ε a = ε c
    · rw [hY c d (by rw [← hc, hd]; exact hab), mul_zero]
    · rw [entry_eq_zero h' hc, zero_mul]
  · rw [entry_eq_zero h hd, mul_zero]

variable {D : D7} {T : HSp D} {Sp : D.what₂.Tau → SPar}

theorem frame_mem_UH (M : DSModel T Sp) (τ : D.what₂.Tau) {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hκ : κ ∈ Formalism.REAL.Kset (M.ε τ)) : (M.fr τ)⁻¹ * κ * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  have hu : IsUnit (M.fr τ).det := (isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : κᴴ * κ = 1 := hκ.1.1
  have h2 : κᴴ * Formalism.REAL.Jm (M.ε τ) * κ = Formalism.REAL.Jm (M.ε τ) := by
    rw [Matrix.mul_assoc, ← hκ.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h3 : M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = κ * M.fr τ := by
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]
  show ((M.fr τ)⁻¹ * κ * M.fr τ)ᴴ * gramAt D T τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = gramAt D T τ
  rw [← M.fr_gram τ]
  calc _ = (M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ))ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ)) := by
        rw [conjTranspose_mul (M.fr τ)]
        simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * (κᴴ * Formalism.REAL.Jm (M.ε τ) * κ) * M.fr τ := by
        rw [h3, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h2]

theorem adAt_mem_pMinus {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel T Sp) (ρ τ : D.what₂.Tau)
    {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hκ : κ ∈ Formalism.REAL.Kset (M.ε ρ))
    {Z : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hZ : Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ) :
    adAt θ (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ)) τ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ := by
  have hs := atTau_spec hθ T ρ (frame_mem_UH M ρ hκ)
  have hi : infMat D.sp.cm.sig T.gram (θ τ) (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ)) *
      infMat D.sp.cm.sig T.gram (θ τ) (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ))⁻¹ = 1 := by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  unfold adAt
  by_cases c : τ = ρ
  · subst c
    have hu : IsUnit (M.fr τ).det := (isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have h1 : κ * κᴴ = 1 := hκ.1.2
    have h1' : κᴴ * κ = 1 := hκ.1.1
    have hJ : κᴴ * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * κᴴ := by
      have := congrArg conjTranspose hκ.2
      rw [conjTranspose_mul, conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at this
      exact this.symm
    rw [hs.2.1] at hi ⊢
    have hi2 : (M.fr τ)⁻¹ * κ * M.fr τ * ((M.fr τ)⁻¹ * κᴴ * M.fr τ) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc _ κᴴ, mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_assoc,
        ← Matrix.mul_assoc κ, h1, Matrix.one_mul, nonsing_inv_mul _ hu]
    rw [← inv_eq_right_inv hi, inv_eq_right_inv hi2]
    intro a b hab
    have e : M.fr τ * ((M.fr τ)⁻¹ * κᴴ * M.fr τ * Z * ((M.fr τ)⁻¹ * κ * M.fr τ)) * (M.fr τ)⁻¹ =
        κᴴ * (M.fr τ * Z * (M.fr τ)⁻¹) * κ := by
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one, mul_nonsing_inv_cancel_left _ _ hu]
    rw [e]
    exact block_conj hκ.2 hJ hZ a b hab
  · rw [hs.2.2 τ c] at hi ⊢
    rw [Matrix.one_mul] at hi
    rw [hi, Matrix.one_mul, Matrix.mul_one]
    exact hZ

variable {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D}

theorem exists_op (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (Z : Matrix (Fin T.rank) (Fin T.rank) ℂ) : ∃ L : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → ∀ h,
      RderC θ T τ Z (fun g => thetaKO om h g f) = fun g => thetaKO om h g (L f) := by
  have key : ∀ X ∈ lieAt T τ, ∃ L : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → ∀ h,
      Rder θ T τ X (fun g => thetaKO om h g f) = fun g => thetaKO om h g (L f) := by
    intro X hX
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ X hX
    refine ⟨L, fun f hf h => funext fun g => ?_⟩
    have := ((hL f hf).2.2.2 (h, g) 0).deriv
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
  obtain ⟨L₁, e1⟩ := key _ h1
  obtain ⟨L₂, e2⟩ := key _ h2
  refine ⟨L₁ + Complex.I • L₂, fun f hf h => ?_⟩
  unfold RderC
  rw [e1 f hf, e2 f hf]
  funext g
  simp [thetaKO]

def killed (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (M : DSModel T Sp) {Y : Type} [AddCommGroup Y]
    [Module ℂ Y] (pt : Y →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P)) : Submodule ℂ Y where
  carrier := {P | ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt P)) = 0}
  add_mem' := by
    intro P Q hP hQ τ Z hZ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    have a := hP τ Z hZ h
    have b := hQ τ Z hZ h
    rw [hL _ (hpt _)] at a b ⊢
    funext g
    have a' := congrFun a g
    have b' := congrFun b g
    simp only [thetaKO, map_add, Pi.add_apply, Pi.zero_apply] at a' b' ⊢
    rw [a', b', add_zero]
  zero_mem' := by
    intro τ Z _ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    rw [hL _ (hpt _)]
    funext g
    simp [thetaKO]
  smul_mem' := by
    intro r P hP τ Z hZ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    have a := hP τ Z hZ h
    rw [hL _ (hpt _)] at a ⊢
    funext g
    have a' := congrFun a g
    simp only [thetaKO, map_smul, Pi.smul_apply, Pi.zero_apply] at a' ⊢
    rw [a', smul_zero]

theorem values_killed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), LowSm M → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → (∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt Δ)) = 0) → ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ (v : ∀ ρ, lowT M ρ) w h, RderC θ T τ Z (fun g => thetaKO om h g (pt (io (PiTensorProduct.tprod ℂ v) w))) = 0 := by
  intro D ψ S T χS χT om hom θ hθ Sp M h1 h2 c hc pt hpt Δ io hio hΔ τ Z hZ v w h
  classical
  obtain ⟨hS, hK, v₀, w₀, hv₀, hw₀, e₀⟩ := hio
  beta_reduce at hS hK
  let N := killed hom hθ M pt hpt
  have step1 : ∀ w, io (PiTensorProduct.tprod ℂ v₀) w ∈ N := by
    obtain ⟨-, -, -, -, -, -, -, hd, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ S hθ
    suffices hst : ∀ g, (N.comap (io (PiTensorProduct.tprod ℂ v₀))).map (c.ρ g) ≤
        N.comap (io (PiTensorProduct.tprod ℂ v₀)) by
      intro w
      refine (((hc.2.2.2.2 _ hst).resolve_left fun h0 => ?_).ge Submodule.mem_top :
        w ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)))
      have hm : w₀ ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)) := by
        show io (PiTensorProduct.tprod ℂ v₀) w₀ ∈ N
        rw [e₀]
        exact hΔ
      rw [h0, Submodule.mem_bot] at hm
      rw [hm, norm_zero] at hw₀
      exact zero_ne_one hw₀
    · rintro g _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, u, hu, rfl⟩ := hd g
      intro τ Z hZ h
      have e : (fun g => thetaKO om h g (pt (io (PiTensorProduct.tprod ℂ v₀) (c.ρ (a * u) x)))) =
          fun g => thetaKO om (h * u) g (pt (io (PiTensorProduct.tprod ℂ v₀) x)) := by
        funext g
        rw [map_mul, hc.1 a ha, one_mul, ← hS u hu]
        unfold thetaKO
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
      rw [e]
      exact hx τ Z hZ (h * u)
  let B : MultilinearMap ℂ (fun τ => lowT M τ) (PolF D T.rank S.rank) :=
    (io.flip w).compMultilinearMap (PiTensorProduct.tprod ℂ)
  refine mem_of_translates h1 h2 B N v₀ (fun ρ h0 => ?_) (step1 w) ?_ v τ Z hZ h
  · have := hv₀ ρ
    rw [h0] at this
    simp at this
  · intro ρ k hk v u hu hv τ Z hZ h
    have e : (fun g => thetaKO om h g (pt (B (Function.update v ρ u)))) =
        rTr T (atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) fun g => thetaKO om h g (pt (B v)) := by
      funext g
      have := hK ρ k hk v u hu w
      show om (h, g) (pt (io (PiTensorProduct.tprod ℂ (Function.update v ρ u)) w)) 0 =
        om (h, g * atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) (pt (io (PiTensorProduct.tprod ℂ v) w)) 0
      rw [← this, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [e, RderC_rTr hθ (isRealPt_atTau hθ ρ (frame_mem_UH M ρ hk)), hv τ _ (adAt_mem_pMinus hθ M ρ τ hk hZ) h]
    rfl

end GlobalTheory.DefLift.LowerKill

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

variable {D : D7} {θ : InfF D}

theorem IsKerSys.lift (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {V W : HSp D} {M : Type} [AddCommGroup M]
    [Module ℂ M] {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (hκ : IsKerSys θ V W κ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hq : IsQuot V μ 𝓕) {F : GA D V → ℂ} (hF : IsCuspForm θ V F) (f : M) :
    (∀ h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ) ∧ IsAutFunSm θ W fun h => ∫ g in 𝓕, κ f g h * F g ∂μ := by
  have hD := GlobalTheory.T.smoothCuspForm_mem_unitaryRapidDecayForms hP D θ hθ V F hF
  obtain ⟨h1, h2, ⟨N, h3⟩, h4⟩ := GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hD
  let L : M → GA D W → ℂ := fun f h => ∫ g in 𝓕, κ f g h * F g ∂μ
  have hd : ∀ f τ, ∀ X ∈ lieAt W τ, ∃ f', ∀ h,
      HasDerivAt (fun t : ℝ => L f (h * oneP θ W τ X t)) (L f' h) 0 := fun f τ X hX =>
    (hκ.derW τ X hX f).imp fun f' e => h4 τ X hX f f' e
  refine ⟨h1 f, ⟨fun γ hγ h => ?_, ?_, h2 f⟩, ?_, GlobalTheory.T.kernelLift_gelfandInvariantFinite_of_finite D θ hθ V W M κ hκ μ 𝓕 hq F hD hF.1.zfin f, ?_⟩
  · have := fun g => hκ.left f 1 (one_mem _) γ hγ g h
    simp only [one_mul] at this
    simp only [this]
  · obtain ⟨U, U', -, hU', e⟩ := hκ.level f
    refine ⟨U', hU', fun k a b h => ?_⟩
    have := fun g => e 1 (one_mem _) (one_mem _) k a b g h
    simp only [mul_one] at this
    simp only [this]
  · refine GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ W (Set.range L) ?_ ?_ _ ⟨f, rfl⟩
    · rintro _ ⟨f, rfl⟩
      exact h2 f
    · rintro _ ⟨f, rfl⟩ τ X hX
      obtain ⟨f', e⟩ := hd f τ X hX
      exact ⟨_, ⟨f', rfl⟩, e⟩
  · obtain ⟨K, hK⟩ := GlobalTheory.T.unitaryAdelicHeight_coset_le_normInf_pow D θ W
    refine ⟨K * N, fun l hl x => ?_⟩
    have hw : ∃ f', l.foldr (fun p φ => Rder θ W p.1 p.2 φ) (L f) = L f' := by
      induction l with
      | nil => exact ⟨f, rfl⟩
      | cons p l ih =>
        obtain ⟨f', e⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
        obtain ⟨f'', e'⟩ := hd f' p.1 p.2 (hl p List.mem_cons_self)
        exact ⟨f'', by rw [List.foldr_cons, e]; exact funext fun h => (e' h).deriv⟩
    obtain ⟨f', e⟩ := hw
    obtain ⟨C, hC⟩ := h3 f'
    obtain ⟨C', hC'⟩ := hK x
    refine ⟨|C| * C' ^ N, fun g hg => ?_⟩
    rw [show (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) = L f from rfl, e]
    refine (hC _).trans ?_
    rw [pow_mul, mul_assoc, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hC' g hg) N)
      (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _)

def matLin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A where
  toFun X := ∑ i, ∑ j, X i j • E i j
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.smul_sum, mul_smul]

theorem matLin_single {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (i j : Fin n) :
    matLin E (Matrix.single i j 1) = E i j := by
  simp [matLin, Matrix.single, ite_and]

theorem isKerSys_thKer (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hw : GlobalTheory.Ker.IsWeak ψ S T om) (hc : OmCont ψ S T om) :
    IsKerSys θ S T (thKer ψ S T om) := by
  have cont : ∀ f, Continuous fun p : GA D S × GA D T => thKer ψ S T om f p.1 p.2 := fun f => hc f.1 f.2 0
  have left : ∀ f, ∀ γ ∈ GQ S, ∀ δ ∈ GQ T, ∀ g h, thKer ψ S T om f (γ * g) (δ * h) = thKer ψ S T om f g h := by
    intro f γ hγ δ hδ g h
    have e : om (γ * g, δ * h) = om (γ, δ) * om (g, h) := by rw [← map_mul]; rfl
    change om (γ * g, δ * h) f.1 0 = om (g, h) f.1 0
    rw [e]
    exact hw.om_aut γ hγ δ hδ _ (hw.om_pres _ _ f.2)
  have level : ∀ f, ∃ (U : Subgroup (GA D S)) (U' : Subgroup (GA D T)), IsOpen (U : Set (GA D S)) ∧
      IsOpen (U' : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC S → ∀ k' ∈ U', k' ∈ GfC T → ∀ g h,
        thKer ψ S T om f (g * k) (h * k') = thKer ψ S T om f g h := by
    intro f
    obtain ⟨U, U', a, b, e⟩ := GlobalTheory.T.exists_open_level_fixing_theta_function D ψ hψ S T om hw hc f.1 f.2
    refine ⟨U, U', a, b, fun k h1 h2 k' h3 h4 g h => ?_⟩
    have e' : om (g * k, h * k') = om (g, h) * om (k, k') := by rw [← map_mul]; rfl
    change om (g * k, h * k') f.1 0 = om (g, h) f.1 0
    rw [e', Module.End.mul_apply, e k h1 h2 k' h3 h4]
  obtain ⟨x, d, hx⟩ := GlobalTheory.T.thetaKernel_lieAction_through_weylAlgebra D ψ hψ S T om hw hc θ hθ
  have derV : ∀ τ, ∀ X ∈ lieAt S τ, ∀ f, ∃ f', ∀ g h,
      HasDerivAt (fun t : ℝ => thKer ψ S T om f (g * oneP θ S τ X t) h) (thKer ψ S T om f' g h) 0 :=
    fun τ X hX f => ((hx τ).2.2 X hX).elim fun _ e => ⟨_, e f⟩
  have derW : ∀ τ, ∀ X ∈ lieAt T τ, ∀ f, ∃ f', ∀ g h,
      HasDerivAt (fun t : ℝ => thKer ψ S T om f g (h * oneP θ T τ X t)) (thKer ψ S T om f' g h) 0 :=
    fun τ X hX f => ((hx τ).2.1 X hX).elim fun _ e => ⟨_, e f⟩
  refine ⟨cont, left, level, ?_, derV, derW, fun τ => ?_⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.T.weilRep_thetaFunction_polynomialGrowth_realPoints D ψ hψ S T om hw θ hθ
    obtain ⟨N', hN'⟩ := GlobalTheory.T.adelicHeight_growth_of_cosetGrowth_unitaryPair D θ hθ S T N
    exact ⟨N', fun f => hN' _ (left f) (level f) fun x y =>
      (hN f.1 f.2 x y).imp fun C e a ha b hb => e a ha b hb 0⟩
  · have sT : ∀ f g, thKer ψ S T om f g ∈ SmFun θ T := fun f g => by
      refine GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ T (Set.range fun f => thKer ψ S T om f g) ?_ ?_ _ ⟨f, rfl⟩
      · rintro _ ⟨f, rfl⟩
        exact (cont f).comp (Continuous.prodMk_right g)
      · rintro _ ⟨f, rfl⟩ τ X hX
        obtain ⟨f', e⟩ := derW τ X hX f
        exact ⟨_, ⟨f', rfl⟩, e g⟩
    have sS : ∀ f h, swapKer (thKer ψ S T om) f h ∈ SmFun θ S := fun f h => by
      refine GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ S (Set.range fun f => swapKer (thKer ψ S T om) f h) ?_ ?_ _ ⟨f, rfl⟩
      · rintro _ ⟨f, rfl⟩
        exact (cont f).comp (Continuous.prodMk_left h)
      · rintro _ ⟨f, rfl⟩ τ X hX
        obtain ⟨f', e⟩ := derV τ X hX f
        exact ⟨_, ⟨f', rfl⟩, fun g => e g h⟩
    obtain ⟨g1, g2⟩ := GlobalTheory.T.glRel_of_canonicalCommutationRelations _ _ _ (x τ) (d τ) (hx τ).1
    obtain ⟨c, e1⟩ := GlobalTheory.T.gelfandInvariants_act_kernelFamily_shifted D θ hθ T _ _ (thKer ψ S T om) sT τ (matLin fun i j => ∑ a, x τ (i, a) * d τ (j, a))
      (by simpa only [matLin_single] using g1) (hx τ).2.1
    obtain ⟨c', e2⟩ := GlobalTheory.T.gelfandInvariants_act_kernelFamily_shifted D θ hθ S _ _ (swapKer (thKer ψ S T om)) sS τ
      (matLin fun a b => -∑ i, x τ (i, b) * d τ (i, a)) (by simpa only [matLin_single] using g2)
      fun Y hY => ((hx τ).2.2 Y hY).imp fun _ e f h g => e f g h
    simp only [matLin_single] at e1 e2
    exact ⟨_, _, e2, e1, (GlobalTheory.T.adjoin_gelfandInvariants_dual_pair_eq _ _ _ (x τ) (d τ) (hx τ).1 c c').symm⟩

theorem toTWsmall_zero (S T : HSp D) : toTWsmall S T 0 = 0 := by
  unfold toTWsmall
  rw [Matrix.zero_mul, Matrix.transpose_zero]

theorem exists_thKer {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (Wf : WeilFun D ψ) {V W : HSp D}
    {χ χ' : IdC D} (ha : admitted V W χ χ') (hr : V.rank < W.rank) :
    ∃ om, GlobalTheory.Ker.IsWeak ψ V W om ∧ OmCont ψ V W om ∧
      ∀ Φ, ∃ f, ∀ g h, Wf.ker V W χ χ' Φ g h = thKer ψ V W om f g h := by
  obtain ⟨om, H, e⟩ := GlobalTheory.T.exists_orientedWeilDatum_of_adelicWeilRep_theta D ψ hψ V W χ χ' _ ha hr (Wf.core.weil V W χ χ' ha)
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr.le
  refine ⟨om, GlobalTheory.Ker.isWeak_of_datum H, H.om_cont, fun Φ => ⟨⟨fun x => Φ.1 (toTWsmall V W x), ?_⟩, fun g h => ?_⟩⟩
  · have := (h7 ψ Φ.1).2 (mem_ThS.1 Φ.2)
    simp only [hE] at this
    exact this
  · have := congrFun (e (g, h) Φ) 0
    rw [toTWsmall_zero] at this
    exact this.symm

theorem liftAut : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LiftAut D := by
  intro hP D θ hθ ψ hψ Wf V W χ χ' ha μ 𝓕 hq Φ F hF
  rcases lt_or_gt_of_ne ha.1 with hr | hr
  · obtain ⟨om, hw, hc, e⟩ := exists_thKer hψ Wf ha hr
    obtain ⟨f, e⟩ := e Φ
    simp only [e]
    exact (isKerSys_thKer hθ hψ hw hc).lift hP hθ hq hF f
  · have ha' : admitted W V χ' χ := ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩
    obtain ⟨om, hw, hc, e⟩ := exists_thKer hψ Wf ha' hr
    have hΦ := (GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ V W Φ.1).2.2 ha.1 (mem_ThS.1 Φ.2)
    obtain ⟨f, e⟩ := e ⟨_, mem_ThS.2 hΦ⟩
    have e' : ∀ g h, Wf.ker V W χ χ' Φ g h = swapKer (thKer ψ W V om) f g h := fun g h =>
      (Wf.om_swap V W χ χ' ha g h Φ ⟨_, mem_ThS.2 hΦ⟩ (fun _ => rfl) 0).symm.trans (e h g)
    simp only [e']
    exact (isKerSys_thKer hθ hψ hw hc).swap.lift hP hθ hq hF f

end GlobalTheory.Mem.Lift

end
end

