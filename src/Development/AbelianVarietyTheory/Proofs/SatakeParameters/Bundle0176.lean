import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0005
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAtStandardPrime
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0165
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0171
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacLat
variable {D : D7}

theorem under_eq_of_delta {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : GlobalTheory.IdemSupport.Comp D Φ)
    {P : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (h1 : Φ (algebraMap (AF D.host.F) (AE D) ε) P ≠ 0) : P.under (𝓞 D.host.F) = v := by
  by_contra hne
  exact h1 ((GlobalTheory.IdemSupport.place_comp hΦ hε).2.2 P hne)

theorem place_of_primeIdem {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) :
    ∃ v ε, IsPlaceIdem D v ε ∧ f = algebraMap (AF D.host.F) (AE D) ε ∧ P.under (𝓞 D.host.F) = v := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hff := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.1 P e f h).1
  rcases h with ⟨hid, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, hT⟩
  · obtain ⟨h1, h2, v, ε, hε, hsum⟩ := hid.1
    refine ⟨v, ε, hε, hsum, under_eq_of_delta hΦ hε ?_⟩
    have hinf : infPart D e = 0 := by
      have : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
      rw [this, map_mul, hsum, (GlobalTheory.IdemSupport.place_comp hΦ hε).1, mul_zero]
    have hd := (GlobalTheory.IdemSupport.tie_iff hΦ h1 hinf P).1 hid.2
    have hc0 : Φ (cA D e) P = 0 := by
      have := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (cA D e) P
      rw [h2, GlobalTheory.IdemSupport.ev_zero, hd.2.1, one_mul] at this
      exact this.symm
    rw [← hsum, GlobalTheory.IdemSupport.ev_add, hd.2.1, hc0, add_zero]
    exact one_ne_zero
  · refine ⟨v, ε, hε, rfl, under_eq_of_delta hΦ hε ?_⟩
    have hd := (GlobalTheory.IdemSupport.tie_iff hΦ hff (GlobalTheory.IdemSupport.place_comp hΦ hε).1 P).1 hT
    rw [hd.2.1]; exact one_ne_zero
end GlobalTheory.VacLat

namespace GlobalTheory.VacLat
variable {D : D7}

theorem two_not_mem {P : Pl D.host.E} {e : AE D} (he : GlobalTheory.IdemSupport.Comparison₂ P e) (hc : cA D e = e) (hi : e * e = e)
    (h0 : infPart D e = 0) : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hd := (GlobalTheory.IdemSupport.tie_iff hΦ hi h0 P).1 he
  have hd' := GlobalTheory.IdemSupport.delta_conj hΦ hd
  rw [hc] at hd'
  have hPP : GlobalTheory.IdemSupport.cP P = P := by
    by_contra hne
    have := hd.2.2 _ hne
    rw [hd'.2.1] at this
    exact one_ne_zero this
  intro h2
  refine Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.not_fixed_ram D P 2 (Or.inl rfl) h2 (Ideal.ext fun x => ?_)
  rw [Ideal.mem_comap]
  have : Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.sgO D x = GlobalTheory.IdemSupport.cO D x := by
    apply RingOfIntegers.ext
    rw [GlobalTheory.IdemSupport.cO_coe, GlobalTheory.SplitIdem.star_eq_conj]
    rfl
  rw [this, ← GlobalTheory.IdemSupport.mem_cP, hPP]

theorem unit_factor {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) (M : ℕ)
    (hM : (M : 𝓞 D.host.F) ∉ v.asIdeal) :
    ∃ γ ∈ intAf D.host.F, ε = pairA D.host.F 0 ((M : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * γ) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have hM0 : (M : D.host.F) ≠ 0 := by
    intro h
    apply hM
    have : (M : 𝓞 D.host.F) = 0 := by
      apply RingOfIntegers.ext; simpa using h
    rw [this]; exact zero_mem _
  refine ⟨α * algebraMap D.host.F _ ((M : D.host.F)⁻¹), fun w => ?_, ?_⟩
  · rw [map_mul, AlgHom.commutes]
    by_cases hw : w = v
    · subst hw
      rw [h1, one_mul]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀]
      have : HeightOneSpectrum.valuation D.host.F w (M : D.host.F) = 1 := by
        rw [← map_natCast (algebraMap (𝓞 D.host.F) D.host.F) M, HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 hM
      rw [this, inv_one]
    · rw [h0 w hw, zero_mul]; exact zero_mem _
  · congr 1
    rw [← mul_assoc, mul_comm _ α, mul_assoc, ← map_natCast (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) M,
      ← map_mul, mul_inv_cancel₀ hM0, map_one, mul_one]
end GlobalTheory.VacLat

namespace GlobalTheory.VacLat
variable {D : D7}

theorem intAf_mul {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F} (hx : x ∈ intAf D.host.F) (hy : y ∈ intAf D.host.F) :
    x * y ∈ intAf D.host.F := fun w => by
  rw [map_mul]; exact mul_mem (hx w) (hy w)

theorem pairA_mul (x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) :
    pairA D.host.F 0 x * pairA D.host.F 0 y = pairA D.host.F 0 (x * y) := by
  exact Prod.ext (zero_mul _) rfl

theorem pairA_smul (a : D.host.F) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) :
    pairA D.host.F 0 (algebraMap D.host.F _ a * x) = a • pairA D.host.F 0 x := by
  refine Prod.ext ?_ ?_
  · exact (smul_zero a).symm
  · exact (Algebra.smul_def a x).symm

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem lat_scale (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (NS NT c : ℕ)
    (hS : ∀ x ∈ L0c D S, (NS : D.host.E) • x ∈ ΛS) (hT : ∀ x ∈ L0c D T, (NT : D.host.E) • x ∈ ΛT)
    (γ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (hγ : γ ∈ intAf D.host.F) (u : WO S T)
    (hu : u ∈ latO S T (L0c D S) (L0c D T) fun _ => True) :
    ∃ u' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ i j, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (((c * NS * NT : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * γ)) * u i j =
        (c • u') i j := by
  set a₀ := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (((c * NS * NT : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * γ)) with ha₀
  let φ : WO S T →+ WO S T := DistribMulAction.toAddMonoidHom (WO S T) a₀
  let ψc : WO S T →+ WO S T := DistribMulAction.toAddMonoidHom (WO S T) c
  have key : latO S T (L0c D S) (L0c D T) (fun _ => True) ≤
      ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)).map ψc).comap φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine ⟨Matrix.of fun i j => (pairA D.host.F 0 (γ * α)) ⊗ₜ[D.host.F]
        (a * ((NT : D.host.E) • t) i * ∑ k, star (((NS : D.host.E) • s) k) * S.gram k j),
      AddSubgroup.subset_closure ⟨γ * α, intAf_mul hγ hα, fun v hv => (hv trivial).elim, a, ha, _, hS s hs, _, hT t ht, rfl⟩, ?_⟩
    ext i j
    simp only [ψc, φ, DistribMulAction.toAddMonoidHom_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Pi.smul_apply]
    rw [ha₀, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.algebraMap_self, RingHom.id_apply, pairA_mul, mul_assoc (((c * NS * NT : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) γ α, ← map_natCast (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)),
      pairA_smul, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul]
    congr 1
    rw [nsmul_eq_mul, Algebra.smul_def, map_natCast]
    simp only [star_mul', star_natCast, Nat.cast_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  obtain ⟨u', hu', he⟩ := key hu
  exact ⟨u', hu', fun i j => (congrFun (congrFun he i) j).symm⟩
end GlobalTheory.VacLat

namespace GlobalTheory.VacLat

theorem isVacAt_of_isLatVac : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) ΛS ΛT (NS NT : ℕ), IsBaseFrame S βS ΛS NS → IsBaseFrame T βT ΛT NT → ∀ P : Pl D.host.E, ((NS * NT : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ f₀, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ → IsVacAt ψ S T P f₀ := by
  intro D ψ S T βS βT ΛS ΛT NS NT hS hT P hP f₀ hth hvac
  refine ⟨hth, fun e f' he u hu hhalf => ?_⟩
  have hNS : (NS : 𝓞 D.host.E) ∉ P.asIdeal := fun h => hP (by rw [Nat.cast_mul]; exact P.asIdeal.mul_mem_right _ h)
  have hNT : (NT : 𝓞 D.host.E) ∉ P.asIdeal := fun h => hP (by rw [Nat.cast_mul]; exact P.asIdeal.mul_mem_left _ h)
  obtain ⟨v, ε, hε, hf, hv⟩ := place_of_primeIdem he
  have hff := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.1 P e f' he).1
  have hunder : ∀ c : ℕ, (c : 𝓞 D.host.E) ∉ P.asIdeal → ((c * NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    intro c hc h
    rw [← hv] at h
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h
    rw [map_natCast, Nat.cast_mul, Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · rcases P.isPrime.mem_or_mem h with h | h
      · exact hc h
      · exact hNS h
    · exact hNT h
  rcases he with ⟨hid, rfl⟩ | ⟨hfe, -, hTie⟩
  · have hfu : ∀ i j, (e + cA D e) * u i j = u i j := by
      have h1 := hid.1.1
      have h2 := hid.1.2.1
      have h3 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
      have h4 : cA D e * e = 0 := by rw [mul_comm]; exact h2
      rcases hhalf with h | h <;> intro i j
      · have h' : e * u i j = u i j := h i j
        rw [← h', ← mul_assoc, add_mul, h1, h4, add_zero]
      · have h' : cA D e * u i j = u i j := h i j
        rw [← h', ← mul_assoc, add_mul, h2, h3, zero_add]
    obtain ⟨γ, hγ, hεγ⟩ := unit_factor hε (1 * NS * NT) (hunder 1 (by rw [Nat.cast_one]; exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)))
    obtain ⟨u', hu', heq⟩ := lat_scale S T ΛS ΛT NS NT 1 hS.2.2.2.1 hT.2.2.2.1 γ hγ u hu
    have hue : u = u' := by
      ext i j
      rw [← hfu i j, hf, hεγ, heq, one_smul]
    subst hue
    rcases hhalf with h | h
    · exact hvac.2 e hid.1 u hu' h
    · refine hvac.2 (cA D e) ⟨by rw [← map_mul, hid.1.1], by rw [cA_cA, mul_comm]; exact hid.1.2.1, ?_⟩ u hu' h
      obtain ⟨w, η, hη, hwη⟩ := hid.1.2.2
      exact ⟨w, η, hη, by rw [cA_cA, add_comm]; exact hwη⟩
  · have hf' : e = algebraMap (AF D.host.F) (AE D) ε := hfe.symm.trans hf
    have hc : cA D e = e := by rw [hf']; exact GlobalTheory.IdemSupport.cA_algebraMap ε
    have hi : e * e = e := hfe ▸ hff
    have h0 : infPart D e = 0 := by
      obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
      rw [hf']; exact (GlobalTheory.IdemSupport.place_comp hΦ hε).1
    have h2 := two_not_mem hTie hc hi h0
    have hfu : ∀ i j, e * u i j = u i j := by
      rcases hhalf with h | h
      · exact fun i j => h i j
      · rw [hc] at h; exact fun i j => h i j
    obtain ⟨γ, hγ, hεγ⟩ := unit_factor hε (2 * NS * NT) (hunder 2 h2)
    obtain ⟨u', hu', heq⟩ := lat_scale S T ΛS ΛT NS NT 2 hS.2.2.2.1 hT.2.2.2.1 γ hγ u hu
    have hue : u = 2 • u' := by
      ext i j
      rw [← hfu i j, hf', hεγ, heq]
    rw [hue]
    exact hvac.1 u' hu'

end GlobalTheory.VacLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogCoordinatesExponentIsCoboundary
section
noncomputable section

namespace GlobalTheory.CobExactProof

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF IsLawOfLog at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.KerInert.BeCob (eLT vLT psiLT)
open GlobalTheory.CurveDictionary (map_cob lgF_eq_logF cc_lgF')

theorem cobExact : Formalism.L2.KerInert.BeCob.CobExact := by
  intro l _ g hLT hOk hb F hF
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  set Lc : PowerSeries ℂ_[l] := lgF ℂ_[l] l with hLc
  have hL0 : PowerSeries.constantCoeff Lc = 0 := cc_lgF' ℂ_[l] l
  have hlog0 : PowerSeries.constantCoeff (Formalism.MainNotions.FormalGroupSystem.logF l) = 0 := by
    have h1 : k0ToC l (PowerSeries.coeff 0 (Formalism.MainNotions.FormalGroupSystem.logF l)) = 0 := by
      rw [← PowerSeries.coeff_map, lgF_eq_logF, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact cc_lgF' ℂ_[l] l
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (map_eq_zero_iff _ (k0ToC l).injective).1 h1
  have hcK : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l)) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hlog0
  have hsK : MvPowerSeries.HasSubst (fun i : Fin 2 =>
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hcK
  set c : Fin 2 → MvPowerSeries (Fin 2) ℂ_[l] := fun i => PowerSeries.subst (MvPowerSeries.X i) Lc with hcdef
  have hcC : ∀ i, MvPowerSeries.constantCoeff (c i) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hL0
  have hsC : MvPowerSeries.HasSubst c := MvPowerSeries.hasSubst_of_constantCoeff_zero hcC
  have hB : MvPowerSeries.map (k0ToC l) (inParam l (beLT hLT)) =
      MvPowerSeries.subst c (Formalism.L2.G.Pend.beC g e) := by
    unfold inParam
    rw [MvPowerSeries.map_subst hsK]
    have hc' : (fun i : Fin 2 => MvPowerSeries.map (k0ToC l)
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l))) = c := by
      funext i
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)),
        MvPowerSeries.map_X, lgF_eq_logF]
    rw [hc']
    congr 1
    exact Formalism.L2.G.Pend.map_beOf hb
  have h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (MvPowerSeries.C e⁻¹ * MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[l]) = 0 := by
    intro i
    rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  unfold Formalism.L2.G.Pend.beC at hB
  rw [Formalism.MainNotions.J.be_subst g hex hsC (Formalism.MainNotions.J.cc_pt g hex (h0 0)) (Formalism.MainNotions.J.cc_pt g hex (h0 1)),
    Formalism.MainNotions.J.pt_subst g hsC (h0 0), Formalism.MainNotions.J.pt_subst g hsC (h0 1), MvPowerSeries.subst_mul hsC,
    MvPowerSeries.subst_mul hsC, MvPowerSeries.subst_C, MvPowerSeries.subst_X hsC, MvPowerSeries.subst_X hsC] at hB
  rw [hB]

  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * Lc) = 0 := by
    rw [map_mul, hL0, mul_zero]
  have hvS : PowerSeries.HasSubst (PowerSeries.C e⁻¹ * Lc) := PowerSeries.HasSubst.of_constantCoeff_zero' hv0
  have hvcc : PowerSeries.constantCoeff (vLT hLT) = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hcA : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.C e⁻¹ * c i) = 0 := by
    intro i; rw [map_mul, hcC i, mul_zero]
  have hat : ∀ i : Fin 2, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[l]) (vLT hLT) =
      g.pt (MvPowerSeries.C e⁻¹ * c i) := by
    intro i
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply hvS
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))]
    unfold G1.pt
    congr 1
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X i), PowerSeries.subst_C]
  have hpsi : ∀ i : Fin 2, at1 i (psiLT hLT) = g.phAt (g.pt (MvPowerSeries.C e⁻¹ * c i)) := by
    intro i
    unfold at1 psiLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hvcc)
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)), hat i]
    rfl
  have hlgA : ∀ i, g.lg (g.pt (MvPowerSeries.C e⁻¹ * c i)) = MvPowerSeries.C e⁻¹ * c i := by
    intro i
    unfold G1.lg G1.pt
    rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex)
      (PowerSeries.HasSubst.of_constantCoeff_zero (hcA i)), hinv,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (hcA i))]
  set Fc := MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F with hFc
  have hFc0 : MvPowerSeries.constantCoeff Fc = 0 := by
    rw [hFc, MvPowerSeries.constantCoeff_map, hF.1, map_zero]
  have hLaw : PowerSeries.subst Fc Lc = c 0 + c 1 := by
    have h := congrArg (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype) hF.2.2
    rw [map_cob _ F hF.1, map_zero, Formalism.L2.Th1.E.Joints.map_lgF'] at h
    unfold cob at1 at h
    rw [← hFc] at h
    show _ = PowerSeries.subst (MvPowerSeries.X 0) Lc + PowerSeries.subst (MvPowerSeries.X 1) Lc
    linear_combination h
  have hadd : g.add (g.pt (MvPowerSeries.C e⁻¹ * c 0)) (g.pt (MvPowerSeries.C e⁻¹ * c 1)) =
      PowerSeries.subst Fc (vLT hLT) := by
    unfold G1.add
    rw [hlgA 0, hlgA 1, ← mul_add, ← hLaw]
    unfold vLT G1.pt
    rw [PowerSeries.subst_comp_subst_apply hvS (PowerSeries.HasSubst.of_constantCoeff_zero hFc0)]
    congr 1
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hFc0), PowerSeries.subst_C]
  unfold G1.be cob
  rw [hadd, ← hpsi 0, ← hpsi 1]
  unfold G1.phAt psiLT
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hvcc)
    (PowerSeries.HasSubst.of_constantCoeff_zero hFc0)]

end GlobalTheory.CobExactProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAtStandardPrimeStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedThetaFamily_normalised_at_standardPrime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N) L → TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N') L' → GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L') (fun z => B.eNat χ N N' L L' (s.flatV N N' z)) p ι := by
  first | exact @GlobalTheory.ThLoc.LocStd.latAt_std | exact GlobalTheory.ThLoc.LocStd.latAt_std | (intros; apply GlobalTheory.ThLoc.LocStd.latAt_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairingEquivContra
section
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InvPairing

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def pairMap (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) :
    π'.IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun b => ⟨B.flip b, mem_smoothPart_of_nhds (Filter.mem_of_superset
        ((hπ' b).mem_nhds (by simp)) fun g hg => by
          have hg' : π' g b = b := hg
          ext a
          show B (π g⁻¹ a) b = B a b
          have h := hB g (π g⁻¹ a) b
          rw [hg'] at h
          rw [← h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])⟩
      map_add' := fun b c => Subtype.ext (by simp)
      map_smul' := fun c b => Subtype.ext (by simp) }
  isIntertwining' g := by
    refine LinearMap.ext fun b => Subtype.ext (LinearMap.ext fun a => ?_)
    show B a (π' g b) = B (π g⁻¹ a) b
    have h := hB g (π g⁻¹ a) b
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    exact h

theorem pairMap_apply (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) (a : V) (b : W) :
    ((pairMap π hπ' B hB b : smoothPart π.dual) : Module.Dual ℂ V) a = B a b := rfl

theorem eq_zero_of_pairMap (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b)
    (h : ∀ b, pairMap π hπ' B hB b = 0) : B = 0 :=
  LinearMap.ext fun a => LinearMap.ext fun b => by
    have := congrArg (fun l : smoothPart π.dual => (l : Module.Dual ℂ V) a) (h b)
    simpa [pairMap_apply] using this

theorem pairMap_bijective (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) (hB0 : B ≠ 0)
    (hirr' : π'.IsIrreducible) (hirr : (contra π).IsIrreducible) :
    Function.Bijective (pairMap π hπ' B hB) := by
  set f := pairMap π hπ' B hB with hf
  constructor
  · let S : Subrepresentation π' :=
      { toSubmodule := LinearMap.ker f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          simp only [LinearMap.mem_ker] at hv ⊢
          have := LinearMap.congr_fun (f.isIntertwining' g) v
          simp only [LinearMap.comp_apply] at this
          rw [this, hv, map_zero] }
    rcases hirr'.eq_bot_or_eq_top S with hS | hS
    · intro x y hxy
      have : x - y ∈ S.toSubmodule := by
        show f.toLinearMap (x - y) = 0
        rw [map_sub]; exact sub_eq_zero.2 hxy
      rw [hS] at this
      exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 this)
    · exfalso
      refine hB0 (eq_zero_of_pairMap π hπ' B hB fun b => ?_)
      have : b ∈ S.toSubmodule := by rw [hS]; exact Submodule.mem_top
      exact this
  · let R : Subrepresentation (contra π) :=
      { toSubmodule := LinearMap.range f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          obtain ⟨w, rfl⟩ := hv
          refine ⟨π' g w, ?_⟩
          have := LinearMap.congr_fun (f.isIntertwining' g) w
          simpa only [LinearMap.comp_apply] using this }
    rcases hirr.eq_bot_or_eq_top R with hR | hR
    · exfalso
      refine hB0 (eq_zero_of_pairMap π hπ' B hB fun b => ?_)
      have : f b ∈ R.toSubmodule := ⟨b, rfl⟩
      rw [hR] at this
      exact (Submodule.mem_bot ℂ).1 this
    · intro l
      have : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
      obtain ⟨b, hb⟩ := this
      exact ⟨b, hb⟩

end GlobalTheory.InvPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrecedingStepDatumIntegralAwayFromLevelsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.precedingStepDatum_integral_away_from_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ al p₀ p Yb x, IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl1 (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 al p₀ p Yb x)) := by
  first | exact @GlobalTheory.xiCpl1_intOff | exact GlobalTheory.xiCpl1_intOff | (intros; apply GlobalTheory.xiCpl1_intOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RegularAlgebraicPurityOfClozel
section
namespace GlobalTheory

theorem regularAlgebraicPurity_of_clozel (hP : GlobalTheory.Published.ClozelPurity) (hC : GlobalTheory.Published.ClozelCohomological) :
    GlobalTheory.Published.RegularAlgebraicPurity := by
  intro E _ _ _ a ha π hr
  exact ⟨hP E a ha π fun τ => (hr τ).2, hC E a ha π hr⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeCombinationsCommuteFixedVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalHeckeCombinations_commute_fixedVectors : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ c c', ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P c (opOf π P c' u) = opOf π P c' (opOf π P c u) := by
  first | exact @GlobalTheory.SphLabelComm.label_ops_comm | exact GlobalTheory.SphLabelComm.label_ops_comm | (intros; apply GlobalTheory.SphLabelComm.label_ops_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriEigenvectorJacquetQuotientNeZeroStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameIwahoriEigenvector_jacquetQuotient_ne_zero : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (v : π.V) (θ : Fin n → kˣ →* ℂˣ), v ≠ 0 → IsIwVec θ π.π v → (Submodule.Quotient.mk v : Jacquet π.π (unipB k (Fin n))) ≠ 0 := by
  first | exact @GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero | exact GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero | (intros; apply GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentRadicalFlagStabilizerStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_flag_stabilizer : ∀ (k : Type) [Field k] (a s : ℕ) (d : Fin s → ℕ) (e : (Σ i, Fin (d i)) ≃ Fin a), GlobalTheory.SmGL.unipRad k e ≠ ⊥ → ∃ W : Submodule k (Fin a → k), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g : GL (Fin a) k, (∀ v, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v ∈ W) → (∀ v ∈ W, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v = 0) → g ∈ GlobalTheory.SmGL.unipRad k e := by
  first | exact @GlobalTheory.UnipFlag.exists_sub | exact GlobalTheory.UnipFlag.exists_sub | (intros; apply GlobalTheory.UnipFlag.exists_sub; all_goals assumption)
end

