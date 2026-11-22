import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroup
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0662
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0165
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0689
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormPlaceLeOfFrobeniusStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_place_le_of_frobenius : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ q : ℕ, 1 < q → ∀ σ : G E Ω, IsFrob A q σ → normV w ≤ q := by
  first | exact @GlobalTheory.NormLeFrob.normV_le_of_isFrob | exact GlobalTheory.NormLeFrob.normV_le_of_isFrob | (intros; apply GlobalTheory.NormLeFrob.normV_le_of_isFrob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefMapSmulMap
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CoefLin

open MvPolynomial Formalism.L2.Pj

variable {σ : Type} (F : IntermediateField ℚ ℂ) (lam : ℂ →ₗ[F] F)

def coefFun (p : MvPolynomial σ ℂ) : MvPolynomial σ F := ∑ m ∈ p.support, monomial m (lam (p.coeff m))

theorem coeff_coefFun (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : (coefFun F lam p).coeff m = lam (p.coeff m) := by
  classical
  rw [coefFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

def coefMap : MvPolynomial σ ℂ →+ MvPolynomial σ F where
  toFun := coefFun F lam
  map_zero' := by ext m; rw [coeff_coefFun, coeff_zero, coeff_zero, map_zero]
  map_add' p q := by ext m; rw [coeff_coefFun, coeff_add, coeff_add, coeff_coefFun, coeff_coefFun, map_add]

variable {F lam}

theorem coeff_coefMap (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    (coefMap F lam p).coeff m = lam (p.coeff m) :=
  coeff_coefFun F lam p m

theorem coefMap_monomial (m : σ →₀ ℕ) (c : ℂ) :
    coefMap F lam (monomial m c) = lam c • monomial m (1 : F) := by
  ext m'
  rw [coeff_coefMap, coeff_smul, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem coefMap_smul_map (c : ℂ) (R : MvPolynomial σ F) :
    coefMap F lam (c • map (algebraMap F ℂ) R) = lam c • R := by
  ext m
  rw [coeff_coefMap, coeff_smul, coeff_map, coeff_smul, smul_eq_mul, smul_eq_mul]
  have : c * algebraMap F ℂ (R.coeff m) = R.coeff m • c := by
    rw [Algebra.smul_def, mul_comm]
  rw [this, map_smul, smul_eq_mul, mul_comm]

theorem coefMap_comm (Φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) (Ψ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (h : ∀ Q, Φ (map (algebraMap F ℂ) Q) = map (algebraMap F ℂ) (Ψ Q)) (p : MvPolynomial σ ℂ) :
    coefMap F lam (Φ p) = Ψ (coefMap F lam p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : (monomial m c : MvPolynomial σ ℂ) = c • map (algebraMap F ℂ) (monomial m (1 : F)) := by
      rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, h, coefMap_smul_map, ← hm, coefMap_monomial, map_smul]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

variable {T : Type} (r : T → ℕ) (n : ℕ)

theorem lap_map (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) (Q : MvPolynomial (Letter T r n) F) :
    lap r n ℂ 1 τ τ' a a' (map (algebraMap F ℂ) Q) = map (algebraMap F ℂ) (lap r n F 1 τ τ' a a' Q) := by
  simp only [lap, LinearMap.sum_apply, map_sum, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [pderiv_map]

theorem rowShift_map (σ₀ : T) (i i' : Fin (r σ₀)) (t : F) (Q : MvPolynomial (Letter T r n) F) :
    rowShift r n ℂ σ₀ i i' (t : ℂ) (map (algebraMap F ℂ) Q) = map (algebraMap F ℂ) (rowShift r n F σ₀ i i' t Q) := by
  have key : (rowShift r n ℂ σ₀ i i' (t : ℂ)).toRingHom.comp (map (algebraMap F ℂ)) =
      (map (algebraMap F ℂ)).comp (rowShift r n F σ₀ i i' t).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [rowShift]
    · intro ℓ
      simp only [rowShift, RingHom.coe_comp, Function.comp_apply, map_X, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_X]
      split_ifs <;> simp
  exact RingHom.congr_fun key Q

end GlobalTheory.CoefLin

namespace GlobalTheory.SingleDatum

open MvPolynomial Formalism.L2.Pj GlobalTheory.CoefLin

theorem HHa_coefLin : ∀ (T : Type) (r : T → ℕ) (n : ℕ) (cj : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (F : IntermediateField ℚ ℂ) (lam : ℂ →ₗ[F] F), ∀ P ∈ HHa r n ℂ cj isX a, ∃ P' ∈ HHa r n F cj isX a,
      ∀ mo, P'.coeff mo = lam (P.coeff mo) := by
  intro T r n cj isX a F lam P hP
  obtain ⟨hH, hR, hD⟩ := hP
  refine ⟨coefMap F lam P, ⟨?_, ?_, ?_⟩, coeff_coefMap P⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at hH ⊢
    intro τ hτ i i'
    rw [← coefMap_comm (lap r n ℂ 1 τ (cj τ) i i') (lap r n F 1 τ (cj τ) i i') (lap_map r n τ (cj τ) i i') P,
      hH τ hτ i i', map_zero]
  · intro σ₀ i i' hii t
    have key := coefMap_comm (lam := lam) (rowShift r n ℂ σ₀ i i' (t : ℂ)).toLinearMap
      (rowShift r n F σ₀ i i' t).toLinearMap (rowShift_map r n σ₀ i i' t) P
    simp only [AlgHom.toLinearMap_apply] at key
    rw [← key, hR σ₀ i i' hii (t : ℂ)]
  · intro m hm σ₀ i
    refine hD m ?_ σ₀ i
    rw [mem_support_iff] at hm ⊢
    intro h0
    apply hm
    rw [coeff_coefMap, h0, map_zero]

end GlobalTheory.SingleDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCocycleOfSemistableCoboundary
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.CocycStLemma

theorem tmul_one_injective {F V B : Type} [Field F] [AddCommGroup V] [Module F V] [Ring B] [Algebra F B]
    [Nontrivial B] : Function.Injective (fun v : V => v ⊗ₜ[F] (1 : B)) := by
  have hinj : Function.Injective (Algebra.linearMap F B) := (algebraMap F B).injective
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F B)
    (LinearMap.ker_eq_bot.mpr hinj)
  intro v w h
  have h2 := congrArg (fun x => TensorProduct.rid F V (LinearMap.lTensor V f x)) h
  have h1 : f 1 = 1 := by
    have := LinearMap.congr_fun hf 1
    simpa using this
  simpa [h1] using h2

end GlobalTheory.CocycStLemma

theorem GlobalTheory.cocycle_of_st_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → c ∈ continuousCocycles ρ := by
  intro l _ P AI T K V _ _ _ _ _ _ _ ρ hρ z c hc
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := GlobalTheory.T.coboundary_deRham_of_coboundary_semistable l P AI T K V ρ c z hc
    refine GlobalTheory.T.continuous_cochain_of_deRham_coboundary l P AI T K V ρ hρ 0 Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) b c ?_
    intro g
    simp [hb g]
  · intro g h
    haveI : Nontrivial P.R.B := nontrivial_B P
    haveI : Nontrivial (Bst P) := Polynomial.nontrivial
    apply GlobalTheory.CocycStLemma.tmul_one_injective (F := ℚ_[l]) (B := Bst P)
    simp only [add_tmul]
    rw [hc, hc g, map_mul, Module.End.mul_apply]
    have e : stRep P ρ g (c h ⊗ₜ[ℚ_[l]] (1 : Bst P)) = ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
      rw [stRep_tmul, map_one]
    rw [← e, hc h, map_sub]
    abel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → Continuous i.symm ∧ (∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) ∧ (∀ x : kˣ, ord k' (Units.map i.toRingHom.toMonoidHom x) = ord k x) ∧ resCard k' = resCard k ∧ ∀ (s : ℂ) (x : kˣ), absPow k' s (Units.map i.toRingHom.toMonoidHom x) = absPow k s x := by
  first | exact @GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation | exact GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation | (intros; apply GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharactersGivenJumpsUnramifiedTwistsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_characters_given_jumps_unramified_twists : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.tableLineDegreeTwo.adm20 D HW F := by
  first | exact @GlobalTheory.CrysCharJumps.adm20_of_fonOf | exact GlobalTheory.CrysCharJumps.adm20_of_fonOf | (intros; apply GlobalTheory.CrysCharJumps.adm20_of_fonOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspKillHolds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.CuspKillProof

theorem cuspKill_holds : ∀ D : D7, CuspKill D := by
  intro D W ν hν s I hI Γ hΓQ hNΓ hnorm 𝓓 h𝓓 Φ φ hΦc hΦΓ hΦN hφ hcusp hint
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W
  haveI : BorelSpace (GA D W) := ⟨rfl⟩
  haveI : Countable (GQ W) := GlobalTheory.AutomorphicL2Unitary.countable_of_discrete
  haveI : Countable Γ := Function.Injective.countable (Subgroup.inclusion_injective hΓQ)
  have hNc : IsClosed (NI W I : Set (GA D W)) := by
    rw [← GlobalTheory.Cusp.NA_frameFlag hI]
    haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
    exact GlobalTheory.Cusp.IsoFlag.isClosed_unip _ _ _
  have hcc : GlobalTheory.Cusp.Cocompact (GQ W) (NI W I) := by
    rw [← GlobalTheory.Cusp.NA_frameFlag hI]
    exact GlobalTheory.Cusp.cocompact_single _
  haveI : LocallyCompactSpace (NI W I) := hNc.locallyCompactSpace
  have hsub : Γ.subgroupOf (NI W I) = (GQ W).subgroupOf (NI W I) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => hΓQ h, fun h => hNΓ ⟨x.2, h⟩⟩
  set κ : Measure (NI W I) := Measure.haar
  set 𝓝 : Set (NI W I) := GlobalTheory.AutomorphicL2Unitary.stdDom ((GQ W).subgroupOf (NI W I))
  have h𝓝Q : IsFundamentalDomain ((GQ W).subgroupOf (NI W I)) 𝓝 κ := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ κ
  have h𝓝Γ : IsFundamentalDomain (Γ.subgroupOf (NI W I)) 𝓝 κ := by rw [hsub]; exact h𝓝Q
  have h𝓝t : κ 𝓝 ≠ ⊤ := hcc.measure_ne_top h𝓝Q
  have h0 : ∀ g, ∫ n in 𝓝, φ ((n : GA D W) * g) ∂κ = 0 := hcusp s I hI κ 𝓝 inferInstance h𝓝Q
  exact GlobalTheory.UnfoldNormal.unfold_zero_mean (GA D W) ν Γ (NI W I) inferInstance hNc hnorm κ 𝓝 inferInstance h𝓝Γ h𝓝t
    Φ φ hΦc.measurable hφ.cont.measurable hΦN hΦΓ (fun γ hγ g => hφ.left γ (hΓQ hγ) g) h0 𝓓 h𝓓 hint

end GlobalTheory.CuspKillProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalEqUnitaryTwist
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspRealTwist

theorem main : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (y : IrrGL k), y.IsCusp →
    ∃ (ρ : IrrGL k) (z : ℝ), ρ.IsCusp ∧ IsUnitarisable ρ.rep ∧ y = ρ.nu z := by
  intro _ k _ _ _ _ _ y hy
  obtain ⟨ω, hωs, hω⟩ := exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
  obtain ⟨s, hs⟩ := GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k ω hωs
  have hN : (y.1 : ℝ) ≠ 0 := by exact_mod_cast hy.1.ne'
  refine ⟨y.nu ((-(s / y.1) : ℝ) : ℂ), s / y.1, hy.nu _, ?_, ?_⟩
  · have hρc : (y.nu ((-(s / y.1) : ℝ) : ℂ)).IsCusp := hy.nu _
    have hcc := UnitaryOrder.hasCentralChar_nu y hω ((-(s / y.1) : ℝ) : ℂ)
    have hi := (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.irr
    have hsm := (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.smooth
    haveI := Model.nontrivial_of_isIrreducible hi
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.V)
    obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hsm (GlobalTheory.SqIntUnit.compactOpen_basis k _) hv₀
    refine GlobalTheory.isUnitarisable_of_isSupercuspidal _ _ _ (l : Module.Dual ℂ _) l.2
      (fun e => hl (by rw [e]; rfl)) hi (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k _ _ _ hρc.2) ?_
    intro g hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨a, rfl⟩ := hg
    refine ⟨_, ?_, hcc a⟩
    have h1 := UnitaryOrder.log_norm_mul_absPow ω (-(s / y.1)) y.1 a
    have hpos := nabs_pos' k a
    rw [hs a, Real.log_rpow hpos] at h1
    have h2 : Real.log ‖(((ω * absPow k ((-(s / y.1) : ℝ) : ℂ) ^ y.1) a : ℂˣ) : ℂ)‖ = 0 := by
      rw [h1]; field_simp; ring
    exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.2 (Units.ne_zero _)) h2
  · rw [IrrGL.nu_nu, show ((-(s / y.1) : ℝ) : ℂ) + ((s / y.1 : ℝ) : ℂ) = 0 by push_cast; ring, IrrGL.nu_zero]

end GlobalTheory.CuspRealTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotSemistableOfMatrixMonodromyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_potSemistable_of_matrix_monodromy : MatThm → GlobalTheory.Published.DeRhamPotSemistable := by
  first | exact @GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm | exact GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm | (intros; apply GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupActsResiduesFrobeniusPower
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

noncomputable section

namespace GlobalTheory.DecFrobPow

theorem frob_pow_apply {F R : Type} [Field F] [Fintype F] [CommRing R] [Algebra F R] (n : ℕ) (x : R) :
    ((FiniteField.frobeniusAlgHom F R) ^ n) x = x ^ (Fintype.card F ^ n) := by
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]

theorem exists_pow_of_algHom {k F : Type} [Field k] [Field F] [Fintype F] [Algebra F k]
    (τ : k →ₐ[F] k) {a : ℕ} (ha : 0 < a) :
    ∃ j : ℕ, ∀ x : k, x ^ (Fintype.card F ^ a) = x → τ x = x ^ (Fintype.card F ^ j) := by
  set q := Fintype.card F with hq
  let S : Subalgebra F k := AlgHom.equalizer ((FiniteField.frobeniusAlgHom F k) ^ a) (AlgHom.id F k)
  have hS : ∀ x, x ∈ S ↔ x ^ (q ^ a) = x := by
    intro x
    show ((FiniteField.frobeniusAlgHom F k) ^ a) x = (AlgHom.id F k) x ↔ _
    rw [frob_pow_apply]; rfl
  let L : IntermediateField F k := S.toIntermediateField (fun x hx => by
    rw [hS] at hx ⊢; rw [inv_pow, hx])
  have hL : ∀ x, x ∈ L ↔ x ^ (q ^ a) = x := hS
  have hq1 : 1 < q := Fintype.one_lt_card
  have hfin : (L : Set k).Finite := by
    have hP : (X ^ q ^ a - X : k[X]) ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero k ha.ne' hq1
    refine (Polynomial.finite_setOfPred_isRoot hP).subset fun x hx => ?_
    have := (hL x).mp hx
    simp [Polynomial.IsRoot, this]
  haveI : Finite L := hfin.to_subtype
  let σ : L →ₐ[F] L := (τ.comp L.val).codRestrict L.toSubalgebra fun x => by
    show τ (x : k) ∈ L
    rw [hL, ← map_pow, (hL x).mp x.2]
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow F L).2 σ
  refine ⟨n, fun x hx => ?_⟩
  have h1 := congrArg (fun f : L →ₐ[F] L => ((f ⟨x, (hL x).mpr hx⟩ : L) : k)) hn
  simp only [frob_pow_apply] at h1
  have h2 : ((σ ⟨x, (hL x).mpr hx⟩ : L) : k) = τ x := rfl
  rw [← h2, ← h1, SubmonoidClass.coe_pow]

end GlobalTheory.DecFrobPow

namespace GlobalTheory.DecFrobPow

theorem exists_place {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (A : ValuationSubring Ω) {p : ℕ} (hp : p.Prime) (hpA : A.valuation (p : Ω) < 1) :
    ∃ wK : HeightOneSpectrum (𝓞 K), IsPlaceOver A wK := by
  let g : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.algebraMap (B := Ω))
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap g
  have hmem : ∀ x : 𝓞 K, x ∈ P ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := fun x =>
    A.valuation_lt_one_iff (g x)
  have hne : P ≠ ⊥ := by
    intro h0
    have hpP : ((p : ℕ) : 𝓞 K) ∈ P := by
      rw [hmem]; simpa using hpA
    rw [h0, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  exact ⟨⟨P, Ideal.comap_isPrime g _, hne⟩, fun x => (hmem x).symm⟩

theorem exists_pow_cong_of_mem {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (A : ValuationSubring Ω) {p : ℕ} (hp : p.Prime) (hpA : A.valuation (p : Ω) < 1) :
    ∃ c : ℕ, 0 < c ∧ ∀ z : K, A.valuation (algebraMap K Ω z) ≤ 1 →
      A.valuation ((algebraMap K Ω z) ^ (p ^ c) - algebraMap K Ω z) < 1 := by
  obtain ⟨wK, hwK⟩ := exists_place (K := K) A hp hpA
  obtain ⟨φ, hφD, hφ⟩ := exists_isFrob (F := K) hwK
  obtain ⟨p', c, hp', hc, hN, hp'A⟩ := GlobalTheory.FrobTeich.exists_prime_pow_normV A wK hwK
  have hchar : ∀ r : ℕ, r.Prime → A.valuation (r : Ω) < 1 → CharP (IsLocalRing.ResidueField A) r := by
    intro r hr hrA
    refine (CharP.charP_iff_prime_eq_zero hr).2 ?_
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      A.valuation_lt_one_iff]
    simpa using hrA
  have hpp : p' = p := by
    haveI := hchar p hp hpA
    haveI := hchar p' hp' hp'A
    exact CharP.eq (IsLocalRing.ResidueField A) ‹CharP _ p'› ‹CharP _ p›
  subst hpp
  refine ⟨c, hc, fun z hz => ?_⟩
  have h1 := hφ _ hz
  rw [hN, φ.commutes] at h1
  rw [← Valuation.map_neg, neg_sub]
  exact h1

end GlobalTheory.DecFrobPow

namespace GlobalTheory.DecFrobPow

theorem pow_pow_eq_self {R : Type} [Monoid R] {r : R} {M : ℕ} (h : r ^ M = r) (b : ℕ) :
    r ^ (M ^ b) = r := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ, pow_mul, ih, h]

theorem exists_field_cong_pow : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w),
    ∀ d ∈ Dec (F := E) A, ∀ y : Ω, ∃ K : IntermediateField E Ω, FiniteDimensional E K ∧ y ∈ K ∧
      ∃ j : ℕ, ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1 := by
  intro E Ω _ _ _ _ _ A w h d hd y
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  set K := IntermediateField.adjoin E ({y} : Set Ω) with hK
  haveI hKfin : FiniteDimensional E K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  haveI : NumberField K := ⟨⟩
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  refine ⟨K, hKfin, IntermediateField.mem_adjoin_simple_self E y, ?_⟩
  obtain ⟨p, b, hp, hb, hq, hpA⟩ := GlobalTheory.FrobTeich.exists_prime_pow_normV A w h
  obtain ⟨c, hc, hcK⟩ := exists_pow_cong_of_mem (K := K) A hp hpA
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 E ⧸ w.asIdeal) = normV w := Fintype.card_eq_nat_card
  let gE : 𝓞 E →+* A := ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)).codRestrict A fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.algebraMap (B := Ω))
  let ι : 𝓞 E ⧸ w.asIdeal →+* IsLocalRing.ResidueField A :=
    Ideal.Quotient.lift w.asIdeal ((IsLocalRing.residue A).comp gE) (fun x hx => by
      show IsLocalRing.residue A (gE x) = 0
      rw [IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
      exact (h x).mpr hx)
  letI : Algebra (𝓞 E ⧸ w.asIdeal) (IsLocalRing.ResidueField A) := ι.toAlgebra
  let D : A.decompositionSubgroup E := ⟨d, hd⟩
  let τ0 : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A :=
    MulSemiringAction.toRingHom (A.decompositionSubgroup E) (IsLocalRing.ResidueField A) D
  have hτ0 : ∀ a : A, τ0 (IsLocalRing.residue A a) = IsLocalRing.residue A (D • a) := fun a =>
    (IsLocalRing.ResidueField.residue_smul (g := D) (r := a)).symm
  have hval : ∀ a : A, ((D • a : A) : Ω) = d a := fun a => rfl
  let τ : IsLocalRing.ResidueField A →ₐ[𝓞 E ⧸ w.asIdeal] IsLocalRing.ResidueField A :=
    { τ0 with
      commutes' := fun c => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
        show τ0 (ι (Ideal.Quotient.mk _ x)) = ι (Ideal.Quotient.mk _ x)
        have e1 : ι (Ideal.Quotient.mk _ x) = IsLocalRing.residue A (gE x) := Ideal.Quotient.lift_mk _ _ _
        rw [e1, hτ0]
        congr 1
        apply Subtype.ext
        rw [hval]
        exact d.commutes _ }
  obtain ⟨j, hj⟩ := exists_pow_of_algHom τ hc
  rw [hcard] at hj
  refine ⟨j, fun z hzK hz => ?_⟩
  let a : A := ⟨z, (A.valuation_le_one_iff z).mp hz⟩
  have h1 : A.valuation (z ^ (p ^ c) - z) < 1 := hcK ⟨z, hzK⟩ hz
  have h2 : IsLocalRing.residue A a ^ (p ^ c) = IsLocalRing.residue A a := by
    rw [← sub_eq_zero, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      A.valuation_lt_one_iff]
    exact h1
  have h3 : IsLocalRing.residue A a ^ (normV w ^ c) = IsLocalRing.residue A a := by
    rw [hq, ← pow_mul, mul_comm, pow_mul]
    exact pow_pow_eq_self h2 b
  have h4 := hj _ h3
  have h5 : τ (IsLocalRing.residue A a) = IsLocalRing.residue A (D • a) := hτ0 a
  rw [h5, ← sub_eq_zero, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    A.valuation_lt_one_iff] at h4
  exact h4

end GlobalTheory.DecFrobPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ElementDenominatorAdm7Statement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adm7_elementDenominator : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm7 D := by
  first | exact @GlobalTheory.elementDenominator_adm7 | exact GlobalTheory.elementDenominator_adm7 | (intros; apply GlobalTheory.elementDenominator_adm7 <;> assumption)
end

