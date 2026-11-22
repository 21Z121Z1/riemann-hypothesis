import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0348
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0429
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0567
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0359
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0338
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0419
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0366
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0778
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOMulSource
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0782
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishesSingleCoefficientOfKernelKills
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesInjective
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceInjectivity

theorem eq_or_conj_of_comap_eq {L : Type} [Field L] [NumberField L] [IsCMField L]
    (P P' : HeightOneSpectrum (𝓞 L))
    (h : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) =
      P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L))) :
    P' = P ∨ ∀ x : 𝓞 L, x ∈ P'.asIdeal ↔ IsCMField.ringOfIntegersComplexConj L x ∈ P.asIdeal := by
  set σ : 𝓞 L →+* 𝓞 L := (IsCMField.ringOfIntegersComplexConj L : 𝓞 L →+* 𝓞 L) with hσ
  have key : ∀ x ∈ P'.asIdeal, x ∈ P.asIdeal ∨ x ∈ P.asIdeal.comap σ := by
    intro x hx
    have hfix : IsCMField.complexConj L ((x * σ x : 𝓞 L) : L) = ((x * σ x : 𝓞 L) : L) := by
      simp [hσ, IsCMField.coe_ringOfIntegersComplexConj, mul_comm]
    obtain ⟨y, hy⟩ := (IsCMField.RingOfIntegers.complexConj_eq_self_iff (K := L) (x * σ x)).1 hfix
    have hy' : algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) y = x * σ x := RingOfIntegers.ext hy
    have h1 : y ∈ P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) := by
      rw [Ideal.mem_comap, hy']; exact P'.asIdeal.mul_mem_right _ hx
    rw [← h, Ideal.mem_comap, hy'] at h1
    rcases P.isPrime.mem_or_mem h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by rw [Ideal.mem_comap]; exact h2)
  have hsub : (P'.asIdeal : Set (𝓞 L)) ⊆ (P.asIdeal : Set (𝓞 L)) ∪ (P.asIdeal.comap σ : Set (𝓞 L)) :=
    fun x hx => key x hx
  have hmax : P'.asIdeal.IsMaximal := P'.isMaximal
  rcases Ideal.subset_union.1 hsub with h3 | h3
  · left
    exact HeightOneSpectrum.ext (hmax.eq_of_le P.isPrime.ne_top h3)
  · right
    have hpr : (P.asIdeal.comap σ).IsPrime := Ideal.comap_isPrime σ P.asIdeal
    have he := hmax.eq_of_le hpr.ne_top h3
    intro x
    rw [he, Ideal.mem_comap]
    rfl

end GlobalTheory.PlaceInjectivity

namespace GlobalTheory.PlaceInjectivity

theorem not_mem_of_coprime {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (w : HeightOneSpectrum (𝓞 E)) (h1 : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) :
    ((q : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have hco : IsCoprime ((p : ℤ)) ((q : ℤ)) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using (Nat.coprime_primes hp hq).mpr hpq)
  have hco' : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) := by
    simpa using hco.map (Int.castRingHom (𝓞 E))
  exact Ideal.IsPrime.notMem_of_isCoprime_of_mem hco' h1

end GlobalTheory.PlaceInjectivity

namespace GlobalTheory.PlaceInj

theorem splitPlace_v_injective : ∀ (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E), (∀ k v, (s k v).w = D.naut.plGw k v) → Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v) := by
  intro D s hs ⟨k, v⟩ ⟨k', v'⟩ heq
  simp only at heq
  have hc : (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      (D.naut.plGw k' v').asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [← hs, ← hs, (s k v).w_under, (s k' v').w_under, heq]
  by_cases hk : k = k'
  · subst hk
    rcases GlobalTheory.PlaceInjectivity.eq_or_conj_of_comap_eq _ _ hc with h | h
    · have := D.naut.plGw_inj k h.symm
      subst this
      rfl
    · exfalso
      apply D.naut.plGw_nconj k v v'
      intro x y hxy
      have hconj : (IsCMField.ringOfIntegersComplexConj D.host.E y : D.host.E) = (x : D.host.E) := by
        rw [IsCMField.coe_ringOfIntegersComplexConj, hxy]
        apply D.host.φ₀.injective
        rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
        simp
      rw [h y, RingOfIntegers.ext hconj]
  · exfalso
    have hg : D.host.g k ≠ D.host.g k' := by
      fin_cases k <;> fin_cases k' <;> simp_all [D.host.g_ne, D.host.g_ne.symm]
    have h1 : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈
        (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [Ideal.mem_comap, map_natCast]; exact D.naut.plGw_over k v
    rw [hc, Ideal.mem_comap, map_natCast] at h1
    exact GlobalTheory.PlaceInjectivity.not_mem_of_coprime (D.host.g_prime k') (D.host.g_prime k) hg.symm _
      (D.naut.plGw_over k' v') h1

end GlobalTheory.PlaceInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StepsOfArtinReciprocity
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

namespace GlobalTheory.Pass

theorem stepsNoCut_of_artin : GlobalTheory.Published.GlobalArtinReciprocity → StepsNoCut := fun hA =>
  ⟨GlobalTheory.CentralIdem.centralIdemCoeff, GlobalTheory.T.central_elements_from_idempotent_coeffs, GlobalTheory.T.typePrimeCompletionDegreeOneCount_proof, GlobalTheory.T.type_parameter_squarefree, GlobalTheory.T.typeFamily_potentiallyCrystalline_common_tame_extension,
    GlobalTheory.PotDual.stepPotDual, GlobalTheory.T.jump_range_positive_sign_place, GlobalTheory.T.dualJumpRangeNegativeSignPlace_proof, GlobalTheory.StepLiftPf.main, GlobalTheory.T.twisted_galois_rep_character_blocks, GlobalTheory.T.twisted_dual_families_continuous,
    GlobalTheory.T.localCountDirectLifting_proof, GlobalTheory.T.localCountDualLifting_proof, GlobalTheory.T.blochKatoCharactersTypePrime_proof, GlobalTheory.Pass.ResidualSpan.main, GlobalTheory.T.global_of_artin_reciprocity hA⟩

end GlobalTheory.Pass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeisOPureTensorO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.FiniteHeisComb

variable {D : D7}

theorem heisO_aPlus (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {u : WO S T}
    (hu : u.map (infPart D) = 0) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    heisO ψ S T u (aPlus (heisO ψ S T) θ τ J z g) = aPlus (heisO ψ S T) θ τ J z (heisO ψ S T u g) := by
  simp only [aPlus, crea]
  change GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T u _ = _
  rw [map_smul, map_sub, map_smul]
  show _ • (heisO ψ S T u (Formalism.IndefR.Datum.dRho _ _ _ _ _) - _ • heisO ψ S T u (Formalism.IndefR.Datum.dRho _ _ _ _ _)) = _
  rw [GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu, GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu]

theorem aPlus_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {S T : HSp D} (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : WO S T → ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (s : Finset (WO S T)) :
    IsThetaFunO ψ S T (∑ u ∈ s, c u • heisO ψ S T u g) ∧
      aPlus (heisO ψ S T) θ τ J z (∑ u ∈ s, c u • heisO ψ S T u g) =
        ∑ u ∈ s, c u • aPlus (heisO ψ S T) θ τ J z (heisO ψ S T u g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (GlobalTheory.OrientedHeis.theta_zero : IsThetaFunO ψ S T 0), ?_⟩
    have e := GlobalTheory.AdTh.SourceBasis.aPlus_smul hψ hθ τ J z 0 (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := S) (T := T))
    simpa using e
  | insert a s ha ih =>
    have ht : IsThetaFunO ψ S T (c a • heisO ψ S T a g) :=
      GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hg a)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨GlobalTheory.OrientedHeis.theta_add ht ih.1, ?_⟩
    rw [GlobalTheory.AdTh.SourceBasis.aPlus_add hψ hθ τ J z ht ih.1, ih.2,
      GlobalTheory.AdTh.SourceBasis.aPlus_smul hψ hθ τ J z _ (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hg a)]

theorem sum_heisO_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (c : WO S T →₀ ℂ), (∀ u ∈ c.support, u.map (infPart D) = 0) → ∀ x : WO S T → ℂ, IsThetaFunO ψ S T x → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, (c.sum fun u z => z • heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT x P)) = pureTensorO ψ θ S T sS sT BS BT (c.sum fun u z => z • heisO ψ S T u x) P := by
  intro D ψ θ S T hψ hθ sS BS sT BT c hc x hx P
  let Φ : Module.End ℂ (WO S T → ℂ) := c.sum fun u z => z • GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T u
  have hΦ : ∀ g, Φ g = c.sum fun u z => z • heisO ψ S T u g := by
    intro g
    simp only [Φ, Finsupp.sum]
    rw [LinearMap.sum_apply]
    rfl
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ ha hb => GlobalTheory.OrientedHeis.theta_add ha hb) (fun a _ h => GlobalTheory.OrientedHeis.theta_smul a h)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) Φ
    (fun k g hg => ⟨?_, ?_⟩) x hx P).2
  · rw [hΦ, hΦ] at h
    exact h
  · exact GlobalTheory.AdTh.SourceBasis.aPlus_th hψ hθ _ _ _ hg
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll]
    rw [hΦ, hΦ, Finsupp.sum, Finsupp.sum, (aPlus_sum hψ hθ τ _ _ c hg c.support).2]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [heisO_aPlus ψ hθ (hc u hu)]

end GlobalTheory.FiniteHeisComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupledStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_parameter_coupled : GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), IsRc hL T I rc → ∀ (L : ∀ k, LabelDatum (D.host.g k)) (k : Fin 2) (v : D.nd.PlG k) (κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k)), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen → TameGen.TameParam (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2) := by
  first | exact @GlobalTheory.TameRecord.tameParam_record | exact GlobalTheory.TameRecord.tameParam_record | (intros; apply GlobalTheory.TameRecord.tameParam_record <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishesSingleCoefficientOfKernelKillsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_vanishes_single_coefficient_of_kernel_kills : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), R.thF i t y = 0 → ∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t (R.ioP i x w)) l g = 0 := by
  first | exact @GlobalTheory.GenRealSchur.lift_vanish_single | exact GlobalTheory.GenRealSchur.lift_vanish_single | (intros; apply GlobalTheory.GenRealSchur.lift_vanish_single <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZero
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FieldTransport

section General
variable {G H : Type} [Group G] [Group H]

def compEquiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {τ : Representation ℂ H W} (φ : ρ.Equiv τ) (f : G →* H) :
    Representation.Equiv (ρ.comp f : Representation ℂ G V) (τ.comp f : Representation ℂ G W) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    have := congrArg (fun L => L v) (φ.toIntertwiningMap.isIntertwining' (f g))
    simpa using this

def compCompEquiv {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f : H →* G)
    (g : G →* H) (h : ∀ x, f (g x) = x) : Representation.Equiv ((ρ.comp f).comp g : Representation ℂ G V) ρ :=
  .mk (LinearEquiv.refl ℂ V) fun x => LinearMap.ext fun v => by simp [h]

variable [TopologicalSpace G] [TopologicalSpace H]

def pullRep (f : G →* H) (hf : Continuous f) (hs : Function.Surjective f) (σ : IrrRep H) : IrrRep G :=
  ⟨σ.V, σ.ρ.comp f, fun v => (σ.smooth v).preimage hf,
    GlobalTheory.JacFactor.isIrreducible_comp_surj σ.ρ f hs σ.irr⟩

end General

section GLmap
variable {R S : Type} [CommRing R] [CommRing S]

abbrev mapGL (e : R ≃+* S) (n : ℕ) : GL (Fin n) R →* GL (Fin n) S := GeneralLinearGroup.map e.toRingHom

theorem mapGL_symm_mapGL (e : R ≃+* S) (n : ℕ) (g : GL (Fin n) R) : mapGL e.symm n (mapGL e n g) = g := by
  ext a b; simp [mapGL]

theorem mapGL_mapGL_symm (e : R ≃+* S) (n : ℕ) (g : GL (Fin n) S) : mapGL e n (mapGL e.symm n g) = g := by
  ext a b; simp [mapGL]

theorem mapGL_surjective (e : R ≃+* S) (n : ℕ) : Function.Surjective (mapGL e n) :=
  fun g => ⟨_, mapGL_mapGL_symm e n g⟩

theorem continuous_mapGL [TopologicalSpace R] [TopologicalSpace S] (e : R ≃+* S) (he : Continuous e) (n : ℕ) :
    Continuous (mapGL e n) :=
  Units.continuous_map (continuous_id.matrix_map he)

end GLmap
end GlobalTheory.FieldTransport

namespace GlobalTheory.FieldTransport

section Fields
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

def transportFun (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL k) : IrrGL k' :=
  ⟨x.1, (pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1) (mapGL_surjective i.symm x.1) x.2.rep).cl⟩

theorem transportFun_left (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) (x : IrrGL k) :
    transportFun i.symm (by simpa using hi) (transportFun i hi' x) = x := by
  refine congrArg (Sigma.mk x.1) ((IrrRep.cl_eq_iff.2 ?_).trans x.2.cl_rep)
  obtain ⟨ψ⟩ := IrrRep.nonempty_equiv_rep
    (pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1) (mapGL_surjective i.symm x.1) x.2.rep)
  exact ⟨(compEquiv ψ (mapGL i.symm.symm x.1)).trans
    (compCompEquiv x.2.rep.ρ (mapGL i.symm x.1) (mapGL i.symm.symm x.1) fun g => mapGL_symm_mapGL i x.1 g)⟩

theorem repRel_iff (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL k) (x' : IrrGL k') :
    RepRel i x x' ↔ transportFun i hi' x = x' := by
  constructor
  · rintro ⟨n, π, π', e, rfl, rfl, he⟩
    refine congrArg (Sigma.mk n) (IrrRep.cl_eq_iff.2 ?_)
    obtain ⟨ψ⟩ := IrrRep.nonempty_equiv_rep π
    refine ⟨(compEquiv ψ (mapGL i.symm n)).trans (.mk e fun g => LinearMap.ext fun v => ?_)⟩
    have := he (mapGL i.symm n g) v
    rw [show GeneralLinearGroup.map i.toRingHom (mapGL i.symm n g) = g from mapGL_mapGL_symm i n g] at this
    simpa using this
  · rintro rfl
    refine ⟨x.1, x.2.rep, pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1)
      (mapGL_surjective i.symm x.1) x.2.rep, LinearEquiv.refl ℂ _,
      congrArg (Sigma.mk x.1) x.2.cl_rep.symm, rfl, fun g v => ?_⟩
    show x.2.rep.ρ g v = x.2.rep.ρ (mapGL i.symm x.1 (mapGL i x.1 g)) v
    rw [mapGL_symm_mapGL]

theorem exists_transport (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) :
    ∃ T : IrrGL k ≃ IrrGL k', (∀ x x', RepRel i x x' ↔ T x = x') ∧ ∀ x, (T x).1 = x.1 := by
  have hi2 : Continuous i.symm.symm := by simpa using hi
  refine ⟨⟨transportFun i hi', transportFun i.symm hi2, fun x => transportFun_left i hi hi' x, fun y => ?_⟩,
    repRel_iff i hi', fun x => rfl⟩
  have := transportFun_left i.symm hi' hi2 y
  simpa using this

end Fields
end GlobalTheory.FieldTransport

open GlobalTheory.FieldTransport in

theorem GlobalTheory.transport_irrGL_bijective : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∃ T : IrrGL k ≃ IrrGL k', (∀ x x', RepRel i x x' ↔ T x = x') ∧ ∀ x, (T x).1 = x.1 := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  exact exists_transport i hi (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi).1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffTendsto
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.TypeRec.TwistInert

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

section Val

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem valuation_lt_one_iff_tendsto (x : K) :
    valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  refine ⟨GlobalTheory.LocalTraceSum.tendsto_pow, fun h => ?_⟩
  have hO := GlobalTheory.LocalTraceSum.isOpen_lt (K := K) 1
  obtain ⟨n, hn⟩ := (h.eventually (hO.mem_nhds (by simp))).exists
  by_contra hx
  have h1 : 1 ≤ valuation K x := not_lt.1 hx
  have h2 : 1 ≤ valuation K (x ^ n) := by rw [map_pow]; exact one_le_pow₀ h1
  exact absurd hn (not_lt.2 h2)

theorem valuation_lt_one_map (f : K →+* L) (hf : Continuous f) {x : K} (hx : valuation K x < 1) :
    valuation L (f x) < 1 := by
  rw [valuation_lt_one_iff_tendsto] at hx ⊢
  simpa [Function.comp_def, map_pow] using (hf.tendsto 0).comp hx

theorem valuation_eq_one_of_map (f : K ≃+* L) (hf : Continuous f) {x : K}
    (hx : valuation L (f x) = 1) : valuation K x = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hv : 0 < valuation K x := by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hx0
  rcases lt_trichotomy (valuation K x) 1 with h | h | h
  · exact absurd hx (ne_of_lt (valuation_lt_one_map f.toRingHom hf h))
  · exact h
  · have h1 : valuation K x⁻¹ < 1 := by rw [map_inv₀]; exact (inv_lt_one₀ hv).2 h
    have h2 := valuation_lt_one_map f.toRingHom hf h1
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀, hx, inv_one] at h2
    exact absurd h2 (lt_irrefl 1)

end Val

def twistEquiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (χ : G →* ℂˣ) :
    (twist π χ).Equiv (twist σ χ) :=
  Representation.Equiv.mk φ.toLinearEquiv fun g => LinearMap.ext fun x => by
    have e := LinearMap.congr_fun (φ.isIntertwining' g) x
    simp only [LinearMap.comp_apply] at e
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, twist_apply, map_smul]
    congr 1

def push {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) (μ : ℚ_[D.host.g k]ˣ →* ℂˣ) :
    ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ :=
  μ.comp (Units.map (I.i k v).symm.toRingHom.toMonoidHom)

theorem isUnram_push {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {μ : ℚ_[D.host.g k]ˣ →* ℂˣ}
    (hμ : IsUnram μ) : IsUnram (push I k v μ) := by
  intro y hy
  apply hμ
  apply valuation_eq_one_of_map (I.i k v) (I.cont k v)
  simpa using hy

theorem detChar_push {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (μ : ℚ_[D.host.g k]ˣ →* ℂˣ)
    (g : GL (Fin n) ℚ_[D.host.g k]) :
    detChar (Fin n) (push I k v μ) (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) = detChar (Fin n) μ g := by
  rw [detChar_apply, detChar_apply, push, MonoidHom.comp_apply]
  congr 1
  ext
  have e : ((g : Matrix (Fin n) (Fin n) ℚ_[D.host.g k]).map (I.i k v)).det = I.i k v (g : Matrix (Fin n) (Fin n) ℚ_[D.host.g k]).det :=
    ((I.i k v).toRingHom.map_det _).symm
  simp [e]

def twistPullEquiv {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (σ : IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E))) (μ : ℚ_[D.host.g k]ˣ →* ℂˣ)
    (hμ : IsSmoothChar (push I k v μ)) :
    (twist (pull I k v σ).ρ (detChar (Fin n) μ)).Equiv
      (pull I k v (irrTwist σ (detChar (Fin n) (push I k v μ)) hμ.detChar)).ρ :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => LinearMap.ext fun x => by
    show (detChar (Fin n) μ g : ℂ) • σ.ρ (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) x =
      (detChar (Fin n) (push I k v μ) (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) : ℂ) •
        σ.ρ (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) x
    rw [detChar_push]

theorem inePol_lpTwist {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (y : GlobalTheory.WeilDeligne.WD h) (ξ : GlobalTheory.WeilDeligne.Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ)
    {σ : G E Ω} (hσ : σ ∈ Ine A) (h1 : ξ (GlobalTheory.WeilDeligne.ineIncl h ⟨σ, hσ⟩) = 1) :
    (y.lpTwist ξ hξ).inePol σ = y.inePol σ := by
  rw [GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ]
  obtain ⟨m, b, rfl⟩ := y.exists_rep
  rw [GlobalTheory.WeilDeligne.WD.lpTwist_mk, GlobalTheory.WeilDeligne.WD.charPol_mk, GlobalTheory.WeilDeligne.WD.charPol_mk]
  congr 1
  show ((ξ (GlobalTheory.WeilDeligne.ineIncl h ⟨σ, hσ⟩) : ℂˣ) : ℂ) • b.ρ (GlobalTheory.WeilDeligne.ineIncl h ⟨σ, hσ⟩) = _
  rw [h1, Units.val_one, one_smul]

theorem inePol_inert : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), IsRc hL T I rc → ∀ (k : Fin 2) (v : D.nd.PlG k) (ρ : Supp.GLRep (D.host.g k)) (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible) (x : GlobalTheory.LocGL.IrrGL ℚ_[D.host.g k]), (GlobalTheory.LocGL.IrrGL.of ρ.2.ρ hs hi).Inert x → D.naut.inePol (rc k v ρ.1 ρ.2) (D.ntypes.tg k v) = D.naut.inePol (rc k v x.1 (Rep.of x.rep)) (D.ntypes.tg k v) := by
  intro hL D T I rc hrc k v ρ hs hi x hx
  obtain ⟨μ, hμ, rfl⟩ := hx
  obtain ⟨σ₁, ⟨e₁⟩⟩ := GlobalTheory.TypeRec.Model.exists_pull I k v ρ.2 ⟨(GlobalTheory.GLp.Model.isIrrRep_iff _).2 hi, hs⟩
  have hμ' : IsUnram (push I k v μ) := isUnram_push I k v hμ
  have hμs : IsSmoothChar (push I k v μ) := isSmoothChar_of_isUnram hμ'
  have e₂ : Nonempty (Rep.of ((IrrGL.of ρ.2.ρ hs hi).tw μ (isSmoothChar_of_isUnram hμ)).rep ≅
      pull I k v (irrTwist σ₁ (detChar (Fin ρ.1) (push I k v μ)) hμs.detChar)) :=
    ⟨Rep.mkIso ((IrrGL.twEquiv _ _ _).symm.trans ((twistEquiv (IrrGL.equivOf ρ.2.ρ hs hi).symm _).trans
      ((twistEquiv (Representation.equivOfIso e₁) _).trans (twistPullEquiv I k v σ₁ μ hμs))))⟩
  have h1 := hrc k v _ σ₁ ρ.2 ⟨e₁⟩
  have h2 := hrc k v _ _ _ e₂
  have hc : GlobalTheory.LocLanglands.cls (irrTwist σ₁ (detChar (Fin ρ.1) (push I k v μ)) hμs.detChar) =
      (GlobalTheory.LocLanglands.cls σ₁).tw (push I k v μ) hμs :=
    congrArg (Sigma.mk _) (clTwist_cl _ _ _).symm
  obtain ⟨a, ha, ε, -, H⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
  rw [T.inePol _ _ _ (D.ntypes.tg_mem k v), T.inePol _ _ _ (D.ntypes.tg_mem k v), h1, h2]
  have h3 := congrArg (fun z => (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 (D.naut.plGw k v)) z).inePol (D.ntypes.tg k v)) hc
  have h4 := congrArg (fun z => GlobalTheory.WeilDeligne.WD.inePol z (D.ntypes.tg k v)) (H.tw_eq (GlobalTheory.LocLanglands.cls σ₁) _ hμs)
  refine Eq.trans ?_ (h3.trans h4).symm
  exact (inePol_lpTwist _ _ _ (D.ntypes.tg_mem k v)
    (hμ' _ (ord_eq_zero_iff.1 (by rw [ha.ord_eq]; simp)))).symm

end GlobalTheory.TypeRec.TwistInert
end
end

