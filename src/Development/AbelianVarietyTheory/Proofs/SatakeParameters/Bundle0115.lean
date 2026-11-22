import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0508
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0445
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0126
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0125
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0128
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalRingCardinality.DataKerI
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0005
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.Bundle0002
import Formalism.GaussJetBounds.GaussJetProofs.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InstFintypeHodgeBidegree
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardCosetsEqSubspacesKernelResidueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_cosets_eq_subspaces_kernel_residue : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (m n j : ℕ) (ι : Type) (α : GL (Fin n) K) (R : Finset ι) (ρ : ι → GL (Fin n) K) (z : Matrix (Fin m) (Fin n) O), j ≤ n → Hk O p j α → Reps O α R ρ → Nat.card {γ : ι // γ ∈ R ∧ IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * (ρ γ).1)} = Nat.card {W : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O) // Module.finrank (IsLocalRing.ResidueField O) W + j = n ∧ W ≤ LinearMap.ker (z.map (IsLocalRing.residue O)).mulVecLin} := by
  first | exact @GlobalTheory.SplitHecke.Cosets.card_cosets | exact GlobalTheory.SplitHecke.Cosets.card_cosets | (intros; apply GlobalTheory.SplitHecke.Cosets.card_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.CrysFromGTwo

theorem matRep_twistM {K Γ : Type} [Field K] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) K)
    (χ : Γ →* Kˣ) (g : Γ) (v : Fin k → K) :
    matRep (twistM M χ) g v = ((χ g : Kˣ) : K) • matRep M g v := by
  change (((χ g : Kˣ) : K) • M g).mulVec v = ((χ g : Kˣ) : K) • (M g).mulVec v
  exact Matrix.smul_mulVec _ _ _

theorem crys_loc (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (hG : SumRepresentations.At.G2 D.nd D.naut i r) (h0 : D.nd.l i ≠ D.host.g 0)
    (h1 : D.nd.l i ≠ D.host.g 1) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x))) := by
  have hc := ((hG w hw).1 h0 h1 x).1
  exact ((D.loc_tie i w hw).2.1 D.R.nV (r x) (hr x).1).1.mp hc

theorem crys_coef (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i) (h : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le _ _ h

theorem crys_chi (hF : GlobalTheory.Published.FontaineBcris) (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r π))))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) := by
  have hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π := by
    obtain ⟨e, he⟩ := hD
    exact ⟨e, fun g u => he g u⟩
  exact GlobalTheory.ChiOneEnl.chiOneE_of_isBlockSum hF D i r ρ π hs hc w hw C.LL C.le

theorem twist_mat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K LL : FinExt l)
    {k : ℕ} (M M' : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (χ : ↥(GK K) →* (↥LL.1)ˣ)
    (ht : IsTwistRep χ (matRep M) (matRep M')) (hχ : IsCrys (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ))
    (h : IsCrys (P.PD K) (matRep M)) : IsCrys (P.PD K) (matRep M') :=
  (GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l P AI T K LL _ _ _ _ χ ht hχ h).1

theorem crys_tw (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i) (hχ : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (h : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  have := D.nd.lPrime i
  have ht : IsTwistRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))
      (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
    refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
    rw [locC_rTwO]
    exact matRep_twistM _ _ g v
  exact twist_mat (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL _ _ _ ht hχ h

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → SumRepresentations.At.G2 D.nd D.naut i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) ∧ ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  intro hF D i r ρ π hr hG h0 h1 hD w hw C
  have hχ := crys_chi hF D i r ρ π hD (fun w' hw' => crys_loc D i r hr hG h0 h1 w' hw' π) w hw C
  have hx : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := fun x =>
    crys_coef D i r w hw C x (crys_loc D i r hr hG h0 h1 w hw x)
  exact ⟨hχ, fun x => ⟨hx x, crys_tw D i r w hw C x hχ (hx x)⟩⟩

end GlobalTheory.CrysFromGTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

variable (D : D7)

def rho {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (z : Bool × HH D) : D.host.E →+* ℂ_[p] :=
  (ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D (tauPl D z))

abbrev JJ (n : Bool × HH D → ℕ) (N N' : ℕ) : Type :=
  (Σ z : Bool × HH D, Fin (n z)) × ((Bool × HH D) × Fin N) × ((Bool × HH D) × Fin N')

def rowL {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (σ : Bool × HH D → 𝓞 D.host.E)
    (l : (Bool × HH D) × Fin N) : Fin N → D.host.E :=
  fun j => (σ l.1 : D.host.E) * (P (tauPl D l.1))⁻¹ l.2 j

def colR {N' : ℕ} (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ' : Bool × HH D → 𝓞 D.host.E)
    (r : (Bool × HH D) × Fin N') : Fin N' → D.host.E :=
  fun i => (σ' r.1 : D.host.E) * P' (tauPl D r.1) i r.2

def mat {n : Bool × HH D → ℕ} {N N' : ℕ} (a : ∀ z, Fin (n z) → D.host.E)
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (σ σ' : Bool × HH D → 𝓞 D.host.E) (j : JJ D n N N') : Matrix (Fin N') (Fin N) D.host.E :=
  Matrix.of fun i k => a j.1.1 j.1.2 * colR D P' σ' j.2.2 i * rowL D P σ j.2.1 k

def vecF {X : Fields} (s : Seam D X) {N N' : ℕ} (M : Matrix (Fin N') (Fin N) D.host.E) : DVar X.Tau N N' → ℂ :=
  fun k => TaylorLogMetric.embT D (s.iT k.1) (M k.2.1 k.2.2)

def act {X : Fields} (s : Seam D X) (N N' : ℕ) (e : 𝓞 D.host.E) : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] (DVar X.Tau N N' → ℂ) where
  toFun x := fun k => TaylorLogMetric.embT D (s.iT k.1) (e : D.host.E) * x k
  map_add' x y := by funext k; simp [mul_add]
  map_smul' c x := by funext k; simp; ring

def gc {p : ℕ} [Fact p.Prime] {n : Bool × HH D → ℕ} (cκ : Bool × HH D → ℂ_[p]) (r : ∀ z, Fin (n z) → ℂ_[p])
    (z : Bool × HH D) (α : Σ z : Bool × HH D, Fin (n z)) : ℂ_[p] :=
  if α.1 = z then cκ z * r α.1 α.2 else 0

def pc {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N : ℕ} (σ : Bool × HH D → 𝓞 D.host.E) (z : Bool × HH D)
    (l : (Bool × HH D) × Fin N) (a : Fin N) : ℂ_[p] :=
  if l = (z, a) then (rho D ι z (σ z : D.host.E))⁻¹ else 0

def coef {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n : Bool × HH D → ℕ} {N N' : ℕ} (cκ : Bool × HH D → ℂ_[p])
    (r : ∀ z, Fin (n z) → ℂ_[p]) (σ σ' : Bool × HH D → 𝓞 D.host.E) (j : JJ D n N N')
    (x : (Bool × HH D) × Fin N × Fin N') : ℂ_[p] :=
  gc D cκ r x.1 j.1 * pc D ι σ x.1 j.2.1 x.2.1 * pc D ι σ' x.1 j.2.2 x.2.2

def uu {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n : Bool × HH D → ℕ} (cκ : Bool × HH D → ℂ_[p])
    (r : ∀ z, Fin (n z) → ℂ_[p]) (a : ∀ z, Fin (n z) → D.host.E) (t : HH D) : ℂ_[p] :=
  ∑ α, ∑ α', gc D cκ r (false, t) α * rho D ι (false, t) (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) *
    gc D cκ r (true, t) α'

end GlobalTheory.DFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatUnramifiedOverRealOfCmSubfield
section
open NumberField IsDedekindDomain

theorem GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 K)), (N : 𝓞 K) ∉ w.asIdeal → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) w.asIdeal := by
  intro E _ _ _
  obtain ⟨d, s, hs, hsn, -⟩ := GlobalTheory.CMGen.exists_sqrt_totallyNegative E
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hsn
    have : s = 0 := by simpa using hs
    rw [this]
    exact zero_mem _
  have h2d : (2 * d : 𝓞 (maximalRealSubfield E)) ≠ 0 := mul_ne_zero two_ne_zero hd0
  refine ⟨Ideal.absNorm (Ideal.span {2 * d}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h2d
  intro K _ _ _ _ w hw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {2 * d}))
  haveI : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  have hint : ∀ x : 𝓞 (maximalRealSubfield E),
      IsIntegral ℤ (algebraMap E K ((x : maximalRealSubfield E) : E)) := fun x =>
    (RingOfIntegers.isIntegral_coe x).map
      ((algebraMap E K).comp (maximalRealSubfield E).subtype).toIntAlgHom
  have hmem : algebraMap E K ((d : maximalRealSubfield E) : E) ∈ maximalRealSubfield K :=
    (GlobalTheory.algebraMap_mem_maximalRealSubfield_iff _).2 (d : maximalRealSubfield E).2
  have hai : IsIntegral ℤ (⟨_, hmem⟩ : maximalRealSubfield K) :=
    (isIntegral_algHom_iff (maximalRealSubfield K).subtype.toIntAlgHom Subtype.val_injective).1 (hint d)
  let a : 𝓞 (maximalRealSubfield K) := ⟨_, hai⟩
  refine GlobalTheory.unramified_adjoin_sqrt_of_not_mem K a (algebraMap E K s) ?_ ?_ w ?_
  · rw [← map_pow, hs]; rfl
  · exact fun h => hsn ((GlobalTheory.algebraMap_mem_maximalRealSubfield_iff _).1 h)
  · intro h
    apply hw
    have h1 : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) (2 * a) ∈ w.asIdeal := h
    let c' : 𝓞 K := ⟨_, hint c⟩
    have h2 : ((Ideal.absNorm (Ideal.span {2 * d}) : ℕ) : 𝓞 K)
        = c' * algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) (2 * a) := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      let f : 𝓞 (maximalRealSubfield E) →+* K :=
        ((algebraMap E K).comp (maximalRealSubfield E).subtype).comp (algebraMap _ _)
      have h3 := congrArg f hc
      rw [map_natCast, map_mul, map_mul, map_ofNat] at h3
      rw [map_natCast, ← h3, map_mul, map_mul, map_mul, map_ofNat, map_ofNat]
      rfl
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfInertPrimeEllipticCurveLocalDataStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_of_inertPrimeEllipticCurveLocalData : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (d : ℕ) [NeZero d], Even d → ∃ (om oms : Fin (d / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p d σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ := by
  first | exact @GlobalTheory.KerStd.BeData.exists_of_curveData | exact GlobalTheory.KerStd.BeData.exists_of_curveData | (intros; apply GlobalTheory.KerStd.BeData.exists_of_curveData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_chart_of_splitIdempotent : ∀ {D : D7} (e : AE D), IsSplitIdem D e → ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), Chart e v π := by
  first | exact @GlobalTheory.SplitChart.exists_chart | exact GlobalTheory.SplitChart.exists_chart | (intros; apply GlobalTheory.SplitChart.exists_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRationalFrame
section
noncomputable section

namespace GlobalTheory.UnUnitCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

section Units

variable {l : ℕ} [Fact l.Prime] {lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l]}

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem exists_place {K : Type} [Field K] [NumberField K] (ψ : K →+* ℂ_[l]) :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal ∧ ∀ x : K, v.valuation K x ≤ 1 → ‖ψ x‖ ≤ 1 := by
  have hint : ∀ a : 𝓞 K, ‖ψ (a : K)‖ ≤ 1 := fun a => norm_le_one_of_isIntegral (map_isIntegral_int ψ a.isIntegral_coe)
  let P : Ideal (𝓞 K) :=
    { carrier := {a | ‖ψ (a : K)‖ < 1}
      add_mem' := fun {a b} ha hb => by
        have e : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by simp
        simp only [Set.mem_ofPred_eq, e, map_add] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        have e : ((c * a : 𝓞 K) : K) = (c : K) * (a : K) := by simp
        simp only [Set.mem_ofPred_eq, smul_eq_mul, e, map_mul, norm_mul] at *
        exact (mul_le_of_le_one_left (norm_nonneg _) (hint c)).trans_lt ha }
  have hP : ∀ a : 𝓞 K, a ∈ P ↔ ‖ψ (a : K)‖ < 1 := fun _ => Iff.rfl
  have hl : ((l : ℕ) : 𝓞 K) ∈ P := by
    rw [hP]
    have : (((l : ℕ) : 𝓞 K) : K) = (l : K) := by simp
    rw [this, map_natCast]
    have h2 : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
    rw [h2, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hpr : P.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} h => ?_⟩
    · have : (1 : 𝓞 K) ∈ P := h ▸ Submodule.mem_top
      rw [hP] at this
      simp at this
    · rw [hP, hP]
      rw [hP] at h
      by_contra hn
      push Not at hn
      have e : ((a * b : 𝓞 K) : K) = (a : K) * (b : K) := by simp
      rw [e, map_mul, norm_mul] at h
      exact absurd (one_le_mul_of_one_le_of_one_le hn.1 hn.2) (not_le.2 h)
  have hne : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hl
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hl)
  refine ⟨⟨P, hpr, hne⟩, hl, fun x hx => ?_⟩
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := ⟨P, hpr, hne⟩) x hx
  have hd : ‖ψ ((d : 𝓞 K) : K)‖ = 1 := le_antisymm (hint _) (not_lt.1 d.2)
  have h2 := congrArg (fun t => ‖ψ t‖) hnd
  simp only [map_mul, norm_mul] at h2
  have h3 : ‖ψ x‖ * ‖ψ ((d : 𝓞 K) : K)‖ = ‖ψ (n : K)‖ := h2
  rw [hd, mul_one] at h3
  rw [h3]; exact hint n

theorem emb_mem {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (x : K) : φ x ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (φ : H.E →+* ℂ) {N : ℕ} (g : GL (Fin N) (Ad H))

end Units

section Rescale

theorem applyAt0_smul {Lt : Type} (N0 N1 l : ℕ) [Fact l.Prime] (a : ℂ_[l])
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (KM.XZ Lt N0 N1) ℤ) :
    KM.applyAt0 N0 N1 l (a • Th) P = a • KM.applyAt0 N0 N1 l Th P := by
  unfold KM.applyAt0
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.smul_monomial, map_smul, smul_eq_mul, smul_eq_mul]
  congr 1
  ring

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

def rescale (E : KerEnt D Dx Tw)
    (t : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) → ℂ_[D.what₂.places.resChar w])
    (ht : ∀ u μ w i c c', t u μ w i c c' ≠ 0) : KerEnt D Dx Tw :=
  { E with
    Th := fun u μ w i c c' => (E.un u μ w i c c' / t u μ w i c c') • E.Th u μ w i c c'
    un := t
    un_ne := ht
    kform := fun u μ w hw i hi c c' v v' h I => by
      rw [E.kform u μ w hw i hi c c' v v' h I, applyAt0_smul, map_smul, smul_eq_mul, ← mul_assoc,
        mul_div_cancel₀ _ (ht u μ w i c c')] }

end Rescale

section Ties

variable {D : D7} {Dx : DivX D} {Tw : TwForms D} {C : CharFrame D} {nch : NChoice D}

def RamTie (Dx : DivX D) (Tp : TupTied D C nch) : Prop :=
  ∀ μ (l : ℕ), l.Prime → (l ∉ Dx.Qp μ ↔ ∀ v, OverP D.host l v → (Tp.xi μ).UnrAt v)

def FrameOf {u : D.what₂.Word} {μ : D.what₂.Tup} (g : Reps D u μ) (fr : Frames D u μ) {l : ℕ} [Fact l.Prime]
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l]) {i : ℕ} (c : (D.chTw u μ).cls i) (y : (D.chTw u μ).Y i) : Prop :=
  ∀ τ, IsLatFrame lam D.host (embTau D τ) (g i c) (fr i y τ)

def UnTie (E : KerEnt D Dx Tw) (g : ∀ u μ, Reps D u μ) (fr : ∀ u μ, Frames D u μ) : Prop :=
  ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    ∃ y y', FrameOf (g u μ) (fr u μ) (E.lam w) c y ∧ FrameOf (g u μ) (fr u μ) (E.lam w) c' y' ∧
      E.un u μ w i c c' = lamV (E.lam w) (epsFr D u μ i c c' y y')

def EpsPowIn (D : D7) : Prop :=
  ∀ u μ i, i < D.R.m → ∀ c c', ∃ n : ℕ, 0 < n ∧ eps D u μ i c c' ^ n ∈ Set.range D.what₂.embLL

def UnitAtLam (Tp : TupTied D C nch) (lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (u : D.what₂.Word) (μ : D.what₂.Tup) (g : Reps D u μ) (fr : Frames D u μ) : Prop :=
  ∀ w : D.what₂.places.Pl, PrimeToLevels D Tp u μ (D.what₂.places.resChar w) →
    ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1))
      (y : (D.chTw u μ).Y i) (y' : (D.chTw u μ).Y (i + 1)),
      FrameOf g fr (lam w) c y → FrameOf g fr (lam w) c' y' → UnitAt (lam w) (epsFr D u μ i c c' y y')

variable (E : KerEnt D Dx Tw) (Tp : TupTied D C nch) (g : ∀ u μ, Reps D u μ) (fr : ∀ u μ, Frames D u μ)

end Ties

end GlobalTheory.UnUnitCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitFrame_selfDualLattice_completion : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ V : HSp D, ∃ β : GL (Fin V.rank) (Fv D.host.F v), Frame V e π β := by
  first | exact @GlobalTheory.SplitFrame.exists_frame | exact GlobalTheory.SplitFrame.exists_frame | (intros; apply GlobalTheory.SplitFrame.exists_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpFactorAllOrbitsEqProdOrbits
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)

namespace GlobalTheory.ExpFacOrbits

theorem expFactor_allOrbits : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (OrbitPlaces.Pl D)) {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (mvExp ((-1 : ℂ_[p]) • Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be)) =
      product_zeroth_first_parts.expS ℂ_[p] (OrbitPlaces.beAll D p (N0 := N) (N1 := N') R (fun _ => -1) (fun _ => be)) := by
  intro D p _ R M N N' eA be hbe
  classical
  set a : ZV (nP D p) M N' → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] := fun y =>
    X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) with ha_def
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (fun y => constantCoeff_X _)
  have hlin : ∀ ab : Fin M × Fin N', (fun s : ZMod (nP D p) =>
      Formalism.DworkPowerSeriesWeights.linSub (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) (s, ab.1, ab.2)) =
      fun s => (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p]) := fun ab =>
    funext fun s => Formalism.DworkPowerSeriesWeights.OrbMul.linSub_idM (s, ab.1, ab.2)
  have hX : ∀ ab : Fin M × Fin N', HasSubst (fun s : ZMod (nP D p) =>
      (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) := fun ab =>
    hasSubst_of_constantCoeff_zero (fun s => constantCoeff_X _)
  have hB : Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be =
      ∑ ab : Fin M × Fin N', subst (fun s : ZMod (nP D p) =>
        (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) be := by
    unfold Formalism.DworkPowerSeriesWeights.bSum
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [hlin ab]
  have hcc : constantCoeff ((-1 : ℂ_[p]) •
      Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be) = 0 := by
    rw [hB, Finset.smul_sum, map_sum]
    refine Finset.sum_eq_zero fun ab _ => ?_
    rw [MvPowerSeries.constantCoeff_smul, constantCoeff_subst_eq_zero (hX ab) (fun s => constantCoeff_X _) hbe,
      smul_zero]
  rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' ha hcc]
  show mvExp _ = mvExp _
  congr 1
  rw [hB, ← coe_substAlgHom ha, map_smul, map_sum, coe_substAlgHom ha]
  have hterm : ∀ ab : Fin M × Fin N', subst a (subst (fun s : ZMod (nP D p) =>
        (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) be) =
      subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p (eA ab.1).1 s, (eA ab.1).2, ab.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be := by
    intro ab
    rw [subst_comp_subst_apply (hX ab) ha]
    congr 1
    funext s
    rw [subst_X ha]
  simp_rw [hterm]
  unfold OrbitPlaces.beAll
  simp only [← Finset.smul_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  rw [Equiv.sum_comp eA (fun x : R × Fin N => ∑ b : Fin N', subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p x.1 s, x.2, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be)]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_coe_sort R (fun r => ∑ a : Fin N, ∑ b : Fin N', subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p r s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be)

end GlobalTheory.ExpFacOrbits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentShapeOfIntegralClassOneLetterStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentShape_of_integralClass_oneLetter : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → nP D p = 1 → ∀ (N N' : ℕ) (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), ‖ep‖ = 1 → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) → OrbitPlaces.ThetaExpansionRealPlaces D p Th := by
  first | exact @GlobalTheory.KerStd.expShape_of_integralClass | exact GlobalTheory.KerStd.expShape_of_integralClass | (intros; apply GlobalTheory.KerStd.expShape_of_integralClass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFiniteQCOmega
section
open CategoryTheory AlgebraicGeometry Module ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeFin

open GlobalTheory.CechDR GlobalTheory.QCoh

variable {k : Type} [Field k] {X : Scheme.{0}} (s : X ⟶ Sp k)

theorem finiteType_sec [LocallyOfFiniteType s] {U : X.Opens} (hU : IsAffineOpen U) :
    Algebra.FiniteType k (Sec s U) := by
  have h1 := LocallyOfFiniteType.finiteType_of_affine_subset s (isAffineOpen_top (Sp k)) hU
    (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

end GlobalTheory.HodgeFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowCoefficientsOfParameterCoefficientsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowCoefficients_of_parameterCoefficients : ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] (Un : (ι →₀ ℕ) → MvPowerSeries ι (K0 p)), (∀ n, inParam p (Un n) = MvPowerSeries.monomial n 1 ∧ (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m (Un n) = 0)) → ∀ (U : MvPowerSeries ι K1) (d : ℕ) (S : Finset (ι →₀ ℕ)), (∀ n : ι →₀ ℕ, n.degree ≤ d → n ∈ S) → ∀ m : ι →₀ ℕ, m.degree ≤ d → MvPowerSeries.coeff m U = ∑ n ∈ S, MvPowerSeries.coeff n (inParamK p K1 U) * algebraMap (K0 p) K1 (MvPowerSeries.coeff m (Un n)) := by
  first | exact @GlobalTheory.TwU.low_coeff_of_param | exact GlobalTheory.TwU.low_coeff_of_param | (intros; apply GlobalTheory.TwU.low_coeff_of_param <;> assumption)
end

