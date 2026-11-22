import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0511
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0512
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0518
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfMutualSpanOfIndepStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_of_mutual_span_of_indep : ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)), (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b f : ι → W), (∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) → (∀ i, ∃ d : ι → R, f i = ∑ k, act (d k) (b k)) → (∀ k, ∃ d : ι → R, b k = ∑ i, act (d i) (f i)) → ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  first | exact @GlobalTheory.linIndep_of_mutual_span_of_indep | exact GlobalTheory.linIndep_of_mutual_span_of_indep | (intros; apply GlobalTheory.linIndep_of_mutual_span_of_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesConditionTwoThreeStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallPrimeLengthBound_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.SmallPrimeLengthBound L tf C → TwistedPlaces.SmallPrimeLengthBound L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree | exact GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree | (intros; apply GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRamifiedTypePrimesStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedPrimeLengthBound_and_generatorPrimeEtaBound_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.RamifiedPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.GeneratorPrimeEtaBound L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes | exact GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes | (intros; apply GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRowsAndBandStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admA_admB_inert_band_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.admA L (tab L X tf C) C ∧ TwistedPlaces.admB L (tab L X tf C) C ∧ TwistedPlaces.MediumInertPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tab L X tf C) C ∧ TwistedPlaces.BandPlaceWeightApproximation L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand | exact GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand | (intros; apply GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionFiveStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundTableAllPrimes_sizeConditionFive : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.adm5 L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLink.adm5_tab | exact GlobalTheory.NLink.adm5_tab | (intros; apply GlobalTheory.NLink.adm5_tab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionSixStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundTableAllPrimes_sizeConditionSix : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.adm6 L (tab L X tf C) := by
  first | exact @GlobalTheory.NLink.adm6_tab | exact GlobalTheory.NLink.adm6_tab | (intros; apply GlobalTheory.NLink.adm6_tab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesVanishingExcludedStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundTableAllPrimes_vanishing_excluded : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.LargePrimeLengthVanishing L (tab L X tf C) ∧ TwistedPlaces.ExceptionalPrimesBounded L (tab L X tf C) := by
  first | exact @GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab | exact GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab | (intros; apply GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableFromDataBandConditionStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundTableFromData_bandCondition : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → TwistedPlaces.BandPlaceWeightApproximation L (tabX L X) C := by
  first | exact @GlobalTheory.NBand.bandPlaceWeightApproximation_tabX | exact GlobalTheory.NBand.bandPlaceWeightApproximation_tabX | (intros; apply GlobalTheory.NBand.bandPlaceWeightApproximation_tabX <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableRowsCDAdmissible
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowCDSize

open Classical

theorem ratIn_le {x y c : ℝ} (hy : y ≤ c) (hc : 0 ≤ c) : ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) ≤ c := by
  by_cases h : x < y
  · exact (RowBSize.ratIn_lt h).le.trans hy
  · rw [RowBSize.ratIn_of_not_lt h]; simpa using hc

theorem one_le_hB {D : D7} (L : SizeData₂ D) : 1 ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.hB
  have := RowBSize.one_le_b' L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem etaP_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ TwistedPlaces.eta₃ L := by
  unfold TwistedPlaces.eta₃
  have := L.etaSz_pos
  positivity

theorem placeWeight_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ TwistedPlaces.wP L := by
  have hb : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := RowBSize.x_pos' L
    have := RowBSize.one_le_b' L
    positivity
  have h1 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    have := RowBSize.x_pos' L
    positivity
  unfold TwistedPlaces.wP TwistedPlaces.wB
  have h2 := L.etaSz_pos
  have h4 : L.sc.w'' D.R.n + L.etaSz ≤ max (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz) := le_max_left _ _
  have h5 : (0:ℝ) ≤ D.R.t := by positivity
  linarith

theorem coreE_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) : 0 ≤ coreE L l := by
  unfold coreE
  have h1 : 0 ≤ TwistedPlaces.hB L / l := div_nonneg (by linarith [one_le_hB L]) (by positivity)
  have h2 : 0 ≤ Real.logb l (TwistedPlaces.hB L) := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg (one_le_hB L)) (Real.log_natCast_nonneg l)
  linarith

theorem flat_nonneg {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) : 0 ≤ flat L bd l := by
  unfold flat
  have := placeWeight_nonneg L
  have := etaP_nonneg L
  have := L.Sc_pos
  have := RowBSize.one_le_Lg L
  have h1 : 0 ≤ (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / l := by positivity
  have h2 : 0 ≤ TwistedPlaces.eta₃ L * (if bd then (1:ℝ) else 0) := by split_ifs <;> simp [*]
  linarith

theorem coreH_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreH L l lam := by
  unfold coreH
  have := RowBSize.hB_nonneg L
  positivity

theorem coreF_nonneg {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreF L bd l lam := by
  unfold coreF
  have := flat_nonneg L bd l
  positivity

theorem coreM_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreM L l lam := by
  unfold coreM
  have := coreE_nonneg L l
  positivity

theorem len_le {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ)
    (hD : KillingConditions.DataAD L HW X R) (hR : R.Le C) (i : D.nd.Loc) (hI : TwistedPlaces.InertK D (D.nd.l i))
    (hB : ¬ KillingConditions.IsRowB L (D.nd.l i)) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    (tabX L X).len i lam ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam +
      C * C * coreM L (D.nd.l i) lam := by
  obtain ⟨-, -, -, -, hC1, -, h1, h2, h3, -⟩ := hR
  have hH := coreH_nonneg L (D.nd.l i) lam
  have hF := coreF_nonneg L (X.band i lam) (D.nd.l i) lam
  have hM := coreM_nonneg L (D.nd.l i) lam
  have hC0 : (0:ℝ) ≤ C := by linarith
  have h0 : 0 ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam +
      C * C * coreM L (D.nd.l i) lam := by positivity
  have key : (tabX L X).len i lam = KillingConditions.supZ i
      (fun _ => ((lenRowCD L (X.band i) R.K₁ R.K₂ R.K₃ (D.nd.l i) lam : ℚ) : ℝ)) := by
    show KillingConditions.lenR X.len0 i lam = _
    unfold KillingConditions.lenR
    congr 1
    funext π
    rw [hD.len0I i hI π lam, hD.rowCD i hI hB]
  rw [key]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    unfold lenRowCD
    refine ratIn_le ?_ h0
    unfold bdCD
    have h4 : R.K₃ ≤ C * C := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hH
    have := mul_le_mul_of_nonneg_right h2 hF
    have := mul_le_mul_of_nonneg_right h4 hM
    linarith
  · exact h0

end GlobalTheory.NLink.RowCDSize

theorem GlobalTheory.NLink.localBoundTable_rowsCD_admissible : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.MediumInertPrimeLengthBound L (tabX L X) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tabX L X) C := by
  intro D L P HW X R C hD hR
  have hfl : ∀ i lam l, TwistedPlaces.flatCD L (tabX L X) i lam l = flat L (X.band i lam) l := fun _ _ _ => rfl
  have he : ∀ l, TwistedPlaces.eP L C l = C * coreE L l := fun _ => rfl
  constructor
  · rintro i - ⟨hI, hA, -, -⟩ lam -
    have h := GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.1 (not_lt.2 hA)) lam
    rw [hfl, he]
    refine h.trans (le_of_eq ?_)
    unfold coreH coreF coreM
    ring
  · rintro i - ⟨hI, -, hO, -⟩ lam -
    have h := GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.2 (not_lt.2 hO)) lam
    rw [hfl, he]
    refine h.trans (le_of_eq ?_)
    unfold coreH coreF coreM
    ring

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalIntegerSpanOfImageIsStableLattice
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def vecLS (a : ℕ) :
    (Fin a → Fin D.R.nV → KK D.nd i) →ₛₗ[(D.nbr i w hw).eO.toRingHom]
      (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) where
  toFun := vecL i w hw
  map_add' u v := by
    funext b j
    simp [vecL]
  map_smul' c v := by
    funext b j
    simp only [vecL, Pi.smul_apply, Algebra.smul_def, map_mul, Br.toLLK_alg]
    rfl

theorem eO_surj : RingHomSurjective (D.nbr i w hw).eO.toRingHom :=
  ⟨(D.nbr i w hw).eO.surjective⟩

theorem latY_map {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    (latY i w hw Y).map ((spanL i w hw Y).subtype.restrictScalars (Br.OLL D.nbr i w hw)) =
      Submodule.span (Br.OLL D.nbr i w hw) (vecL i w hw '' (Y : Set _)) := by
  rw [latY, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨vecL i w hw y, Submodule.subset_span ⟨y, hy, rfl⟩⟩, ⟨y, hy, rfl⟩, rfl⟩

theorem latY_fg {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (hY : Y.FG) :
    (latY i w hw Y).FG := by
  have hinj : Function.Injective ((spanL i w hw Y).subtype.restrictScalars (Br.OLL D.nbr i w hw)) :=
    Subtype.val_injective
  apply Submodule.fg_of_fg_map_injective _ hinj
  rw [latY_map]
  haveI := eO_surj i w hw
  obtain ⟨S, rfl⟩ := hY
  have h : ∀ T : Set (Fin a → Fin D.R.nV → KK D.nd i), vecL i w hw '' T = (vecLS i w hw a) '' T :=
    fun _ => rfl
  rw [h, ← Submodule.map_coe, Submodule.span_eq, Submodule.map_span]
  classical
  exact ⟨(S.image (vecLS i w hw a)), by rw [Finset.coe_image]⟩

theorem span_stable_of_gen {R K M : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup M] [Module K M]
    [Module R M] (hT : IsScalarTower R K M) (f : M →ₗ[K] M) (s : Set M) (h : ∀ v ∈ s, f v ∈ s) :
    ∀ v ∈ Submodule.span R s, f v ∈ Submodule.span R s := by
  intro v hv
  haveI := hT
  have key : Submodule.span R s ≤ (Submodule.span R s).comap (f.restrictScalars R) :=
    Submodule.span_le.2 fun u hu => Submodule.subset_span (h u hu)
  exact key hv

theorem latY_stable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) :
    ∀ g, ∀ u ∈ latY i w hw Y,
      subRho (sumG i w hw r Xs hr x) (spanL i w hw Y) (spanL_stable i w hw r Xs hr x Y hst) g u ∈ latY i w hw Y := by
  intro g
  apply span_stable_of_gen (K := Br.LL D.nbr i w hw)
  · exact ⟨fun c k u => Subtype.ext (smul_assoc c k (u.1 : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw))⟩
  rintro v ⟨y, hy, hv⟩
  refine ⟨actK i r Xs x (gl i w hw g) y, hst _ y hy, ?_⟩
  show _ = (sumG i w hw r Xs hr x).ρ g (v : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw)
  rw [← hv, sumG_vecL]

theorem latY_span {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule.span (Br.LL D.nbr i w hw) ((latY i w hw Y : Set ↥(spanL i w hw Y))) = ⊤ := by
  apply Submodule.map_injective_of_injective (spanL i w hw Y).injective_subtype
  rw [Submodule.map_span, Submodule.map_subtype_top]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    apply Submodule.subset_span
    exact ⟨⟨vecL i w hw y, Submodule.subset_span ⟨y, hy, rfl⟩⟩,
      Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩

theorem latY_free {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (hY : Y.FG) :
    Module.Free (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) := by
  haveI : Module.Finite (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) :=
    Module.Finite.iff_fg.2 (latY_fg i w hw Y hY)
  haveI : NoZeroSMulDivisors (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) := by
    constructor
    intro c u h
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    have h1 : ((c • u : ↥(latY i w hw Y)) : ↥(spanL i w hw Y)) = 0 := by rw [h]; rfl
    have h2 : ((algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) c) • (u : ↥(spanL i w hw Y))) = 0 := by
      rw [algebraMap_smul]; exact h1
    have hc' : algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) c ≠ 0 := by
      intro h0; apply hc; exact Subtype.val_injective h0
    have := (smul_eq_zero.1 h2).resolve_left hc'
    exact Subtype.ext this
  exact Module.free_of_finite_type_torsion_free'

theorem latY_lattice : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y), Y.FG →
    ∃ LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ, LY.T = latY i w hw Y := by
  intro D i w hw r Xs hr a x Y hst hY
  exact ⟨{ T := latY i w hw Y
           stable := latY_stable i w hw r Xs hr x Y hst
           fg := latY_fg i w hw Y hY
           free := latY_free i w hw Y hY
           span := latY_span i w hw Y }, rfl⟩

end GlobalTheory.Pass.LocDual.OneX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTwistDual
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistRead

theorem matRep_apply {F Γ : Type} [CommRing F] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) F)
    (g : Γ) (v : Fin k → F) : matRep M g v = (M g).mulVec v := by
  simp [matRep, Matrix.toLinAlgEquiv'_apply]

theorem local_twist_dual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K LL : FinExt l) (hs : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1) {n : ℕ}
    (R T U : ↥(GK K) →* Matrix (Fin n) (Fin n) ↥LL.1)
    (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1)
    (hν : ∀ g x, ν g x = χ g • x) (hR : ∀ g, R g = χ g • T g)
    (hU : ∀ g, U g = ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (T g⁻¹).transpose)
    (dR : IsDR (P.PD K) (matRep R)) (dν : IsDR (P.PD K) ν)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ) (hc : ∀ a : ℤ, multV (P.PD K) ν τ a = if a = c then 1 else 0) :
    IsDR (P.PD K) (matRep T) ∧ IsDR (P.PD K) (matRep U) ∧
      ∀ a : ℤ, multV (P.PD K) (matRep T) τ a = multV (P.PD K) (matRep R) τ (a + c) ∧
        multV (P.PD K) (matRep U) τ a = multV (P.PD K) (matRep R) τ (c - a - 1) := by
  have hRT : ∀ g x, matRep R g x = χ g • matRep T g x := by
    intro g x
    rw [matRep_apply, matRep_apply, hR, Matrix.smul_mulVec]
  have dT : IsDR (P.PD K) (matRep T) :=
    (GlobalTheory.TwistDR.isDR_twist_iff l P AI hT K LL _ (matRep T) (matRep R) ν χ hν hRT dν).2 dR
  have jT : ∀ a : ℤ, multV (P.PD K) (matRep R) τ (a + c) = multV (P.PD K) (matRep T) τ a :=
    GlobalTheory.TwistJump.multV_twist_char l P AI hT K LL _ (matRep T) (matRep R) ν χ hν hRT dν τ c hc
  have hb : Function.Bijective (dotProductBilin ↥LL.1 ↥LL.1 :
      (Fin n → ↥LL.1) →ₗ[↥LL.1] (Fin n → ↥LL.1) →ₗ[↥LL.1] ↥LL.1) :=
    (dotProductEquiv ↥LL.1 (Fin n)).bijective
  have hd := GlobalTheory.T.galois_representation_hom_finite_dimensional l P AI hT K LL _ (matRep T) _ (matRep U) _ 1 hb (by
    intro g x y
    rw [matRep_apply, matRep_apply, hU, zpow_one]
    simp only [dotProductBilin_apply_apply, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]) dT
  refine ⟨dT, hd.1, fun a => ⟨(jT a).symm, ?_⟩⟩
  have h1 := hd.2 τ (-a - 1) hs
  have h2 := jT (-a - 1)
  rw [show -(-a - 1) - 1 = a by ring] at h1
  rw [show -a - 1 + c = c - a - 1 by ring] at h2
  rw [h1, h2]

set_option maxHeartbeats 1000000 in

theorem twist_dual_mult : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) → ∀ (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (τ : D.host.E →+* Qbar (D.nd.l i)), (∀ x : D.host.E, τ x = ((τ' (Br.cEw D.nbr i w hw x) : ↥LL'.1) : Om (D.nd.l i))) → ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (χ : GE D.nd →* GL (Fin 1) (D.nd.O i)) (c : ℤ), Continuous (fun g => rO D.nd i r x g) → (∀ g, (χ g : Matrix (Fin 1) (Fin 1) (D.nd.O i)) 0 0 = ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i)) → D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w → D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) χ) w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) χ) τ = {c} → IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) ∧ IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' a = (((D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ).count (a + c) : ℕ) : ℤ) ∧ multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))) τ' a = (((D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ).count (c - a - 1) : ℕ) : ℤ) := by
  intro D i w hw hT LL' h τ' τ hτ r x χ c hr hχ dr dχ hc
  have tie := D.loc_tie i w hw
  set f : D.nd.O i →+* ↥LL'.1 :=
    (IntermediateField.inclusion h).toRingHom.comp (D.nbr i w hw).toLL with hf
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (continuous_subtype_val.comp (D.nbr i w hw).eO_cont)
  have hmap : ∀ (m : ℕ) (ρ : GE D.nd →* GL (Fin m) (D.nd.O i)),
      mapRep (algebraMap ↥LL'.1 (Qbar (D.nd.l i))) (mapRep f ρ) = mapRep (iotaOQ D.nd D.naut i) ρ := by
    intro m ρ
    ext g a b
    exact (tie.1 _).symm
  have cr : Continuous (fun g => ((mapRep f (r x) g : GL (Fin D.R.nV) ↥LL'.1) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) ↥LL'.1)) := hr.matrix_map hfc
  have cχ : Continuous (fun g => ((mapRep f χ g : GL (Fin 1) ↥LL'.1) : Matrix (Fin 1) (Fin 1) ↥LL'.1)) := by
    refine Continuous.matrix_map (A := fun g => (χ g : Matrix (Fin 1) (Fin 1) (D.nd.O i))) ?_ hfc
    refine continuous_matrix fun a b => ?_
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    simp only [hχ]
    exact D.nd.chi_cont i 1
  have tr := tie.2.2 LL' h _ _ cr
  have tχ := tie.2.2 LL' h _ _ cχ
  rw [hmap] at tr tχ
  have dr' := tr.2.1.1 dr
  have dχ' := tχ.2.1.1 dχ
  have jr := (tr.2.2.2 τ τ' hτ).2 dr'
  have jχ := (tχ.2.2.2 τ τ' hτ).2 dχ'
  have hs : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
    haveI : FiniteDimensional ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := (D.nbr i w hw).Kw.2
    have := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw LL'
      (fun σ y => h ((D.nbr i w hw).LL_split σ y)) inferInstance).2
    rw [Nat.card_eq_fintype_card]
    exact this
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  have hrep : matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rO D.nd i r x))) =
      (D.nbr i w hw).repE LL' ((mapRep f (r x)).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [matRep_apply]
    rfl
  have key := local_twist_dual (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) hT (D.nbr i w hw).Kw LL' hs
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rO D.nd i r x)))
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))
    ((D.nbr i w hw).repE LL' ((mapRep f χ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype))
    (fun g => f (D.nd.chi i 1 (ι g) : (D.nd.O i)ˣ))
    (by
      intro g v
      funext a
      change Matrix.mulVec ((χ (ι g) : Matrix (Fin 1) (Fin 1) (D.nd.O i)).map f) v a = _
      rw [Subsingleton.elim a 0]
      simp [Matrix.mulVec, dotProduct, hχ])
    (by
      intro g
      ext a b
      congr 1
      change f (rO D.nd i r x (ι g) a b) = f (D.nd.chi i 1 (ι g) : (D.nd.O i)ˣ) *
        f ((((D.nd.chi i 1 (ι g))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g) a b)
      rw [← map_mul, Units.mul_inv_cancel_left])
    (by
      intro g
      have e := congrArg Units.val (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
      have e' : f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) =
          ((cycLL ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) :=
        by
        have e2 := congrArg (IntermediateField.inclusion h) e
        exact e2.trans ((IntermediateField.inclusion h).commutes _)
      rw [← e']
      ext a b
      congr 1
      change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
          rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
        f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
      rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
      congr 1
      ring)
    (by
      rw [hrep]
      unfold IsDR
      rw [Module.finrank_fin_fun]
      exact dr')
    (by
      unfold IsDR
      rw [Module.finrank_fin_fun]
      exact dχ')
    τ' c
    (by
      intro a
      refine (jχ a).symm.trans ?_
      rw [hc, Multiset.count_singleton]
      split_ifs <;> rfl)
  rw [hrep] at key
  refine ⟨key.1, key.2.1, fun a => ⟨?_, ?_⟩⟩
  · exact (key.2.2 a).1.trans (jr (a + c)).symm
  · exact (key.2.2 a).2.trans (jr (c - a - 1)).symm

end GlobalTheory.TwistRead
end

