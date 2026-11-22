import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0874
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0144
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Formalism.LocalToGlobal.NormalizedHeckeFactors.WittCoreInclusionMulVecMemLatticeCompletionAtPla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0875
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralRankinSelbergThetaEqWhittakerUnfolding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0871
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoefficientContinuousNormInvarian
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.JSW.WhitNorm

theorem continuous_whit_and_norm_mul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∀ γ g, F (ratGL E a γ * g) = F g) →
    Continuous (GlobalTheory.JSW.whit F) ∧ ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖ := by
  intro E _ _ _ a F hF hl
  refine ⟨?_, fun u hu g => ?_⟩
  · have e : GlobalTheory.JSW.whit F = GroundTheory.Automorphic.FourierWhittaker.partialCoeff F 0 :=
      funext fun g => GroundTheory.Automorphic.FourierWhittaker.whittaker_eq_partialCoeff_zero hF g
    rw [e]
    exact GroundTheory.Automorphic.FourierWhittaker.continuous_partialCoeff hF 0
  · have hu' : u ∈ GlobalTheory.JSW.NA E a := (GlobalTheory.SmGL.mem_unipB _).1 hu
    rw [GlobalTheory.JSW.WhitModel.whit_mul hF hl hu' g, norm_mul, GlobalTheory.JSW.psiN, Circle.norm_coe, one_mul]

end GlobalTheory.JSW.WhitNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSetupCountEqZeroOffBadPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin IsAlgPos)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs.SetupPin

variable {D : D7}

theorem goodSetup_badPlaces_conj (F : TwFrameC D) {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) :
    ∀ i, ∀ P ∈ D.ntw.S0 i, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ D.ntw.S0 i := by
  intro i P hP P' hc
  have hP' : P ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E))) := hP
  rw [T.ringSpec_excludedPlaces_eq i] at hP'
  show P' ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E)))
  rw [T.ringSpec_excludedPlaces_eq i]
  rcases hP' with (((h | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Formalism.L2.placesOver_conj D _ h hc))))
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h
    exact Or.inl (Or.inl (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨k, Formalism.L2.placesOver_conj D _ hk hc⟩))))
  · exact Or.inl (Or.inl (Or.inr (Formalism.L2.placesOver_conj D _ h hc)))
  · exact Or.inl (Or.inr (Formalism.L2.placesOver_conj D _ h hc))
  · exact Or.inr (T.concreteTwistFrame_extraExcludedPlaces_conj i P P' h hc)

theorem goodSetup_placesOverTwo_subset (F : TwFrameC D) {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) (h2 : 2 ∈ low) :
    ∀ i, placesOver D.host.E 2 ⊆ ↑(D.ntw.S0 i) := by
  intro i P hP
  show P ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E)))
  rw [T.ringSpec_excludedPlaces_eq i]
  exact Or.inr (T.concreteTwistFrame_extraExcluded_over_smallPrimes i 2 h2 hP)

theorem q_dvd_discr (D : D7) : D.host.q ∣ (NumberField.discr D.host.E).natAbs :=
  Int.natCast_dvd.1 D.host.q_dvd_discr

theorem goodSetup_count_eq_zero_off_badPlaces (F : TwFrameC D) {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) (h2 : 2 ∈ low)
    (hd : (NumberField.discr D.host.E).natAbs.primeFactors ⊆ low) (hc : (Ideal.absNorm D.host.ccK).primeFactors ⊆ low) :
    ∀ i P, P ∉ D.ntw.S0 i → FractionalIdeal.count D.host.E P D.host.AA = 0 := by
  intro i P hP
  by_contra hA
  have hb : ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    by_contra hb
    exact hA (GlobalTheory.HalfCompare.primeToAA_of_not_mem hb)
  obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under P
  have hdiv : p ∣ GlobalTheory.HalfCompare.badInt D := (hpP _).1 hb
  have hlow : p ∈ low := by
    unfold GlobalTheory.HalfCompare.badInt at hdiv
    rcases hp.dvd_mul.1 hdiv with h | h
    · exact hd (Nat.mem_primeFactors.2 ⟨hp,
        Int.natCast_dvd.1 ((D.host.dvd_discr_iff_dvd_condN hp).2 (h.mul_right D.host.d)),
        Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)⟩)
    · exact hc (Nat.mem_primeFactors.2 ⟨hp, h, by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot⟩)
  apply hP
  show P ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E)))
  rw [T.ringSpec_excludedPlaces_eq i]
  exact Or.inr (T.concreteTwistFrame_extraExcluded_over_smallPrimes i p hlow ((hpP p).2 dvd_rfl))

theorem mk_fractionRing_le {R : Type} [CommRing R] [IsDomain R] (h : Cardinal.mk R ≤ Cardinal.continuum) :
    Cardinal.mk (FractionRing R) ≤ Cardinal.continuum := by
  have hs : Function.Surjective
      (fun p : R × nonZeroDivisors R => IsLocalization.mk' (FractionRing R) p.1 p.2) := fun z => by
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) z
    exact ⟨(x, y), hxy⟩
  refine (Cardinal.mk_le_of_surjective hs).trans ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc Cardinal.mk R * Cardinal.mk (nonZeroDivisors R) ≤ Cardinal.continuum * Cardinal.continuum :=
        mul_le_mul' h ((Cardinal.mk_subtype_le _).trans h)
    _ = Cardinal.continuum := Cardinal.continuum_mul_self

theorem mk_frac_Ok (F : TwFrameC D) : ∀ i k, Cardinal.mk (FractionRing (D.ntw.Ok i k)) ≤ Cardinal.continuum := by
  intro i k
  haveI := D.ntw.lPrime i
  apply mk_fractionRing_le
  have hinj : Function.Injective (fun x : D.ntw.Ok i k => ((F.eOk i k x : _) : ℂ_[D.ntw.l i])) :=
    Subtype.val_injective.comp (F.eOk i k).injective
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [(GlobalTheory.PadicCard.card_padicAlgCl_padicComplex (D.ntw.l i)).2, Cardinal.mk_complex]

theorem continuous_comp_of_isOpen_ker {Γ B Y : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group B]
    [TopologicalSpace Y] (φ : Γ →* B) (f : B → Y) (h : IsOpen (φ.ker : Set Γ)) : Continuous (f ∘ φ) := by
  have hloc : IsLocallyConstant (f ∘ φ) := by
    intro s
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun g' => g⁻¹ * g') ⁻¹' (φ.ker : Set Γ), fun g' hg' => ?_,
      h.preimage (continuous_const.mul continuous_id), ?_⟩
    · have h1 : φ (g⁻¹ * g') = 1 := hg'
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      show f (φ g') ∈ s
      rw [← h1]
      exact hg
    · show φ (g⁻¹ * g) = 1
      rw [inv_mul_cancel, map_one]
  exact hloc.continuous

theorem delAt_alg (C : CharFrame D) (l : ℕ) : IsAlgPos (C.delAt l) 0 := by
  unfold CharFrame.delAt
  split_ifs
  · obtain ⟨n, h0, h⟩ := C.isDel'.fin
    exact GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd h0 h
  · obtain ⟨n, h0, h⟩ := C.isDel.fin
    exact GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd h0 h

end GlobalTheory.TwInputs.SetupPin

namespace GlobalTheory.TwInputs.SetupPin

variable {D : D7}

theorem exists_art_gal (hA : GlobalTheory.Published.GlobalArtinReciprocity) (cf : CharFrame D) (hR : DeltaRead D cf) :
    ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧ ∀ i b,
      ∃ (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ),
        (∀ x, ι (κ ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x) ∧
        GlobalTheory.GalChar.IsGal art κ ι (cf.delAt (D.ntw.l i)) (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) := by
  obtain ⟨art, hart⟩ := hA D.host.E D.nd.Om
  refine ⟨art, hart, fun i b => ?_⟩
  haveI := D.ntw.lPrime i
  obtain ⟨ρ⟩ := GlobalTheory.Triple.Reading.nonempty (X := D.ntw) i b
  have hker : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have hχ : IsAlgPos (cf.delAt (D.ntw.l i)) 0 := delAt_alg cf _
  obtain ⟨r0, hr0, hL⟩ := hart.exists_isLAdicOf ρ.ι hχ
  have hc : Continuous (GlobalTheory.GalChar.inQ ρ.κ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))) :=
    continuous_comp_of_isOpen_ker (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
      (Units.map (GlobalTheory.GalChar.toQ ρ.κ).toMonoidHom) hker
  have hz : ∀ v, ‖(((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)‖ = 1 := fun v => cf.delAt_unitary _ _
  have heq : GlobalTheory.GalChar.inQ ρ.κ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) = r0 := by
    refine GlobalTheory.GalChar.eq_of_frob hart hc hr0 ?_
    filter_upwards [GlobalTheory.GalChar.away_ae (E := D.host.E) (D.ntw.l i) (Fact.out : (D.ntw.l i).Prime).ne_zero,
      GlobalTheory.GalChar.unr_ae (cf.delAt (D.ntw.l i))] with v hv hu A hA σ hσ
    obtain ⟨x, hx, hd⟩ := hR i v hv hu A σ hA hσ
    have hx' : D.what₂.embLL (x : D.what₂.LL) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)⁻¹ := by
      rw [hx, Units.val_inv_eq_inv_val]
    apply Units.ext
    rw [hL.frob_unr hart (Or.inr rfl) hu hA hσ, GlobalTheory.GalChar.inQ_val]
    cases b
    · have hstar : (x : D.what₂.LL) = star ((x⁻¹ : D.LL0) : D.what₂.LL) := by
        apply D.what₂.embLL.injective
        rw [D.starLL_cx, IntermediateField.coe_inv, map_inv₀, hx', inv_inv, ← Complex.inv_eq_conj (hz v)]
      have h1 : ρ.ι (ρ.κ (D.ntw.emb0 i x)) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ) := by
        rw [← D.ntw.restX_coefficientEmbedding_conj i x⁻¹ x hstar]
        have := ρ.read x⁻¹
        simp only [GlobalTheory.Triple.embSide, Bool.false_eq_true, if_false] at this
        rw [this]
        show D.what₂.embLL ((x⁻¹ : D.LL0) : D.what₂.LL) = _
        rw [IntermediateField.coe_inv, map_inv₀, hx', inv_inv]
      show GlobalTheory.GalChar.toQ ρ.κ (((D.ntw.delta i)⁻¹ σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = _
      rw [MonoidHom.inv_apply, map_units_inv]
      congr 1
      show ρ.κ (algebraMap _ _ _) = _
      rw [hd, ← h1, ρ.ι.symm_apply_apply]
    · have h1 : ρ.ι (ρ.κ (D.ntw.emb0 i x)) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)⁻¹ := by
        have := ρ.read x
        simp only [GlobalTheory.Triple.embSide, if_true] at this
        rw [this]
        exact hx'
      show ρ.κ (algebraMap _ _ ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) = _
      rw [hd, ← map_inv₀, ← h1, ρ.ι.symm_apply_apply]
  refine ⟨ρ.κ, ρ.ι, fun x => ?_, hχ, ?_, ?_⟩
  · have := ρ.read x
    cases b <;> simpa [GlobalTheory.Triple.embSide] using this
  · exact continuous_comp_of_isOpen_ker (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) Units.val hker
  · rw [heq]
    exact hL

end GlobalTheory.TwInputs.SetupPin

namespace GlobalTheory.TwInputs.SetupPin

end GlobalTheory.TwInputs.SetupPin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicMapExtremalVectorEqPhaseSmulLetters
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.SerIntLetters
open GlobalTheory.AdTh.PhaseMap GlobalTheory.SerLetters

set_option maxHeartbeats 1600000 in

theorem io_eq_phase_smul_harmLetters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank ≃ FVar D (Wc D i).rank (Vc D i).rank, IsLetters (T.Q.Dw ((i : ℕ) + 1)) lt → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∃ J : VsV D i ℂ →ₗ[ℂ] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ, (∀ v, J v ∈ HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank ℂ ComplexEmbedding.conjugate (InPsi T.Q.H) (fun τ j => wtA (κ i) (τ, j))) ∧ (∀ k : Subfield ℂ, (∀ x ∈ T.Q.c.F, x ∈ k) → ∀ v : VsV D i ℂ, (∀ m, MvPolynomial.coeff m (v : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) ∈ k) → ∀ mo, (J v).coeff mo ∈ k) ∧ ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v, pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 v)) = ka • stdF R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) f (MvPolynomial.rename lt (J v)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hLaws hL hGrp hFam hMod hThP hTie i hstd u hu c0 hc lt hlt
  obtain ⟨ka, hka, io, hio, hJ⟩ := io_eq_phase_smul_letters D G Pl0 T0 A T R κ v₀ hL hFam hMod hThP hTie i hstd u hu c0 hc
    (⇑lt) (fun ℓ => hlt ℓ)
  let b : Formalism.L2.DIV.VVIdx (lamV D i) → VsV D i ℂ := fun j =>
    GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i) j)
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range b) := fun x _ => by
    obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) x
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hli : LinearIndependent ℂ b := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank hsp ?_
    rw [Module.finrank_eq_card_basis (Formalism.L2.DIV.bVV ℂ (lamV D i))]
  let e : Formalism.L2.DIV.VVIdx (lamV D i) → MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ := fun j =>
    MvPolynomial.map (inC T.Q.c) (io (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i) j))
  let J : VsV D i ℂ →ₗ[ℂ] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ := (Module.Basis.mk hli hsp).constr ℂ e
  have hJv : ∀ a : Formalism.L2.DIV.VVIdx (lamV D i) → ℂ, J (∑ j, a j • b j) = ∑ j, a j • e j := fun a => by
    simp only [map_sum, map_smul, J]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show b j = Module.Basis.mk hli hsp j from (Module.Basis.mk_apply hli hsp j).symm, Module.Basis.constr_basis]
  refine ⟨ka, hka, J, fun v => ?_, fun k hk v hv mo => ?_, fun f hf v => ?_⟩
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) v
    rw [hJv]
    refine GlobalTheory.PtId.mem_HHa_of_span _ _ _ _ _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    exact GlobalTheory.SerLetters.map_mem_HHa (inC T.Q.c) (GlobalTheory.PtId.mem_HHa_of_span _ _ _ _ _ _ (hio _))
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) v
    have hF : ∀ x : T.Q.c.F, inC T.Q.c x ∈ k := fun x => hk _ (by rw [show inC T.Q.c x = (x : ℂ) from rfl]; exact x.2)
    let φ : T.Q.c.F →+* k := (inC T.Q.c).codRestrict k hF
    let eK : Formalism.L2.DIV.VVIdx (lamV D i) → Formalism.L2.DIV.Pol k D.what₂.Tau (Vc D i).rank := fun j =>
      MvPolynomial.map φ (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i) j : Formalism.L2.DIV.Pol T.Q.c.F D.what₂.Tau (Vc D i).rank)
    have hmap : ∀ j, MvPolynomial.map k.subtype (eK j) = (b j : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) := fun j => by
      show MvPolynomial.map k.subtype (MvPolynomial.map φ _) = MvPolynomial.map (inC T.Q.c) _
      rw [MvPolynomial.map_map]
      rfl
    have hli' : LinearIndependent ℂ fun j => MvPolynomial.map k.subtype (eK j) := by
      have h2 := hli.map' (Submodule.subtype _) (Submodule.ker_subtype _)
      have e2 : (fun j => MvPolynomial.map k.subtype (eK j)) = (Submodule.subtype _) ∘ b := funext hmap
      rw [e2]
      exact h2
    have hsum : (∑ j, a j • MvPolynomial.map k.subtype (eK j)) =
        ((∑ j, a j • b j : VsV D i ℂ) : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) := by
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hmap]
    have hcoef : ∀ m, MvPolynomial.coeff m (∑ j, a j • MvPolynomial.map k.subtype (eK j)) ∈ k.subtype.fieldRange := fun m => by
      rw [hsum]
      exact RingHom.mem_fieldRange.2 ⟨⟨_, hv m⟩, rfl⟩
    have ha : ∀ j, a j ∈ k := fun j => by
      obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.1 (coord_mem_fieldRange k.subtype eK hli' a hcoef j)
      rw [← hy]
      exact y.2
    rw [hJv, MvPolynomial.coeff_sum]
    refine Subfield.sum_mem _ fun j _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    exact Subfield.mul_mem _ (ha j) (by rw [MvPolynomial.coeff_map]; exact hF _)
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) v
    rw [hJv]
    simp only [map_sum, map_smul]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ f hf, GlobalTheory.AdTh.PhaseMap.toF_apply, smul_comm]

end GlobalTheory.SerIntLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProducStatement
section
open NumberField IsDedekindDomain GlobalTheory.JSW
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProd_localRankinSelbergFactor_self_of_eulerProduct : ∀ (I : Type) (q : I → ℕ) (n : ℕ) (α : I → Fin n → ℂˣ), (∀ w, 2 ≤ q w) →
    (∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤) →
    (∀ x : ℝ, 1 < x →
      HasProd (fun w => locL (q w) (Finset.univ.val.map (α w))
          ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ))
        (((GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) ∧
      1 ≤ (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) ∧
    ContinuousOn (fun x => (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) (Set.Ioi 1) := by
  first | exact @GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL | exact GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL | (intros; apply GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
section
open MeasureTheory
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct : ∀ {I : Type} (q : I → ℕ) {n : ℕ} (α β : I → Fin n → ℂˣ) (x : ℝ), 1 < x → (∀ i, 2 ≤ q i) →
    GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    HasSum (fun l : I →₀ (Fin n → ℤ) => l.prod fun i v => GlobalTheory.ZEul.rsTerm (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v)
      (∏' i, GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i)) ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) := by
  first | exact @GlobalTheory.ZEul.hasSum_rsTerm_finsupp | exact GlobalTheory.ZEul.hasSum_rsTerm_finsupp | (intros; apply GlobalTheory.ZEul.hasSum_rsTerm_finsupp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleModuleDetDiagonalUniformiserMul
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.CellDec.DetMod

theorem prod_adl {E : Type} [Field E] [NumberField E] {ι : Type} (s : Finset ι)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : ι → HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    ∏ i ∈ s, GlobalTheory.CellDec.adl ϖ (m i) = GlobalTheory.CellDec.adl ϖ (∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.CellDec.adl_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, GlobalTheory.CellDec.adl_add]

theorem det_finGL' {E : Type} [Field E] [NumberField E] {a : ℕ} (k : GL (Fin a) (Af E)) :
    GeneralLinearGroup.det (finGL E a k) = finId E (GeneralLinearGroup.det k) := by
  let p : Ad E →+* InfiniteAdeleRing E := RingHom.fst (InfiniteAdeleRing E) (Af E)
  refine Units.ext (Prod.ext ?_ ?_)
  · have h := GlobalTheory.CuspRep.det_map p (finGL E a k)
    have h0 : GeneralLinearGroup.map p (finGL E a k) = 1 :=
      map_cornerGL_of_zero (sFin E) p (fun x => rfl) k
    rw [h0, map_one, Units.val_one] at h
    change p _ = _
    rw [← h]
    change (1 : InfiniteAdeleRing E) = (1 : InfiniteAdeleRing E) - 0 + 0
    simp
  · have h := GlobalTheory.CuspRep.det_map (pFin E) (finGL E a k)
    have h0 : GeneralLinearGroup.map (pFin E) (finGL E a k) = GeneralLinearGroup.map (RingHom.id _) k :=
      map_cornerGL_of_hom (sFin E) (pFin E) (RingHom.id _) (fun x => rfl) k
    rw [h0] at h
    change pFin E _ = _
    rw [← h]
    change _ = (1 : Af E) - 1 + (GeneralLinearGroup.det k : (Af E)ˣ)
    rw [sub_self, zero_add]
    rfl

end GlobalTheory.CellDec.DetMod

theorem GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n),
      (ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l * g)) : ℝ) =
        (∏ v ∈ l.support, ((qV E v : ℝ) ^ (∑ i, l v i))⁻¹) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
  intro E _ _ n ϖ hϖ l g
  rw [map_mul, map_mul, Positive.val_mul]
  congr 1
  have hdet : GeneralLinearGroup.det (GlobalTheory.SmGL.diagT (Af E) (Fin n)
      fun i => GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)) =
      ∏ i, GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, Matrix.det_diagonal, Units.coe_prod]
  unfold GlobalTheory.CellDec.tl
  rw [GlobalTheory.CellDec.DetMod.det_finGL', hdet, GlobalTheory.CellDec.DetMod.prod_adl]
  rw [GlobalTheory.AdeleScale.ideleModule_finId_adl ϖ hϖ _ l.support]
  · refine Finset.prod_congr rfl fun v _ => ?_
    congr 2
    rw [Finsupp.finset_sum_apply]
    rfl
  · intro v hv
    rw [Finsupp.notMem_support_iff] at hv
    rw [Finsupp.finset_sum_apply]
    simp [hv]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnAbsDetRpowLeOneFundamentalDomainStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ s : ℝ, 0 < s → IntegrableOn (fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ s) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  first | exact @GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low | exact GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low | (intros; apply GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnMinAbsDetInvFundamentalDomainStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_min_absDet_inv_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ), 0 < m →
    ∀ (μ : Measure (GA E m)) [μ.IsHaarMeasure] (𝓕 : Set (GA E m)),
      IsFundamentalDomain (ratGL E m).range 𝓕 μ →
      IntegrableOn (fun h : GA E m => min (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)
        (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)⁻¹) 𝓕 μ := by
  first | exact @GlobalTheory.FinVolGL.integrableOn_min_absDet | exact GlobalTheory.FinVolGL.integrableOn_min_absDet | (intros; apply GlobalTheory.FinVolGL.integrableOn_min_absDet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralRankinSelbergThetaEqWhittakerUnfoldingStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_rankinSelbergTheta_eq_whittakerUnfolding : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (π : CuspSub E a), π.IsUnitary → ∀ (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕₀ : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ → ∀ x : ℝ,
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
    ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ := by
  first | (exact @GlobalTheory.RSUnfold.lintegral_theta_eq_whit) | (exact GlobalTheory.RSUnfold.lintegral_theta_eq_whit) | (intros; apply GlobalTheory.RSUnfold.lintegral_theta_eq_whit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuousStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CellDec
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_unipotentCell_pos_lt_top_continuous : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (μ : Measure (GA E n)) [μ.IsHaarMeasure] (S : Finset (HeightOneSpectrum (𝓞 E))) (𝓕 : Set (GA E n)), IsFundamentalDomain (NE E n) 𝓕 μ → ∀ B : ℝ → GA E n → ℝ, Continuous (Function.uncurry B) → (∀ x g, 0 ≤ B x g) → (∀ x, 0 < B x 1) → (∀ x, ∀ u ∈ NA E n, ∀ g, B x (u * g) = B x g) → (∃ K : Set (GA E n), IsCompact K ∧ ∀ x g, g ∈ C0 E n S → B x g ≠ 0 → ∃ u ∈ NA E n, u * g ∈ K) → (∀ x, 0 < ∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ ∧ ∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ < ⊤) ∧ Continuous fun x => (∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ).toReal := by
  first | exact @GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous | exact GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous | (intros; apply GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModerateGrowthRapidKernelOperatorStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderateGrowth_rapidKernelOperator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Growth F → GlobalTheory.MSpanDecay.Growth (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  first | exact @GlobalTheory.MSpanDecay.growth_kernel | exact GlobalTheory.MSpanDecay.growth_kernel | (intros; apply GlobalTheory.MSpanDecay.growth_kernel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNonzeroRationalVectorLeShortestVectorStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_nonzeroRationalVector_le_shortestVector : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (N : ℕ), Module.finrank ℝ (Fin a → Cinf E) ≤ N → ∃ (M : ℕ) (C : ℝ), ∀ (h : GA E a) (A : ℝ) (c : (Fin a → E) → ℂ), 0 ≤ A → (∀ ξ : Fin a → E, (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)) ∉ latt a J → c ξ = 0) → (∀ ξ ξ' : Fin a → E, ξ' ≠ 0 → (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)) ∈ latt a J → ‖c ξ‖ * (1 + ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)‖) ^ M ≤ A * ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)‖ ^ N) → Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∧ ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ ≤ C * A := by
  first | exact @GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest | exact GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest | (intros; apply GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest <;> assumption)
end

