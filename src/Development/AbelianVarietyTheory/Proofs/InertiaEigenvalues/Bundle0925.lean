import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0915
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0918
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0920
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0875
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0917
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0543
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergCellIntegralFinitePartNonneg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBlochKatoReadOfTensorSelmerAddCoboundary
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section

namespace GlobalTheory.UseLoc.Cases

theorem chiT_one_eq {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  simp [chiT, chiOC]

section GenRead

variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL] {k : ℕ}

def iotaL (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (M N : G →* Matrix (Fin k) (Fin k) O) (lam : O) (a : ℕ) :
    ↥(stdLatG (LL := LL) hinj M).T ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin k → LL) ⧸ (stdLatG (LL := LL) hinj N).T :=
  iotaW LL lam a k

theorem iotaL_tmul (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (M N : G →* Matrix (Fin k) (Fin k) O) (lam : O) (a : ℕ) (t : ↥(stdLatG (LL := LL) hinj M).T)
    (x : ↥(Xq LL lam a)) (s : LL) (hs : Submodule.Quotient.mk s = (x : LL ⧸ intO (O := O) LL)) :
    iotaL hinj M N lam a (t ⊗ₜ x) = Submodule.Quotient.mk (s • (t : Fin k → LL)) := by
  obtain ⟨x, hx⟩ := x
  change Submodule.Quotient.mk s = x at hs
  subst hs
  rfl

theorem matRep_twistM_apply {G : Type} [Group G] (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ) (g : G)
    (v : Fin k → LL) :
    matRep (mapM (algebraMap O LL) (twistM N θ)) g v = ((θ g : Oˣ) : O) • matRep (mapM (algebraMap O LL) N) g v := by
  have hM : (mapM (algebraMap O LL) (twistM N θ)) g =
      algebraMap O LL ((θ g : Oˣ) : O) • (mapM (algebraMap O LL) N) g := by
    ext p q
    simp [mapM, twistM, Matrix.smul_apply, smul_eq_mul, map_mul]
  change ((mapM (algebraMap O LL) (twistM N θ)) g).mulVec v = ((θ g : Oˣ) : O) • ((mapM (algebraMap O LL) N) g).mulVec v
  rw [hM, Matrix.smul_mulVec, algebraMap_smul]

theorem actD_iotaL (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : ∀ g, (((χ g)⁻¹ : Oˣ) : O) * ((θ g : Oˣ) : O) = 1)
    (lam : O) (a : ℕ) (g : G) (y : ↥(stdLatG (LL := LL) hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a)) :
    actD (stdLatG hinj N) g (iotaL hinj (twistM N θ) N lam a y) =
      iotaL hinj (twistM N θ) N lam a (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) χ g y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul t x =>
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (x : LL ⧸ intO (O := O) LL)
    rw [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, map_smul, iotaL_tmul hinj _ N lam a _ x s hs,
      iotaL_tmul hinj _ N lam a _ x s hs, ← Submodule.Quotient.mk_smul]
    change Submodule.Quotient.mk (matRep (mapM (algebraMap O LL) N) g (s • (t : Fin k → LL))) =
      Submodule.Quotient.mk ((((χ g)⁻¹ : Oˣ) : O) • s • matRep (mapM (algebraMap O LL) (twistM N θ)) g (t : Fin k → LL))
    congr 1
    rw [matRep_twistM_apply, LinearMap.map_smul, smul_comm _ s, ← mul_smul, hχ g, one_smul]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [Algebra Qp LL]
    [TopologicalSpace (Fin k → LL)] [ContinuousAdd (Fin k → LL)] [ContinuousConstSMul LL (Fin k → LL)]

theorem readW_gen (PD : PeriodData G Qp K₀ K B BdR) (hinj : Function.Injective (algebraMap O LL))
    (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : ∀ g, (((χ g)⁻¹ : Oˣ) : O) * ((θ g : Oˣ) : O) = 1)
    (lam : O) (a : ℕ) (z' : G → ↥(stdLatG (LL := LL) hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a))
    (hz : tableLineDegreeTwo.InHfX PD (stdLatG (LL := LL) hinj (twistM N θ)) (stdLatG hinj N) ↥(Xq LL lam a) χ z') :
    (fun g => iotaL hinj (twistM N θ) N lam a (z' g)) ∈ HfD PD (stdLatG (LL := LL) hinj N) := by
  obtain ⟨n, c, x, m, hc, hz⟩ := hz
  choose s hs using fun j => Submodule.Quotient.mk_surjective _ (x j : LL ⧸ intO (O := O) LL)
  have e : (fun g => iotaL hinj (twistM N θ) N lam a (z' g)) =
      (∑ j, LinearMap.compLeft (stdLatG (LL := LL) hinj N).T.mkQ G (s j • fun g => (c j g : Fin k → LL))) +
        LinearMap.pi (fun g => actD (stdLatG (LL := LL) hinj N) g - LinearMap.id)
          (iotaL hinj (twistM N θ) N lam a m) := by
    funext g
    rw [hz g, map_add, map_sum, map_sub, ← actD_iotaL hinj N θ χ hχ lam a g m]
    simp only [Pi.add_apply, Finset.sum_apply, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iotaL_tmul hinj _ N lam a _ (x j) (s j) (hs j)]
    rfl
  rw [e]
  refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.mem_sup_left (Submodule.mem_map_of_mem ?_))
    (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
  exact (Submodule.restrictScalars_mem O _ _).2 ((finiteCocycles PD _).smul_mem (s j) (hc j).2)

end GenRead

theorem chiT_one_inv_mul {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
    (g : Br.G D.nbr i w hw) :
    (((chiT C θ 1 g)⁻¹ : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) = 1 := by
  rw [chiT_one_eq]
  simp

theorem readW_main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.InHfX (Br.PD D.loc D.nbr i w hw) (latC C (twistM N θ)) (latC C N) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaW ↥C.LL.1 lam a k (z' g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C N) := by
  intro D i w hw C lam k N θ a z' hz
  exact readW_gen (Br.PD D.loc D.nbr i w hw) Subtype.val_injective N θ (chiT C θ 1) (chiT_one_inv_mul C θ) lam a z' hz

end GlobalTheory.UseLoc.Cases

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCoboundaryReadOfTwistedCharacterCoboundary
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases.ReadC

section Gen
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {G : Type} [Group G]

theorem actT_latOne (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (g : G) :
    Formalism.WeaklyAdmissibleFiltrations.actT (latOne hinj ψ) g = ((ψ g : Oˣ) : O) • LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  simp only [Formalism.WeaklyAdmissibleFiltrations.actT, LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul]
  show ((tableLineDegreeTwo.charL (LL := LL) ψ g : LLˣ) : LL) • x = ((ψ g : Oˣ) : O) • x
  simp [tableLineDegreeTwo.charL, Algebra.smul_def]

theorem actTw_latOne (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ) (g : G) :
    tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g = (((χ g)⁻¹ * ψ g : Oˣ) : O) • LinearMap.id := by
  rw [tableLineDegreeTwo.actTw, actT_latOne, LinearMap.rTensor_smul, LinearMap.rTensor_id, smul_smul, Units.val_mul]

theorem actD_one (hinj : Function.Injective (algebraMap O LL)) (M : G →* Matrix (Fin 1) (Fin 1) O) (g : G) :
    actD (stdLatG hinj M) g = M g 0 0 • LinearMap.id := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply, LinearMap.id_apply, actD,
    ← Submodule.Quotient.mk_smul]
  erw [Submodule.mapQ_apply]
  congr 1
  funext j
  fin_cases j
  simp [stdLatG, matRep, mapM, Matrix.mulVec, dotProduct, Algebra.smul_def]

theorem equivG (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ)
    (M : G →* Matrix (Fin 1) (Fin 1) O) (hM : ∀ g, M g 0 0 = (((χ g)⁻¹ * ψ g : Oˣ) : O)) (g : G)
    (u : ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a)) :
    iotaC LL lam a (tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g u) =
      actD (stdLatG hinj M) g (iotaC LL lam a u) := by
  have h1 : tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g u = (((χ g)⁻¹ * ψ g : Oˣ) : O) • u := by
    rw [actTw_latOne]; rfl
  rw [h1, actD_one, hM]
  exact (iotaC LL lam a).map_smul _ u

end Gen
end GlobalTheory.UseLoc.Cases.ReadC

namespace GlobalTheory.UseLoc.Cases.ReadC
section Gen2
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {G : Type} [Group G]

theorem readG (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ)
    (M : G →* Matrix (Fin 1) (Fin 1) O) (hM : ∀ g, M g 0 0 = (((χ g)⁻¹ * ψ g : Oˣ) : O))
    (z' : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a))
    (hz : tableLineDegreeTwo.IsCob (latOne hinj ψ) ↥(Xq LL lam a) χ z') :
    (fun g => iotaC LL lam a (z' g)) ∈ BD (stdLatG hinj M) := by
  obtain ⟨m, hm⟩ := hz
  refine ⟨iotaC LL lam a m, ?_⟩
  funext g
  have key := equivG hinj lam a ψ χ M hM g m
  rw [hm g]
  refine Eq.trans ?_ ((iotaC LL lam a).map_sub _ m).symm
  exact (congrArg (fun y => y - iotaC LL lam a m) key).symm

end Gen2
end GlobalTheory.UseLoc.Cases.ReadC

namespace GlobalTheory.UseLoc.Cases.ReadC

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem entry (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 = ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  simp [locOC, chiOC, Br.locO, mapM, chiRatO, twistM, Br.iota]

theorem ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) (g : Br.G D.nbr i w hw) :
    (chiT C θ 1 g)⁻¹ * chiT C θ c g = chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g := by
  have h1 : chiOC C 1 g = 1 := by simp [chiOC]
  simp only [chiT, MonoidHom.mul_apply, mul_inv_cancel, h1, one_mul]
  rw [mul_comm (chiOC C _ g) (θ g)]
  exact inv_mul_cancel_left _ _

theorem entry_ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 = (((chiT C θ 1 g)⁻¹ * chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  rw [entry, ratio]

end GlobalTheory.UseLoc.Cases.ReadC

theorem GlobalTheory.UseLoc.Cases.readC_cob : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ)
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCob (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c))) :=
  fun D i w hw C lam θ c a z' hz =>
    ReadC.readG (LL := ↥C.LL.1) Subtype.val_injective lam a (chiT C θ c) (chiT C θ 1) (locOC C (chiRatO D.nd i c))
      (ReadC.entry_ratio C θ c) z' hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalIffUnrOfLawsT
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.RecT
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RecT.SphLaw

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def consEquiv (n : ℕ) : ((Fin 1 → ℂ) × (Fin n → ℂ)) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v := Fin.cons (v.1 0) v.2
  invFun f := (fun _ => f 0, Fin.tail f)
  map_add' x y := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  left_inv v := Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; simp) (funext fun j => by simp [Fin.tail])
  right_inv f := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

theorem diag_sum_iso {n : ℕ} (c : Fin (n + 1) → ℂˣ) :
    ((WDRep.diag h fun _ : Fin 1 => c 0).sum (WDRep.diag h fun i : Fin n => c i.succ)).Iso (WDRep.diag h c) := by
  refine ⟨consEquiv n, fun σ v => ?_, fun v => ?_⟩
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]

theorem sumList_cons (x : WD h) (l : List (WD h)) : sumList (x :: l) = x.lpSum (sumList l) := rfl

theorem sumList_ofFn_diag : ∀ (n : ℕ) (c : Fin n → ℂˣ),
    sumList (List.ofFn fun i => WD.mk (WDRep.diag h fun _ : Fin 1 => c i)) = WD.mk (WDRep.diag h c)
  | 0, c => by
      rw [List.ofFn_zero]
      show WD.lpZero h = _
      unfold WD.lpZero
      congr 2
      funext i
      exact i.elim0
  | n + 1, c => by
      rw [List.ofFn_succ]
      rw [sumList_cons]
      rw [sumList_ofFn_diag n (fun i => c i.succ), WD.lpSum_mk]
      exact WD.sound (diag_sum_iso c)

theorem zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  GlobalTheory.zelevinskyPolynomialRing_of_parts GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.segmentRepresentation'
    GlobalTheory.grothendieckRingPolynomial_outright

theorem geometricLemma : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.geometricLemmaFiltration_holds

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (w.adicCompletion E) → WD h}

theorem sat (H : LawsT a ha rc) (x : IrrGL (w.adicCompletion E)) (α : Fin x.1 → ℂˣ) (hα : HasSatake x.rep α) :
    rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hL := GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar GlobalTheory.langlandsExhaustionGL_holds
    GlobalTheory.langlandsMultisegments_outright GlobalTheory.standardCosocleGL_holds zelevinskyPolynomialRing geometricLemma
    GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _

end GlobalTheory.RecT.SphLaw

namespace GlobalTheory.RecT

theorem isSpherical_iff_unr_of_lawsT : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (rc : IrrGL (w.adicCompletion E) → WD h), LawsT a ha rc → ∀ x : IrrGL (w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr := by
  intro E Ω _ _ _ _ _ A w h a ha rc H x
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  constructor
  · intro hs
    obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) x.1
      ⟨x.2.rep.V, x.2.rep.ρ, x.2.rep.smooth, x.2.rep.irr⟩ hs
    rw [SphLaw.sat H x α hα]
    exact (WD.unr_mk _).2 (WDRep.unr_diag _)
  · intro hu
    obtain ⟨α, hα⟩ := GlobalTheory.LocLanglands.unr_eq_diag_inv E Ω A w h (rc x) hu
    obtain ⟨π, hπ⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := w.adicCompletion E) α
    have φ := equivRep π
    have hπ' : HasSatake (cls π).rep α := ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hπ.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hπ.2.2⟩
    have e1 := SphLaw.sat H (cls π) α hπ'
    have hsupp := GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries (w.adicCompletion E) _
      (fun i => unrChar (w.adicCompletion E) (α i)) (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ _))
      (cls π).2.rep hπ'.2.2
    have hg : Good (cls π) := Model.good_of_toral ⟨_, hsupp, fun y hy => by
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
      rfl⟩
    have e2 : x = cls π := H.inj x (cls π) hg (hα.trans e1.symm)
    rw [e2]
    exact hπ'.2.1

end GlobalTheory.RecT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointConditionAdm5
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NSizes

theorem main : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X 120 := by
  intro hP D L P nch HW F Cm X C₂ hS
  have hb : ((0 : ℕ) : ℝ) ≤ L.sc.b := by
    simp only [Nat.cast_zero]
    exact (Real.exp_pos _).le
  have hub := GlobalTheory.T.split_bound_of_params hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P
    (le_trans (by norm_num) hS.big) le_rfl hb (hS.facts.admJ L hS.par) hS.par67 hS.facts.toCore.admA
    hS.facts.Conclusion1.1 hS.facts.Conclusion1.2.2 hS.facts.Conclusion2.1 hS.facts.Conclusion2.2.2 hS.facts.rhoBar hS.facts.large.2.1
    hS.facts.large.2.2 hS.facts.nct hS.facts.trip hS.facts.same hS.facts.block hS.facts.muUnr hS.facts.depthG
  obtain ⟨-, -, -, -, hCB, hC0, ⟨M0, h0', hW⟩, -⟩ := hub
  intro i hT hg hR
  refine ⟨hCB i hT hg hR, ?_, ?_⟩
  · have h := GlobalTheory.T.maxLength_localInvariants_twisted_fractionModInteger_le D i (X.dc i).col (fun h => hR.1 (Or.inl h)) (fun h => hR.2.1 (Or.inl h))
      (fun h => hR.2.1 (Or.inr h)) (fun u hu => ((X.dc i).cover u).1 (Or.inr hu))
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  · intro hsp u hu
    refine ⟨hC0 i hT hg hR hsp u hu, fun π hπ => ?_⟩
    obtain ⟨hu', s, hs, hc, hcrys, hJ, hnj, hcle⟩ := hW i hT hg hsp u hu π hπ
    have hWat := GlobalTheory.T.crystallineLatticeWachModuleExists_proof D HW F Cm (D.nd.l i) (D.nbr i u hu').Kw s (D.nbr i u hu').LL hs
    have hHW := hWat (GlobalTheory.HubX.wLat D i (X.ρ i) π u hu' hc) M0 h0' hcrys hJ
    have hkill := GlobalTheory.T.torsion_exponent_kills_invariants_of_good hP.bk hP.tate hP.euler D HW F Cm (D.nd.l i) (D.nbr i u hu').Kw s (D.nbr i u hu').LL hs
      M0 h0' (GlobalTheory.HubX.wLat D i (X.ρ i) π u hu' hc) hHW hnj
    have hlen := GlobalTheory.T.lenUnit_invariants_twistedLattice_le_of_killingExponent D HW i (X.ρ i) π u hu' s hs hc (X.c0 i u) _ rfl (by
      intro x hx
      have e := hkill x hx
      rw [← Nat.sub_add_cancel hcle, pow_add, mul_smul, e, smul_zero])
    have h1 := hC0 i hT hg hR hsp u hu
    have hr : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
    calc (Br.h0W i u (X.ρ i) π : ℝ) ≤ (D.R.r : ℝ) * (X.c0 i u : ℕ) := hlen
      _ ≤ (D.R.r : ℝ) * (120 * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L) := mul_le_mul_of_nonneg_left h1 hr
      _ = 120 * D.R.r * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L := by ring

end GlobalTheory.NSizes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatMMemOfLeHalf
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnivCover

variable {D : D7}

def delDet (V : HSp D) {C : Type} [AddCommGroup C] (u : GlobalTheory.ExportSeries.UnivTwist D C) (Q : Finset (Pl D.host.E))
    (g : GA D V) : ↥Q → C :=
  Multiplicative.toAdd (GlobalTheory.ExportSeries.detChar V (u.delQ Q) g)

example (V : HSp D) {C : Type} [AddCommGroup C] (Q : Finset (Pl D.host.E)) (g : GA D V) :
    delDet V (⟨fun _ => 1, fun _ => 1⟩ : GlobalTheory.ExportSeries.UnivTwist D C) Q g = 0 := by
  funext q
  rfl

end GlobalTheory.UnivCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergCellIntegralFinitePartNonnegStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_cell_integral_finite_part_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ) (F : (Fin (m + 1) → Ad E) → ℂ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    (∀ k : GL (Fin (m + r + 1 + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + r + 1 + 1)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + r + 1 + 1) k) = GlobalTheory.JSW.whit φ g) →
    (∀ k : GL (Fin (m + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + 1)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) k) = GlobalTheory.JSW.whit φ' g) →
    (∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
    Continuous κ → (∀ h, 0 ≤ κ h) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, κ h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) →
    (∃ h₀ ∈ GlobalTheory.JSW.supS E (m + 1) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0 ∧ 0 < (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h₀)).re) →
    Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) → (∀ y, 0 ≤ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).re ∧ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).im = 0) →
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        (∀ g ∉ GlobalTheory.CellDec.C0 E (m + 1) S, f g = 0) ∧
        (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' 0 g = (f g : ℂ)) ∧
        (∀ (x : ℝ) (g : GA E (m + 1)), ((GlobalTheory.RSnm.detAbs g ^ x : ℝ) : ℂ) = Complex.exp (x * t g)) ∧
        (∀ x : ℝ, ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (g))‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (g) ^ (x - ((r : ℝ) + 1)))) ∂μ ≠ ⊤) ∧
        (∀ π' : CuspSub E (m + 1), π'.IsUnitary → φ' ∈ GlobalTheory.JSW.mspanR π' →
          F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)) → ∀ x : ℝ, 1 < x →
          ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (‖GlobalTheory.JSW.whit φ' (g)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (g) ^ x)) ∂μ ≠ ⊤) := by
  first | (exact @GlobalTheory.RSnmFT.exists_cellPart_unfoldedIntegral_positive_alt) | (exact GlobalTheory.RSnmFT.exists_cellPart_unfoldedIntegral_positive_alt) | (intros; apply GlobalTheory.RSnmFT.exists_cellPart_unfoldedIntegral_positive_alt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCocycleDescentEnlargementStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedCocycle_descent_enlargement : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (I : Subgroup (Br.G D.nbr i w hw))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ Z1urD (latC C (locOC C M)) I → z ∈ Z1urD (Br.locLat D.nbr i w hw M) I := by
  first | exact @GlobalTheory.UseLoc.descUr_mem | exact GlobalTheory.UseLoc.descUr_mem | (intros; apply GlobalTheory.UseLoc.descUr_mem <;> assumption)
end

