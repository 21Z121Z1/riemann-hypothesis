import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0978
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0962
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0837
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0970
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0977
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0979
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0958
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0975
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0109
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0882
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0056
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0887
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0926

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverGalois

theorem fieldRange_of_normal (L : IntermediateField ℚ ℂ) [hN : Normal ℚ L] (f : L →+* ℂ) :
    f.toRatAlgHom.fieldRange = L :=
  @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ L (by convert hN; exact Subsingleton.elim _ _) f.toRatAlgHom

theorem exists_goodCover_galois (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (hJ : LawsJ T) (i : Fin D.R.m) (hj : InR D ((i : ℕ) + 1)) (n pd : ℕ) (I : Ideal (𝓞 D.host.E))
    (haux : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M pd)
    (hK : I = Ideal.span {x | x ∈ I ∧ x ∈ Algebra.adjoin ℤ {T.Q.H.w0}})
    (hprod : I * I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = Ideal.span {(pd : 𝓞 D.host.E)})
    (hsup : I ⊔ I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤)
    (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [Normal ℚ L] (hle : T.Q.c.F ≤ L)
    (hz : zeta (T.Q.l.M * pd) ∈ L) (hsm : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SmallIn R i (L.val : L →+* ℂ))
    (hray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * pd) L.toSubfield) :
    ∃ C : Cover T ((i : ℕ) + 1) T.σ₀, C.d.pd = pd ∧ C.d.I = I ∧ C.σ₂.fieldRange = L.toSubfield ∧
      GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.GoodCover T R i C n := by
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨hodd, -, -, hcop, -⟩ := id haux
  have hnum := GlobalTheory.T.numerical_consequences_of_pins D T.Q hJ.toLawsM.pins
  have hA : T.Q.l.A = 1 := hnum.2.1
  have hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    have := hnum.2.2.2.2.2.2 _ hj; omega
  obtain ⟨l₂, hd, hM, hMb, hA₂⟩ := (GlobalTheory.exists_level_mul_split _ T.Q.H T.Q.l).1 pd I hodd hcop hK hprod hsup
  obtain ⟨Xo₂⟩ := GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level _ T.Q.H (T.Q.Dw ((i : ℕ) + 1)) l₂ hpq
  let c' : Coeff T.Q.l :=
    { F := L, fin := inferInstance, conj := fun τ a => hle (T.Q.c.conj τ a)
      zeta_mem := hle T.Q.c.zeta_mem, le := T.Q.c.le.trans hle }
  have hM' : l₂.M' = T.Q.l.M * pd := by
    rw [Level.M', hA₂, hA, hM, Nat.lcm_one_right]
  let c₂ : Coeff l₂ :=
    { F := c'.F, fin := c'.fin, conj := c'.conj
      zeta_mem := by rw [hM']; exact hz
      le := by have h := c'.le; unfold KA at h ⊢; rw [hA₂]; exact h }
  obtain ⟨d, hdpd, hdI, hdl, -, -, -, hlev, -⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev _ T.Q.H (T.Q.Dw ((i : ℕ) + 1)) T.Q.l
    (T.Q.Xo ((i : ℕ) + 1)) c' hpq 0 pd I l₂ Xo₂ c₂ rfl hd hM hcop hMb hsup
  obtain ⟨σ', hσ'⟩ := GlobalTheory.CoverExists.exists_ext_of_le (K := T.Q.c.F) (L := L) hle T.σ₀
  let σ₂ : d.c₂.F →+* ℂ := σ'.comp (d.eF.symm : d.c₂.F →+* c'.F)
  have hσ₂ : σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF T.Q.c c' hle)) = T.σ₀ := by
    rw [← hσ']; ext x; simp [σ₂, incF]
  have hA1 : d.l₂.A = 1 := by rw [hdl, hA₂, hA]
  obtain ⟨U₂, dict₂, hU⟩ := GlobalTheory.T.exists_levelCover_uniformisation_dictionary D T hJ _ hj T.σ₀ hσ c' hle d σ₂ hlev hA1 hσ₂

  have hrange : (σ'.toRatAlgHom).fieldRange = L := fieldRange_of_normal L σ'
  have hsurj : ∀ y : L, ∃ z : d.c₂.F, σ₂ z = (y : ℂ) := by
    intro y
    have hy : (y : ℂ) ∈ (σ'.toRatAlgHom).fieldRange := by rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.1 hy
    exact ⟨d.eF x, by simp [σ₂, ← hx]⟩
  have hfr : σ₂.fieldRange = L.toSubfield := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      have : σ' (d.eF.symm z) ∈ (σ'.toRatAlgHom).fieldRange := AlgHom.mem_fieldRange.2 ⟨_, rfl⟩
      rw [hrange] at this
      exact this
    · intro hx
      obtain ⟨z, hz'⟩ := hsurj ⟨x, hx⟩
      exact ⟨z, hz'⟩
  have hsm₂ : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SmallIn R i σ₂ := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨y, hy⟩ := hsm.1 v hv
      obtain ⟨z, hz'⟩ := hsurj y
      exact ⟨z, hz'.trans hy⟩
    · obtain ⟨y, hy⟩ := hsm.2 v hv
      obtain ⟨z, hz'⟩ := hsurj y
      exact ⟨z, hz'.trans hy⟩
  let C₀ : Cover T ((i : ℕ) + 1) T.σ₀ := ⟨c', hle, d, σ₂, U₂, dict₂, fun _ => 1⟩
  have hdom : ∀ m, Even m → Dom (0 : (D.host.E →+* ℂ) × ℕ → ℕ) m := fun m hm =>
    ⟨fun _ _ _ _ => le_rfl, hm⟩
  have hauxd : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M d.pd := hdpd ▸ haux
  by_cases hn : Even n
  · obtain ⟨cc₂, hcc⟩ := GlobalTheory.T.uniformisedLevelCover_exists_constants_dominantWeights D T hJ _ hj T.σ₀ hσ C₀ (hU _) n
    refine ⟨⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩, hdpd, hdI, hfr, hU cc₂, hcc, hauxd, hsm₂, ?_⟩
    show GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * d.pd) σ₂.fieldRange
    rw [hfr, hdpd]; exact hray
  · obtain ⟨cc₂, hcc⟩ := GlobalTheory.T.uniformisedLevelCover_exists_constants_dominantWeights D T hJ _ hj T.σ₀ hσ C₀ (hU _) 0
    refine ⟨⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩, hdpd, hdI, hfr, hU cc₂, fun a ha => absurd ha.2 hn, hauxd, hsm₂, ?_⟩
    show GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * d.pd) σ₂.fieldRange
    rw [hfr, hdpd]; exact hray

end GlobalTheory.CoverGalois
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelPointRepsConjugateHalfModLattice
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
namespace GlobalTheory.FlipReps

theorem flip_reps : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) ∧ (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') ∧ (∀ y : WO V W, IsHalf (cA D eT) y → m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → ∃ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) ∧ Y.card = flipIdx V W T m := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT
  obtain ⟨-, -, -, -, hSV, hSW, -⟩ := hP
  have hm0 : 0 < m := hm.pos
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hT
  set Λ := latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) with hΛ
  have hcard : Nat.card (GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m) = flipIdx V W T m := by
    have hc' : cA D eT = ∑ PP ∈ T, cA D (es PP) := by rw [hsum, map_sum]
    rw [hc', GlobalTheory.T.card_divisionPointsModHalfLattice_finset_sum Λ (fun c hc u hu => GlobalTheory.PlaceModelSum.idem_smul_latO hc hu) T (fun PP => cA D (es PP)) ?_ ?_ m]
    · unfold flipIdx
      refine Finset.prod_congr rfl fun PP hPP => ?_
      have hi : Formalism.L2.NTheta.IsIdemAt (cA D (es PP)) (Formalism.L2.DIV.conjPl PP) :=
        GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun _ => Iff.rfl
      rw [GlobalTheory.T.card_divisionPoints_half_split_place_norm_pow D V W ΛV ΛW hSV hSW _ _ hi m hm0, GlobalTheory.T.absNorm_maxPowDividing_conjugatePlace]
    · intro i hi; rw [← map_mul, (hes i hi).1.1]
    · intro i hi j hj hij; rw [← map_mul, GlobalTheory.Tow.idemAt_orth (hes i hi) (hes j hj) hij, map_zero]
  have hfin : Finite (GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact flipIdx_ne_zero V W T hm0.ne')
  letI := Fintype.ofFinite (GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m)
  have hhalf : ∀ y : WO V W, cA D eT • y = y → IsHalf (cA D eT) y := fun y hy =>
    (GlobalTheory.PlaceModel.isHalf_iff V W).2 ((GlobalTheory.PlaceModel.mem_half V W).2 hy)
  have hhalf' : ∀ y : WO V W, IsHalf (cA D eT) y → cA D eT • y = y := fun y hy =>
    (GlobalTheory.PlaceModel.mem_half V W).1 ((GlobalTheory.PlaceModel.isHalf_iff V W).1 hy)
  refine ⟨Finset.univ.image (fun q : GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m =>
    ((GlobalTheory.DivPtFourier.rep q : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W)), ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨hhalf _ (GlobalTheory.DivPtFourier.rep q).2.1, (GlobalTheory.DivPtFourier.rep q).2.2⟩
  · intro y hy y' hy' hyy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy'
    have hqq : q' = q := by
      rw [← GlobalTheory.DivPtFourier.mk_rep q, ← GlobalTheory.DivPtFourier.mk_rep q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine ⟨?_, ?_⟩
      · have : ((-GlobalTheory.DivPtFourier.rep q' + GlobalTheory.DivPtFourier.rep q : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) =
            ((GlobalTheory.DivPtFourier.rep q : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) -
              ((GlobalTheory.DivPtFourier.rep q' : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) := by
          push_cast; abel
        rw [this]; exact hyy
      · exact (GlobalTheory.PlaceModel.half V W (cA D eT)).add_mem ((GlobalTheory.PlaceModel.half V W (cA D eT)).neg_mem
          ((GlobalTheory.PlaceModel.mem_half V W).2 (GlobalTheory.DivPtFourier.rep q').2.1))
          ((GlobalTheory.PlaceModel.mem_half V W).2 (GlobalTheory.DivPtFourier.rep q).2.1)
    rw [hqq]
  · intro y hy hmy
    have hyd : y ∈ GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m := ⟨hhalf' y hy, hmy⟩
    set q : GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m := QuotientAddGroup.mk (⟨y, hyd⟩ : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m))
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ q), ?_⟩
    have h := GlobalTheory.DivPtFourier.mk_rep q
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have : ((-GlobalTheory.DivPtFourier.rep q + ⟨y, hyd⟩ : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) =
        y - ((GlobalTheory.DivPtFourier.rep q : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) := by
      push_cast; abel
    rw [← this]; exact h.1
  · rw [Finset.card_image_of_injective _ GlobalTheory.DivPtFourier.rep_injective, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]

end GlobalTheory.FlipReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPartDenominatorBoundedByPrimePowerStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPart_denominator_bounded_by_prime_power : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ l : ℕ, l.Prime → ∀ s : GA D V, ∃ c : ℕ, ∀ z : GA D V, OneAt V l z → ∀ (γ h : GA D V) (γ' : GL (Fin V.rank) D.host.E) (k : Bridge.Gf V) (bad : ℕ), GlobalTheory.Member.IsRat V γ γ' → l ∣ bad → SplitOffBad V bad h → Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank → Bridge.hLat V k⁻¹ = Formalism.L2.Pj.stdLat D.host.E V.rank → fin V (s * z) = fin V γ * fin V h * k → DenomAt l c γ' := by
  first | exact @GlobalTheory.MoveDenom.denomAt_of_move | exact GlobalTheory.MoveDenom.denomAt_of_move | (intros; apply GlobalTheory.MoveDenom.denomAt_of_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowClosureLinking
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem linkN_row : Hypotheses₂ → ∀ (Q : GlobalTheory.Mem.Top.V4.Slot) (Lk : GlobalTheory.Fc.LkT GlobalTheory.Fc.Bundle) (C : ℝ) (CT : ℕ), 0 ≤ C →
    GlobalTheory.Fc.RowE Q Lk (fun _ D O _ _ => GlobalTheory.NFacts.Facts D O.ex.nch ∧ Extra D C CT) →
    GlobalTheory.Fc.R1.PredicateAtBundlePoints Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) →
    GlobalTheory.Fc.R1.PredicateAtBundlePoints Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  intro hP Q Lk C CT hC hE h23
  refine ((GlobalTheory.Fc.RowE.row hE).and h23).imp fun 𝒜 σ _ hh => ?_
  obtain ⟨hA, ε1, hε, hcl⟩ := hh
  refine ⟨ε1, hε, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := hcl e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  have hF : FactsF Fm C CT := fun x hx i => hA Fm (GlobalTheory.Cp.d3_a hc) x hx i
  exact GlobalTheory.T.linkN_along_family_of_localBounds Fm (GlobalTheory.T.conclusion_of_family_facts hP Fm C CT hC hc.1.2 hF (hK Fm CH hc hL))

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceCombinationCoverFormIntegralOverPrimeStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceCombination_coverForm_integral_over_prime : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)), (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → ∀ (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) (β k) ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)) → (∀ k, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (β k)) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ N : ℕ, ∀ b : 𝓞 C.d.c₂.F, (∀ la' : HeightOneSpectrum (𝓞 C.d.c₂.F), la' ≠ la → (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la'.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → b ∈ la'.asIdeal ^ N) → ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (∑ k, (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) • β k) := by
  first | exact @GlobalTheory.TraceIdem.trace_comb_integral | exact GlobalTheory.TraceIdem.trace_comb_integral | (intros; apply GlobalTheory.TraceIdem.trace_comb_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulPartialRankinSelbergL
section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ GlobalTheory.ZEul Filter Topology Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.ZEul.Smooth

theorem zint_eq_mul_partialL_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) → (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ (N : ℕ) (Φ : (Fin a → Cinf E) → ℂ) (π π' : CuspSub E a) (φ φ' : GA E a → ℂ), CG.mk π = σ ∧ CG.mk π' = σ' ∧ φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ (∀ ℓ : Fin a, (ℓ : ℕ) + 1 = a → tsupport Φ ⊆ {u | ∀ w, u ℓ w ≠ 0}) ∧ ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ φ Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ' φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ' w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  intro E _ _ _ a σ σ' ha hσ hσ' T hTs hψ hT hT'
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨α, _ℓ, _Φ, _J, _η, π, ω, _φ, hα, hπ, hω, hωc, _h1, _h2, _h3, _h4, _h5, _h6, _h7, hZ⟩ := GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m + 1) σ ha hσ T hT
  obtain ⟨α', _ℓ', _Φ', _J', _η', π', ω', _φ', hα', hπ', hω', hωc', _h1', _h2', _h3', _h4', _h5', _h6', _h7', hZ'⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m + 1) σ' ha hσ' T hT'
  subst hπ hπ'
  obtain ⟨μ₀, hμ₀, 𝓕₁, h𝓕₁⟩ : ∃ (μ : Measure (GA E (m + 1))) (_ : μ.IsHaarMeasure) (𝓕 : Set (GA E (m + 1))),
      IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ := by
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
    haveI : DiscreteTopology (ratGL E (m + 1)).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E (m + 1)
    obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E (m + 1)).range
    exact ⟨Measure.haar, inferInstance, 𝓕, h𝓕 _⟩
  have hfin : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ μ₀ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  have hfin' : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α' w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ' μ₀ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  classical
  let αe : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ := fun w => if h : w ∉ T then α ⟨w, h⟩ else fun _ => 1
  let αe' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ := fun w => if h : w ∉ T then α' ⟨w, h⟩ else fun _ => 1
  have hαe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe w.1 = α w := fun w => dif_pos w.2
  have hαe' : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe' w.1 = α' w := fun w => dif_pos w.2
  have hsatσ : ∀ (ρ : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk ρ).HasSat w B) →
      HasSatGL w (ρ.locRep w) (sat (CG.mk ρ) w) := fun ρ w h => by
    rw [← CG.hasSat_mk, sat, dif_pos h]
    exact h.choose_spec
  have hs : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, Finset.univ.val.map (αe w.1) = sat (CG.mk π) w.1 := fun w => by
    rw [hαe w]; exact hα w
  have hs' : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, Finset.univ.val.map (αe' w.1) = sat (CG.mk π') w.1 := fun w => by
    rw [hαe' w]; exact hα' w
  have hsat : ∀ w ∉ T, HasSatGL w (π.locRep w) (Finset.univ.val.map (αe w)) := fun w hw => by
    rw [hs ⟨w, hw⟩]; exact hsatσ π w (hT w hw)
  have hsat' : ∀ w ∉ T, HasSatGL w (π'.locRep w) (Finset.univ.val.map (αe' w)) := fun w hw => by
    rw [hs' ⟨w, hw⟩]; exact hsatσ π' w (hT' w hw)
  obtain ⟨b, hb1, hbN, hbC, hbF⟩ := GlobalTheory.T.exists_bump_shintani_alt E m T hψ
  obtain ⟨φ, hφR, hU, hK, hW⟩ := hbF π αe hsat
  obtain ⟨φ', hφR', hU', hK', hW'⟩ := hbF π' αe' hsat'
  obtain ⟨hφ0, hφ0', N, Φ, hN, hΦc, hΦs, hΦr, hΦp, hC2⟩ := GlobalTheory.T.unfolded_polarised_integral_bumped_forms E m T hTs hψ b hb1 hbN hbC π π' ω ω' hω hω' hωc hωc' αe αe'
    hsat hsat' φ φ' hφR hφR' hU hK hU' hK' hW hW'
  refine ⟨N, Φ, π, π', φ, φ', rfl, rfl, hφR, hφR', hφ0, hφ0', hN, hΦc, hΦs, ?_, ?_⟩
  · intro ℓ hℓ
    have hl : ℓ = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hl
    exact hΦr
  intro μ hμ 𝓕 h𝓕
  obtain ⟨𝓕₀, h𝓕₀⟩ := GlobalTheory.ZEul.exists_fundamentalDomain_NE E (m + 1) μ
  obtain ⟨c, hc, hC1⟩ := GlobalTheory.T.polarisedThetaIntegral_unfold_whittaker E m μ
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hid⟩ := hC2 μ 𝓕₀ h𝓕₀
  obtain ⟨hdiff, hreal⟩ := GlobalTheory.T.exp_integral_differentiable_real_re_pos (μ.restrict 𝓕₀) f t hfm htm hf0 hfi hR
  refine ⟨fun s => (c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (s * t g) ∂μ, (differentiable_const _).mul hdiff, ?_, ?_⟩
  · intro x
    obtain ⟨him, hre⟩ := hreal x
    have hre' := hre hfpos
    refine ⟨?_, ?_⟩
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_pos hc hre'
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, him, mul_zero]
  · intro x hx
    have hq : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, 2 ≤ Ideal.absNorm w.1.asIdeal :=
      fun w => HeightOneSpectrum.one_lt_absNorm w.1
    have e1 : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m + 1)) => ((αe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α w i : ℂˣ) : ℂ) := by funext w i; rw [hαe w]
    have e1' : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m + 1)) => ((αe' w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α' w i : ℂˣ) : ℂ) := by funext w i; rw [hαe' w]
    have hf1 : GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
        (fun w i => ((αe w.1 i : ℂˣ) : ℂ)) x ≠ ⊤ := by rw [e1]; exact hfin x hx
    have hf1' : GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
        (fun w i => ((αe' w.1 i : ℂˣ) : ℂ)) x ≠ ⊤ := by rw [e1']; exact hfin' x hx
    obtain ⟨hd, hd', e12, e11, e22⟩ := hid x hx hf1 hf1'
    have z12 := (hC1 π π' ω ω' hω hω' hωc hωc' φ φ' hφR hφR' N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd hd').2
    have z11 := (hC1 π π ω ω hω hω hωc hωc φ φ hφR hφR N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd hd).2
    have z22 := (hC1 π' π' ω' ω' hω' hω' hωc' hωc' φ' φ' hφR' hφR' N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd' hd').2
    have A12 := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe w.1) (fun w => αe' w.1) x hx hq hf1 hf1').tsum_eq
    have A11 := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe w.1) (fun w => αe w.1) x hx hq hf1 hf1).tsum_eq
    have A22 := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe' w.1) (fun w => αe' w.1) x hx hq hf1' hf1').tsum_eq
    simp only [hs, hs'] at A12 A11 A22
    refine ⟨?_, ?_, ?_⟩
    · rw [z12, e12, A12]; ring
    · rw [z11, e11, A11]; ring
    · rw [z22, e22, A22]; ring

end GlobalTheory.ZEul.Smooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsOnePlaceStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_descent_integral_forms_one_place : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ la : HeightOneSpectrum (𝓞 C.d.c₂.F), ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc {la} → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n {la}, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a := by
  first | exact @GlobalTheory.DescLoc.desc_loc | exact GlobalTheory.DescLoc.desc_loc | (intros; apply GlobalTheory.DescLoc.desc_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumIdentityConstantsCoverOfDominantPinsStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumIdentityConstants_cover_of_dominantPins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ ph : ℂ, ‖ph‖ = 1 → BaseCc T R i hV ph → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → (∀ a, Dom a (κ i).n → C.IsPinned a (κ i).n) → CovCc T R i hV ph C := by
  first | exact @GlobalTheory.LevelSeries.covCc_of_pinned | exact GlobalTheory.LevelSeries.covCc_of_pinned | (intros; apply GlobalTheory.LevelSeries.covCc_of_pinned <;> assumption)
end

