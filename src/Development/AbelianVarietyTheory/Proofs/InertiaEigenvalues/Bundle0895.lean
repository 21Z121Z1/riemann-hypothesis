import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0728
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0871
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0887
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0888
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroup
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstOfCrys

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem mulV_crisIncl_comm {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] (c : ↥(MaximalUnramifiedExtension l)) (x : P.R.B ⊗[ℚ_[l]] V) :
    mulV P LL V c (crisIncl P LL V (TensorProduct.comm ℚ_[l] P.R.B V x)) =
      crisIncl P LL V (TensorProduct.comm ℚ_[l] P.R.B V (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c • x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
    rw [TensorProduct.smul_tmul', TensorProduct.comm_tmul, TensorProduct.comm_tmul, crisIncl_tmul, crisIncl_tmul,
      mulV_tmul, Polynomial.algebraMap_apply, smul_eq_mul, C_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem isPst_of_isCrys (T : LocTied l P AI) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) (hc : IsCrys (P.PD K) ρ) : IsPst P ρ := by
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have hf := GlobalTheory.Per.TiedRestrict.fracInv_of_tied T K
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  have hup := GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg ρ
  obtain ⟨hfin, -⟩ := GlobalTheory.RegularRing.finite_le₀ (P.PD K) hf ρ
  have hd := (GlobalTheory.RegularRing.isCrys_iff_finrank (P.PD K) ρ).1 hc
  let e := Module.finBasisOfFinrankEq ↥(K0 K) _ hd
  have hB := GlobalTheory.RegularRing.indepB (P.PD K) hf ρ e e.linearIndependent
  have hmem : ∀ i, crisIncl P ↥LL.1 V (TensorProduct.comm ℚ_[l] P.R.B V (e i : P.R.B ⊗[ℚ_[l]] V)) ∈ Dpst P ρ := by
    intro i
    refine (mem_Dpst P ρ).mpr ⟨K, fun g _ => ?_⟩
    rw [stRep_crisIncl]
    congr 1
    exact (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.mem_Dcris (PD := P.PD K) ρ _).1 (e i).2 g
  let y : Fin (finrank ℚ_[l] V) → DpstUr P ρ := fun i => toUr P ρ ⟨_, hmem i⟩
  have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) y := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 : (((toUr P ρ).symm (∑ j, c j • y j) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = 0 := by
      rw [hc]; rfl
    have h2 : (((toUr P ρ).symm (∑ j, c j • y j) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
        crisIncl P ↥LL.1 V (TensorProduct.comm ℚ_[l] P.R.B V
          (∑ j, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j) • (e j : P.R.B ⊗[ℚ_[l]] V))) := by
      rw [map_sum, Submodule.coe_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mulV_crisIncl_comm]
      rfl
    rw [h2] at h1
    have h3 : ∑ j, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j) • (e j : P.R.B ⊗[ℚ_[l]] V) = 0 :=
      (TensorProduct.comm ℚ_[l] P.R.B V).injective
        (crisIncl_injective P (h1.trans (map_zero _).symm) |>.trans (map_zero _).symm)
    have h4 := Fintype.linearIndependent_iff.1 hB (fun j => algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j)) h3 i
    exact (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (h4.trans (map_zero _).symm)
  have hlow : (finrank ℚ_[l] V : Cardinal) ≤ Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) := by
    have := hli.cardinal_le_rank
    rwa [Cardinal.mk_fintype, Fintype.card_fin] at this
  have hV : Module.rank ℚ_[l] V = (finrank ℚ_[l] V : Cardinal) := (Module.finrank_eq_rank ℚ_[l] V).symm
  rw [IsPst, hV]
  exact le_antisymm hup hlow

end GlobalTheory.PstOfCrys

namespace GlobalTheory.PstOfCrys

theorem pst_of_pc : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) = algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c') (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) → GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) := by
  intro D i w hw K' h hN hF hS m r _ hpc
  let r' : ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)) →* GL (Fin m) ↥(D.nbr i w hw).LL.1 :=
    mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))
  have hmodel : IsModel (D.nbr i w hw)
      (resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) (D.nbr i w hw).LL r' := by
    refine ⟨le_rfl, ?_⟩
    ext g a b
    exact ((D.loc_tie i w hw).1 _).symm
  refine ⟨(D.nbr i w hw).LL, r', hmodel, ?_⟩
  have hc := ((GlobalTheory.PcRes.main _ (D.loc (D.nd.l i)) _ K' (D.nbr i w hw).LL h hN hF hS _ _).2).1 hpc
  have hp := isPst_of_isCrys (D.locT (D.nd.l i)) _ hc
  exact (GlobalTheory.PstLaws.isPst_resTo_iff (D.loc (D.nd.l i)) _ h).1 hp

end GlobalTheory.PstOfCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireGood
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.RSnmGood

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def contGood : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Continuous F ∧ GlobalTheory.MSpanDecay.Good F}
  zero_mem' := ⟨continuous_const, (GlobalTheory.MSpanDecay.goodSub E a).zero_mem⟩
  add_mem' := fun h h' => ⟨h.1.add h'.1, (GlobalTheory.MSpanDecay.goodSub E a).add_mem h.2 h'.2⟩
  smul_mem' := fun z _ h => ⟨h.1.const_smul z, (GlobalTheory.MSpanDecay.goodSub E a).smul_mem z h.2⟩

theorem mspanR_le_contGood (ha : 0 < a) {π : CuspSub E a} (hπ : π.IsUnitary) :
    GlobalTheory.JSW.mspanR π ≤ contGood E a := by
  refine sInf_le ⟨fun φ hφ => ?_, fun F hF h => ?_, fun F hF X _ ν hν k γ hk => ?_⟩
  · exact ⟨(GlobalTheory.RSnm.mem_goodFns ha hπ (Submodule.mem_sup_left ⟨φ, hφ, rfl⟩)).1, GlobalTheory.MSpanDecay.good_of_mem hπ hφ⟩
  · exact ⟨hF.1.comp (continuous_id.mul continuous_const), GlobalTheory.RtGood.good_mul_right E a F h hF.2⟩
  · haveI := hν
    refine ⟨?_, GlobalTheory.MSpanDecay.Good.kernel hF.2 hk⟩
    exact (GlobalTheory.JSW.kerOp_integrable_continuous E a X ν k γ hk ⟨F, hF.2.1⟩ hF.1
      (GlobalTheory.RSnm.bounded_of_decays ha hF.2.decays)).2

theorem mspanR_le_goodFns (ha : 0 < a) {π : CuspSub E a} (hπ : π.IsUnitary) :
    GlobalTheory.JSW.mspanR π ≤ GlobalTheory.RSnm.goodFns a := fun F hF =>
  ⟨(mspanR_le_contGood ha hπ hF).1, (mspanR_le_contGood ha hπ hF).2.decays,
    (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ.contra (GlobalTheory.JSW.invT_mem_mspanR_contra E a π F hF)).decays⟩

open GroundTheory.Automorphic in

theorem rsIntegral_entire_good {m n : ℕ} (hm0 : 0 < m) (hmn : m < n) {φ : GA E n → ℂ} (g1 : φ ∈ GlobalTheory.RSnm.goodFns n)
    {φ' : GA E m → ℂ} (g2 : φ' ∈ GlobalTheory.RSnm.goodFns m) {F : (Fin m → Ad E) → ℂ}
    (hF : F ∈ GJMatrix.schwartzBruhatPi E (Fin m)) (μ : Measure (GA E m)) [μ.IsHaarMeasure] {𝓕 : Set (GA E m)}
    (h𝓕 : IsFundamentalDomain (ratGL E m).range 𝓕 μ) :
    (∀ s : ℂ, IntegrableOn (GlobalTheory.RSnm.rsIntegrand m hmn.le F φ φ' s) 𝓕 μ) ∧
      ∀ s : ℂ, AnalyticAt ℂ (fun s => ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand m hmn.le F φ φ' s h ∂μ) s := by
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.RSnm.bounded_of_decays (hm0.trans hmn) g1.2.1
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.RSnm.bounded_of_decays hm0 g2.2.1
  set A : GA E m → ℂ := fun h => FourierWhittaker.partialCoeff (GlobalTheory.RSnm.colSmooth m F φ) (m + 1)
    (FourierWhittaker.blockGL hmn.le h) * (starRingEnd ℂ) (φ' h)
  have hAc : Continuous A :=
    ((FourierWhittaker.continuous_partialCoeff (GlobalTheory.RSnm.continuous_colSmooth hF g1.1 hC₁) (m + 1)).comp
      (GlobalTheory.RSnm.continuous_blockGL hmn.le)).mul (Complex.continuous_conj.comp g2.1)
  have hbd : ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖A h‖ ≤ C * (min (GlobalTheory.RSnm.detAbs h) (GlobalTheory.RSnm.detAbs h)⁻¹) ^ N := by
    intro N
    obtain ⟨C, hC⟩ := GlobalTheory.RSnm.colSmooth_bound hmn g1 hF N
    refine ⟨C * C₂, fun h => ?_⟩
    have hP := GlobalTheory.RSnm.partialCoeff_bound hmn (b := fun t => C * (min t t⁻¹) ^ N) hC (n - (m + 1)) (m + 1) (by omega)
      le_rfl _ (GlobalTheory.RSnm.inS_blockGL hmn h)
    simp only [GlobalTheory.RSnm.detAbs_blockGL] at hP
    rw [norm_mul, Complex.norm_conj]
    calc _ ≤ C * (min (GlobalTheory.RSnm.detAbs h) (GlobalTheory.RSnm.detAbs h)⁻¹) ^ N * C₂ :=
          mul_le_mul hP (hC₂ h) (norm_nonneg _) ((norm_nonneg _).trans hP)
      _ = _ := by ring
  obtain ⟨hI, hD⟩ := GlobalTheory.T.mellinType_integral_entire_of_rapid_decay (μ.restrict 𝓕) A GlobalTheory.RSnm.detAbs hAc.aestronglyMeasurable
    GlobalTheory.RSnm.continuous_detAbs.measurable GlobalTheory.RSnm.detAbs_pos (GlobalTheory.T.integrableOn_min_absDet_inv_fundamentalDomain E m hm0 μ 𝓕 h𝓕) hbd
  have e : ∀ s, GlobalTheory.RSnm.rsIntegrand m hmn.le F φ φ' s =
      fun h => A h * ((GlobalTheory.RSnm.detAbs h : ℝ) : ℂ) ^ (s - ((n : ℂ) - m) / 2) := fun s => rfl
  refine ⟨fun s => by rw [e]; exact hI _, fun s => ?_⟩
  simp only [e]
  exact (hD.analyticAt _).comp (analyticAt_id.sub analyticAt_const)

end GlobalTheory.RSnmGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralRsHatZero
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.RSResidue

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem mem_bddForms {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (h : π.HasCentChar ω) {φ : Sm E a}
    (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspan π) : φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω :=
  hφ.elim (fun h' => GlobalTheory.Petersson.mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω h h')
    (fun h' => GlobalTheory.JSWPos.mspan_le_bddForms hω h h')

theorem rsHat_zero {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (F F' : Sm E a) (hΦ : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) 0 =
      (∫ x, rsInf ℓ F.1 F'.1 Φ g x ∂infMeasure E a) * ((finiteMeasurePi E (latt a J)).toReal : ℂ) := by
  have h := rsHat_eq J η F F' hΦ g 0
  simp only [rsHat] at h
  rw [h]
  have h0 : (fun i => pFin E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have h1 : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have h2 : (latt a (traceDualIdeal E J)).indicator (1 : (Fin a → Af E) → ℂ) 0 = 1 :=
    Set.indicator_of_mem (s := latt a (traceDualIdeal E J)) (show (0 : Fin a → Af E) ∈ latt a (traceDualIdeal E J) from
      fun i => (idealFiniteAdeles (traceDualIdeal E J)).zero_mem) _
  rw [h0, h1, h2]
  simp [infFourier]

theorem setIntegral_mul_right {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕 μ) {f : GA E a → ℂ}
    (hf : ∀ γ ∈ latticeGL E a, ∀ g, f (γ * g) = f g) (h : GA E a) :
    ∫ g in 𝓕, f (g * h) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  haveI := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hmp : MeasurePreserving (fun g => g * h) μ μ := measurePreserving_mul_right μ h
  have e1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight h) f ((fun g => g * h⁻¹) ⁻¹' 𝓕)
  have e2 : (fun g => g * h) ⁻¹' ((fun g => g * h⁻¹) ⁻¹' 𝓕) = 𝓕 := by ext; simp
  rw [e2] at e1
  rw [e1]
  have h2 : IsFundamentalDomain (latticeGL E a) ((fun g => g * h⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ h⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  haveI : DiscreteTopology (latticeGL E a) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL
  have hI : GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) f := hf
  have A := (GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h2 (GlobalTheory.AutomorphicL2Unitary.descend (latticeGL E a) f)).trans
    (integral_congr_ae (Eventually.of_forall hI.descend_mk))
  have B := (GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕 (GlobalTheory.AutomorphicL2Unitary.descend (latticeGL E a) f)).trans
    (integral_congr_ae (Eventually.of_forall hI.descend_mk))
  exact A.symm.trans B

end GlobalTheory.RSResidue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalLocalFactorNormSqStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_local_factor_norm_sq : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α : Fin (n + 1) → ℂ) (x : ℝ) (ν : Fin (n + 1) → ℤ), 0 ≤ ν (Fin.last n) →
    ENNReal.ofReal ((q : ℝ) ^ GlobalTheory.CellDec.wtS (n + 1) ν) * ENNReal.ofReal ((q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) *
      ‖GlobalTheory.RSCell.sphZ q α ν‖ₑ ^ 2 = GlobalTheory.RSCell.locFac q α x ν := by
  first | exact @GlobalTheory.RSCell.locFac_eq_wtS_sphZ | exact GlobalTheory.RSCell.locFac_eq_wtS_sphZ | (intros; apply GlobalTheory.RSCell.locFac_eq_wtS_sphZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharacterTame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.PendOf.isTame_mu_plGw : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (S : Reading P.T), IsTrue P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu := by
  intro hL D P S hS i k v hw
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hc := hS.mu i _ hw j hjj
  have hc' : IsComp (P.tp.tup (D.nd.mu i) j) (D.naut.plGw k v) ((P.tp.tup (D.nd.mu i) j).loc (D.naut.plGw k v)) :=
    ⟨GlobalTheory.HeckeComp.smooth_loc _ _, fun _ => rfl⟩
  rw [GlobalTheory.HeckeComp.eq_of_isComp hc' hc]
  exact GlobalTheory.MuTameQS.isTame_loc (GlobalTheory.MuTameQS.tameAt_mul ((P.cf.isMu0 j).tame _) (P.tp.xi_tame _ _))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharacterUnitValue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TupleCharAtType

theorem natCast_notMem {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    {v : HeightOneSpectrum (𝓞 E)} (hv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal) : ((q : ℕ) : 𝓞 E) ∉ v.asIdeal := fun hv' => by
  obtain ⟨s, t, hst⟩ : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hst]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hv')

theorem isUnitAt_of_notMem {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} (u : 𝓞 E)
    (hu : (u : E) ≠ 0) (hv : u ∉ v.asIdeal) : IsUnitAt v (atFin v (Units.mk0 (u : E) hu)) := by
  show Valued.v ((u : E) : v.adicCompletion E) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv

theorem xi_unrAt {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (P : Pin hL D) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) :
    (P.tp.xi (D.nd.mu i)).UnrAt (D.naut.plGw k v) := by
  have hwg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hgp := D.host.g_prime k
  rw [D.nd.mu_w i, P.tp.xi_tw, D.nd.w_l i]

  have hdel : (P.cf.delAt (D.nd.l i)).UnrAt (D.naut.plGw k v) := by
    unfold CharFrame.delAt
    split_ifs
    · exact P.cf.isDel'.unr _ (natCast_notMem hgp D.host.pde'_prime (D.host.pde_ne_g k).2.symm hwg)
    · exact P.cf.isDel.unr _ (natCast_notMem hgp D.host.pde_prime (D.host.pde_ne_g k).1.symm hwg)

  have hpsi : (P.tp.psi (D.nd.w i)).UnrAt (D.naut.plGw k v) := by
    have hψ := P.tp.psi_is (D.nd.w i) (D.nd.w_tw i)
    by_cases hl : D.nd.l i = D.host.g k
    · intro x _
      refine hψ.atl _ ?_ x
      unfold OverP
      rw [D.nd.w_l i, hl]
      exact hwg
    · refine (hψ.ram _).2 ?_
      rw [← P.Q_eq i]
      have hlp : (D.nd.l i).Prime := (D.nd.lPrime i).out
      have hS : D.naut.plGw k v ∈ D.nd.S i := by
        rw [D.nd.S_def i]
        refine ⟨?_, natCast_notMem hgp hlp (Ne.symm hl) hwg⟩
        fin_cases k
        · exact Or.inl hwg
        · exact Or.inr (Or.inl hwg)
      exact Finset.disjoint_left.mp (D.nd.SQ_disj i) hS
  intro x hx
  rw [HChar.loc_mul, hdel x hx, hpsi x hx, mul_one]

theorem value : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (S : Reading P.T), IsTrue P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal → (((S i _ hw).mu (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = (((P.cf.mu0 j).locK (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  intro hL D P S hS i k v hw j hj u hu hnot
  rw [(hS.mu i _ hw j hj).2 (Units.mk0 (u : D.host.E) hu)]
  have hx := xi_unrAt P i k v _ (isUnitAt_of_notMem u hu hnot)
  show (((P.cf.mu0 j * P.tp.xi (D.nd.mu i)).loc (D.naut.plGw k v) (atFin _ (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = _
  rw [HChar.loc_mul, hx, mul_one]
  rfl

end GlobalTheory.TupleCharAtType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLocalComponentConjEqInverseTransposeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceLocalComponent_conj_eq_inverseTranspose : ∀ (D : D7) (n : ℕ) (π : NG.AutRep D.host.E n) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion D.host.E))), IsLocS π.S s σ →
    ∃ (κ : s.w.adicCompletion D.host.E ≃+* (GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E)
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
      Continuous κ ∧ (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) ∧
      IsLocS π.S (GlobalTheory.TypeTame.conjSP s) σ' ∧
      ∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a) := by
  first | exact @GlobalTheory.ConjLocComp.exists_isLocS_conjSP | exact GlobalTheory.ConjLocComp.exists_isLocS_conjSP | (intros; apply GlobalTheory.ConjLocComp.exists_isLocS_conjSP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdParabolicTwistedTraceSumNeZeroOfVector
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LevelType

theorem StdBlock.mul {p r : ℕ} {a : ℕ} {x y : GL (Fin r) (ZMod p)} (hx : StdBlock a x) (hy : StdBlock a y) :
    StdBlock a (x * y) := by
  intro i j hij
  rw [Units.val_mul, Matrix.mul_apply]
  by_cases hi : i.val ≤ a
  · have hj : ¬ a ≤ j.val := fun h => hij ⟨hi, h⟩
    have : ∀ k, y.val k j = if k = j then 1 else 0 := fun k => hy k j (fun h => hj h.2)
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hx i j hij
  · have : ∀ k, x.val i k = if i = k then 1 else 0 := fun k => hx i k (fun h => hi h.1)
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hy i j hij

theorem stdBlock_one {p r : ℕ} (a : ℕ) : StdBlock a (1 : GL (Fin r) (ZMod p)) := by
  intro i j _
  simp [Matrix.one_apply]

theorem stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (r a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (v : ρ), v ≠ 0 → StdVec ρ.ρ a θ v → stdTrace a θ ρ.character ≠ 0 := by
  intro p _ r a θ ρ v hv0 hv
  classical
  set S : Finset (GL (Fin r) (ZMod p)) := Finset.univ.filter (StdBlock a) with hS
  set c : GL (Fin r) (ZMod p) → ℂ := fun x => (((θ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) with hc
  have hcm : ∀ x y, c (x * y) = c x * c y := fun x y => by
    simp [hc, map_mul, mul_inv, Units.val_mul, mul_comm]
  set E : Module.End ℂ ρ := ∑ x ∈ S, c x • ρ.ρ x with hE
  have htr : stdTrace a θ ρ.character = LinearMap.trace ℂ ρ E := by
    rw [hE, map_sum, stdTrace, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp [FDRep.character, hc]
  have himg : ∀ x ∈ S, S.image (x * ·) = S := fun x hx => by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
      exact hx.mul hy
    · rw [Finset.card_image_of_injective _ (mul_right_injective x)]
  have hEE : E * E = (S.card : ℂ) • E := by
    have : ∀ x ∈ S, (c x • ρ.ρ x) * E = E := fun x hx => by
      rw [hE, Finset.mul_sum]
      conv_rhs => rw [← himg x hx]
      rw [Finset.sum_image (fun y _ z _ h => mul_left_cancel h)]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [smul_mul_smul_comm, ← map_mul, hcm x y]
    calc E * E = ∑ x ∈ S, (c x • ρ.ρ x) * E := by rw [hE, Finset.sum_mul]
      _ = ∑ x ∈ S, E := Finset.sum_congr rfl this
      _ = (S.card : ℂ) • E := by rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hEv : E v = (S.card : ℂ) • v := by
    rw [hE, LinearMap.sum_apply, Finset.sum_congr rfl (g := fun _ => v), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro x hx
    rw [LinearMap.smul_apply, hv x (by simpa [hS] using hx), smul_smul]
    simp [hc]
  have hcard : (S.card : ℂ) ≠ 0 := by
    have : (1 : GL (Fin r) (ZMod p)) ∈ S := by simpa [hS] using stdBlock_one (p := p) (r := r) a
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem this)
  set P : Module.End ℂ ρ := (S.card : ℂ)⁻¹ • E with hP
  have hPP : IsIdempotentElem P := by
    rw [IsIdempotentElem, hP, smul_mul_smul_comm, hEE, smul_smul]
    congr 1
    field_simp
  have hPv : P v = v := by
    rw [hP, LinearMap.smul_apply, hEv, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hP0 : P ≠ 0 := fun h => hv0 (by rw [← hPv, h, LinearMap.zero_apply])
  have htP : LinearMap.trace ℂ ρ P ≠ 0 := fun h => hP0 ((LinearMap.IsIdempotentElem.trace_eq_zero_iff hPP).1 h)
  rw [htr]
  have : E = (S.card : ℂ) • P := by rw [hP, smul_smul, mul_inv_cancel₀ hcard, one_smul]
  rw [this, map_smul, smul_eq_mul]
  exact mul_ne_zero hcard htP

end GlobalTheory.LevelType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationFinitePlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_generation_finitePlaces : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GenFin R i t := by
  first | exact @GlobalTheory.DownLift.GenFinite.genFin | exact GlobalTheory.DownLift.GenFinite.genFin | (intros; apply GlobalTheory.DownLift.GenFinite.genFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBoundedStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedIntegrand_measurable_invariant_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (φ φ' : GA E (m + 1) → ℂ)
    (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous Φ → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    Measurable (GlobalTheory.ZEul.uInt φ φ' Φ N x) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, GlobalTheory.ZEul.uInt φ φ' Φ N x (u * g) = GlobalTheory.ZEul.uInt φ φ' Φ N x g) ∧
    ∀ g, ‖GlobalTheory.ZEul.uInt φ φ' Φ N x g‖ ≤ (‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ + ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖) / 2 := by
  first | exact @GlobalTheory.ZEulProps.uInt_props | exact GlobalTheory.ZEulProps.uInt_props | (intros; apply GlobalTheory.ZEulProps.uInt_props <;> assumption)
end

