import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0671
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.LubinTateReciprocity
import GroundTheory.LocalFields.Existence
import GroundTheory.LocalFields.KroneckerWeber
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0689
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorMulLocalOperatorHasSum

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionPreservesCuspidal
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.CuspExt

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero h).charPol σ = 1 := by
  rw [WD.lpZero, WD.charPol_mk]
  exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree]; simp)

theorem charPol_sumList (l : List (WD h)) (σ : Weil h) :
    (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod := by
  induction l with
  | nil => simp [sumList, charPol_lpZero]
  | cons b l ih =>
    have : sumList (b :: l) = WD.lpSum b (sumList l) := rfl
    rw [this, WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {r : IrrGL (w.adicCompletion E) → WD h}

theorem nu_eq (H : CuspLaws a ha e r) {x : IrrGL (w.adicCompletion E)} (hx : x.IsCusp) (s : ℝ) :
    r (x.nu s) = (r x).lpTw s := by
  rw [IrrGL.nu, H.twist x hx, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

theorem charPol_seg (H : CuspLaws a ha e r) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).charPol σ
      = (Δ.ms.map fun y => (r y).charPol σ).prod := by
  rw [(GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (r Δ.first)).2 Δ.len σ, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (r (Δ.term j)).charPol σ = ((r Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, nu_eq H Δ.isCusp_first]
  change _ = ∏ j : Fin Δ.len, (fun y => (r y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((r Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

end GlobalTheory.LocLanglands.CuspExt

namespace GlobalTheory.LocLanglands

end GlobalTheory.LocLanglands

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingAdmittedHypothesesAllStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLifting_admittedHypotheses_all : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ElementDenominator.Adm2 D HW F := by
  first | exact @GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt | exact GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt | (intros; apply GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalOperatorScalarOnSphericalEigenspaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOperator_scalar_on_sphericalEigenspace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, BadSupp R i t → LevFix R i t → LocSmall R i t → LevProd R i → TransLaws R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ c, ∀ y ∈ part R i ∅ c, ∀ v, ∃ z : ℂ, Eu.Zop R i t μ 𝓕 v y = z • y := by
  first | exact @GlobalTheory.RawLift.Eig.zop_eigen | exact GlobalTheory.RawLift.Eig.zop_eigen | (intros; apply GlobalTheory.RawLift.Eig.zop_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTorsionGaloisAction
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem localArtinMap_unitUniformizerPow_lubinTateTorsion
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (Ω : Type) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [Algebra K Ω]
    [ValuativeExtension K Ω] [IsSepClosure K Ω] {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}
    (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) (k : ℤ) (n : ℕ) (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) :
    x ∈ lubinTateTorsion Ω (hπ := hπ) hf n →
    ∃ hz : x.val ∈ maximalAbelianExtension K Ω,
      ((localArtinMap K Ω (unitUniformizerPow hπ u k) ⟨x.val, hz⟩ : maximalAbelianExtension K Ω) : Ω) =
        (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x).val := by
  intro hx
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K

  have hx' : x ∈ lubinTateTorsion Ω (hπ := hπ) hf (n + 1) := by
    rw [mem_lubinTateTorsion] at hx ⊢
    rw [pow_succ', mul_smul, hx, smul_zero]
  have hab : IsAbelianGalois K (lubinTateField Ω hπ hf (n + 1) ⊔ ⊥ : IntermediateField K Ω) := by
    rw [sup_bot_eq]
    exact isAbelianGalois_of_mul_comm _ (lubinTateField_mul_comm hπ hf (n + 1))
  have hmem : x.val ∈ (lubinTateField Ω hπ hf (n + 1) ⊔ ⊥ : IntermediateField K Ω) :=
    le_sup_left (a := lubinTateField Ω hπ hf (n + 1)) (val_mem_lubinTateField hπ hf hx')
  refine ⟨le_maximalAbelianExtension _ hmem, ?_⟩
  obtain ⟨τ, hτd, hτ⟩ := exists_lubinTate_action (Ω := Ω) hπ hf n.succ_pos u k
  have h := restrictAb_localArtinMap_lubinTate hπ hf n.succ_pos ⊥ bot_le u k τ hτd hτ
  have e := congrArg (fun σ => (((σ ⟨x.val, hmem⟩ :
    (lubinTateField Ω hπ hf (n + 1) ⊔ ⊥ : IntermediateField K Ω))) : Ω)) h
  rw [restrictAb_apply, AlgEquiv.restrictNormalHom_apply] at e
  rw [e, ← lubinTateGalPointMap_val, hτ x hx']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeOfFrameMatrixIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.IntHalfLat

open GlobalTheory.AdelicLatMove

variable {D : D7}

theorem hatSelfDual {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : IsSelfDualC V Λ) :
    GlobalTheory.ParahoricLift.HatSelfDual D.sp.cm.sig V.gram Λ := by
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have h1 : ∀ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun _ h => Formalism.UG.P.csDual_sig_mem D.sp.cm.sig h
  have h2 : ∀ z, z ∈ GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ↔
      GlobalTheory.LevSplit.swp D.host.F D.host.E z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z
    rw [← GlobalTheory.LatDual.integralTensorAdeles_eq_adelicCompletion_one]
    exact GlobalTheory.IdemSupport.mem_intAE_iff z
  have h3 : ∀ x, D.sp.cm.sig x = GlobalTheory.Member.cF D x := fun _ => rfl
  refine GlobalTheory.ParahoricLift.hatL_selfDual_gen (GlobalTheory.Member.cF D) D.sp.cm.sig h3 V.gram Λ hΛ.1.fg hΛ.1.span_eq_top hcc hG hdet
    (fun v => ?_) h1 h2
  rw [hΛ.2 v]
  refine forall₂_congr fun y _ => ?_
  rw [FractionalIdeal.mem_one_iff]
  have e : (∑ a, ∑ b, v a * V.gramᵀ a b * GlobalTheory.Member.cF D (y b)) = ∑ i, ∑ j, star (y i) * V.gram i j * v j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.transpose_apply, show GlobalTheory.Member.cF D (y a) = star (y a) from rfl]
    ring
  rw [e]

theorem cF_cF (z : EAf D) : cF D (cF D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e α => rw [cF_tmul, cF_tmul, star_star]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cF_eToEAf (x : D.host.E) : cF D (eToEAf D x) = eToEAf D (star x) := rfl

theorem exists_dual {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : IsSelfDualC V Λ)
    {β : GL (Fin V.rank) (EAf D)} (hβ : IsFrame β Λ) (j : Fin V.rank) :
    ∃ s ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, ∀ l, ∑ k, cF D (s k) * eToEAf D (V.gram k l) = (β⁻¹).val j l := by
  set Z : Matrix (Fin V.rank) (Fin V.rank) (EAf D) := (β⁻¹).val * (V.gram⁻¹).map (eToEAf D) with hZ
  have hZG : Z * V.gram.map (eToEAf D) = (β⁻¹).val := by
    rw [hZ, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit V),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have hrow : ∀ l, ∑ k, cF D (cF D (Z j k)) * eToEAf D (V.gram k l) = (β⁻¹).val j l := fun l => by
    rw [← hZG, Matrix.mul_apply]
    simp only [cF_cF, Matrix.map_apply]
  refine ⟨fun k => cF D (Z j k), (hatSelfDual hΛ _).2 fun z hz => ?_, hrow⟩
  have h1 : cF D (((β⁻¹).val *ᵥ z) j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    Formalism.UG.P.csDual_sig_mem D.sp.cm.sig ((hβ z).1 hz j)
  have e : cF D (((β⁻¹).val *ᵥ z) j) = ∑ a, ∑ b, cF D (z a) * eToEAf D (V.gram a b) * cF D (Z j b) := by
    rw [Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hrow a, map_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, cF_cF, cF_eToEAf, GlobalTheory.LatVac.gram_star]
    ring
  rw [e] at h1
  exact h1

theorem smul_mem_lat {S T : HSp D} {F : Frame S T} (hF : F.Good) {e : AE D} {P : Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (hP : FractionalIdeal.count D.host.E P D.host.AA = 0) {x : WO S T}
    (hx : IsIntM (frMapO S T F.βS F.βT x)) : e • x ∈ F.lat := by
  obtain ⟨a, ha, haA⟩ := GlobalTheory.fractionalIdeal_exists_int_not_mem_of_count_eq_zero P D.host.AA
    (GlobalTheory.SplitHomLattice.ideal_ne_zero D) hP
  have ha0 : a ≠ 0 := fun h => ha (h ▸ zero_mem _)
  have ha' : (a : D.host.E) ≠ 0 := by exact_mod_cast ha0
  have hw : finPart D (e * incA D ((a : D.host.E))⁻¹) ∈ intAE D := by
    by_contra h
    exact ha ((he.2 a ha0).2 h)
  choose s hs hs' using exists_dual hF.sdS hF.frS
  set Y : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := x.map (toEAf D) * F.βS.val with hY
  have ht : ∀ j, (fun i => Y i j) ∈ Formalism.L2.Herm.hatL (F := D.host.F) F.ΛT := fun j => by
    refine (hF.frT _).2 fun i => ?_
    have e1 : ((F.βT⁻¹).val *ᵥ fun i => Y i j) i = frMapO S T F.βS F.βT x i j := by
      rw [frMapO, Matrix.mul_assoc]
      rfl
    rw [e1]
    exact hx i j
  have hU := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hw _
    (sum_mem fun j (_ : j ∈ Finset.univ) => rankOne_mem_latO S T F.ΛS F.ΛT (a : D.host.E) haA (s j) (hs j) _ (ht j))
  convert hU using 1
  ext i l
  have hYZ : ∑ j, Y i j * (F.βS⁻¹).val j l = toEAf D (x i l) := by
    rw [← Matrix.mul_apply, hY, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Matrix.map_apply]
  have hsum : (∑ j, rankOne S T (a : D.host.E) (s j) fun i => Y i j) i l =
      incA D (a : D.host.E) * x i l * finEmb D 1 := by
    rw [Matrix.sum_apply, ← finEmb_mul, mul_one, map_mul, toEAf_incA, ← hYZ, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rankOne, Matrix.of_apply, hs' j l, mul_assoc]
  have h1 : e * finEmb D 1 = e := GlobalTheory.PlaceDatum.mul_pair_one (GlobalTheory.SplitScalar.infPart_splitIdem he.1)
  have h2 : incA D ((a : D.host.E))⁻¹ * incA D (a : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha', map_one]
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, hsum]
  linear_combination (-(x i l)) * h1 - (e * x i l * finEmb D 1) * h2

theorem mem_lat_of_frMapO_int : ∀ {D : D7} {S T : HSp D} {F : Frame S T}, F.Good → ∀ {R : Finset (Pl D.host.E)},
    PlacesOK ∅ R → ∀ {x : WO S T}, IsHalf (idem R) x → IsIntM (frMapO S T F.βS F.βT x) → x ∈ F.lat := by
  intro D S T F hF R hR x hx hi
  have e : x = ∑ PP ∈ R, idemAt PP • x := by
    rw [← Finset.sum_smul]
    exact (Matrix.ext fun i j => hx i j).symm
  rw [e]
  refine sum_mem fun PP hPP => ?_
  obtain ⟨P, -, hRP, hP⟩ := hR.split
  exact smul_mem_lat hF (hP.isIdemAt (hRP hPP)) (hR.prime PP (Or.inr hPP) PP (Or.inl rfl)) hi

end GlobalTheory.IntHalfLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallRingEquivFixed
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

namespace GlobalTheory.FixedAlgebraic

theorem mem_of_forall_ringEquiv_fixed :
    ∀ (K : Subfield ℂ) (x : ℂ), IsAlgebraic ℚ x →
      (∀ τ : ℂ ≃+* ℂ, (∀ y ∈ K, τ y = y) → τ x = x) → x ∈ K := by
  intro K x _ hx
  obtain ⟨y, hy⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := K) x
    fun σ => hx σ.toRingEquiv fun y hy => σ.commutes ⟨y, hy⟩
  rw [← hy]
  exact y.2

end GlobalTheory.FixedAlgebraic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicDetCharacterFunctionConjStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicDetCharacterFunction_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ) (x : G), ∃ a' : Fin D.R.r → kP PP.1, a' ≠ 0 ∧ ∀ g, mirC R i PP a tr ε (x * g * x⁻¹) = mirC R i PP a' tr ε g := by
  first | exact @GlobalTheory.DownLift.GenFinite.mirC_conj | exact GlobalTheory.DownLift.GenFinite.mirC_conj | (intros; apply GlobalTheory.DownLift.GenFinite.mirC_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSameSatakeParametersStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_equiv_of_same_satakeParameters : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (α : Fin n → ℂˣ) (π π' : IrrRep (GL (Fin n) k)), HasSatake π.ρ α → HasSatake π'.ρ α → Nonempty (π.ρ.Equiv π'.ρ) := by
  first | exact @GlobalTheory.SmGL.SphUniq.equiv_of_hasSatake | exact GlobalTheory.SmGL.SphUniq.equiv_of_hasSatake | (intros; apply GlobalTheory.SmGL.SphUniq.equiv_of_hasSatake <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

variable {D : D7}

abbrev OI (v : FinPl D) : Type := v.adicCompletionIntegers D.host.F

def InvForm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u, IsHalf e u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f

def InPow {v : FinPl D} (ϖ : OI v) (N : ℕ) {m n : Type} (x : Matrix m n (Fv D.host.F v)) : Prop :=
  ∀ i j, ∃ o : OI v, x i j = algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N * o)

def Bdd {v : FinPl D} (ϖ : OI v) (N : ℕ) {m n : Type} (x : Matrix m n (Fv D.host.F v)) : Prop :=
  ∀ i j, ∃ o : OI v, algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N) * x i j = algebraMap (OI v) (Fv D.host.F v) o

def comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  c.sum fun u z => z • heisO ψ S T u f

def RelOff (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Sb : Finset (FinPl D)) (p f : WO S T → ℂ) : Prop :=
  ∀ c : WO S T →₀ ℂ, (∀ u ∈ c.support, OffPl Sb u) → comb ψ S T c p = 0 → comb ψ S T c f = 0

def CoEig (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (p f : WO S T → ℂ) (u : WO S T) : Prop :=
  ∃ c : ℂ, heisO ψ S T u p = c • p ∧ heisO ψ S T u f = c • f

def Shape (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (A : Set (WO S T)) (x₀ : WO S T) (f : WO S T → ℂ) : Prop :=
  (∀ z ∈ A, heisO ψ S T z f = f) ∧
    ∀ y, IsHalf e y → (∀ z ∈ A, ψ (symplO S T z y) = 1) → heisO ψ S T y f = ψ (symplO S T x₀ y) • f

def halfPow {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) (ϖ : OI v) (N : ℕ) : Set (WO S T) :=
  {z | IsHalf (cA D e) z ∧ InPow ϖ N (adjCo φ S T BS BT z)}

def rowIx {n r t : ℕ} (h : r + t = n) : Fin r ⊕ Fin t ≃ Fin n := finSumFinEquiv.trans (finCongr h)

def co {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) {r t : ℕ} (hS : r + t = S.rank) (hT : r = T.rank) (x : WO S T) :
    Matrix (Fin r ⊕ Fin t) (Fin r) (Fv D.host.F v) :=
  (adjCo φ S T BS BT x).submatrix (rowIx hS) (finCongr hT)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rank_V (i : Fin D.R.m) : D.R.r + D.R.t = (Vc D i).rank := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm

theorem rank_weight_component_eq (i : Fin D.R.m) : D.R.r = (Wc D i).rank := (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).symm

def coR (R : RealDat D A Ks) (i : Fin D.R.m) {v : FinPl D} (φ : SplitProj D v) (x : WO (Vc D i) (Wc D i)) :
    Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) :=
  co φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (rank_V i) (rank_weight_component_eq i) x

def ActAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : Pl D.host.E) {v : FinPl D} (φ : SplitProj D v) (e : AE D)
    (red : OI v →+* kP PP) : Prop :=
  ∀ h : GL (Fin (Vc D i).rank) (OI v), ∃ κ : GA D (Vc D i), Formalism.L2.Theta.SuppAt e (Vc D i) κ ∧ κ ∈ GfC (Vc D i) ∧
    finE (Vc D i) κ ∈ Formalism.L2.DIV.St (R.βV i) ∧
    grpCo φ (Vc D i) (frCo φ (R.βV i)) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h ∧
    redFn (R.βV i) PP (finE (Vc D i) κ) = Matrix.GeneralLinearGroup.map red h ∧
    (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) ∧
    ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      ℓ (R.ωP i t (κ, 1) f) = ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map red h)) : ℂˣ) : ℂ) * ℓ f

theorem placeIdem_eq {v : FinPl D} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    algebraMap (AF D.host.F) (AE D) ε = idem D (.inl v) := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  obtain ⟨α', e', h1', h2'⟩ := ((GlobalTheory.PlaceTensor.idem_spec D).2.2.2.1 v).2.2
  have : α = α' := by
    apply Subtype.ext
    funext w
    by_cases hw : w = v
    · subst hw; exact h1.trans h1'.symm
    · exact (h2 w hw).trans (h2' w hw).symm
  rw [this, ← e']
  rfl

theorem suppIn_of_suppAt {v : FinPl D} {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) {Sb : Finset (FinPl D)}
    (hv : v ∈ Sb) {V : HSp D} {g : GA D V} (hg : Formalism.L2.Theta.SuppAt e V g) : SuppIn Sb V g := by
  obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  have hg' : ∀ i j, idem D (.inl v) * (Formalism.L2.Theta.mt V g - 1) i j = (Formalism.L2.Theta.mt V g - 1) i j := fun i j => by
    rw [← he.2.1]; exact hg i j
  refine ⟨Matrix.ext fun i j => ?_, fun w hw ε hε i j => ?_⟩
  · rw [Matrix.map_apply, ← hg', map_mul, (h4 v).1, zero_mul]; rfl
  · rw [placeIdem_eq hε, ← hg', ← mul_assoc, h2 _ _ (fun h => hw (by rw [Sum.inl.inj h]; exact hv)), zero_mul]

end GlobalTheory.DownLift.GenSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalUnitaryLagrangianActionEqOfMemFrameUnipoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalUnitaryLagrangianAction_eq_of_mem_frameUnipotent : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ n : GQ W, (n : GA D W) ∈ NI W I → GlobalTheory.RallisCusp.lagAct W n Y = Y := by
  first | exact @GlobalTheory.RallisCuspStab.lagAct_eq_of_mem_NI | exact GlobalTheory.RallisCuspStab.lagAct_eq_of_mem_NI | (intros; apply GlobalTheory.RallisCuspStab.lagAct_eq_of_mem_NI <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorFamilyProdUpdateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslateOperator_familyProd_update : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i, TransLaws R i → ∀ (F : ∀ v, Eu.LX R i v), {w | F w ≠ Eu.lx0 R i w}.Finite → ∀ v, F v = Eu.lx0 R i v → Eu.famProd R i F ∈ GfC (Wc D i) ∧ ∀ x : Eu.LX R i v, Eu.Bop R i (Eu.famProd R i (Function.update F v x)) = Eu.Bop R i (Eu.famProd R i F * Eu.rep x) := by
  first | exact @GlobalTheory.RawLift.Eu.bop_famProd_update | exact GlobalTheory.RawLift.Eu.bop_famProd_update | (intros; apply GlobalTheory.RawLift.Eu.bop_famProd_update <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorMulLocalOperatorHasSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslateOperator_mul_localOperator_hasSum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → TransLaws R i → LevFix R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ v, ∀ γ ∈ GfC (Wc D i), HasSum (fun x : Eu.LX R i v => Eu.acoef R i t μ 𝓕 v x • Eu.Bop R i (γ * Eu.rep x)) (Eu.Bop R i γ * Eu.Zop R i t μ 𝓕 v) := by
  first | exact @GlobalTheory.RawLift.Eu.bop_mul_zop_hasSum | exact GlobalTheory.RawLift.Eu.bop_mul_zop_hasSum | (intros; apply GlobalTheory.RawLift.Eu.bop_mul_zop_hasSum <;> assumption)
end

