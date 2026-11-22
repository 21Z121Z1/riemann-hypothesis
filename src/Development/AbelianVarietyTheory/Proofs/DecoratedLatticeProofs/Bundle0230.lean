import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealLastStageNormalizedOfScalarHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTwNorm

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem orZero_of {X : Type} [Zero X] {p : X → Prop} {x : X} (hx : p x) : OrZero p x :=
  ⟨fun _ => hx, fun hn => absurd ⟨x, hx⟩ hn⟩

theorem baseW_of_given (hG : Given R F) : R.BaseW F := by
  obtain ⟨lev, grp, fam, models, chain, thP⟩ := hG.core
  exact ⟨lev, grp, fam, models,
    ⟨chain.ωY, chain.ωX, chain.vY, chain.vX, chain.ptY, chain.ptX, fun k hk => orZero_of fun t => chain.ItY t k hk,
      orZero_of chain.ItX, fun t k hk => orZero_of (chain.ioY t k (by omega)), fun t => orZero_of (chain.ioX t),
      fun t => orZero_of (chain.Th t)⟩,
    ⟨thP.ωP, thP.vP, thP.pt_theta, fun i => orZero_of (thP.ioP i), fun i t => orZero_of ⟨thP.thF_mem i t, thP.thF i t⟩,
      fun i t => orZero_of (thP.thG i t)⟩⟩

theorem alg_step {d I aa xy ipv P P' na : ℂ} (hna : na ≠ 0) (e1 : aa = na ^ 2) (e2 : P = P') (h1 : d * I = aa * xy)
    (h2 : I = ipv * P) : xy = d * P' / na ^ 2 * ipv := by
  subst e1 e2 h2
  field_simp
  linear_combination -h1

theorem riesz {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, ℓ w = ⟪a, w⟫_ℂ :=
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap ℓ), fun w => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl⟩

theorem normX : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ h : RangeX R, NormX R h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG h
  have hB := baseW_of_given R F hG
  have hm := hG.core.models
  obtain ⟨w0, v0, hw0⟩ : ∃ (w : R.cX.W) (v : R.MX.Vec), R.prX w (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hm.prX.1
    refine LinearMap.ext fun w => LinearMap.ext fun x => ?_
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v => simp [hc w v]
    | add x y hx hy => simp [map_add, hx, hy]
  obtain ⟨a, ha⟩ := riesz (R.prX.flip (PiTensorProduct.tprod ℂ v0))
  have ha' : ∀ w, R.prX w (PiTensorProduct.tprod ℂ v0) = ⟪a, w⟫_ℂ := fun w => ha w
  have hna : a ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [ha']; simp)
  have hv : ∀ τ, (v0 τ : R.MX.H τ) ≠ 0 := by
    intro τ h0
    apply hw0
    have : v0 τ = 0 := Subtype.ext h0
    rw [(PiTensorProduct.tprod ℂ).map_coord_zero τ this, map_zero]
  haveI : Nontrivial R.cX.W := hm.cX.2.2.2.1
  have hd : (0 : ℝ) < Module.finrank ℂ R.cX.W := by exact_mod_cast Module.finrank_pos
  have hP : (0 : ℝ) < ∏ τ, ‖(v0 τ : R.MX.H τ)‖ ^ 2 :=
    Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.2 (hv τ)) 2
  have hA : (0 : ℝ) < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.2 hna) 2
  refine ⟨(Module.finrank ℂ R.cX.W : ℝ) * (∏ τ, ‖(v0 τ : R.MX.H τ)‖ ^ 2) / ‖a‖ ^ 2, by positivity, fun t => ⟨?_, ?_⟩⟩
  · have hi := GlobalTheory.DefiniteMult.top_injective R hm.inf hm.cX hm.prX hm.HX t
    refine ⟨fun x y e => ?_, fun z => ?_⟩
    · have e2 := (LinearEquiv.ofEq _ _ (h t)).injective e
      exact hi (congrArg Subtype.val e2)
    · obtain ⟨u, hu⟩ := (LinearMap.surjective_rangeRestrict _) ((LinearEquiv.ofEq _ _ (h t)).symm z)
      refine ⟨u, ?_⟩
      simp only [toCC, hu]
      exact (LinearEquiv.ofEq _ _ (h t)).apply_symm_apply z
  · intro ipD ip hM x y
    have hS := hM.schur (toCC R h t y) (toCC R h t x) (PiTensorProduct.tprod ℂ v0) (PiTensorProduct.tprod ℂ v0)
    have hS' := hS.trans (congrArg _ (hM.pure v0 v0))
    have hI := (GlobalTheory.T.unfolding_schur_orthogonality_definite_coefficients D G Pl0 T A Ks R F hB t x y a a).2
    have hJ : (∫ g in R.fdX t, star ⟪a, R.cX.ext ((R.HX t).e x) g⟫_ℂ * ⟪a, R.cX.ext ((R.HX t).e y) g⟫_ℂ ∂(R.νX t)) =
        ip (toCC R h t y) (toCC R h t x) * ∏ τ, ⟪(v0 τ : R.MX.H τ), (v0 τ : R.MX.H τ)⟫_ℂ := by
      refine Eq.trans ?_ hS'
      unfold Lift.pet
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have e3 : (((toCC R h t y : (stX R t).CC (comR R t)) : SmT (stX R t).M →ₗ[ℂ] (GA D (stX R t).V → ℂ))
          (PiTensorProduct.tprod ℂ v0)) g = R.prX (R.cX.ext ((R.HX t).e y) g) (PiTensorProduct.tprod ℂ v0) := rfl
      have e4 : (((toCC R h t x : (stX R t).CC (comR R t)) : SmT (stX R t).M →ₗ[ℂ] (GA D (stX R t).V → ℂ))
          (PiTensorProduct.tprod ℂ v0)) g = R.prX (R.cX.ext ((R.HX t).e x) g) (PiTensorProduct.tprod ℂ v0) := rfl
      simp only [e3, e4, ha', starRingEnd_apply]
      exact mul_comm _ _
    have e1 : ⟪a, a⟫_ℂ = ((‖a‖ : ℂ)) ^ 2 := inner_self_eq_norm_sq_to_K a
    have e2 : (∏ τ, ⟪(v0 τ : R.MX.H τ), (v0 τ : R.MX.H τ)⟫_ℂ) = ∏ τ, ((‖(v0 τ : R.MX.H τ)‖ : ℂ)) ^ 2 :=
      Finset.prod_congr rfl fun τ _ => inner_self_eq_norm_sq_to_K _
    have hA' : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hna).ne'
    have H := alg_step hA' e1 e2 hI hJ
    rw [H]
    push_cast
    ring
end GlobalTheory.ChainTwNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealRepresentationMovesRieszVectorFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem piU_rieszJ : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (s : X.B.I.Ginf), s ∈ Hinf X u → ∀ z z' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), Formalism.L2.Forms.IsTr (Formalism.L2.SG.ColDict.sTil X tr.wt s) z z' → X.piU u s (rieszJ tr z) = rieszJ tr z' := by
  intro D X u F tr s hs z z' hz
  have hrep := X.piU_rep u
  have hS := hinf_le_sinf X u s hs
  have hSi := hinf_le_sinf X u _ ((Hinf X u).inv_mem hs)
  refine ext_inner_left ℂ fun η => ?_
  have hη : X.piU u s (X.piU u s⁻¹ η) = η := by
    rw [← ContinuousLinearMap.mul_apply, ← hrep.2.1 _ hS _ hSi, mul_inv_cancel, hrep.1]
    rfl
  rw [← hη, hrep.2.2.1 s hS, inner_rieszJ, inner_rieszJ, tr.J_eqv s hs _ z' z hz]

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowFourierOntoAndSpanTransformedLastRowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_fourier_onto_and_span_transformed_last_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z], (∀ b : SB (Matrix Unit n k), ∃ c : SB (Matrix n Unit k), ∀ η, b.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ())) ∧ ∀ Ξ₂ : SB (Matrix (Z ⊕ Unit) n k), ∃ (N : ℕ) (a : Fin N → SB (Matrix Z n k)) (c : Fin N → SB (Matrix n Unit k)) (g : Fin N → SB (Matrix (Z ⊕ Unit) n k)), (∀ i x, (g i).1 x = (a i).1 x.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => (c i).1 (Matrix.of fun r _ => y r)) (x (Sum.inr ()))) ∧ Ξ₂ = ∑ i, g i := by
  first | exact @GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow | exact GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow | (intros; apply GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctions
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem sch_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f f', IsThetaFunO ψ (dblSp A) B f → IsThetaFunO ψ (dblSp A) B f' → ∀ c : ℂ, IsThetaFunO ψ (dblSp A) B (f + f') ∧ IsThetaFunO ψ (dblSp A) B (c • f) ∧ sch ψ A B ν 𝓨 (f + f') = sch ψ A B ν 𝓨 f + sch ψ A B ν 𝓨 f' ∧ sch ψ A B ν 𝓨 (c • f) = c • sch ψ A B ν 𝓨 f := by
  intro D ψ hψ A B ν 𝓨 hν f f' hf hf' c
  refine ⟨GlobalTheory.OrientedHeis.theta_add hf hf', GlobalTheory.OrientedHeis.theta_smul c hf, ?_, ?_⟩
  · funext x
    have h1 := (dblDec A).integrableOn_mixS hψ.1.1 hν hf x 0
    have h2 := (dblDec A).integrableOn_mixS hψ.1.1 hν hf' x 0
    simp only [sch, HypDec.mixS, HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
    exact integral_add h1 h2
  · funext x
    simp only [sch, HypDec.mixS, HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
      integral_const_mul]

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurProductTypingsAgreeThetaChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.IPDictPf

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem isInnerProduct_of_isMet' (t : T) (k : ℕ) {ipD ip} (hm : IsMet (comR R t) (stY R t k) ipD ip) (x y : (stY R t k).CC (comR R t)) :
    GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsIP R t k (PiTensorProduct.lift.symm x.1) (PiTensorProduct.lift.symm y.1) (ip y x) := by
  intro v v'
  have h1 := hm.integ y x (PiTensorProduct.tprod ℂ v') (PiTensorProduct.tprod ℂ v)
  have h2 := hm.schur y x (PiTensorProduct.tprod ℂ v') (PiTensorProduct.tprod ℂ v)
  rw [hm.pure v' v] at h2
  have e : (fun g => star ((PiTensorProduct.lift.symm x.1) v g) * (PiTensorProduct.lift.symm y.1) v' g) =
      fun g => PiLocalization₂.val y (PiTensorProduct.tprod ℂ v') g * conj (PiLocalization₂.val x (PiTensorProduct.tprod ℂ v) g) := by
    funext g; rw [mul_comm]; rfl
  refine ⟨?_, ?_⟩
  · exact (congrArg (fun F => IntegrableOn F (stY R t k).fd (stY R t k).ν) e).mpr h1
  · exact (congrArg (fun F : GA D (stY R t k).V → ℂ => ∫ g in (stY R t k).fd, F g ∂(stY R t k).ν) e).trans h2

theorem exists_tprod_ne {k : ℕ} (w : SmT (R.MY k)) (hw : w ≠ 0) : ∃ v : (R.MY k).Vec, PiTensorProduct.tprod ℂ v ≠ 0 := by
  by_contra h
  push_neg at h
  have hid : (LinearMap.id : SmT (R.MY k) →ₗ[ℂ] SmT (R.MY k)) = 0 :=
    PiTensorProduct.ext (MultilinearMap.ext fun v => by simpa using h v)
  exact hw (by simpa using LinearMap.congr_fun hid w)

theorem exists_vec (hC : R.IsChain) (t : T) {k : ℕ} (hk : k < D.R.m) {ipD ip} (hm : IsMet (comR R t) (stY R t k) ipD ip) :
    ∃ v : (R.MY k).Vec, ∏ τ, ⟪(v τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ ≠ 0 := by
  have hw : ∃ w : SmT (R.MY k), w ≠ 0 := by
    by_cases hkk : k + 1 < D.R.m
    · by_contra h
      push_neg at h
      exact (hC.ItY t k hkk).ne (LinearMap.ext fun φ => LinearMap.ext fun x => by simpa using h (R.ItY k φ x))
    · obtain rfl : k = D.R.m - 1 := by omega
      by_contra h
      push_neg at h
      exact (hC.ItX t).ne (LinearMap.ext fun φ => LinearMap.ext fun x => by simpa using h (R.ItX φ x))
  obtain ⟨w, hw⟩ := hw
  obtain ⟨v, hv⟩ := exists_tprod_ne R w hw
  refine ⟨v, fun h0 => ?_⟩
  have hp := hm.posD (PiTensorProduct.tprod ℂ v) hv
  rw [hm.pure v v] at hp
  change 0 < (∏ τ, ⟪(v τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ).re at hp
  rw [h0] at hp
  simp at hp

theorem ipDict (R : RealDat D A Ks) (F : Face D A) (hG : Given R F) : IPDict R := by
  intro t k hk ipD ip hm x y a
  obtain ⟨v, hv⟩ := exists_vec R hG.core.chain t hk hm
  exact ⟨fun h => hasPeterssonInner_unique _ _ _ _ _ v hv h (isInnerProduct_of_isMet' R t k hm x y), fun h => h ▸ isInnerProduct_of_isMet' R t k hm x y⟩

theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → IPDict R := fun R F hG => ipDict R F hG

end GlobalTheory.ChainTw.IPDictPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelFinitePartFrameActionMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.AdBridge

namespace GlobalTheory.Core.Mi.FinFrame

theorem eq_self_of_rat_of_int (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : E ⊗[F] Formalism.MainNotions.S.Af F →+* E ⊗[F] Formalism.MainNotions.S.Af F)
    (hι : ∀ x, ι (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x) = Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x)
    (hO : ∀ a ∈ IntAf F E, ι a ∈ IntAf F E) (a : E ⊗[F] Formalism.MainNotions.S.Af F) : ι a = a := by
  obtain ⟨-, hden, hzero, hdenom, -⟩ := GlobalTheory.St.G.IntAd.integral_adeles_properties F E
  have key : ∀ b ∈ IntAf F E, ι b = b := by
    intro b hb
    rw [← sub_eq_zero]
    refine hzero _ fun m hm => ?_
    obtain ⟨x, t, ht, rfl⟩ := hden b hb m hm
    refine ⟨ι t - t, (IntAf F E).sub_mem (hO _ ht) ht, ?_⟩
    simp only [map_add, map_mul, map_natCast, hι]
    ring
  obtain ⟨m, hm, hma⟩ := hdenom a
  have h := key _ hma
  simp only [map_mul, map_natCast] at h
  have hu : IsUnit (m : E ⊗[F] Formalism.MainNotions.S.Af F) := by
    have : IsUnit (m : F) := (Nat.cast_ne_zero.2 hm.ne').isUnit
    simpa using this.map (algebraMap F (E ⊗[F] Formalism.MainNotions.S.Af F))
  exact hu.mul_left_cancel h

theorem tauF_eq (D : D7) (z : AE D) : tauF (Formalism.L2.SG.InstExistsPf.instOf D) z = toEAf D z := by
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero (toEAf D)).symm
  | tmul a x => exact tauF_tmul (Formalism.L2.SG.InstExistsPf.instOf D) a x
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add (toEAf D) x y).symm)

theorem fmat_iota (D : D7) (g : GA D (D.sp.Y 0)) :
    (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = (mt (D.sp.Y 0) g).map (toEAf D) := by
  have hb := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  refine (hb.2.trans (congrArg (fun q => ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) q) key)).trans ?_
  ext i j
  exact tauF_eq D _

theorem toEAf_incA (D : D7) (y : D.host.E) :
    toEAf D (incA D y) = Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) y :=
  (tauF_eq D _).symm.trans (tauF_tmul (Formalism.L2.SG.InstExistsPf.instOf D) 1 y)

theorem map_cols {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {m n : ℕ} (M : Matrix (Fin m) (Fin m) A)
    (N : Matrix (Fin m) (Fin n) A) (P : Matrix (Fin n) (Fin n) A) (h : M * N = N * P) (j : Fin n) :
    M.map f *ᵥ (fun k => f (N k j)) = ∑ i, f (P i j) • fun k => f (N k i) := by
  funext k
  have h3 := congrArg f (congrFun (congrFun h k) j)
  simp only [Matrix.mul_apply, map_sum, map_mul] at h3
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h3]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem embA_cols {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (a : GA D A)
    (j : Fin A.rank) :
    (mt S (embA d o a)).map (toEAf D) *ᵥ
        (fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k j)) =
      ∑ i, toEAf D (mt A a i j) • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k i) := by
  have h1 : mt S (embA d o a) ⬝ (d.j0 ⬝ o.jA) = (d.j0 ⬝ o.jA) ⬝ mt A a := by
    change mt S (d.emb0 (o.emb (a, 1))) ⬝ (d.j0 ⬝ o.jA) = _
    rw [← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
  have h2 : d.j0 ⬝ o.jA = (d.i₀ * o.iA).map (incA D) := (Matrix.map_mul (f := incA D)).symm
  rw [h2] at h1
  have h3 := map_cols (toEAf D) _ _ _ h1 j
  simp only [Matrix.map_apply, toEAf_incA] at h3
  exact h3

theorem transport (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n)
    (ιA : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hrat : ∀ x : I.E, ιA (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιE x))
    (hint : ∀ a, a ∈ IntAf I.F I.E ↔ ιA a ∈ IntAf D.host.F D.host.E)
    {n : ℕ} (q : Fin n → Fin I.n → I.E) (g : GA D (D.sp.Y 0)) (c : Fin n → GlobalTheory.AdForm.EF D) (j : Fin n)
    (H : (mt (D.sp.Y 0) g).map (toEAf D) *ᵥ
        (fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q j (Fin.cast hr k)))) =
      ∑ i, c i • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q i (Fin.cast hr k)))) :
    I.fmat (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D g)).2 *ᵥ incl I (q j) = ∑ i, ιA.symm (c i) • incl I (q i) := by
  generalize hI.symm = e
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hA : ∀ a, ιA a = a := eq_self_of_rat_of_int (Formalism.L2.SG.InstExistsPf.instOf D).F (Formalism.L2.SG.InstExistsPf.instOf D).E ιA.toRingHom
    (fun x => (hrat x).trans (congrArg _ (hid x))) (fun a ha => (hint a).1 ha)
  have hA' : ∀ a, ιA.symm a = a := fun a => (hA _).symm.trans (ιA.apply_symm_apply a)
  simp only [hid] at H
  simp only [hA']
  change (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ _ = _
  rw [fmat_iota]
  exact H

theorem repM_toH : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F), IdE X → B.Adapted tr.wt → ∀ a : GA D (D.sp.X 0), RepM X tr.wt tr.ιA ((B.toH a).2 : X.B.I.Gf) (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) := by
  intro D X h u ψ B F tr hId hAd a j
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  refine transport D X.B.I X.ιE hId h (rank_eq X h) tr.ιA tr.ιA_rat tr.ιA_int
    (fun i => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt i)) (embA B.d B.o a)
    (fun i => GlobalTheory.AdForm.finM (D.sp.X 0) hn a i j) j ?_
  have H := embA_cols B.d B.o a (Fin.cast hn.symm j)
  simp only [hAd _ _] at H
  refine H.trans ?_
  exact Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl

end GlobalTheory.Core.Mi.FinFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelImageRationalStabilizerPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem toH_rat : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (a : GA D (D.sp.X 0)), a ∈ GQ (D.sp.X 0) → ∃ γ : Gam X u, iotaI X u γ = (B.toH a).1 ∧ iotaF X u γ = (B.toH a).2 := by
  intro D X h u ψ B a ha
  have hrat : embA B.d B.o a ∈ GQ (D.sp.Y 0) := by
    have e : embA B.d B.o a = B.d.emb0 (B.o.emb (a, 1)) := rfl
    rw [e]
    exact B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ ha (one_mem _))
  have k : ∀ {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA), x ∈ I.GFset → castGA e x ∈ I'.GFset := by
    intro I I' e x hx
    subst e
    exact hx
  have hr : iotaX X h (embA B.d B.o a) ∈ X.B.I.GFset :=
    k h.symm _ ((Formalism.IndefR.RationalEmbedding.iota_rat D _).1 hrat)
  have hH := (B.tieH (embA B.d B.o a)).1 ⟨a, rfl⟩
  exact ⟨⟨iotaX X h (embA B.d B.o a), Subgroup.mem_inf.2 ⟨hr, Subgroup.mem_prod.2 hH⟩⟩, rfl, rfl⟩

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFubiniTwoLiftsModerateGrowthKernelsStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_fubini_two_lifts_moderate_growth_kernels : ∀ (D : D7) (A B : HSp D) (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ K₁ K₂ : GA D A → GA D B → ℂ, (∀ K ∈ ({K₁, K₂} : Set (GA D A → GA D B → ℂ)), Continuous (Function.uncurry K) ∧ (∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) ∧ (∀ g, MemL2Quotient (GQ B) mH (K g)) ∧ (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (K g) (K g)) ∧ ∀ h, GlobalTheory.Grow.ModGrowth A fun g => K g h) → ∀ u₁ u₂ : GA D A → ℂ, GlobalTheory.Grow.RapidDec A u₁ → GlobalTheory.Grow.RapidDec A u₂ → let θ₁ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₁ g h * u₁ g) q ∂autMeasure A m; let θ₂ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₂ g h * u₂ g) q ∂autMeasure A m; (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₁ g h * u₁ g) (autMeasure A m)) ∧ (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₂ g h * u₂ g) (autMeasure A m)) ∧ MemL2Quotient (GQ B) mH θ₁ ∧ MemL2Quotient (GQ B) mH θ₂ ∧ petersson B mH θ₁ θ₂ = ∫ q : AutQ A × AutQ A, petersson B mH (K₁ q.1.out) (K₂ q.2.out) * u₁ q.1.out * conj (u₂ q.2.out) ∂(autMeasure A m).prod (autMeasure A m) := by
  first | exact @GlobalTheory.Core.Rk.Seesaw.seesaw_fubini | exact GlobalTheory.Core.Rk.Seesaw.seesaw_fubini | (intros; apply GlobalTheory.Core.Rk.Seesaw.seesaw_fubini <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralUnramifiedPlacesUnionEqLocalFactorsStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_unramified_places_union_eq_local_factors : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SphFactor D → LocalZetaOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ → ∀ s : ℂ, (A.rank : ℝ) < s.re → Integrable (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s) m → ∀ S₁ S₂ : Finset (FinPl D), Sf ⊆ S₁ → Disjoint S₁ S₂ → ∀ S₃ : Finset (FinPl D), (∀ u, u ∈ S₃ ↔ u ∈ S₁ ∨ u ∈ S₂) → ∫ g in openOff A LA S₃, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m = (∏ v ∈ S₂, GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s) * ∫ g in openOff A LA S₁, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m := by
  first | exact @GlobalTheory.Core.Rk.EulStep.setIntegral_openOff_union | exact GlobalTheory.Core.Rk.EulStep.setIntegral_openOff_union | (intros; apply GlobalTheory.Core.Rk.EulStep.setIntegral_openOff_union <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

set_option synthInstance.maxHeartbeats 400000 in

theorem shift_char_realPar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∃ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ ∧ IsCharAF D.host.F (shift ψ lam) ∧ ∃ l : D.what₂.Tau → ℝ, HasRealPar (shift ψ lam) θ l ∧ ∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖ := by
  intro D ψ hψ θ hθ μ hμ
  have hstar : ∀ x : D.host.E, star x = IsCMField.complexConj D.host.E x := fun _ => rfl
  set y : D.host.E := -D.host.xi0 / μ with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y := by
    rw [hy_def, map_div₀, map_neg, conj_xi0_alt, ← hstar μ, hμ.2, neg_neg, div_neg, neg_div]
  have hyF : y ∈ D.host.F := (IsCMField.complexConj_eq_self_iff D.host.E y).1 hyc
  have hy0 : y ≠ 0 := div_ne_zero (neg_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)) hμ.1
  let lam : D.host.F := ⟨y, hyF⟩
  have hlam : algebraMap D.host.F D.host.E lam = y := rfl
  have hlam0 : lam ≠ 0 := fun h => hy0 (by rw [← hlam, h, map_zero])
  refine ⟨lam, hlam, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hψ.1.1.comp (continuous_const.mul continuous_id)
    · intro x; exact hψ.1.2.1 _
    · intro a
      rw [shift, AddChar.mulShift_apply, ← map_mul]
      exact hψ.1.2.2.1 _
    · obtain ⟨x, hx⟩ := hψ.1.2.2.2
      refine ⟨algebraMap D.host.F (AF D.host.F) lam⁻¹ * x, ?_⟩
      rw [shift, AddChar.mulShift_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hlam0, map_one, one_mul]
      exact hx
  ·
    have hreal : ∀ τ, (tauE D τ y).im = 0 := by
      intro τ
      have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
      rw [hyc] at h
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    refine ⟨fun τ => -(tauE D τ y).re, ?_, ?_⟩
    · intro x
      have e1 : psiInf D.host.F (shift ψ lam) x =
          psiInf D.host.F ψ (algebraMap D.host.F (Ainf D.host.F) lam * x) := by
        simp only [psiInf, shift, AddChar.mulShift_apply]
        congr 1
        show (algebraMap D.host.F (Ainf D.host.F) lam * x, algebraMap D.host.F (Af D.host.F) lam * 0) = _
        rw [mul_zero]; rfl
      rw [e1, hψ.2.2 θ hθ]
      congr 1
      have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) lam * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
          θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
        intro ρ
        have e3 : (algebraMap D.host.F (Ainf D.host.F) lam * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
            (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
            ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one, hlam]
        rw [e3, map_mul, (hθ ρ).1]
      simp only [e2]
      have e4 : ∀ ρ, (((-(tauE D ρ y).re : ℝ)) : ℂ) = -tauE D ρ y := by
        intro ρ
        apply Complex.ext <;> simp [hreal ρ]
      simp only [e4, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun ρ _ => ?_
      ring
    · intro τ
      have h1 : |(tauE D τ y).re| = ‖tauE D τ y‖ := by
        rw [← Complex.abs_re_eq_norm.2 (hreal τ)]
      rw [abs_neg, h1, hy_def, map_div₀, map_neg, norm_div, norm_neg]

end GlobalTheory.StdUnn
end

