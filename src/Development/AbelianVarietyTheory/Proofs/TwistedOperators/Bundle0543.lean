import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0481
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0486
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0480
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0529
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingPiCurry
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Topology

noncomputable section
namespace GlobalTheory.ColFourier

section Curry
variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)] {Y : (i : ι) → κ i → Type*}
  [∀ i j, MeasurableSpace (Y i j)]

theorem measurePreserving_piCurry (μ : ∀ i j, Measure (Y i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry Y) (Measure.pi fun p : (i : ι) × κ i => μ p.1 p.2)
      (Measure.pi fun i => Measure.pi fun j => μ i j) := by
  refine ⟨(MeasurableEquiv.piCurry Y).measurable, ?_⟩
  symm
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.univ.pi '' Set.univ.pi fun j => {s : Set (Y i j) | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi fun j => (μ i j).toFiniteSpanningSetsIn) fun s hs => ?_
  choose S hS hSs using hs
  have hpre : (MeasurableEquiv.piCurry Y) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun p : (i : ι) × κ i => S p.1 p.2 := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi, ← hSs, MeasurableEquiv.piCurry_apply, Sigma.forall]
    rfl
  rw [Measure.map_apply (MeasurableEquiv.piCurry Y).measurable (MeasurableSet.univ_pi fun i => by
      rw [← hSs i]; exact MeasurableSet.univ_pi fun j => hS i j (Set.mem_univ j)), hpre, Measure.pi_pi,
    Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hSs i, Measure.pi_pi]

end Curry

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A C : Type*} [Fintype A] [DecidableEq C]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in

def restrictCols (P : Finset C) (X : Matrix A C k) : Matrix A P k := Matrix.of fun i j => X i j

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
@[simp] theorem restrictCols_setCols (P : Finset C) (Y : Matrix A C k) (U : Matrix A P k) :
    restrictCols P (setCols P Y U) = U := by
  ext i j; simp [restrictCols, setCols, j.2]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
@[simp] theorem setCols_restrictCols (P : Finset C) (Y : Matrix A C k) : setCols P Y (restrictCols P Y) = Y := by
  ext i j; by_cases h : j ∈ P <;> simp [restrictCols, setCols, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
@[simp] theorem setCols_setCols (P : Finset C) (Y : Matrix A C k) (U V : Matrix A P k) :
    setCols P (setCols P Y U) V = setCols P Y V := by
  ext i j; by_cases h : j ∈ P <;> simp [setCols, h]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_restrictCols (P : Finset C) : Continuous (restrictCols (k := k) (A := A) P) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (j : C)).comp (continuous_apply i)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_setCols (P : Finset C) (Y : Matrix A C k) : Continuous (setCols P Y) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : j ∈ P
  · simp only [setCols, of_apply, dif_pos h]
    exact (continuous_apply (⟨j, h⟩ : P)).comp (continuous_apply i)
  · simp only [setCols, of_apply, dif_neg h]
    exact continuous_const

theorem comp_setCols_mem_SB {Ξ : Matrix A C k → ℂ} (hΞ : Ξ ∈ SB (Matrix A C k)) (P : Finset C)
    (Y : Matrix A C k) : (fun U => Ξ (setCols P Y U)) ∈ SB (Matrix A P k) := by
  haveI := t2Space k
  refine ⟨hΞ.1.comp_continuous (continuous_setCols P Y),
    HasCompactSupport.intro (hΞ.2.image (continuous_restrictCols P)) fun U hU => ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h => hU ⟨_, h, restrictCols_setCols P Y U⟩

theorem pairCols_eq_dotProduct (P : Finset C) (Y : Matrix A C k) (U : Matrix A P k) :
    pairCols P Y U = (fun p : (_ : A) × P => U p.1 p.2) ⬝ᵥ (fun p : (_ : A) × P => Y p.1 p.2) := by
  simp only [pairCols, dotProduct, Fintype.sum_sigma]

variable [MeasurableSpace k] [BorelSpace k]

omit [DecidableEq C] in

theorem isAddHaarMeasure_volM (m : Measure k) [m.IsAddHaarMeasure] (B : Type*) [Fintype B] :
    (volM m A B).IsAddHaarMeasure := by
  haveI := secondCountable k; haveI := t2Space k
  haveI : (Measure.pi fun _ : B => m).IsAddHaarMeasure := inferInstance
  exact Measure.pi.isAddHaarMeasure (fun _ : A => (Measure.pi fun _ : B => m))

omit [DecidableEq C] in

theorem integral_volM (m : Measure k) [SigmaFinite m] (B : Type*) [Fintype B] (f : Matrix A B k → ℂ) :
    ∫ U, f U ∂(volM m A B) =
      ∫ x : (_ : A) × B → k, f (Matrix.of fun i j => x ⟨i, j⟩) ∂(Measure.pi fun _ => m) := by
  have h := measurePreserving_piCurry (Y := fun (_ : A) (_ : B) => k) (fun _ _ => m)
  exact (h.integral_comp' (g := f)).symm

theorem fourierInt_eq_pi (ψ : AddChar k Circle) (m : Measure k) [SigmaFinite m] (P : Finset C)
    (Φ : Matrix A C k → ℂ) (Y : Matrix A C k) :
    fourierInt ψ m P Φ Y = ∫ x : (_ : A) × P → k, Φ (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩)) *
      (ψ (x ⬝ᵥ fun p => Y p.1 p.2) : ℂ) ∂(Measure.pi fun _ => m) := by
  rw [fourierInt, integral_volM]
  congr 1
  funext x
  rw [pairCols_eq_dotProduct]
  rfl

end GlobalTheory.ColFourier

namespace GlobalTheory.ColFourier
variable {k : Type*} [Field k] [ValuativeRel k]

theorem hasConductor_inv {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) : HasConductor ψ⁻¹ c := fun x => by
  simpa only [AddChar.inv_apply', inv_eq_one] using h x

end GlobalTheory.ColFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

theorem GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ κ : GA D (Yc D 0), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → finE (Yc D 0) κ ∈ St β → (((iotaX X h).toMulEquiv κ).2 ∈ X.K2 ↔ ∀ PP ∈ R.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp β hβ hred κ hK hS
  classical
  obtain ⟨⟨I⟩, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq, lam_eq, ds, low, g_eq, g0_eq, Rph,
    Rph_spec, eX, fY, ee, ff, ef, Lb, Lb_perp, Lam_split, zu, zu_norm, zu_orth, zu_Lb, Fu, Fu_e, flagZVector, Fu_fixed,
    psiEf, psiEf_add, psiEf_int, psiEf_rat, e0, f0, z0, bw, bwd, ew, vectorsInLattice, basisApprox, gramIntegral, formsAtZero, weightVectorsIntegral, ew_idem,
    ew_orth, ew_int, ew_full, bw_w, bwd_w, bw_dual, latticeSpan⟩ := X
  dsimp only at h
  subst h
  dsimp only at g_eq
  subst g_eq
  have hFH : Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd ew :=
    ⟨vectorsInLattice, gramIntegral, formsAtZero, weightVectorsIntegral, ew_orth, bw_w, bwd_w, bw_dual, latticeSpan⟩
  obtain ⟨hgP, hZ⟩ := GlobalTheory.T.divisibility_typeProduct_read_levelPlaces R F hIs hGrp
  have hL : (II D).L = Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 := by
    ext x
    refine (Formalism.L2.SG.InstExistsPf.mem_Lv D x).trans ?_
    simp only [Formalism.L2.Herm.crdLat, Formalism.L2.Herm.crd]
    constructor
    · intro hx
      refine ⟨(VS D).frame.equivFun.symm x, ?_, (VS D).frame.equivFun.apply_symm_apply x⟩
      have e := Module.Basis.equivFun_symm_apply (VS D).frame x
      rw [← e] at hx
      exact hx
    · rintro ⟨y, hy, hyx⟩
      change (VS D).frame.equivFun y = x at hyx
      rw [← hyx, (VS D).frame.sum_equivFun y]
      exact hy
  have hβ' : IsFrame β (II D).L := by rw [hL]; exact hβ
  have hloc : ∀ PP ∈ R.Pg, ∃ w : Bool,
      LocAt (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd ew β PP w := by
    intro PP hP
    obtain ⟨h1, h2, hA1, hA0⟩ := GlobalTheory.T.residue_idempotent_conj_at_levelPlace (D.host.g 0 * D.host.g 1) ew ew_idem ew_orth ew_int ew_full PP (hgP PP hP)
    have hr : RedIs β PP (if GlobalTheory.StdFrames.cpt PP ew = 1 then
        flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 bw z0
      else flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (fun i => bwd (Fin.rev i)) z0) := hred PP hP
    by_cases hc : GlobalTheory.StdFrames.cpt PP ew = 1
    · rw [if_pos hc] at hr
      exact ⟨true, hgP PP hP, fun _ => by simpa using (hA1 hc).1, fun _ => by simpa using (hA1 hc).2, hr⟩
    · rw [if_neg hc] at hr
      exact ⟨false, hgP PP hP, fun _ => by simpa using (hA0 hc).1, fun _ => by simpa using (hA0 hc).2, hr⟩
  have hxM : (II D).fmat ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = (finE (Yc D 0) κ).val := GlobalTheory.T.finiteMatrix_iota_eq_finitePart κ
  show _ ∧ _ ↔ _
  constructor
  · rintro ⟨-, hc⟩ PP hP
    obtain ⟨w, hw⟩ := hloc PP hP
    exact GlobalTheory.T.congruences_reduction_mem_symmetricUnipotent _ e0 f0 z0 bw bwd ew hFH β PP w hβ' hw _ (finE (Yc D 0) κ) hK hxM hS hc
  · intro hu
    exact ⟨hK, GlobalTheory.T.local_frame_hermitian_ideal _ e0 f0 z0 bw bwd ew hFH β R.Pg hβ' hloc hZ _ (finE (Yc D 0) κ) hK hxM hS hu⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfFunctionProductSumsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory

theorem funSub_evalExpand_exists {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] :
    ∃ (P : Finset X) (e : X → V), ∀ w ∈ W, w = ∑ x ∈ P, (w : X → ℂ) x • e x := by
  first
  | exact @_root_.GlobalTheory.FinsetKernelTrivial.main
  | exact _root_.GlobalTheory.FinsetKernelTrivial.main
  | (apply _root_.GlobalTheory.FinsetKernelTrivial.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinsetKernelTrivial.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinsetKernelTrivial.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinsetKernelTrivial.main ..)

theorem funSub_multilinear_expand {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    {V : ∀ i, Submodule ℂ (X i → ℂ)} {N : Type} [AddCommMonoid N] [Module ℂ N]
    (Φ : MultilinearMap ℂ (fun i => V i) N) (P : ∀ i, Finset (X i)) (e : ∀ i, X i → V i)
    (h : ∀ i, V i) (hh : ∀ i, h i = ∑ x ∈ P i, (h i : X i → ℂ) x • e i x) :
    Φ h = ∑ x ∈ Fintype.piFinset P, (∏ i, (h i : X i → ℂ) (x i)) • Φ (fun i => e i (x i)) := by
  conv_lhs => rw [show h = fun i => ∑ x ∈ P i, (h i : X i → ℂ) x • e i x from funext hh]
  rw [Φ.map_sum_finset]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Φ.map_smul_univ]

end GlobalTheory

namespace GlobalTheory

theorem funProd_multilinear_sum_eq : ∀ {ι κ Δ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    {V : ∀ i, Submodule ℂ (X i → ℂ)} {V' : ∀ j, Submodule ℂ (Y j → ℂ)}
    (M : MultilinearMap ℂ (fun i => V i) (MultilinearMap ℂ (fun j => V' j) ℂ)) (τ : Δ →₀ ℂ)
    (f f' : Δ → ∀ i, V i) (g g' : Δ → ∀ j, V' j),
    (∀ (x : ∀ i, X i) (y : ∀ j, Y j),
      (τ.sum fun d a => a * (∏ i, (f d i : X i → ℂ) (x i)) * ∏ j, (g d j : Y j → ℂ) (y j)) =
        τ.sum fun d a => a * (∏ i, (f' d i : X i → ℂ) (x i)) * ∏ j, (g' d j : Y j → ℂ) (y j)) →
    (τ.sum fun d a => a * M (f d) (g d)) = τ.sum fun d a => a * M (f' d) (g' d) := by
  intro ι κ Δ _ _ _ _ X Y V V' M τ f f' g g' hfg
  classical
  let Wf : ∀ i, Submodule ℂ (V i) := fun i =>
    Submodule.span ℂ ((τ.support.image (fun d => f d i) ∪ τ.support.image (fun d => f' d i) :
      Finset (V i)) : Set (V i))
  let Wg : ∀ j, Submodule ℂ (V' j) := fun j =>
    Submodule.span ℂ ((τ.support.image (fun d => g d j) ∪ τ.support.image (fun d => g' d j) :
      Finset (V' j)) : Set (V' j))
  choose P e hP using fun i => funSub_evalExpand_exists (V i) (Wf i)
  choose Q e' hQ using fun j => funSub_evalExpand_exists (V' j) (Wg j)
  have key : ∀ (F : Δ → ∀ i, V i) (G : Δ → ∀ j, V' j),
      (∀ d ∈ τ.support, ∀ i, F d i ∈ Wf i) → (∀ d ∈ τ.support, ∀ j, G d j ∈ Wg j) →
      (τ.sum fun d a => a * M (F d) (G d)) =
        ∑ x ∈ Fintype.piFinset P, ∑ y ∈ Fintype.piFinset Q,
          M (fun i => e i (x i)) (fun j => e' j (y j)) *
            τ.sum fun d a => a * (∏ i, (F d i : X i → ℂ) (x i)) * ∏ j, (G d j : Y j → ℂ) (y j) := by
    intro F G hF hG
    have hM : ∀ d ∈ τ.support, M (F d) (G d) = ∑ x ∈ Fintype.piFinset P, ∑ y ∈ Fintype.piFinset Q,
        M (fun i => e i (x i)) (fun j => e' j (y j)) *
          ((∏ i, (F d i : X i → ℂ) (x i)) * ∏ j, (G d j : Y j → ℂ) (y j)) := by
      intro d hd
      rw [funSub_multilinear_expand M P e (F d) (fun i => hP i _ (hF d hd i))]
      rw [MultilinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [MultilinearMap.smul_apply,
        funSub_multilinear_expand (M fun i => e i (x i)) Q e' (G d) (fun j => hQ j _ (hG d hd j)),
        smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [smul_eq_mul]; ring
    rw [Finsupp.sum]
    refine (Finset.sum_congr rfl (fun d hd => congrArg (τ d * ·) (hM d hd))).trans ?_
    simp_rw [Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  have memf : ∀ d ∈ τ.support, ∀ i, f d i ∈ Wf i := fun d hd i =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inl ⟨d, hd, rfl⟩)
  have memf' : ∀ d ∈ τ.support, ∀ i, f' d i ∈ Wf i := fun d hd i =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨d, hd, rfl⟩)
  have memg : ∀ d ∈ τ.support, ∀ j, g d j ∈ Wg j := fun d hd j =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inl ⟨d, hd, rfl⟩)
  have memg' : ∀ d ∈ τ.support, ∀ j, g' d j ∈ Wg j := fun d hd j =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨d, hd, rfl⟩)
  rw [key f g memf memg, key f' g' memf' memg']
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [hfg x y]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaFifth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownConv

theorem dn_integrableOn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi Φ hΦ φ hφ h
  obtain ⟨hν, h𝓕⟩ := MeasDat.haar_fd (hG.meas.P (i + 1) hi)
  exact integrableOn_thetaKO_mul_cusp hP.cuspRapidDecay hB.inf true ((hG.arrows.dn i hi).weil) hΦ hν h𝓕 hφ.1 hφ.2.1 h

end GlobalTheory.DownConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate
open GlobalTheory.UpArrowConv

namespace GlobalTheory.UpArrowConv

theorem up_conv : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ h
  have hω := (hG.arrows.dn i hi).weil
  have hm := (hG.meas.P i hi.le).2 (by omega)
  have key := conj_thetaKO_mul_integrableOn hP.cuspRapidDecay hR.inf hω hΦ hm.1.1 hm.2 hφ.1 hφ.2.1
    ((GlobalTheory.Grid.ofSgn true _).symm h)
  have e : (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) =
      fun g => starRingEnd ℂ (thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm h) g Φ) * φ g :=
    funext fun g => by rw [thetaKO_toSgn]
  rw [e]
  exact key

end GlobalTheory.UpArrowConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaSecond
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.UpConjLift

theorem up_isAutFunSm : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → IsAutFunSm R.θ (G.P (i + 1)).V (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro _ hPr D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ _
  have hq : GlobalTheory.Mem.Th.IsQuot (G.P i).V (G.mP i).ν (G.mP i).fd := by
    have := (hG.meas.P i hi.le).2 (by omega)
    exact ⟨this.1.1, this.2⟩
  exact (conj_lift hPr.cuspRapidDecay hR.inf (G.dn i).ω (hG.arrows.dn i hi).weil hΦ hq ⟨hφ.1, hφ.2.1⟩).2

end GlobalTheory.UpConjLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaSixthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negative_parabolic_theta_sixth : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsAutFunSm R.θ (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  first | exact @GlobalTheory.DnLiftAut.isAutFunSm_lift_dn | exact GlobalTheory.DnLiftAut.isAutFunSm_lift_dn | (intros; apply GlobalTheory.DnLiftAut.isAutFunSm_lift_dn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFirstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negative_theta_level_first : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) := by
  first | exact @GlobalTheory.CuspThetaConvX.integrableOn_thetaKO_mul_cusp | exact GlobalTheory.CuspThetaConvX.integrableOn_thetaKO_mul_cusp | (intros; apply GlobalTheory.CuspThetaConvX.integrableOn_thetaKO_mul_cusp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSecondStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negative_theta_level_second : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsAutFunSm R.θ (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  first | exact @GlobalTheory.ArrowLiftAut.liftX_isAutFunSm | exact GlobalTheory.ArrowLiftAut.liftX_isAutFunSm | (intros; apply GlobalTheory.ArrowLiftAut.liftX_isAutFunSm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqUnitaryEmbeddingOrthogonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sq_unitaryEmbedding_orthogonal : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B : Fr V), Adapted d A B → ∀ (x : GA D Y) (τ : D.what₂.Tau) (y : Fin Y.rank → D.host.E) (u : D.host.E), nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) ^ 2 = nrm θ A x τ y ^ 2 + ‖tauE D τ u‖ ^ 2 := by
  first | exact @GlobalTheory.SepPer.norm_sq_unitaryEmbedding_add | exact GlobalTheory.SepPer.norm_sq_unitaryEmbedding_add | (intros; apply GlobalTheory.SepPer.norm_sq_unitaryEmbedding_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedDefiniteKernelEntriesIsAlgebraicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedDefiniteKernel_entries_isAlgebraic : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → GlobalTheory.NormSum.Inp D → GlobalTheory.SumSize.DictAt ch → ∀ (t : T) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → WtOK ch.G p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 → d.P = locPl ch.G t → ch.S.Z.HasVec d → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (a : VVIdx (wt ch.G p.big)) (b : VVIdx (wt ch.G p.small)), IsAlgebraic ℚ (ch.S.Z.kk d x y a b) := by
  first | exact @GlobalTheory.KernelAlg.kk_isAlgebraic | exact GlobalTheory.KernelAlg.kk_isAlgebraic | (intros; apply GlobalTheory.KernelAlg.kk_isAlgebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorAdd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

open MvPolynomial

private theorem jetLin_add_tab {K : Type} [Field K] {ι : Type} {a b : ℕ} (J J' : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K) :
    Formalism.L2.Ker.jetLin (J + J') = Formalism.L2.Ker.jetLin J + Formalism.L2.Ker.jetLin J' := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) K).ext fun m => ?_
  simp only [Formalism.L2.Ker.jetLin, LinearMap.add_apply, Module.Basis.constr_basis, Pi.add_apply, map_add]

theorem kkVec_add : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ},
    IsThetaFunO W.ψ _ _ f → IsThetaFunO W.ψ _ _ f' → ∀ (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (f + f') x y = kkVec S p f x y + kkVec S p f' x y := by
  intro D T L sc G W U S p f f' hf hf' x y
  have hJ : ∀ x' y', GlobalTheory.FunObj.jetTab W S.N.frC p (f + f') x' y' =
      GlobalTheory.FunObj.jetTab W S.N.frC p f x' y' + GlobalTheory.FunObj.jetTab W S.N.frC p f' x' y' := by
    intro x' y'
    funext k
    simp only [GlobalTheory.FunObj.jetTab, GlobalTheory.FunObj.kerFin, GlobalTheory.FunObj.fockIn, Pi.add_apply]
    rw [GlobalTheory.SpecFac.pureTensorO_add W.ψ_std W.θ_is _ _ _ _ hf hf']
    simp only [GlobalTheory.ChiGrid.GridData.Weil.ker, thetaKO, map_add, Pi.add_apply]
  unfold kkVec GlobalTheory.FunObj.fockComp
  rw [hJ, ← smul_add]
  congr 1
  ext1 F
  simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, jetLin_add_tab, LinearMap.comp_apply, LinearMap.add_apply, map_add]

end GlobalTheory.TopZeroInv
end
end

