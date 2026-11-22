import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0301
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0315
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0303
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IndexAtLevelIffOuterClausesAnd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceDoubleCosetOperatorSemisimpleTypeSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInner
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftDefiniteFormsEqUnitaryFormsClassSumPairing
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.LiftForms

theorem exists_embed {K N W : Type} [Field K] [AddCommGroup N] [Module ℂ N] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {σ : K →+* ℂ} {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (li : LinearIndependent ℂ (fun k => j (Pi.single k 1)))
    (sp : Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤) (a : (Fin n → K) → N)
    (hadd : ∀ x y, a (x + y) = a x + a y) (hsmul : ∀ (c : K) x, a (c • x) = σ c • a x)
    (C : Submodule ℂ N) (ip : N → N → ℂ) (hC : PeterssonHilbertSpace.IsHermPos C ip) (hsp : Submodule.span ℂ (Set.range a) = C)
    (hip : ∀ x x', ⟪j x, j x'⟫_ℂ = ip (a x) (a x')) :
    ∃ J : W →ₗ[ℂ] N, Function.Injective J ∧ LinearMap.range J = C ∧ (∀ x x', ⟪x, x'⟫_ℂ = ip (J x) (J x')) ∧
      ∀ x, J (j x) = a x := by
  classical
  let b : Module.Basis (Fin n) ℂ W := Module.Basis.mk li sp.ge
  have hb : ∀ k, b k = j (Pi.single k 1) := fun k => Module.Basis.mk_apply li sp.ge k
  let J : W →ₗ[ℂ] N := b.constr ℂ fun k => a (Pi.single k 1)
  let a' : (Fin n → K) →ₛₗ[σ] N := { toFun := a, map_add' := hadd, map_smul' := hsmul }
  have hJ : ∀ x, J (j x) = a x := by
    have h : (J : W →ₛₗ[RingHom.id ℂ] N).comp j = a' := by
      refine (Pi.basisFun K (Fin n)).ext fun k => ?_
      rw [Pi.basisFun_apply, LinearMap.comp_apply, ← hb]
      exact b.constr_basis ℂ _ k
    intro x
    exact LinearMap.congr_fun h x
  have htop : ∀ u : W, u ∈ Submodule.span ℂ (Set.range j) := by
    intro u
    have hu : u ∈ Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) := sp ▸ Submodule.mem_top
    exact Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩) hu
  have hr : LinearMap.range J = C := by
    have h1 : Submodule.span ℂ (Set.range j) = ⊤ := eq_top_iff.2 fun u _ => htop u
    rw [LinearMap.range_eq_map, ← h1, Submodule.map_span, ← Set.range_comp, ← hsp]
    congr 2
    exact funext hJ
  have hm : ∀ u, J u ∈ C := fun u => hr ▸ LinearMap.mem_range_self J u
  have hz : ∀ v, ip 0 (J v) = 0 := by
    intro v
    have := hC.smul 0 0 ⟨_, hm v⟩
    simpa using this
  have left : ∀ v, (∀ x, ⟪j x, v⟫_ℂ = ip (J (j x)) (J v)) → ∀ u, ⟪u, v⟫_ℂ = ip (J u) (J v) := by
    intro v hv u
    induction htop u using Submodule.span_induction with
    | mem _ h => obtain ⟨x, rfl⟩ := h; exact hv x
    | zero => rw [inner_zero_left, map_zero, hz]
    | add p q _ _ hp hq =>
      rw [inner_add_left, map_add, hp, hq]
      exact (hC.add ⟨_, hm p⟩ ⟨_, hm q⟩ ⟨_, hm v⟩).symm
    | smul s p _ hp =>
      rw [inner_smul_left, map_smul, hp]
      exact (hC.smul s ⟨_, hm p⟩ ⟨_, hm v⟩).symm
  have hall : ∀ u v, ⟪u, v⟫_ℂ = ip (J u) (J v) := by
    intro u v
    refine left v (fun x => ?_) u
    have h1 : ⟪v, j x⟫_ℂ = ip (J v) (J (j x)) := left (j x) (fun x' => by rw [hJ, hJ, hip]) v
    rw [← inner_conj_symm, h1]
    exact hC.herm ⟨_, hm v⟩ ⟨_, hm (j x)⟩
  refine ⟨J, ?_, hr, hall, hJ⟩
  rw [injective_iff_map_eq_zero]
  intro u hu
  have h := hall u u
  rw [show ip (J u) (J u) = ip 0 (J u) by rw [hu], hz] at h
  exact inner_self_eq_zero.1 h

set_option maxHeartbeats 2000000 in

theorem lift_forms_embed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m) (t : T) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 i t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] W), LinearIndependent ℂ (fun k => j (Pi.single k 1)) → Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤ → (∀ x x', ⟪j x, j x'⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A3.A F.lv2.P0 F.lv2.ψ0 i t) x x')) → ∃ J : W →ₗ[ℂ] (GA D ((y.L F.lv2).V i) → (y.L F.lv2).TauV i), Function.Injective J ∧ LinearMap.range J = (y.L F.lv2).Amt (y.tup t) i ∧ (∀ x x', ⟪x, x'⟫_ℂ = (y.L F.lv2).ipA (y.tup t) i (J x) (J x')) ∧ ∀ x, J (j x) = R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ _ hP hH y i t W _ _ j li sp hip
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  have hok : A3.A.fam.Ok 1 := hH.ok.ok2
  have h := (GlobalTheory.T.classSums_eq_pairings_topChain_lifts D G Pl0 T A3.A Ks R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj hB hP.keep.prX hok (y.tup t)).2.2 i
  have hA := GlobalTheory.HilbertLevels.hermA R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj (y.tup t) i
  have key : ∀ t', t' = t → (Submodule.span ℂ (Set.range fun x => R.toRealDat.extV i t' (R.toRealDat.jV i t' (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t' x))) = (y.L F.lv2).Amt (y.tup t) i ∧ ∀ x x', (y.L F.lv2).ipA (y.tup t) i (R.toRealDat.extV i t' (R.toRealDat.jV i t' (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t' x))) (R.toRealDat.extV i t' (R.toRealDat.jV i t' (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t' x'))) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A3.A F.lv2.P0 F.lv2.ψ0 i t') x x')) →
      (Submodule.span ℂ (Set.range fun x => R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x))) = (y.L F.lv2).Amt (y.tup t) i ∧ ∀ x x', (y.L F.lv2).ipA (y.tup t) i (R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x))) (R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x'))) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A3.A F.lv2.P0 F.lv2.ψ0 i t) x x')) := by
    rintro _ rfl h'
    exact h'
  obtain ⟨h1, h2⟩ := key (y.tupT (y.tup t)) (y.tupT_tup t) h
  refine exists_embed j li sp
    (fun x => R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x))) ?_ ?_ _ _ hA h1 ?_
  · intro x x'
    simp only [DatApi.liftForm_add]
    exact (congrArg _ (map_add (R.toRealDat.jV i t) _ _)).trans (map_add (R.toRealDat.extV i t) _ _)
  · intro c x
    simp only [DatApi.liftForm_smul]
    exact (congrArg _ (map_smulₛₗ (R.toRealDat.jV i t) _ _)).trans (map_smul (R.toRealDat.extV i t) _ _)
  · intro x x'
    exact (hip x x').trans (h2 x x').symm

end GlobalTheory.Mem.R3.Rw.LiftForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapMemSpanImage
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df.RowsEx

theorem map_mem_span_image {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) (S : Set V) {x : V} (hx : x ∈ Submodule.span K S) :
    j x ∈ Submodule.span ℂ (j '' S) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul k y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem span_image_eq_top {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) {ι : Type} (b : Module.Basis ι K V) (S : Set V)
    (hS : Submodule.span K S = ⊤) (hb : Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) :
    Submodule.span ℂ (j '' S) = ⊤ := by
  rw [eq_top_iff, ← hb, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact map_mem_span_image σ j S (by rw [hS]; exact Submodule.mem_top)

end GlobalTheory.Mem.Df.RowsEx

open GlobalTheory.Mem.Df.RowsEx in
theorem GlobalTheory.Mem.Df.rowsDef_nonempty : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), Nonempty (RowsDef I l hX) := by
  intro B X I hI hP l hX
  classical
  have hb := fun a => GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis I hX a
  choose j hj using fun a => (hb a).2.1
  have hA := fun a => GlobalTheory.T.exists_equiv_hermitianFrameNorm_at_complexPlace B.LL B.embLL (MtHL I hX a) (MtCx I a) (j a) (hb a).1.1
    (by simpa only [hj] using (hb a).2.2.1) (by simpa only [hj] using (hb a).2.2.2)
  choose n gA hgA using hA
  have hme := GlobalTheory.T.exists_tupleUnitaryForms_equiv_periodRowForms I hI hP l hX
  choose mq hmq using hme
  let jj : ∀ a, (MtHL I hX a).V →ₛₗ[B.embLL] EuclideanSpace ℂ (Fin (n a)) := fun a => (gA a).toLinearMap.comp (j a)
  letI : ∀ a, Module (𝓞 B.LL) (MtHL I hX a).V := fun a => (MtHL I hX a).modOV
  haveI : ∀ a, IsScalarTower (𝓞 B.LL) B.LL (MtHL I hX a).V := fun a => (MtHL I hX a).towV
  have hL := fun a => GlobalTheory.exists_oLat_of_fg_ringOfIntegers B.O B.LL B.OtoLL B.embLL (MtHL I hX a).V
    (EuclideanSpace ℂ (Fin (n a))) (jj a) (MtHL I hX a).L B.O_int (hb a).1.2.1
    (span_image_eq_top B.embLL (jj a) (MtHL I hX a).b _ (hb a).1.2.2 (by
      have h2 := (hb a).2.2.2
      simp only [← hj] at h2
      have : (Set.range fun i => jj a ((MtHL I hX a).b i)) = (gA a).toLinearMap '' (Set.range fun i => j a ((MtHL I hX a).b i)) := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, h2, Submodule.map_top, LinearEquiv.range]))
  choose L hLc hLg hLy hLs using hL
  let mt : B.places.Pl → (I.cols l).Tup := fun w => if B.places.resChar w = B.host.pde then I.muStar' else I.muStar
  have hmt : ∀ w, mt (B.places.conj w) = mt w := fun w => by
    simp only [mt, GlobalTheory.Mem.Top.TwFin.resChar_conj]
  obtain ⟨W, g, hstd, hmuAt, hmuTw, he0, heT, hcar, hgen, heOp, hze⟩ :=
    GlobalTheory.T.exists_rows_prescribedUnitaryForms_standIns B (I.cols l) n (fun u => (mq u I.mu0).symm.trans (gA I.mu0))
      (fun u a => (mq u a).symm.trans (gA a)) L mt hmt (GlobalTheory.T.stepZeroColumns_classSumForm_posDef I hI hP l hX)
  letI := W.instAmb
  letI := W.instAmbi
  refine ⟨⟨W, fun a => (gA a).trans (g a).toLinearEquiv, ?_, hstd⟩⟩
  refine
    { muAt := hmuAt
      muTw := hmuTw
      eMt0 := ?_
      eMtTw := ?_
      norm := ?_
      lat := ?_
      gen := ?_
      eOp := heOp
      ze := hze }
  · intro u F
    have h : W.eMt0 u (mq u I.mu0 F) = g (I.cols l).mu0 (gA I.mu0 F) :=
      (he0 u _).trans (congrArg (g (I.cols l).mu0) (congrArg (gA I.mu0) ((mq u I.mu0).symm_apply_apply F)))
    have h' : (W.eMt0 u).symm (g (I.cols l).mu0 (gA I.mu0 F)) = mq u I.mu0 F := by
      rw [← h]; exact (W.eMt0 u).symm_apply_apply _
    have hs := hmq u I.mu0 F
    rw [← h'] at hs
    exact hs
  · intro u a F
    have h : W.eMtTw u a (mq u a F) = g a (gA a F) :=
      (heT u a _).trans (congrArg (g a) (congrArg (gA a) ((mq u a).symm_apply_apply F)))
    have h' : (W.eMtTw u a).symm (g a (gA a F)) = mq u a F := by
      rw [← h]; exact (W.eMtTw u a).symm_apply_apply _
    have hs := hmq u a F
    rw [← h'] at hs
    exact hs
  · intro a x
    have h := (g a).norm_map (gA a (toCx I hX a x))
    exact (hgA a x).trans ((congrArg (fun z => ‖gA a z‖) (hj a x)).trans h.symm)
  · intro a y
    constructor
    · intro hy
      have hy' : g a ((g a).symm y) ∈ (W.Mtilde a).carrier := by simpa using hy
      obtain ⟨x, hx, hxy⟩ := (Set.ext_iff.1 (hLc a) _).1 ((hcar a _).1 hy')
      refine ⟨x, hx, ?_⟩
      have h1 : gA a (toCx I hX a x) = (g a).symm y := (congrArg (gA a) (hj a x)).symm.trans hxy
      have h2 : g a (gA a (toCx I hX a x)) = y := by rw [h1]; simp
      exact h2
    · rintro ⟨x, hx, rfl⟩
      have h1 : jj a x = gA a (toCx I hX a x) := congrArg (gA a) (hj a x)
      have h2 : g a (jj a x) ∈ (W.Mtilde a).carrier := (hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 ⟨x, hx, rfl⟩)
      rw [h1] at h2
      exact h2
  · intro a y hy
    have hy' : g a ((g a).symm y) ∈ (W.Mtilde a).gen := by simpa using hy
    have h1 := hLg a _ ((hgen a _).1 hy')
    have h2 : g a ((g a).symm y) ∈ (W.Mtilde a).carrier := (hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 h1)
    simpa using h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedFormsCommensurableOfUStableInjective
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelCommensurable

theorem exists_nsmul_map_mem {K V W : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (A : Submodule (𝓞 K) W) (hA : A.FG) (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤)
    (f : W →ₗ[K] V) : ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ A, n • f x ∈ L := by
  classical
  obtain ⟨s, rfl⟩ := hA
  have h : ∀ x : W, ∃ n : ℕ, n ≠ 0 ∧ n • f x ∈ L := fun x =>
    GlobalTheory.Mem.Full.exists_nsmul_mem_of_span L (f x) (by rw [hL]; trivial)
  choose c hc0 hc using h
  refine ⟨∏ x ∈ s, c x, Finset.prod_ne_zero_iff.2 fun x _ => hc0 x, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem c (Finset.mem_coe.1 hy)
    rw [hk, mul_comm, mul_smul]
    exact L.toAddSubmonoid.nsmul_mem (hc y) k
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, smul_add]; exact L.add_mem hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul K r y, map_smul, smul_comm, algebraMap_smul]
    exact L.smul_mem r hy

open GlobalTheory.LevelIndexCompare GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks in

theorem commensurable : ∀ (D : D7) (u : D.what₂.Word), (∀ v, ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)) → (∀ v, ∀ φ ∈ (D.mem u).A.Mram, LT.Uop D u 0 v φ = 0 → φ = 0) → ∀ w : D.what₂.places.Pl, ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧ ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x) := by
  classical
  intro D u hst hinj w
  have hex : ∀ v, ∃ g, IsScaledU D u w v g := fun v => (exists_isScaledU_iff D u w v).2 (hst v)
  choose g hg using hex
  haveI : Module.Finite D.what₂.LL (LT.Vl D u 0) := Module.Finite.of_basis ((D.fm u).lat 0).b
  have hgi : ∀ v, IsUnit (g v) := by
    intro v
    rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hg v x
    rw [hx, Submodule.coe_zero, map_zero] at h1
    have h2 := (smul_eq_zero.1 h1.symm).resolve_left (zpow_ne_zero _ (T_ne_zero D u))
    have h3 := hinj v _ x.2 h2
    exact Subtype.ext ((D.fm u).emb_inj 0 (h3.trans (map_zero _).symm))
  set G : Module.End D.what₂.LL (D.fm u).ramSub := ((LT.VVT D u w).toList.map g).prod ^ D.R.m with hG
  have hGu : IsUnit G := by
    refine IsUnit.pow _ (List.prod_isUnit fun a ha => ?_)
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
    exact hgi v
  obtain ⟨H, hH⟩ := hGu.exists_right_inv
  have hmem : ∀ x, D.nuIn u x ∈ (D.fm u).ramSub := fun x => D.nuIn_range u ▸ ⟨x, rfl⟩
  let e : (D.div.Nu u).V →ₗ[D.what₂.LL] (D.fm u).ramSub := LinearMap.codRestrict _ (D.nuIn u) hmem
  obtain ⟨n₁, hn₁, h₁⟩ := exists_nsmul_map_mem (DV.MramL D u) (D.MramL_fg u) ((D.fm u).lat 0).L
    ((D.fm u).lat_good 0).2.2 ((D.fm u).ramSub.subtype ∘ₗ H ∘ₗ e)
  obtain ⟨n₂, hn₂, h₂⟩ := exists_nsmul_map_mem (DV.MramL D u) (D.MramL_fg u) ((D.fm u).lat 0).L
    ((D.fm u).lat_good 0).2.2 ((D.fm u).ramSub.subtype ∘ₗ G ∘ₗ e)
  refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, fun x hx => ?_, fun x hx => ?_⟩
  · rw [mem_Nlam_iff D u w g (fun v _ => hg v)]
    have hL : (((n₁ * n₂) • H (e x) : (D.fm u).ramSub) : LT.Vl D u 0) ∈ ((D.fm u).lat 0).L := by
      rw [mul_comm, mul_smul, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower]
      exact ((D.fm u).lat 0).L.toAddSubmonoid.nsmul_mem (h₁ x hx) n₂
    refine ⟨⟨_, ⟨Submodule.subset_span hL, ((n₁ * n₂) • H (e x)).2⟩⟩, ?_⟩
    show _ = ((G ((n₁ * n₂) • H (e x)) : (D.fm u).ramSub) : LT.Vl D u 0)
    rw [map_nsmul G, ← Module.End.mul_apply, hH, map_nsmul]
    rfl
  · rw [mem_Nlam_iff D u w g (fun v _ => hg v)] at hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨s, hs, hsy⟩ := D.inLoc_of_mem_locW w _ _ y.2.1
    obtain ⟨z, hz⟩ : (y : LT.Vl D u 0) ∈ LinearMap.range (D.nuIn u) := by
      rw [D.nuIn_range u]; exact y.2.2
    have hsm : ∀ t, D.nuIn u (s • t) = s • D.nuIn u t := fun t =>
      map_smul ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL)) s t
    have hzM : s • z ∈ DV.MramL D u := by
      show D.nuIn u (s • z) ∈ ((D.fm u).lat 0).L
      rw [hsm, hz]; exact hsy
    have h3 := h₂ _ hzM
    have hez : e z = incl D u w y := Subtype.ext hz
    have h4 : ((D.fm u).ramSub.subtype ∘ₗ G ∘ₗ e) (s • z) = s • D.nuIn u x := by
      rw [← algebraMap_smul D.what₂.LL s z, map_smul, algebraMap_smul, hy]
      show s • ((G (e z) : (D.fm u).ramSub) : LT.Vl D u 0) = _
      rw [hez]
    rw [h4] at h3
    refine ⟨s, hs, ?_⟩
    show D.nuIn u (s • (n₁ * n₂) • x) ∈ ((D.fm u).lat 0).L
    rw [hsm, map_nsmul, smul_comm, mul_smul]
    exact ((D.fm u).lat 0).L.toAddSubmonoid.nsmul_mem h3 n₁

end GlobalTheory.LevelCommensurable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsomOfInducedHermitianBundles
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.InducedIsom

open OfModel

theorem valAt_ne_zero {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {f : Z.functionField}
    (hf : UnitAt (below y) f) : valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map _).ne_zero

theorem isRatSec_lift {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (j : Z ⟶ X)
    (ρ : X.functionField ≃+* Z.functionField)
    (hρ : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Z ∈ j ⁻¹ᵁ U) (s : Γ(X, U)),
      ρ (fnOf U hU s) = fnOf (j ⁻¹ᵁ U) hU' (j.app U s))
    (hj : j (genericPoint Z) = genericPoint X) (B : LB X) {r : (B.pull j).ι → Z.functionFieldˣ}
    (hr : IsRatSec (B.pull j) r) :
    IsRatSec B fun i => Units.map ρ.symm.toMonoidHom (r fun _ => i) := by
  intro i i' h
  have h' : genericPoint Z ∈ j ⁻¹ᵁ (B.U i ⊓ B.U i') := by
    change j (genericPoint Z) ∈ B.U i ⊓ B.U i'
    rwa [hj]
  have h₂ : genericPoint Z ∈ (B.pull j).U (fun _ => i) ⊓ (B.pull j).U (fun _ => i') :=
    ⟨Set.mem_iInter.2 fun _ => h'.1, Set.mem_iInter.2 fun _ => h'.2⟩
  have l : (B.pull j).U (fun _ => i) ⊓ (B.pull j).U (fun _ => i') ≤ j ⁻¹ᵁ (B.U i ⊓ B.U i') :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have hg : ((B.pull j).g (fun _ => i) (fun _ => i')).val = resG Z l (j.app _ (B.g i i').val) := by
    have : (B.pull j).g (fun _ => i) (fun _ => i') = res l (pullU j _ (B.g i i')) := by
      change ∏ _k : PUnit, _ = _
      exact (Fintype.prod_unique _).trans (zpow_one _)
    rw [this]
    rfl
  have e := hr (fun _ => i) (fun _ => i') h₂
  rw [hg, fnOf_resG, ← hρ _ h] at e
  apply ρ.injective
  rw [map_mul]
  exact (ρ.apply_symm_apply _).trans (e.trans (congrArg _ (ρ.apply_symm_apply _).symm))

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

theorem w_div_eq_one {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgPt Y) {D : Y.Dv} {k : ℕ} {a b : Y.Fnˣ}
    (ha : (k • D).IsEqn (below y.1) a) (hb : (k • D).IsEqn (below y.1) b)
    (h : Real.log (e.w (valAt y.1 (((eqn D (below y.1))⁻¹ ^ k * a : Y.Fnˣ) : Y.Fn))) =
      Real.log (e.w (valAt y.1 (((eqn D (below y.1))⁻¹ ^ k * b : Y.Fnˣ) : Y.Fn)))) :
    e.w (valAt y.1 ((b : Y.Fn) / a)) = 1 := by
  have h₀ : (k • D).IsEqn (below y.1) (eqn D (below y.1) ^ k) :=
    (D.exists_isEqn (below y.1)).choose_spec.nsmul k
  have hu {c : Y.Fnˣ} (hc : (k • D).IsEqn (below y.1) c) :
      UnitAt (below y.1) (((eqn D (below y.1))⁻¹ ^ k * c : Y.Fnˣ) : Y.Fn) := by
    have := h₀.iff_unitAt.1 hc
    rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this
  have e₁ : (((eqn D (below y.1))⁻¹ ^ k * b : Y.Fnˣ) : Y.Fn) =
      (b : Y.Fn) / a * (((eqn D (below y.1))⁻¹ ^ k * a : Y.Fnˣ) : Y.Fn) := by
    rw [Units.val_mul, Units.val_mul, mul_left_comm, div_mul_cancel₀ _ a.ne_zero]
  have pa := e.w.pos (valAt_ne_zero _ (hu ha))
  have pb := e.w.pos (valAt_ne_zero _ (hu hb))
  have e₂ := Real.log_injOn_pos pa pb h
  rw [e₁, valAt_mul _ (ha.iff_unitAt.1 hb).regAt (hu ha).regAt, map_mul] at e₂
  exact mul_right_cancel₀ pa.ne' (e₂.symm.trans (one_mul _).symm)

theorem ratIsom_of_induced : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (N : TrueGeo.Model Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X → ∀ (L L' : HermLB N.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced N L k cf → A.Induced N L' k cf → (haveI := N.ar.isIntegral; RatIsom L L') := by
  intro F _ _ C Y A N hN L L' k cf ⟨_, r, hr, hc, hf⟩ ⟨_, r', hr', hc', hf'⟩
  haveI := N.ar.isIntegral
  obtain ⟨ρ, hρ, hj, -, hv, hx⟩ := GlobalTheory.T.model_function_field_compatibility F Y N
  have hR := isRatSec_lift N.j ρ hρ hj L.B hr.isRatSec
  have hR' := isRatSec_lift N.j ρ hρ hj L'.B hr'.isRatSec
  have hP := presents_divOfRatSec L.isLB hR
  have eρ (a b : Y.Fnˣ) : ρ ((Units.map ρ.symm.toMonoidHom b : N.X.functionField) /
      (Units.map ρ.symm.toMonoidHom a : N.X.functionField)) = (b : Y.Fn) / a := by
    rw [map_div₀]
    exact congrArg₂ (· / ·) (ρ.apply_symm_apply _) (ρ.apply_symm_apply _)
  refine ⟨_, _, _, hP, ⟨L'.isLB, hR', fun j x hxj => ?_⟩, fun τ y' i j hi hj' => ?_⟩
  · obtain ⟨i, hxi⟩ := exists_chart L.isLB x
    refine (hP.isEqn i x hxi).iff_unitAt.2
      ((unitAt_iff (div_ne_zero (Units.ne_zero _) (Units.ne_zero _))).2 ⟨?_, ?_⟩)
    · refine GlobalTheory.T.regular_of_valuation_bounded_at_points F Y N hN (L.B.U i ⊓ L'.B.U j) _ (fun v e y yt h hU => ?_) x ⟨hxi, hxj⟩
      have h₁ : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun z hz => (hU hz).1
      have h₂ : ⊤ ≤ yt ⁻¹ᵁ L'.B.U j := fun z hz => (hU hz).2
      rw [hv, eρ]
      refine (w_div_eq_one e y
        (hr.isEqn _ _ (le_chart N L.B e y yt h (i := fun _ => i) h₁ trivial))
        (hr'.isEqn _ _ (le_chart N L'.B e y yt h (i := fun _ => j) h₂ trivial)) ?_).le
      linarith [hf v e y yt (fun _ => i) h h₁, hf' v e y yt (fun _ => j) h h₂]
    · rw [inv_div]
      refine GlobalTheory.T.regular_of_valuation_bounded_at_points F Y N hN (L.B.U i ⊓ L'.B.U j) _ (fun v e y yt h hU => ?_) x ⟨hxi, hxj⟩
      have h₁ : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun z hz => (hU hz).1
      have h₂ : ⊤ ≤ yt ⁻¹ᵁ L'.B.U j := fun z hz => (hU hz).2
      rw [hv, eρ]
      refine (w_div_eq_one e y
        (hr'.isEqn _ _ (le_chart N L'.B e y yt h (i := fun _ => j) h₂ trivial))
        (hr.isEqn _ _ (le_chart N L.B e y yt h (i := fun _ => i) h₁ trivial)) ?_).le
      linarith [hf v e y yt (fun _ => i) h h₁, hf' v e y yt (fun _ => j) h h₂]
  · obtain ⟨σ, rfl, y, hy⟩ := GlobalTheory.T.complex_points_lift_model F Y N τ y'
    have hu : under y' = N.j (under y) := by
      change y'.1 _ = _
      rw [hy]
      rfl
    have h₁ : under y ∈ (L.B.pull N.j).U fun _ => i := Set.mem_iInter.2 fun _ => by
      change N.j (under y) ∈ L.B.U i
      rw [← hu]
      exact mem_ptsIn.1 hi
    have h₂ : under y ∈ (L'.B.pull N.j).U fun _ => j := Set.mem_iInter.2 fun _ => by
      change N.j (under y) ∈ L'.B.U j
      rw [← hu]
      exact mem_ptsIn.1 hj'
    have q₁ := hr.isEqn _ _ h₁
    have q₂ := hr'.isEqn _ _ h₂
    have hg := (CartierDiv.isEqn_iff_generatesAt_inv.1 q₁).regularAt
    have h₈ : ratVal (1 : Y.Fn) y = 1 := by
      have e := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
      rwa [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e
    have e := (hc σ y y' _ _ hy h₁ hg).symm.trans (hc' σ y y' _ _ hy h₂ hg)
    rw [inv_mul_cancel₀ (Units.ne_zero _), h₈, ← div_eq_inv_mul, norm_one, one_pow, one_mul] at e
    have h0 := ratVal_ne_zero (q₁.iff_unitAt.1 q₂)
    have e' := congrArg Real.log e
    rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 h0)) (Real.exp_ne_zero _), Real.log_exp,
      Real.log_exp] at e'
    rw [Units.val_div_eq_div_val, hx σ y y' hy, eρ]
    linarith

end GlobalTheory.TrueGeo.InducedIsom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldDegreeLeAndRootDiscrBoundStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassField_degree_le_and_rootDiscrBound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (φ : E →+* ℂ) (N : ℕ) (M : IntermediateField ℚ ℂ) (h : IsRayFieldIn φ (natIdeal E N) M), N ≠ 0 → degOver φ M h.emb_mem ≤ classNumber E * N ^ Module.finrank ℚ E ∧ Sz M (Real.log (Module.finrank ℚ E) + Real.log (degOver φ M h.emb_mem)) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + Real.log N + Real.log (degOver φ M h.emb_mem)) := by
  first | exact @GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz | exact GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz | (intros; apply GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelIndexStabilizerEqLocalRelIndex
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.L2
open Formalism.AUTREP (GAf)

namespace GlobalTheory.LocRelIndex

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (J : Subgroup (GAf L n)) (H : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))), (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ s.loc n κ ∈ H)) → J.relIndex (GlobalTheory.HeckeScalarSph.locK n s.v) = H.relIndex (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) := by
  intro L _ _ _ n s J H hJH
  set K := GlobalTheory.HeckeScalarSph.locK (L := L) n s.v with hK
  set O := Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring with hO
  let φ : K →* O :=
    ((s.loc n).comp K.subtype).codRestrict O (fun κ => (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s κ.2.2).2 κ.2.1)
  have hsurj : Function.Surjective φ := by
    intro A
    obtain ⟨x, hx, -⟩ := (GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s).2.2 A.1
    refine ⟨⟨x, ?_, hx.1⟩, ?_⟩
    · exact (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx.1).1 (hx.2 ▸ A.2)
    · exact Subtype.ext hx.2
  have hcomap : J.subgroupOf K = (H.subgroupOf O).comap φ := by
    ext κ
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact hJH κ κ.2.2
  rw [Subgroup.relIndex, Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj]

end GlobalTheory.LocRelIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceDoubleCosetOperatorSemisimpleTypeSpaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_doubleCosetOperator_semisimple_typeSpace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ μ : ℂ, NG.tN J s ϖ k (NG.tN J s ϖ k f - μ • f) = μ • (NG.tN J s ϖ k f - μ • f) → NG.tN J s ϖ k f = μ • f := by
  first | exact @GlobalTheory.HeckeNormal.tN_semisimple | exact GlobalTheory.HeckeNormal.tN_semisimple | (intros; apply GlobalTheory.HeckeNormal.tN_semisimple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInnerStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeSpaces_orthogonal_of_classSum_inner : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → FiniteDimensional ℂ (NG.TypeSp a.ρ J χ) ∧ ∃ (ι : Type) (_ : Finite ι) (S : ι → Submodule ℂ (GAf L n → a.W)), (∀ i, NG.IsIrrRep a.ρ (S i)) ∧ (∀ i i', NG.IsoRep (S i) (S i') → i = i') ∧ (∀ S', NG.IsIrrRep a.ρ S' → NG.isoTyp a.ρ S' ⊓ NG.TypeSp a.ρ J χ ≠ ⊥ → ∃ i, NG.IsoRep (S i) S') ∧ (∀ i, NG.isoTyp a.ρ (S i) ⊓ NG.TypeSp a.ρ J χ ≠ ⊥) ∧ iSupIndep (fun i => NG.isoTyp a.ρ (S i)) ∧ ⨆ i, NG.isoTyp a.ρ (S i) ⊓ NG.TypeSp a.ρ J χ = NG.TypeSp a.ρ J χ := by
  first | exact @GlobalTheory.CompRed.typeSp_decomp | exact GlobalTheory.CompRed.typeSp_decomp | (intros; apply GlobalTheory.CompRed.typeSp_decomp <;> assumption)
end

