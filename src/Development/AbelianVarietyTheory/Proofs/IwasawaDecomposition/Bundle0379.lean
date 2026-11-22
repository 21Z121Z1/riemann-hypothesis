import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0373
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0344
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0377
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0234
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0362
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0035
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
import Formalism.LocalToGlobal.Columns.ChainTwOk
import Formalism.LocalToGlobal.Columns.Bundle0046
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutRepIsotypicSplitPlaceLocalComponent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeFrob

theorem rt_mul_apply {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (a b : GAf L n) (f : GAf L n → W) :
    NG.rt L n (a * b) f = NG.rt L n a (NG.rt L n b f) := by
  funext g; simp [NG.rt, mul_assoc]

theorem exists_ne_zero_of_irrRep {G : Type} [Group G] [TopologicalSpace G] (σ : GlobalTheory.SmGL.IrrRep G) :
    ∃ a : σ.V, a ≠ 0 := by
  by_contra hne
  push_neg at hne
  have h := σ.irr
  haveI : Subsingleton σ.V := ⟨fun a b => by rw [hne a, hne b]⟩
  exact (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem mem_iSup_range_locMap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : σ.V →ₗ[ℂ] (GAf L n → π.W)),
    Function.Injective T → (∀ a, T a ∈ π.S) → GlobalTheory.HeckeFrob.IsLocMap s σ i T →
    ∀ g ∈ π.S, g ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 := by
  intro L _ _ _ n π s σ i T hTi hTS hT g hg
  set I : Submodule ℂ (GAf L n → π.W) :=
    ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 with hIdef
  have hIS : I ≤ π.S := iSup_le fun T' => by
    rintro _ ⟨a, rfl⟩
    exact T'.2.1 a
  have hsub : NG.IsSubrep π.ρ I := by
    refine ⟨hIS.trans π.irrS.1.le, ?_⟩
    intro h f hf
    obtain ⟨x, y, hx, hy, rfl⟩ := (GlobalTheory.SplitAdelic.main L n s).1 h
    have hcomm := (GlobalTheory.SplitAdelic.main L n s).2.1
    refine Submodule.iSup_induction (motive := fun f => NG.rt L n (x * y) f ∈ I) _ hf ?_ ?_ ?_
    · rintro T' _ ⟨a, rfl⟩
      let T'' : σ.V →ₗ[ℂ] (GAf L n → π.W) := (NG.rt L n y).comp T'.1
      have hT'' : (∀ a, T'' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'' := by
        refine ⟨fun a => π.irrS.1.stable y _ (T'.2.1 a), fun z hz a => ?_⟩
        change NG.rt L n y (T'.1 _) = NG.rt L n z (NG.rt L n y (T'.1 a))
        rw [T'.2.2 z hz a, ← rt_mul_apply, ← rt_mul_apply, (hcomm z y hz hy).eq]
      have key : NG.rt L n (x * y) (T'.1 a) =
          T'' (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) := by
        rw [hT''.2 x hx a, rt_mul_apply]
        rfl
      rw [key]
      exact Submodule.mem_iSup_of_mem ⟨T'', hT''⟩ ⟨_, rfl⟩
    · rw [map_zero]; exact zero_mem _
    · intro f₁ f₂ h₁ h₂
      rw [map_add]; exact add_mem h₁ h₂
  rcases π.irrS.2.2 I hsub hIS with hbot | htop
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne_zero_of_irrRep σ
    have hmem : T a ∈ I := Submodule.mem_iSup_of_mem ⟨T, hTS, hT⟩ ⟨a, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact ha (hTi (hmem.trans (map_zero T).symm))
  · rw [htop]; exact hg

end GlobalTheory.HeckeFrob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChosenHalfSplitPlacesMeetsConjugatePairOnceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenHalf_splitPlaces_meets_conjugatePair_once : ∀ (D : D7) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), (∀ v, NG.OverPl (Pq v) v) →
    ∀ S : Finset (PlE D.host), (∀ P ∈ S, IsSplitPl D.host P) →
    (∀ P ∈ S, ∃ P' ∈ qpOf D Pq S, P' = P ∨ IsConjPl D.host P P') ∧ ∀ P ∈ qpOf D Pq S, ∀ P' ∈ qpOf D Pq S, ¬ IsConjPl D.host P P' := by
  first | exact @GlobalTheory.ChosenHalf.qpOf_half | exact GlobalTheory.ChosenHalf.qpOf_half | (intros; apply GlobalTheory.ChosenHalf.qpOf_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumsEqPairingsTopChainLifts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.TopNorm

theorem ipVia_self {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N]
    (e : H →ₗ[ℂ] N) (he : Function.Injective e) (u v : H) : ipVia e (e u) (e v) = ⟪u, v⟫_ℂ := by
  unfold ipVia
  split_ifs with h
  · have h1 : h.1.choose = u := he h.1.choose_spec
    have h2 : h.2.choose = v := he h.2.choose_spec
    rw [h1, h2]
  · exact absurd ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ h

set_option maxHeartbeats 2000000 in

theorem classSums_topNorm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → let C := toChainReal R F tupT hm hTop; let L := toLiftReal R F tupT hm hTop hinj; ∀ μ : D.what₂.Tup, (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP true μ ∧ ∀ x y, C.ipXP true μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P1 F.ψ1 (tupT μ)) x y)) ∧ (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP false μ ∧ ∀ x y, C.ipXP false μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P0 F.ψ0 (tupT μ)) x y)) ∧ ∀ i : Fin D.R.m, (let a := fun x => R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)); Submodule.span ℂ (Set.range a) = L.Amt μ i ∧ ∀ x y, L.ipA μ i (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i (tupT μ)) x y)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hB hPr hOk C L μ
  refine ⟨⟨GlobalTheory.T.rowLevelForms_span_definiteMultiplicitySpace D G Pl0 T A Ks R F hB hPr hOk hTop true (tupT μ), fun x y => ?_⟩,
    ⟨GlobalTheory.T.rowLevelForms_span_definiteMultiplicitySpace D G Pl0 T A Ks R F hB hPr hOk hTop false (tupT μ), fun x y => ?_⟩,
    fun i => ⟨GlobalTheory.T.span_liftForms_baseLevel_eq_hilbertImage D G Pl0 T A Ks R F hB hOk hinj i (tupT μ), fun x y => ?_⟩⟩
  · have h1 := GlobalTheory.T.schur_orthogonality_dim_pairing_eq_inner D G Pl0 T A Ks R F hB hPr (tupT μ) (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))
      (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) y))
    have h3 := GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum D G Pl0 T A Ks R F hB true (tupT μ) x y
    have e1 : ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ)) =
        (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) (div_one (∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)))
    refine Eq.trans ?_ h3
    show (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ) *
        ipMT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) y))))) = _
    exact congrArg (fun z : ℂ => (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * z) ((congrArg (· * _) e1).trans h1)
  · have h1 := GlobalTheory.T.schur_orthogonality_dim_pairing_eq_inner D G Pl0 T A Ks R F hB hPr (tupT μ) (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))
      (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) y))
    have h3 := GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum D G Pl0 T A Ks R F hB false (tupT μ) x y
    have e1 : ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ)) =
        (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) (div_one (∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)))
    refine Eq.trans ?_ h3
    show (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ) *
        ipMT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) y))))) = _
    exact congrArg (fun z : ℂ => (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * z) ((congrArg (· * _) e1).trans h1)
  · have h5 := GlobalTheory.T.hilbert_inner_liftForms_eq_base_level_hermitian D G Pl0 T A Ks R F hB i (tupT μ) x y
    refine Eq.trans ?_ h5
    show (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ipVia (R.extV i (tupT μ))
      (R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)))
      (R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) y))) = _
    exact congrArg (fun z : ℂ => (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * z) (ipVia_self _ (hinj i (tupT μ)) _ _)

end GlobalTheory.TopNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnTwistedArgsSecond
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.column_twisted_args_second : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.CuspidalSpectrumGL → GlobalTheory.HeightCounting.CgCmp hL := by
  intro _ _ _ _ _ _ _
  exact ⟨⟨⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEvaluationHasRowLevel
section
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
noncomputable section

namespace GlobalTheory.ConjRowLevelSee

theorem conjMap_level_of_seeAt : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ JR R F, ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = chiR R F k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t _ _ _ _ _ hsee c _ Φ hΦ hrep u (k : GA D (D.sp.Y 0)) hk (g : GA D (D.sp.Y 0))
  obtain ⟨ψ, hψ⟩ := hrep u
  show star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)))
      (iotaX X h ((g * k * t⁻¹ : GA D (D.sp.Y 0))))) = _ *
    star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)))
      (iotaX X h ((g * t⁻¹ : GA D (D.sp.Y 0)))))
  rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  obtain ⟨hJ, hχ⟩ := hsee.conj k
  have hmem := hJ.1 hk
  have hval := hχ hk
  set x := iotaX X h ((t⁻¹)⁻¹ * k * t⁻¹ : GA D (D.sp.Y 0)) with hxdef
  have hx : x.1 = 1 ∧ x.2 ∈ X.K2 := hmem
  have hxeq : x = (1, x.2) := Prod.ext hx.1 rfl
  have hΦk : X.B.R (1, x.2) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) =
      X.chi2 x.2 • Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)) := by
    obtain ⟨T', -, hT'⟩ := hΦ
    rw [← hT']
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (T' _)) (GlobalTheory.ConjRowLevel.reg_comp_Re X x.2 hx.2)
  have hrep2 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ (1, x.2)
  rw [hΦk] at hrep2
  have key := Formalism.L2.SG.EvalTOntoRep.contRep_unique X hrep2 (Formalism.L2.SG.EvalTOntoRep.contRep_smul X _ hψ)
  have e1 : (g * k * t⁻¹ : GA D (D.sp.Y 0)) = g * t⁻¹ * ((t⁻¹)⁻¹ * k * t⁻¹) := by group
  have hkey : ∀ z, ψ (z * x) = X.chi2 x.2 * ψ z := by
    intro z
    conv_lhs => rw [hxeq]
    exact congrFun key z
  have hm : iotaX X h ((g * k * t⁻¹ : GA D (D.sp.Y 0))) = iotaX X h ((g * t⁻¹ : GA D (D.sp.Y 0))) * x := by
    rw [e1, hxdef]
    exact map_mul (iotaX X h) _ _
  rw [hm, hkey, star_mul']
  exact congrArg (· * _) hval

end GlobalTheory.ConjRowLevelSee
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalActIntertwines
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem coeFn_sum_smul {α : Type} [MeasurableSpace α] {μ : Measure α} {ι : Type} [Fintype ι] (c : ι → ℂ)
    (u : ι → Lp ℂ 2 μ) :
    ((∑ i, c i • u i : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => ∑ i, c i * (u i : α → ℂ) x := by
  first
  | exact @_root_.GlobalTheory.FinsetSumSmulCoe.main
  | exact _root_.GlobalTheory.FinsetSumSmulCoe.main
  | (apply _root_.GlobalTheory.FinsetSumSmulCoe.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinsetSumSmulCoe.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinsetSumSmulCoe.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinsetSumSmulCoe.main ..)

theorem sum_smul_apply {ι α : Type} [Fintype ι] (L : ι → (α → ℂ) →ₗ[ℂ] (α → ℂ)) (c : ι → ℂ) (φ : α → ℂ) (y : α) :
    (∑ i, c i • L i) φ y = ∑ i, c i * L i φ y := by
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp

theorem iotaX_symm_rat {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (z : X.B.I.GA)
    (hz : z ∈ X.B.I.GFset) : (iotaX X h).symm z ∈ GQ (D.sp.Y 0) := by
  have aux : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (z : I.GA), z ∈ I.GFset →
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)).symm z ∈ GQ (D.sp.Y 0) := by
    intro I hI z hz
    subst hI
    have e : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)).symm z =
        (Formalism.IndefR.RationalEmbedding.iota D).symm z := rfl
    rw [e, Formalism.IndefR.RationalEmbedding.iota_rat, ContinuousMulEquiv.apply_symm_apply]
    exact hz
  exact aux X.B.I h z hz

theorem ev_translate {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (σ : G0g D.nd ≃* G')
    (red : X.B.I.Gf → G0g D.nd) (hB : LevelMatchB R F X h t σ red) (S : MMap (MP R)) (hS : S ∈ MultR R F)
    (k : X.B.I.Gf) (hk : k ∈ X.B.I.Kset) (x : X.B.I.GA) :
    ev (MP R) v₀ S ((iotaX X h).symm (x * (1, k)) * t) =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) (S v₀) ((iotaX X h).symm x * t) := by
  have hk' := hB.2 k hk S hS v₀ ((iotaX X h).symm x * t)
  refine Eq.trans ?_ hk'
  have e : (iotaX X h).symm (x * (1, k)) * t = (iotaX X h).symm x * t * (show GA D (D.sp.Y 0) from kap X h t k) := by
    unfold kap
    rw [map_mul]
    group
  show S v₀ _ = S v₀ _
  rw [e]
  rfl

theorem evalAct_intertwines : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) [Fintype (G0g D.nd)] (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (σ : G0g D.nd ≃* G') (red : X.B.I.Gf → G0g D.nd), LevelMatchB R F X h t σ red → ∀ S ∈ MultR R F, ∀ f : L2X X, (f =ᵐ[muX X] fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) → (∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g) → ∀ (a : G0g D.nd → ℂ) (s : G0g D.nd → X.B.I.Gf), (∀ γ, s γ ∈ X.B.I.Kset ∧ red (s γ) = γ) → (∑ γ, star (a γ) • star (X.B.R (1, s γ) (star f)) : L2X X) =ᵐ[muX X] fun x => gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (fun g => star (a (σ.symm g))) (S v₀) ((iotaX X h).symm x * t) := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F _ X h t v₀ σ red hB S hS f hf hinv a s hs
  have hU : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  have hFD := Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec

  have hφinv : ∀ γ ∈ X.B.I.GFset, ∀ y : X.B.I.GA,
      ev (MP R) v₀ S ((iotaX X h).symm (γ * y) * t) = ev (MP R) v₀ S ((iotaX X h).symm y * t) := by
    intro γ hγ y
    show S v₀ _ = S v₀ _
    rw [map_mul, mul_assoc]
    exact hinv _ (iotaX_symm_rat X h γ hγ) _
  have key : ∀ k ∈ X.B.I.Kset, ((X.B.R (1, k) f : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x =>
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) (S v₀) ((iotaX X h).symm x * t) := by
    intro k hk
    have hP : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) ((1, k) : X.B.I.GA) :=
      Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k
    have hPi : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) (((1, k) : X.B.I.GA)⁻¹) := by
      have : ((1, k) : X.B.I.GA)⁻¹ = (1, k⁻¹) := Prod.ext inv_one rfl
      rw [this]; exact Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k⁻¹
    obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map hFD hP hPi
    have e1 := X.B.R_spec (1, k) f
    have e3 : ∀ᵐ x ∂(muX X), (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) =
        ev (MP R) v₀ S ((iotaX X h).symm (X.B.I.rep X.B.fund (x * (1, k))) * t) := by
      refine ae_of_ae_map (p := fun y => (f : X.B.I.GA → ℂ) y = ev (MP R) v₀ S ((iotaX X h).symm y * t)) h1 ?_
      rw [h2]
      exact hf
    filter_upwards [e1, e3] with x a1 a3
    rw [a1]
    show (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) = _
    rw [a3]
    obtain ⟨γ, hγ, hrep, -⟩ := Formalism.MainNotions.LeviCoordinates.rr_rep_spec hFD (x * (1, k))
    rw [Formalism.MainNotions.LeviCoordinates.rr_rep_eq_rep, show (Formalism.MainNotions.LeviCoordinates.rr_rep X.B.I.GFset X.B.fund (x * (1, k))) = γ * (x * (1, k)) from hrep,
      hφinv γ hγ]
    exact ev_translate R F X h t v₀ σ red hB S hS k hk x
  have hall : ∀ᵐ x ∂(muX X), ∀ γ, ((X.B.R (1, s γ) f : L2X X) : X.B.I.GA → ℂ) x =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red (s γ)))) (S v₀) ((iotaX X h).symm x * t) :=
    ae_all_iff.2 fun γ => key (s γ) (hs γ).1
  have hsum := coeFn_sum_smul (μ := muX X) (fun γ => star (a γ)) (fun γ => star (X.B.R (1, s γ) (star f)))
  filter_upwards [hsum, hall] with x b1 b2
  rw [b1]
  simp only [Formalism.L2.SG.Pf.RowDictPf.R_star, star_star]
  simp only [b2, (hs _).2]
  unfold gaL
  refine Eq.trans ?_ (sum_smul_apply _ _ _ _).symm
  refine Fintype.sum_equiv σ.toEquiv _ _ (fun γ => ?_)
  show _ = star (a (σ.symm (σ γ))) * _
  rw [MulEquiv.symm_apply_apply]
  rfl

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjReferenceChartIndex
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch

theorem pi_conj {X : Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ Λ' : LevFam X.E X.K n SG) (x : ∀ w : SG, GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal))
    (hH : ∀ w hbar, hbar ∈ (Λ w).H ↔ x w * hbar * (x w)⁻¹ ∈ (Λ' w).H)
    (hL : ∀ w (hbar : ↥(Λ w).H) (hbar' : ↥(Λ' w).H), hbar'.1 = x w * hbar.1 * (x w)⁻¹ →
      (Λ w).lam hbar = (Λ' w).lam hbar') :
    (∀ g : GLG X.E n SG, g ∈ Λ.grp ↔ (fun w => x w * g w * (x w)⁻¹) ∈ Λ'.grp) ∧
    ∀ (g : ↥Λ.grp) (g0 : ↥Λ'.grp), (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) → Λ.chr g = Λ'.chr g0 := by
  refine ⟨fun g => ?_, fun g g0 hg => ?_⟩
  · simp only [LevFam.grp, Subgroup.mem_pi, Set.mem_univ, true_implies]
    exact forall_congr' fun w => hH w (g w)
  · rw [LevFam.chr_apply, LevFam.chr_apply]
    exact Finset.prod_congr rfl fun w _ => hL w _ _ (hg w)

section Gen

variable {Xf : Fields} {Pr : Primes Xf} {R : Ranks} {Ch : Chars Xf Pr R.m}
  {sel : HeightOneSpectrum (𝓞 Xf.F) → HeightOneSpectrum (𝓞 Xf.E)} {S : Set ℕ} {mu : Tup Xf.F Xf.E Xf.K S}
  {cst : LocCst Xf (rowSG Pr sel mu)} {L : ChIdx Xf Pr R (QE sel (mu : Chr Xf.F Xf.E Xf.K))} {G : ChGlob Xf R.m} {m2 : ℕ}

theorem cosetOne (hX : Xf.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel Xf sel) (hs : cst.sharp = true)
    (hok : L.Ok Ch sel mu cst G m2) : ∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
      SameDC (Pr := Pr) true j P.1 1 (L.h j b P) := by
  have hB := clL_base hok hX hPr hCh hs
  intro j
  induction j with
  | zero =>
    intro _ b P _
    rw [hok.zero_h]
    exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  | succ i ih =>
    intro hj b P hP
    by_cases hi : i < m2
    · obtain ⟨al, hal⟩ := hok.nonvan i hi b P
      have h1 := ih (by omega) al P hP
      have hs1 := hok.stabG i al P hP
      have hs2 := hok.stabG (i + 1) b P hP
      have h2 := (GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset Ch sel mu cst L G m2 hX hPr hCh hsel hs hok i hi P hP _ _ hs1 hs2 (by rw [hs]; exact h1)).1 hal
      have h3 := twSurjG G.σ₀ hB hi P hP _ hs2 h2
      rwa [hs] at h3
    · obtain rfl : i = m2 := by omega
      rw [hok.last_h]
      exact ⟨1, one_mem _, 1, one_mem _, by simp⟩

theorem idx_nonempty (hX : Xf.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel Xf sel) (hs : cst.sharp = true)
    (hok : L.Ok Ch sel mu cst G m2) (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) :
    ∀ j, j ≤ m2 + 1 → Nonempty (L.β j) := by
  have hB := clL_base hok hX hPr hCh hs
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨b, -⟩ := hok.zero_uniq
    exact ⟨b⟩
  | succ i ih =>
    intro hj
    by_cases hi : i < m2
    · obtain ⟨al⟩ := ih (by omega)
      obtain ⟨b, -⟩ := hok.surj i hi (fun _ => 1) (fun _ _ => one_mem _) (fun P hP => absurd (hQ P) hP)
        (fun P => ⟨al, (GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset Ch sel mu cst L G m2 hX hPr hCh hsel hs hok i hi P (hQ P) _ _ (hok.stabG i al P (hQ P))
          (one_mem _) (by rw [hs]; exact cosetOne hX hPr hCh hsel hs hok i (by omega) al P (hQ P))).2
          (twNonVanG G.σ₀ hB hi P (hQ P))⟩)
      exact ⟨b⟩
    · obtain rfl : i = m2 := by omega
      obtain ⟨b, -⟩ := hok.last_uniq
      exact ⟨b⟩

end Gen

end GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch

open Classical in

theorem idx_match : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ b : Idx I.sel (I.tup a) (I.idx a) i, ∃ (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i)
      (x : ∀ w : (B.primes X).vGs, GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ w.1.asIdeal)),
      (i + 1 = B.R.m → ∀ w, x w = 1) ∧
      (∀ g : GLG B.fields.E (B.R.N i) (B.primes X).vGs, g ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp ↔
        (fun w => x w * g w * (x w)⁻¹) ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp) ∧
      ∀ (g : ↥(levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp) (g0 : ↥(levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp),
        (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) →
        (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).chr g = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).chr g0 := by
  intro B X I h l a i hi1 hi b
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hoka := h.idx_ok a
  have hok0 := h.idx_ok I.mu0
  generalize B.R.m - 2 = m2 at hoka hok0
  have hm := hoka.hm
  have hQ0 : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs := fun P =>
    (Finset.mem_union.1 P.2).resolve_right (by
      have e : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
      rw [e]
      exact Finset.notMem_empty _)
  rcases b with ⟨_ | β, hb⟩
  · exact absurd (hb.2 hi) (by simp)
  have key : ∃ β0 : (I.idx I.mu0).β i, ∀ w : (B.primes X).vGs, ∃ (r κ : AutY B.fields B.R i),
      r ∈ Loc.R1 B.fields.E (B.R.N i) (cOf B.R i) ∧ κ ∈ Jat (Pr := B.primes X) true i w.1 ∧
      (I.idx a).h i β ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * (I.idx I.mu0).h i β0 ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ ∧
      (i + 1 = B.R.m → r = 1) := by
    by_cases hlast : i = m2 + 1
    · subst hlast
      obtain ⟨β0, -⟩ := hok0.last_uniq
      refine ⟨β0, fun w => ⟨1, 1, one_mem _, one_mem _, ?_, fun _ => rfl⟩⟩
      rw [hoka.last_h, hok0.last_h]
      simp
    · obtain ⟨β0⟩ := idx_nonempty hX l.pr h.ch_ok h.sel_ok (h.sharp I.mu0) hok0 hQ0 i (by omega)
      refine ⟨β0, fun w => ?_⟩
      obtain ⟨r1, hr1, κ1, hκ1, e1⟩ :=
        cosetOne hX l.pr h.ch_ok h.sel_ok (h.sharp a) hoka i (by omega) β ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2
      obtain ⟨r0, hr0, κ0, hκ0, e0⟩ :=
        cosetOne hX l.pr h.ch_ok h.sel_ok (h.sharp I.mu0) hok0 i (by omega) β0 ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2
      refine ⟨r1 * r0⁻¹, κ0⁻¹ * κ1, mul_mem hr1 (inv_mem hr0), mul_mem (inv_mem hκ0) hκ1, ?_, fun e => absurd e (by omega)⟩
      rw [e1, e0]
      group
  obtain ⟨β0, hw⟩ := key
  choose r κ hr hκ he hr1 using hw
  have gc := fun w => GlobalTheory.T.doubleCoset_reps_conjugate_level_groups I.Ch I.sel (I.tup a) (I.tup I.mu0) (I.cst a) (I.cst I.mu0) (I.idx a) (I.idx I.mu0) I.glob m2
    hX l.pr h.ch_ok (h.sharp a) (h.sharp I.mu0) hoka hok0 i (by omega) β β0 w (r w) (κ w) (hr w) (hκ w) (he w)
  choose x hx1 hxH hxL using gc
  refine ⟨⟨some β0, by simp [hi]⟩, x, fun e w => hx1 w (hr1 w e), ?_⟩
  exact pi_conj ((I.idx a).levG i β) ((I.idx I.mu0).levG i β0) x hxH hxL

end GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionFieldMapFullFlagGenericPointStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionField_map_fullFlag_generic_point : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∃ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ ∧ CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) := by
  first | exact @GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic | exact GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic | (intros; apply GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyHeckeCompatibleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_hecke_compatible : ∀ (hArt : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (hψ : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (μ : D.naut.CG 1), D.naut.csd μ → (∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j) → ∀ w, SplitOut X.nd i w → D.naut.unr (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) ∧ ∀ (B : ValuationSubring X.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om), IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ → D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2)) = {(qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i)))} := by
  first | exact @GlobalTheory.AutPart.chiMu_unr_frob | exact GlobalTheory.AutPart.chiMu_unr_frob | (intros; apply GlobalTheory.AutPart.chiMu_unr_frob <;> assumption)
end

