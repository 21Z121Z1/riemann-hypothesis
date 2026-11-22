import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0365
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ScalAtZeroOfLiftMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunOFockMovedVecTop
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowClaim

theorem isThetaFunO_fock_movedVec_top {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {U : Set T} (S : GridChoice W U) {j : ℕ} (hj : j < D.R.m)
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (t : T) (d : FinDatum G t (.top t j))
    (hd : S.Z.HasVec d) :
    IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (W.fock (.top t j) (movedVec t S d) Q) := by
  have hr : (Pair.top t j : Pair T).InRange D.R.m := by
    show j + 1 ≤ D.R.m
    omega
  have hω := W.om_is _ hr
  obtain ⟨f, hf⟩ := hd
  have hf0 : IsThetaFunO W.ψ _ _ f :=
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is hf ((S.Z.vac_is (.top t j) (show j + 1 ≤ D.R.m by omega)).2.theta)
  have hv : IsThetaFunO W.ψ _ _ (S.Z.vec d) := by
    rw [Normal.vec, FinDatum.vec_eq W hf]
    exact hω.om_pres _ _ hf0
  have hm : IsThetaFunO W.ψ _ _ (movedVec t S d) := hω.om_pres _ _ hv
  exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hm Q

theorem kerA_col_aut_cont : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (t : T), t ∈ U → ∀ (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    (∀ γ ∈ GQ (G.V (.top j)), ∀ g h, W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) (γ * g) h =
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) g h) ∧
    ∀ z h, Continuous fun k : GinfC (G.V (.top j)) =>
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) (z * k) h := by
  intro D T L sc G W U S μ0 _ j hj Q t _ d hd
  have hr : (Pair.top t j : Pair T).InRange D.R.m := by
    show j + 1 ≤ D.R.m
    omega
  have hω := W.om_is _ hr
  have hF := isThetaFunO_fock_movedVec_top S hj Q t d hd
  refine ⟨fun γ hγ g h => ?_, fun z h => ?_⟩
  · show thetaKO (W.om (.top t j)) (γ * g) h _ = thetaKO (W.om (.top t j)) g h _
    have e : ((γ * g, h) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) = (γ, 1) * (g, h) := by simp
    unfold thetaKO
    rw [e, map_mul]
    exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hF)
  · show Continuous fun k : GinfC (G.V (.top j)) => thetaKO (W.om (.top t j)) (z * k) h _
    exact (hω.om_cont _ hF 0).comp ((continuous_const.mul continuous_subtype_val).prodMk continuous_const)

end GlobalTheory.RowClaim

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KeyFinHolds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEx

theorem keyFin_holds : KeyFin := by
  classical
  intro P Ξ hΞ
  let U : Key P := {p | p.1 ∈ Ξ ∧ {w | ¬ p.1.UnrAt w}.Finite ∧ ∀ w ∈ p.2, ¬ p.1.UnrAt w}
  have hU : U.Finite := by
    refine (hΞ.biUnion (t := fun ξ => {p ∈ U | p.1 = ξ}) fun ξ _ => ?_).subset fun p hp => Set.mem_biUnion hp.1 ⟨hp, rfl⟩
    by_cases hf : {w | ¬ ξ.UnrAt w}.Finite
    · refine ((hf.toFinset.powerset.finite_toSet).image fun Q => (ξ, Q)).subset ?_
      rintro ⟨a, Q⟩ ⟨h, rfl⟩
      exact ⟨Q, Finset.mem_coe.2 (Finset.mem_powerset.2 fun w hw => hf.mem_toFinset.2 (h.2.2 w hw)), rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro ⟨a, Q⟩ ⟨h, rfl⟩
      exact hf h.2.1
  refine ⟨{κ | κ ⊆ U}, hU.finite_subsets, ?_⟩
  rintro X T L μ₀ rfl hL h
  refine ⟨keyOf L, ?_, HEq.rfl⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨ξ, h1, h2⟩ := h t
  refine ⟨by rw [← eq_of_heq h2] at h1; exact h1, ?_, fun w hw => (hL.Q_ram t w).2 (Or.inl hw)⟩
  refine ((L.Q t).finite_toSet.union ((L.Q t).finite_toSet.image Formalism.DivisionValues.conjPl)).subset fun w hw => ?_
  rcases (hL.Q_ram t w).1 hw with h | ⟨w', h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨w', h, (GlobalTheory.GoodPrimes.isConjPl_iff.1 h').symm⟩

end GlobalTheory.RowEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatAtVSelfDual
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.PsiUnrSelfDual

open GlobalTheory.InertSelfDual

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem latAtV_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr B.ψ v →
    (∀ z : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z →
      (z ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W v ↔ ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W v,
        B.ψ (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F G.V.J)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F G.W.J) z γ) = 1)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hunr z hz
  have hV := hT.geo.hV
  have hW := hT.geo.hW
  constructor
  · intro hzm γ hγ
    have h := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V G.W _ _ _ _ hT.base hV hW v (-1) 1
      (by rw [map_one]; exact one_mem _) z hzm γ hγ
    simpa using h
  · intro hψ
    haveI := hT.base.unram
    obtain ⟨m, s, c, hsc⟩ := exists_traceFamily (F := F) (E := E)
    obtain ⟨k, S, T, hS, hTm, hTS⟩ := exists_formFrame σ G.V.J (det_ne_zero_of_herm σ B hV) G.V.L hV.lat
      (fun y hy => (hV.dual y).2 fun x hx => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]; exact RingOfIntegers.isIntegral_coe r)
    obtain ⟨k', S', T', hS', hTm', hTS'⟩ := exists_formFrame σ G.W.J (det_ne_zero_of_skew σ B hW) G.W.L hW.lat
      (fun y hy => (hW.dual y).2 fun x hx o => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]
        exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (RingOfIntegers.isIntegral_coe r)))
    set C := incM F (G.V.J * S.map σ)ᵀ * z * (incM F (G.W.J * S'.map σ)ᵀ)ᵀ with hC
    have hCat : ∀ j l, At (evFin F v) (C j l) := fun j l u hu => by
      have hz' : u • z = 0 := hz u hu
      have h1 : u • C = incM F (G.V.J * S.map σ)ᵀ * (u • z) * (incM F (G.W.J * S'.map σ)ᵀ)ᵀ := by
        rw [hC, Matrix.mul_smul, Matrix.smul_mul]
      rw [hz', Matrix.mul_zero, Matrix.zero_mul] at h1
      have := congrFun (congrFun h1 j) l
      simpa using this
    have hint : ∀ (e : E), IsIntegral ℤ e → ∀ j l, evFin F v (Algebra.trace (AF F) (AE F E)
        (inclR (F := F) (AF F) (σ e) * C j l)) ∈ v.adicCompletionIntegers F := by
      intro e hei j l
      set M := incM F (Matrix.vecMulVec (fun i => e * S i j) (fun i => S' i l)) with hM
      set t := symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) z M with ht
      have hx : (fun i => e * S i j) ∈ G.V.L := by
        have := G.V.L.smul_mem (⟨e, hei⟩ : 𝓞 E) (hS j)
        convert this using 1
        ext i; first | rfl | simp [Algebra.smul_def]
      have htat : At (evFin F v) t := fun u hu => by
        have := GlobalTheory.LatVac.symp_smul_smul σ (incM F G.V.J) (incM F G.W.J) (-1) u 1 z M
        rw [hz u hu, one_smul, mul_one, GlobalTheory.LatVacArith.symp_zero_left] at this
        exact this.symm
      have htC : t = -Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (σ e) * C j l) := by
        rw [ht, symp, hM, hTens_frame, neg_one_mul, map_neg]
      have key : ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v t * y) = 1 := by
        intro y hy
        have hmem : GlobalTheory.LatVac.liftV v y • M ∈ latAtV G.V G.W v :=
          AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v y, by rw [GlobalTheory.LatVac.evFin_liftV]; exact hy,
            _, hx, _, hS' l, rfl⟩
        have h1 := hψ _ hmem
        have h2 := GlobalTheory.LatVac.symp_smul_smul σ (incM F G.V.J) (incM F G.W.J) (-1) 1 (GlobalTheory.LatVac.liftV v y) z M
        rw [one_smul, one_mul] at h2
        rw [h2] at h1
        have hat2 : At (evFin F v) (GlobalTheory.LatVac.liftV v y * t) := fun u hu => by
          have := htat u hu
          rw [smul_eq_mul] at this ⊢
          rw [mul_left_comm, this, mul_zero]
        rw [GlobalTheory.VacIndic.psi_of_at _ hat2, map_mul, GlobalTheory.LatVac.evFin_liftV, mul_comm] at h1
        exact h1
      have := (hunr _).1 key
      rw [htC, map_neg] at this
      exact neg_mem_iff.1 this
    have hσ : Function.Bijective σ := AlgHom.bijective σ
    have hint' : ∀ i j l, evFin F v (Algebra.trace (AF F) (AE F E)
        (inclR (F := F) (AF F) (c i : E) * C j l)) ∈ v.adicCompletionIntegers F := by
      intro i j l
      obtain ⟨e, he⟩ := hσ.2 (c i : E)
      have hei : IsIntegral ℤ e := by
        rw [← isIntegral_algHom_iff ((σ : E →+* E).toIntAlgHom) hσ.1]
        show IsIntegral ℤ (σ e)
        rw [he]; exact RingOfIntegers.isIntegral_coe _
      have := hint e hei j l
      rwa [he] at this
    rw [decomp T (G.V.J * S.map σ)ᵀ T' (G.W.J * S'.map σ)ᵀ hTS hTS' z, ← hC]
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.sum_mem _ fun l _ => ?_
    rw [trace_expand s c hsc (C j l), Finset.sum_smul]
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
    refine ⟨_, fun u hu => ?_, hint' i j l, fun r => (s i : E) * T r j, ?_, fun r => T' r l, hTm' l, ?_⟩
    · rw [smul_eq_mul, ← smul_eq_mul, ← map_smul, ← mul_smul_comm]
      have := hCat j l u hu
      rw [this, mul_zero, map_zero]
    · have := G.V.L.smul_mem (s i) (hTm j)
      convert this using 1
      ext r; simp [Algebra.smul_def]
    · rw [smul_assoc]
      congr 1
      ext p q
      simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, map_mul, smul_eq_mul]
      ring

end GlobalTheory.PsiUnrSelfDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelTowerConvergenceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_tower_convergence : GlobalTheory.FunPr.Hypotheses₂ → RowTower → RowConv := by
  first | exact @GlobalTheory.RowConvAll.rowConv | exact GlobalTheory.RowConvAll.rowConv | (intros; apply GlobalTheory.RowConvAll.rowConv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarIdentityOffFixedPlaceBaseLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalarOff

section SlopeTestRemainingChoices
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem range_adjoint_smul_le' {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (c : ℂ) (f : E →ₗ[ℂ] E') :
    LinearMap.range (LinearMap.adjoint (c • f)) ≤ LinearMap.range (LinearMap.adjoint f) := by
  rintro _ ⟨y, rfl⟩
  rw [RealDat3.adjoint_smul']
  exact ⟨starRingEnd ℂ c • y, by simp⟩

theorem jV_mem_range (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (t : T0) :
    ∀ z ∈ (R.toCx3 F).Zl j t, R.jV j t z ∈ LinearMap.range (LinearMap.adjoint (R.thG j t)) := by
  intro z hz
  have hx1 := range_adjoint_smul_le' (R.phs j) (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j t)) hz
  exact (GlobalTheory.AdjBlock.mem_range_adjoint_tw (twAt D.what₂.embLL A3.A.v0) (R.thG j t) (R.jV j t z)).1 hx1

end SlopeTestRemainingChoices

theorem galD_base : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.ConjScalar.ConjScalarAt R.toRealDat → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → R.toRealDat.LUnif → ((R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso) → (R.toCx3 F).GalD F.cr false := by
  intro hHowe hCRL D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s hOk hC hEx hCS hψ fw hBar hIo hPins hRow0 hPT hU hfacts
  obtain ⟨h5, hrat, h3w, hprov⟩ := hfacts
  have hcore := GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx
  intro j v hv p
  obtain ⟨a, ha⟩ := GlobalTheory.T.thetaLiftPoints_part_eigenforms_coefficientField R F s hOk hC h3w j p
  have hOne := hPT j hU (hRow0 j)
  have hHerm : Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A3.A.fam.L j A3.A.μ0).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0))
      ((A3.A.fam.L j A3.A.μ0).XQ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0)) := hprov j
  have hBH : BlockHyp (A3.A.fam.L j A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 s :=
    ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.lifts j A3.A.μ0⟩
  have hfE := GlobalTheory.QuotRational.fE_mem_cmMax _ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) A3.A.v0 s hBH hHerm
  obtain ⟨l, hl⟩ := GlobalTheory.T.rationalLift_readings_scale_classSum_eigenspaces hHowe hCRL T R.toRealDat κ v₀ O F.lv2 _ hcore.1 hψ hCS fw hBar hIo hU hPins j hOne
    (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) hHerm hfE (jV_mem_range R F j A3.A.μ0) v.embedding a
  have hmaj := (GlobalTheory.Proof.ConjugateTransposeMajorant.majAt_eq_csumAt _ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) hHerm hfE).1 v
  have hco := GlobalTheory.ConjScalarCoord.liftMat_isRatLift_inner R F h5 hrat j
  have hS : ∀ x, (R.toCx3 F).tC F.cr false j A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp j p → ∀ y,
      ⟪(R.toCx3 F).wC false j v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec x)),
        (R.toCx3 F).wC false j v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec y))⟫_ℂ =
      ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT j A3.A.μ0) v x y := by
    intro x hx y
    have e1 := hco.2 v hv x y
    have e2 := hl x (F.cr.toL (R.toCx3 F).zs false j A3.A.μ0 y) _ _ (ha x hx) (hco.1 x) (hco.1 y)
    have e3 := hmaj x y
    rw [e1, e2]
    erw [e3]
    exact mul_left_comm _ _ _
  intro x hx y
  by_cases hP : R.PartAt F j p v
  · have e : R.lam3 j A3.A.μ0 p v = l := hC.scal.off j p v l hv hP hS
    exact (hS x hx y).trans (congrArg (fun t : ℝ => (t : ℂ) * _) e.symm)
  · have h0 := GlobalTheory.ScalarConjugation.maj_eq_zero _ v x y (by by_contra hn; exact hP ⟨x, hx, hn⟩)
    exact (hS x hx y).trans ((mul_eq_zero_of_right _ h0).trans (mul_eq_zero_of_right _ h0).symm)

end GlobalTheory.ConjScalarOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasColOfChoice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColMeas

open Matrix
open scoped TensorProduct

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem frame_sub_eq (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E))
    (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    (β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ v - v) = ((intGL F E n y).1 - 1) *ᵥ ((β⁻¹).1 *ᵥ v) := by
  have e3 : (frGL β y).1 = β.1 * (intGL F E n y).1 * (β⁻¹).1 := rfl
  rw [e3, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]

theorem mem_princGL_iff {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hfr : IsFrame β Λ) (I : Ideal (𝓞 E)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ GlobalTheory.Grid.princGL β I ↔ x ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := F) Λ) ∧
      ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ v - v ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ) := by
  rw [GlobalTheory.Grid.mem_princGL, ← stabilizer_eq_stabilizer_lattice F E n Λ β hfr]
  constructor
  · rintro ⟨y, rfl, hy⟩
    refine ⟨⟨y, rfl⟩, fun v hv => ?_⟩
    rw [GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr I, frame_sub_eq]
    intro i
    have hw := (hfr v).1 hv
    simp only [Matrix.mulVec, dotProduct]
    refine GlobalTheory.FrameIdeal.inId_sum _ fun k => ?_
    rw [mul_comm]
    exact GlobalTheory.FrameIdeal.inId_mul (hw k) ⟨_, hy i k, GlobalTheory.LevRedTriv.coe_sub_one_apply y i k⟩
  · rintro ⟨⟨y, rfl⟩, h⟩
    refine ⟨y, rfl, fun i j => ?_⟩
    have h1 := (GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr I _).1 (h _ (GlobalTheory.ChainOnto.LStab.col_mem_hatL hfr j)) i
    have e : (β⁻¹).1 *ᵥ (β.1 *ᵥ Pi.single j 1) = Pi.single j (1 : E ⊗[F] Formalism.L2.Herm.Af F) := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [frame_sub_eq, e, Matrix.mulVec_single_one] at h1
    obtain ⟨s, hs, e⟩ := h1
    have : s = (y.1 - 1) i j := Subtype.ext (e.trans (GlobalTheory.LevRedTriv.coe_sub_one_apply y i j).symm)
    exact this ▸ hs

theorem princ_eq_congLev [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ) (I : Ideal (𝓞 E)) :
    UA hc J ⊓ GlobalTheory.Grid.princGL β I = congLev hc J Λ I := by
  ext x
  rw [Subgroup.mem_inf, mem_princGL_iff hfr, mem_congLev]

end General

end GlobalTheory.ColMeas

end

noncomputable section

namespace GlobalTheory.ColMeas

open GlobalTheory.GridJoin

theorem exists_measDat {D : D7} (N : GlobalTheory.Grid.Node D) {V : HSp D} (hsp : SameSp V N.V)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hlat : HEq N.Λ Λ) (hfr : IsFrame N.β N.Λ)
    (I : Ideal (𝓞 D.host.E)) {ν : Measure (GA D V)} {fd : Set (GA D V)}
    (hm : Lev.IsMeasFD V (congLev D.sp.cm V.gram Λ I) ν fd) :
    ∃ md : N.MeasDat, HEq md.ν ν ∧ HEq md.fd fd ∧ md.Is False (N.princ I) := by
  obtain ⟨L, h1, h2, e⟩ := hsp
  obtain ⟨V', S, M, Λ', β⟩ := N
  simp only at e hlat hfr ⊢
  subst e
  obtain rfl := eq_of_heq hlat
  refine ⟨⟨ν, fd⟩, HEq.rfl, HEq.rfl, fun h => h.elim, fun _ => ?_⟩
  unfold GlobalTheory.Grid.Node.princ
  rw [princ_eq_congLev _ _ hfr]
  exact hm

end GlobalTheory.ColMeas

end

noncomputable section

namespace GlobalTheory.ColMeas

theorem measCol_of_choice : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
    (G : GlobalTheory.Grid.GridPre R), G.IsMeas → GlobalTheory.GridJoin.SpMatch G ch.W →
    (∀ i, i ≤ D.R.m → Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ) → ch.M.IsRow →
    ∃ (m00 : (G.V 0 0).MeasDat) (mV : ∀ i j, (G.nV i j).MeasDat),
      (GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).IsMeas ∧
      (∀ i, i ≤ D.R.m → HEq ((GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).measCol i).ν (ch.M.ν (.grid i 0))) ∧
      (∀ i, i ≤ D.R.m → HEq ((GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX).measCol i).fd (ch.M.fd (.grid i 0))) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch G hG hsp hfr hrow
  have H : ∀ i, ∃ md : (G.V i 0).MeasDat, i ≤ D.R.m → HEq md.ν (ch.M.ν (.grid i 0)) ∧
      HEq md.fd (ch.M.fd (.grid i 0)) ∧ md.Is False ((G.V i 0).princ (G.lvl R)) := by
    intro i
    by_cases hi : i ≤ D.R.m
    · have hN := hsp.vert i 0 hi (Nat.zero_le _)
      have hr := hrow.row i hi
      have hne : GlobalTheory.ChiGrid.Node.neg D.R.m (.grid i 0) ≠ 0 := by
        simp only [GlobalTheory.ChiGrid.Node.neg, Nat.sub_zero]
        have := D.R.two_le_m
        omega
      unfold Vol.IsAt at hr
      rw [if_neg hne] at hr
      obtain ⟨md, h1, h2, h3⟩ := exists_measDat (G.V i 0) hN.sp hN.lat (hfr i hi) _ hr
      exact ⟨md, fun _ => ⟨h1, h2, hsp.lvl ▸ h3⟩⟩
    · exact ⟨G.measCol i, fun h => absurd h hi⟩
  choose f hf using H
  refine ⟨f 0, fun i j => match j with | 0 => f (i + 1) | j + 1 => G.mV i (j + 1),
    ⟨fun i hi => ?_, fun i j hi hj => hG.vert i j hi hj, hG.P, hG.X⟩, fun i hi => ?_, fun i hi => ?_⟩
  · cases i <;> exact (hf _ hi).2.2
  · cases i <;> exact (hf _ hi).1
  · cases i <;> exact (hf _ hi).2.1

end GlobalTheory.ColMeas

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSpanThetaSeriesOfBoundedHolomorphicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_thetaSeries_of_boundedHolomorphic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → HolUpTo C B (ThFr.wtOf C.X C.hr c c' S.rank) z φ → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → φ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') := by
  first | exact @GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo | exact GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo | (intros; apply GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelTarget_bump_mul_coreTheta_exists : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (v : VolM D ρ S.rank) (β : Mx D S.rank ρ → ℂ) (g : WO S T₀ → ℂ), IsBump β → IsThetaFunO ψ S T₀ g → ∃ Φ, IsThetaFunO ψ S T Φ ∧ ∀ y, d.mixT S ψ v.μ v.𝓕 Φ y = β y • g := by
  first | exact @GlobalTheory.MixAdj.mixT_bump_smul | exact GlobalTheory.MixAdj.mixT_bump_smul | (intros; apply GlobalTheory.MixAdj.mixT_bump_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAllDataProductsEqFourierJacobiPeriodStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodAllData_products_eq_fourierJacobiPeriod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Lnk B.L B.ζ L' ζ') (χA χz χ' : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omz : Om J.W₀ L'), s.χV = χA * χz → IsWeilDatumO ψ B.A J.W₀ χA s.χW oma → IsWeilDatumO ψ J.W₀ L' χ' χz omz → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) Ξ₁ Ξ₂, IsThetaFunO ψ B.A J.W₀ Ξ₁ → IsThetaFunO ψ B.L J.W₀ Ξ₂ → J.perAll ψ B s.om₀ φ G (B.o.boxS J.W₀ Ξ₁ Ξ₂) = J.per ψ ζ' omz (liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁) G (fun w => star (Ξ₂ (l.κ J.W₀ w))) := by
  first | exact @GlobalTheory.LinkProd.perAll_box_eq_per | exact GlobalTheory.LinkProd.perAll_box_eq_per | (intros; apply GlobalTheory.LinkProd.perAll_box_eq_per <;> assumption)
end

