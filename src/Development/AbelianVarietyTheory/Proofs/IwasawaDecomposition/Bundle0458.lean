import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0449
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0109
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
import Formalism.LocalRingCardinality.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0448
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0007
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RecExGOfRecAtG
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0124
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStep
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationGoodRowsToConjugateGoodRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eC_conj_of_match {R : RealDat D A Ks} {σ : G0g D.nd ≃* G'} (hC : LevelMatchC R σ) (g k : G') :
    RealDat.eC (A := A) D.what₂.embLL (g * k * g⁻¹) = RealDat.eC (A := A) D.what₂.embLL k := by
  have e : ∀ x : G', RealDat.eC (A := A) D.what₂.embLL x = star (D.ntypes.e0.coeff (σ.symm x)) := fun x => by
    rw [hC, MulEquiv.apply_symm_apply]
  rw [e, e, show σ.symm (g * k * g⁻¹) = σ.symm g * σ.symm k * (σ.symm g)⁻¹ by simp, GlobalTheory.ProjComm.goodProjector_coeff_classFunction]

theorem eC_conv_of_match {R : RealDat D A Ks} {σ : G0g D.nd ≃* G'} (hC : LevelMatchC R σ) (g : G') :
    ∑ a, RealDat.eC (A := A) D.what₂.embLL a * RealDat.eC (A := A) D.what₂.embLL (a⁻¹ * g) =
      RealDat.eC (A := A) D.what₂.embLL g := by
  have e : ∀ x : G', RealDat.eC (A := A) D.what₂.embLL x = star (D.ntypes.e0.coeff (σ.symm x)) := fun x => by
    rw [hC, MulEquiv.apply_symm_apply]
  simp only [e]
  rw [← GlobalTheory.ProjectedLift.conv_of_idem _ (GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D).2 (σ.symm g), star_sum]
  refine Fintype.sum_equiv σ.symm.toEquiv _ _ fun a => ?_
  show _ = star (D.ntypes.e0.coeff (σ.symm a) * D.ntypes.e0.coeff ((σ.symm a)⁻¹ * σ.symm g))
  rw [star_mul', map_mul, map_inv]

theorem goodProjector_maps_rows_into_goodRows {R : RealDat D A Ks} {F : Face D A} (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf)
    {σ : G0g D.nd ≃* G'} (hC : LevelMatchC R σ) {S : MMap (MP R)} (hS : S ∈ MultR R F) :
    postOn (MP R) R.e0 S ∈ EP R F := by
  have hX : S ∈ GlobalTheory.Mem.Th.multAt R (R.levR F true) A.μ0 0 := by
    rw [GlobalTheory.Mem.Th.multAt_zero]; exact hS
  have h0 := GlobalTheory.Mem.Th.multAt_le R _ A.μ0 0 hX
  rw [GlobalTheory.Mem.Th.multAt_zero] at h0 hX
  have hL := GlobalTheory.ProjectedLift.liftsExist_rows R hl
  have h1 : postOn (R.MY 0) R.e0 S ∈ R.EEat R.triv :=
    GlobalTheory.ProjectedLift.postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hi hL R.eG _ (eC_conv_of_match hC) h0
  refine ⟨GlobalTheory.KeepLevel.mem_mult_of_level h1.1 fun v => ?_, h1.2⟩
  have a0 : HasType _ (R.βY 0) (R.dat0 R.triv) (S v) := ((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ S).1 h0).lev v
  refine GlobalTheory.KeepLevel.hasType_of_comm (L := R.dat0 R.triv) (P := R.levR F true) hL R.e0 a0
    (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 h1.1).lev v) (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ S).1 hX).lev v)
    fun g => ?_
  obtain ⟨g, rfl⟩ := R.eG.surjective g
  exact GlobalTheory.ProjComm.gaL_comm (L := R.dat0 R.triv) R.eG _ (eC_conj_of_match hC) g a0

set_option maxHeartbeats 1000000 in

theorem evalOn_good : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ), R.toLevCh.Is A.μ0 → R.models_inf → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → SeeAt R F X h t → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) X G (iotaX X h).toMulEquiv t c := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h G t v₀ c hl hi hv hsee hJe
  obtain ⟨σ, red, hA, hB, hC⟩ := hsee.mat
  obtain ⟨J, hJ⟩ := hJe
  have hle : EP R F ≤ MultR R F := inf_le_left
  have hmult : ∀ S ∈ MultR R F, IsMultMap R.θ (MP R) (JR R F) (chiR R F) S := fun S hS =>
    (GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ S).1 hS
  have hGQ : ∀ S ∈ MultR R F, ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g := fun S hS =>
    ((hmult S hS).aut v₀).left
  choose s0 hs0 using hB.1.2.2.1
  have hs0' : ∀ γ, s0 γ ∈ X.B.I.Kset ∧ red (s0 γ) = γ := hs0

  have hinv : ∀ S : MultR R F, ∀ k ∈ X.B.I.Kg X.B.g,
      X.B.R (1, k) (star ((J S : conjRows X) : L2X X)) = star ((J S : conjRows X) : L2X X) := by
    intro S k hk
    classical
    have hkK : k ∈ X.B.I.Kset := hk.1
    have hrk : red k = 1 := (hB.1.2.2.2 k hkK).2 hk
    let a : G0g D.nd → ℂ := fun γ => if γ = 1 then 1 else 0
    let s : G0g D.nd → X.B.I.Gf := fun γ => if γ = 1 then k else s0 γ
    have hs : ∀ γ, s γ ∈ X.B.I.Kset ∧ red (s γ) = γ := by
      intro γ
      by_cases hγ : γ = 1
      · subst hγ
        simp only [s, if_pos rfl]
        exact ⟨hkK, hrk⟩
      · simp only [s, if_neg hγ]
        exact hs0' γ
    have hI := GlobalTheory.Mem.SRe.evalAct_intertwines D G' Pl0 T A Ks R F X h t v₀ σ red hB (S : MMap (MP R)) S.2
      ((J S : conjRows X) : L2X X) (hJ S).1 (hGQ _ S.2) a s hs
    have e1 : (∑ γ, star (a γ) • star (X.B.R (1, s γ) (star ((J S : conjRows X) : L2X X))) : L2X X) =
        star (X.B.R (1, k) (star ((J S : conjRows X) : L2X X))) := by
      rw [Finset.sum_eq_single (1 : G0g D.nd)]
      · simp [a, s]
      · intro b _ hb
        simp [a, hb]
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    have hsum : (gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG fun g => star (a (σ.symm g))) =
        actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG 1) := by
      unfold gaL
      rw [Finset.sum_eq_single (1 : G')]
      · have ha1 : a (σ.symm 1) = 1 := by simp [a]
        simp only [ha1, star_one, one_smul]
        rfl
      · intro b _ hb
        have hb' : σ.symm b ≠ 1 := by
          intro h1
          apply hb
          simpa using congrArg σ h1
        have ha0 : a (σ.symm b) = 0 := by simp [a, hb']
        simp only [ha0, star_zero, zero_smul]
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    have e2 : ∀ y : GA D (D.sp.Y 0),
        (gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG fun g => star (a (σ.symm g))) ((S : MMap (MP R)) v₀) y =
          (S : MMap (MP R)) v₀ y := by
      intro y
      rw [hsum]
      have hB2 := hB.2 k hkK (S : MMap (MP R)) S.2 v₀ y
      rw [hrk, map_one σ] at hB2
      refine hB2.symm.trans ?_
      have hK2 := (Formalism.L2.SG.Closed.level_subgroup_properties X).1 k hk
      obtain ⟨hkJ, hkχ⟩ := hA k hK2.1
      have hχ1 : chiR R F (kap X h t k) = 1 := hkχ.trans (by rw [hK2.2, star_one])
      refine ((hmult _ S.2).lev v₀ _ hkJ y).trans ?_
      rw [hχ1, one_mul]
    have e3 : ((star (X.B.R (1, k) (star ((J S : conjRows X) : L2X X))) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
        (((J S : conjRows X) : L2X X) : X.B.I.GA → ℂ) := by
      rw [← e1]
      exact hI.trans (Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => e2 _) (hJ S).1.symm)
    have e4 := congrArg star (Lp.ext e3)
    rwa [star_star] at e4

  have key : ∀ S : MultR R F,
      ((J ⟨postOn (MP R) R.e0 S, hle (goodProjector_maps_rows_into_goodRows hl hi hC S.2)⟩ : conjRows X) : L2X X) =
        star (G.Rg (star ((J S : conjRows X) : L2X X))) := by
    intro S
    have hexp := GlobalTheory.Mem.GoodExpand.rg_expand D X G red s0 hB.1 hs0' _ (hinv S)
    have hI := GlobalTheory.Mem.SRe.evalAct_intertwines D G' Pl0 T A Ks R F X h t v₀ σ red hB (S : MMap (MP R)) S.2
      ((J S : conjRows X) : L2X X) (hJ S).1 (hGQ _ S.2) (fun γ => D.ntypes.e0.coeff γ) s0 hs0'
    have e1 : star (G.Rg (star ((J S : conjRows X) : L2X X))) = ∑ γ, star (D.ntypes.e0.coeff γ) •
        star (X.B.R (1, s0 γ) (star ((J S : conjRows X) : L2X X))) := by
      rw [hexp]
      change conjL (muX X) _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [LinearIsometryEquiv.map_smulₛₗ, conjL_apply, starRingEnd_apply]
    have e2 : (gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG fun g => star (D.ntypes.e0.coeff (σ.symm g))) = R.e0 := by
      unfold RealDat.e0
      congr 1
      funext g
      rw [hC, MulEquiv.apply_symm_apply]
    rw [e1]
    apply Lp.ext
    refine (hJ _).1.trans (Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => ?_) hI.symm)
    rw [e2]
    rfl
  have hEPS : ∀ S : MultR R F, (S : MMap (MP R)) ∈ EP R F ↔ postOn (MP R) R.e0 S = S := by
    intro S
    constructor
    · intro hS
      exact sub_eq_zero.1 (LinearMap.mem_ker.1 hS.2)
    · intro e
      exact ⟨S.2, LinearMap.mem_ker.2 (sub_eq_zero.2 e)⟩
  have hconj : ∀ Fx : L2X X, Fx ∈ EEC X G → Fx ∈ conjRows X := fun Fx hF => (Submodule.mem_inf.1 hF).1
  let L0 : EP R F →ₗ[ℂ] L2X X :=
    (conjRows X).subtype ∘ₗ (J : MultR R F →ₗ[ℂ] conjRows X) ∘ₗ Submodule.inclusion hle
  have hL0 : ∀ S : EP R F, L0 S ∈ EEC X G := by
    intro S
    have hS1 : postOn (MP R) R.e0 (Submodule.inclusion hle S : MultR R F) = (Submodule.inclusion hle S : MultR R F) :=
      (hEPS _).1 S.2
    have k1 := key (Submodule.inclusion hle S)
    have e : (⟨postOn (MP R) R.e0 (Submodule.inclusion hle S : MultR R F),
        hle (goodProjector_maps_rows_into_goodRows hl hi hC (Submodule.inclusion hle S).2)⟩ : MultR R F) = Submodule.inclusion hle S :=
      Subtype.ext hS1
    rw [e] at k1
    have k2 : G.Rg (star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X)) =
        star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) := by
      have k3 := congrArg star k1
      rw [star_star] at k3
      exact k3.symm
    refine Submodule.mem_inf.2 ⟨(J (Submodule.inclusion hle S)).2, LinearMap.mem_ker.2 ?_⟩
    change G.Rg (star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X)) -
      star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) = 0
    rw [k2, sub_self]
  let L : EP R F →ₗ[ℂ] EEC X G := L0.codRestrict (EEC X G) hL0
  have hLv : ∀ S : EP R F, ((L S : EEC X G) : L2X X) = ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) :=
    fun S => rfl
  have hinj : Function.Injective L := by
    intro x y hxy
    have e1 : ((L x : EEC X G) : L2X X) = ((L y : EEC X G) : L2X X) := by rw [hxy]
    rw [hLv, hLv] at e1
    exact Submodule.inclusion_injective hle (J.injective (Subtype.ext e1))
  have hsurj : Function.Surjective L := by
    intro Fx
    let F' : conjRows X := ⟨(Fx : L2X X), hconj _ Fx.2⟩
    let S : MultR R F := J.symm F'
    have hJS : ((J S : conjRows X) : L2X X) = (Fx : L2X X) := by
      show ((J (J.symm F') : conjRows X) : L2X X) = _
      rw [LinearEquiv.apply_symm_apply]
    have hRg : G.Rg (star (Fx : L2X X)) = star (Fx : L2X X) := by
      have := LinearMap.mem_ker.1 (Submodule.mem_inf.1 Fx.2).2
      exact sub_eq_zero.1 this
    have k1 := key S
    rw [hJS, hRg, star_star, ← hJS] at k1
    have hfix : postOn (MP R) R.e0 S = S := congrArg Subtype.val (J.injective (Subtype.ext k1))
    refine ⟨⟨(S : MMap (MP R)), (hEPS S).2 hfix⟩, Subtype.ext ?_⟩
    rw [hLv]
    exact hJS
  let j : EP R F ≃ₗ[ℂ] EEC X G := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have hj : ∀ S : EP R F, ((j S : EEC X G) : L2X X) = ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) :=
    fun S => rfl
  refine ⟨⟨j, fun S => ?_⟩, ⟨v₀, hv, j, fun S => ?_⟩⟩
  · rw [hj]
    exact hJ _
  · rw [hj]
    exact hJ _

end GlobalTheory.Mem.SRe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField

namespace GlobalTheory.Mem.R3.LedRec

set_option maxHeartbeats 1000000 in

theorem ev_exists_sizeData : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) →
    (∀ w j, X.toD7.what₂.Aj j w = 0) →
    ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ SizesAt L ∧ Nonempty (ParameterChoice' X.toD7 L) ∧
      8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max x0 x1, ?_⟩
  rintro K rfl rfl rfl hs hx X hO heta hA
  have hP := K.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx) hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) (fun w _ j _ _ => hA w j)
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  exact ⟨L, e1, M.sizes, ⟨M.params⟩, M.parT.nV_ge⟩

def bare {B : Base} {C : Cols B} (W : RowsRest B C) : RowsRest B C :=
  { GaloisStage.adapt W with Ij := fun _ _ _ => 0, jw := fun _ _ _ => 0 }

theorem exists_bare (hG : GlobalTheory.Published.GreenCuspidal) {B : Base} {C : Cols B} (a : Late B C) (f : Fr B.toPre) (η : ℝ) :
    ∃ b : Late B C, GrpTrue b.N f ∧ b.V.div.etaF = η ∧ ∀ w j, b.D.what₂.Aj j w = 0 := by
  obtain ⟨N, -, -, hN, -⟩ := exists_nStage_grpTrue hG B C (bare a.W) (GlobalTheory.MemN.shaOK_shaTrue B.toPre) (fun _ _ _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) f
  exact ⟨⟨bare a.W, { a.V with div := { a.V.div with etaF := η } }, { a.S with }, N, a.G⟩, hN, rfl, fun _ _ => rfl⟩

def sameGrp {B : Base} {C : Cols B} {a b : Late B C} {f : Fr B.toPre} (h : GrpTrue a.N f) (h' : GrpTrue b.N f) : SameGrp a b where
  e := plEquiv a.N.naut b.N.naut
  pl := TypesTrue.plGw_plEquiv h h'
  e0 := h.typeIdempotent_coeff_across_layers h'

end GlobalTheory.Mem.R3.LedRec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientFieldFormOfPolynomialModelValueStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientField_form_of_polynomialModel_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls (i + 1) → ((I.rec7 l Z).chTw u μ).Y (i + 1) → ℂ, φ ∈ ((I.tw l l0 Z).fm u μ).Fi (i + 1) → (∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c') → ∃ x, ((I.tw l l0 Z).fm u μ).emb (i + 1) x = φ := by
  first | exact @GlobalTheory.Mem.Col2.TC.form_of_rat_values | exact GlobalTheory.Mem.Col2.TC.form_of_rat_values | (intros; apply GlobalTheory.Mem.Col2.TC.form_of_rat_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionalFrameMinorPolynomialsEqMinorProdStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functional_frameMinorPolynomials_eq_minorProduct : ∀ (D : D7) (k : Type) [Field k] [CharZero k] (N : ℕ) (nu : Bool × Formalism.MainNotions.G.HH D → YoungDiagram)
    (J : KM.ColChoice N nu), ∃ ph : Module.Dual k (MvPolynomial ((Bool × Formalism.MainNotions.G.HH D) × ℕ × Fin N) k),
      ∀ y : Bool × Formalism.MainNotions.G.HH D → Fin N → ℕ → k, ph (GL3Columns.DeX N nu y) = GL3Columns.minY N nu J y := by
  first | exact @GlobalTheory.Mem.RangeMinors.exists_dual_DeX_eq_minY | exact GlobalTheory.Mem.RangeMinors.exists_dual_DeX_eq_minY | (intros; apply GlobalTheory.Mem.RangeMinors.exists_dual_DeX_eq_minY <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerLiftModNatIntegralAdeleTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftModG

theorem exists_lift_mod_g : ∀ (D : D7) (X : HidaSetting D) (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F), s ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E → ∃ α : 𝓞 D.host.E, ZMod' X.B.I X.B.g (s - Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))) := by
  intro D X s hs
  have hg : X.B.g ≠ 0 := by
    rw [X.g_eq]; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  set I : Ideal (𝓞 X.B.I.E) := Ideal.span {((X.B.g : ℕ) : 𝓞 X.B.I.E)} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg
  obtain ⟨q, hq⟩ := cmpS_surj (F := X.B.I.F) I hI0 (Ideal.Quotient.mk _ ⟨s, hs⟩)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have h1 : Ideal.Quotient.mk (idS X.B.I.F I) (oToS X.B.I.F X.B.I.E a) = Ideal.Quotient.mk _ ⟨s, hs⟩ := hq
  rw [Ideal.Quotient.eq] at h1
  have h2 : (⟨s, hs⟩ - oToS X.B.I.F X.B.I.E a) ∈ Ideal.span {oToS X.B.I.F X.B.I.E ((X.B.g : ℕ) : 𝓞 X.B.I.E)} := by
    have := (Ideal.neg_mem_iff _).2 h1
    rw [neg_sub] at this
    simpa [idS, hI, Ideal.map_span] using this
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h2
  refine ⟨RingOfIntegers.mapRingEquiv X.ιE a, t, t.2, ?_⟩
  have e1 : X.ιE.symm ((RingOfIntegers.mapRingEquiv X.ιE a : 𝓞 D.host.E) : D.host.E) = (a : X.B.I.E) := by
    rw [RingOfIntegers.mapRingEquiv_apply]; exact X.ιE.symm_apply_apply _
  rw [e1]
  have := congrArg (fun y : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E => (y : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ht
  simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, map_natCast, Subring.coe_natCast] at this
  rw [mul_comm] at this
  exact this.symm

end GlobalTheory.Mem.LiftModG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsK1PointCongruentStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_K1_point_congruent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → ∀ c : ℕ, ∃ z ∈ K1 hc n ST SG, (∀ P : Q, Sm Valued.v (dep P.1 c) (locM P.1 z - 1)) ∧ ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * z) p := by
  first | exact @GlobalTheory.Mem.ColAd.exists_K1_isPtOf | exact GlobalTheory.Mem.ColAd.exists_K1_isPtOf | (intros; apply GlobalTheory.Mem.ColAd.exists_K1_isPtOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayeredDataOfGoodScaleContexts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem recExP_of_recAtG : StandardLattice.SiegelMassRatioCM → ∀ (Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop), RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) → (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) → RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) := by
  intro hconds Q' QO h hq
  obtain ⟨ε0, hε0, h⟩ := h
  obtain ⟨ε1, hε1, hq⟩ := hq
  refine ⟨min ε0 ε1, lt_min hε0 hε1, fun eps C8 C5 c6 Cb he he0 he52 hC8 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb he (he0.trans (min_le_left _ _)) he52 hC8
  obtain ⟨K1, hq⟩ := hq eps C8 C5 c6 Cb he (he0.trans (min_le_right _ _)) he52 hC8
  refine ⟨K0.sup K1, fun C hstd hC hL => ?_⟩
  obtain ⟨c1, h⟩ := h C hstd hC (large_of_sup hL).1
  obtain ⟨c1', hq⟩ := hq C hstd hC (large_of_sup hL).2
  refine ⟨max (max c1 c1') 0, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hcD)
  obtain ⟨c2q, hq⟩ := hq cD (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hcD)
  obtain ⟨c2', hlow⟩ := GlobalTheory.EX.WinLow.window_lower hconds eps C he he52 hstd cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max (max c2 c2q) c2', fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hch)
  have hq := hq ch (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hch)
  obtain ⟨x1, hlow⟩ := hlow ch (le_trans (le_max_right _ _) hch)
  obtain ⟨x2, hint⟩ := exists_du_nat eps he he52
  have hq' : ∃ x3 : ℝ, Par.Pos ⟨eps, C, cD, ch, C5, c6, Cb⟩ → ∀ K : Ctx, Par.Of ⟨eps, C, cD, ch, C5, c6, Cb⟩ K → x3 ≤ K.s.x →
      ∀ β : BPt K, β.Is Q' → QO ⟨eps, C, cD, ch, C5, c6, Cb⟩ β.D β.O := by
    by_cases hp : Par.Pos ⟨eps, C, cD, ch, C5, c6, Cb⟩
    · obtain ⟨x3, h3⟩ := hq hp
      exact ⟨x3, fun _ => h3⟩
    · exact ⟨0, fun hp' => absurd hp' hp⟩
  obtain ⟨x3, hq'⟩ := hq'
  refine ⟨1, max (max x0 x3) (max x1 x2), one_pos, fun s P a b c hs hx d3 => ?_⟩
  have hok := d3.ok
  have hx0 : x0 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : x3 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : x1 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨du, hpos, hdu⟩ := hint s C cD ch P _ a b c hs hx2 hok
  obtain ⟨hD, hDle⟩ := GlobalTheory.Mem.Top.DsLow.DsP_pos_and_lower P
  refine ⟨du, DsP P, hpos, hD, fun u => ?_, fun Lv h1 h2 h3 => ?_⟩
  · rw [one_mul]
    exact hlow s P _ a b c du (DsP P) hs hx1 hok hdu hDle u
  · let K : Ctx := ⟨s, C, cD, ch, P, _, a, b, c, hstd, hok, Lv, fun u => by rw [h1]; exact hdu u, h2, h3⟩
    obtain ⟨D, Y, g1, g2, g3, g4, ⟨X, f, T, co, hQ, he⟩, u1, u2, u3⟩ := h K rfl rfl rfl hs hx0 d3
    refine ⟨D, Y, g1, g2, g3, g4, fun p p1 p2 p3 p4 => ⟨fun hp => ?_, ?_⟩⟩
    · obtain ⟨rfl, he⟩ := Sigma.mk.inj he
      exact hq' hp K ⟨rfl, rfl, rfl, hs, d3⟩ hx3
        ⟨X, f, T, co, Y, eq_of_heq he, p, p1, p2, p3, p4, ⟨C5, c6, Cb, d3⟩, g2, g3, u1, u2⟩ hQ
    · exact DQ.qd_setDiv D (Y.obj p) (nPrime p.L) p.ht ⟨u1, u2, u3⟩

end GlobalTheory.Fc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFamilyCharacterExponentStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelFamily_character_exponent : ∀ {X : Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG), ∃ m : ℕ, 0 < m ∧ ∀ h, Λ.chr h ^ m = 1 := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.levFam_chr_exp | exact GlobalTheory.Mem.Col2.TopCh.levFam_chr_exp | (intros; apply GlobalTheory.Mem.Col2.TopCh.levFam_chr_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStepStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplicityLift_lastChainStep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.chain_ωX → R.chain_vX → R.chain_ptX → R.chain_ItX → ∃ io, ({ R with ioX := io } : RealDat D A Ks).chain_ioX := by
  first | exact @GlobalTheory.DefLift.exists_lift_last | exact GlobalTheory.DefLift.exists_lift_last | (intros; apply GlobalTheory.DefLift.exists_lift_last <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfMulK1Standard
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh.KStd

theorem K1_le_J0_empty {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) :
    K1 B.sp.cm n ST SG ≤ J0 B.sp.cm n ∅ := by
  intro t ht
  have h1 := principal_le_congruence_subgroup B.sp.cm n ST SG ht
  unfold J0 at h1 ⊢
  simp only [Subgroup.mem_inf] at h1 ⊢
  refine ⟨h1.1, ?_⟩
  simp

theorem exists_ptOf_mul_K1 : ∀ {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) (k t : GA B n), t ∈ K1 B.sp.cm n ST SG → (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) → ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (k * t) p ∧ p.deco.1.N = stdLat B.fields.E n := by
  intro B n _ ST SG k t ht ⟨p, hp, hN⟩
  have hz : t ∈ J0 B.sp.cm n ∅ := K1_le_J0_empty n ST SG ht
  have h2 := (isPtOf_mul_J0 B.host.F B.host.E B.sp.cm n ∅ ∅ ∅ k t p p
    (redG B.sp.cm n ∅ ∅ ⟨t, hz⟩)⁻¹).2.1 rfl hp hz (by rw [inv_inv])
  have e : (((1, (redG B.sp.cm n ∅ ∅ ⟨t, hz⟩)⁻¹, 1) : UF B.fields.E n × GLG B.fields.E n ∅ × GLQ B.fields.E n ∅) • p) = p := by
    have : (redG B.sp.cm n ∅ ∅ ⟨t, hz⟩)⁻¹ = 1 := Subsingleton.elim _ _
    rw [this]
    exact one_smul _ p
  rw [e] at h2
  exact ⟨p, h2, hN⟩

end GlobalTheory.Mem.Col2.TopCh.KStd

end
end

