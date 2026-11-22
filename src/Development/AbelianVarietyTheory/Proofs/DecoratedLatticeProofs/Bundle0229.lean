import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnn
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

variable {D : D7}

open Matrix

theorem Tm_row_sub (A : HSp D) (μ : D.host.E) (a : Fin A.rank) :
    (fun k => Tm A μ (finSumFinEquiv (Sum.inl a)) k - Tm A μ (finSumFinEquiv (Sum.inr a)) k) =
      Pi.single (finSumFinEquiv (Sum.inr a)) μ := by
  funext k
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  simp only [Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases s with j | j
  · simp only [Tm, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, GlobalTheory.Core.Rk.SWLaw.dblDec,
      GlobalTheory.Core.Rk.SWLaw.stackRows, fromRows_apply_inl, fromRows_apply_inr, sub_self, reduceCtorEq, if_false]
  · simp only [Tm, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, GlobalTheory.Core.Rk.SWLaw.dblDec,
      GlobalTheory.Core.Rk.SWLaw.stackRows, Matrix.smul_apply, fromRows_apply_inl, fromRows_apply_inr, Matrix.neg_apply,
      Matrix.one_apply, Sum.inr.injEq, smul_eq_mul]
    by_cases h : j = a
    · subst h
      simp only [if_true]
      have h2 : (2 : D.host.E) ≠ 0 := two_ne_zero
      field_simp
      ring
    · simp [h, Ne.symm h]

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

variable {D : D7}

open Matrix

theorem rat_Tm_mulVec_sub (A : HSp D) (μ : D.host.E) (w : Fin (A.rank + A.rank) → AE D) (a : Fin A.rank) :
    (rat (Tm A μ) *ᵥ w) (finSumFinEquiv (Sum.inl a)) - (rat (Tm A μ) *ᵥ w) (finSumFinEquiv (Sum.inr a)) =
      incA D μ * w (finSumFinEquiv (Sum.inr a)) := by
  have hrow := Tm_row_sub A μ a
  calc _ = ∑ k, incA D ((Pi.single (finSumFinEquiv (Sum.inr a)) μ : Fin (A.rank + A.rank) → D.host.E) k) * w k := by
        rw [mulVec, mulVec, dotProduct, dotProduct, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk : Tm A μ (finSumFinEquiv (Sum.inl a)) k - Tm A μ (finSumFinEquiv (Sum.inr a)) k =
            (Pi.single (finSumFinEquiv (Sum.inr a)) μ : Fin (A.rank + A.rank) → D.host.E) k := congrFun hrow k
        rw [← hk, map_sub, sub_mul]
        rfl
    _ = _ := by
        rw [Finset.sum_eq_single (finSumFinEquiv (Sum.inr a)) (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero, zero_mul])
          (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same]

theorem rat_Tm_mulVec_mem_diagSub_iff (A : HSp D) {μ : D.host.E} (hμ : IsSkew μ) (w : Fin (A.rank + A.rank) → AE D) :
    rat (Tm A μ) *ᵥ w ∈ diagSub (AE D) finSumFinEquiv ↔ w ∈ upperHalf D A.rank := by
  have hu : IsUnit (incA D μ) := (isUnit_iff_ne_zero.2 hμ.1).map _
  simp only [diagSub, upperHalf, LinearMap.mem_eqLocus, LinearMap.mem_ker, funext_iff, LinearMap.funLeft_apply,
    Function.comp_apply, Pi.zero_apply]
  exact forall_congr' fun a => by rw [← sub_eq_zero, rat_Tm_mulVec_sub, hu.mul_right_eq_zero]

theorem exists_rat_Tm_mulVec_eq (A : HSp D) {μ : D.host.E} (hμ : IsSkew μ) (v : Fin (A.rank + A.rank) → AE D)
    (hv : v ∈ diagSub (AE D) finSumFinEquiv) : ∃ w ∈ upperHalf D A.rank, rat (Tm A μ) *ᵥ w = v := by
  have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
  let x : Fin A.rank → AE D := fun a => v (finSumFinEquiv (Sum.inl a))
  let w : Fin (A.rank + A.rank) → AE D := fun k => Sum.elim (rat A.gram *ᵥ x) 0 (finSumFinEquiv.symm k)
  have hw : w ∈ upperHalf D A.rank := by
    simp only [upperHalf, LinearMap.mem_ker, funext_iff, LinearMap.funLeft_apply, Function.comp_apply,
      Pi.zero_apply, w, Equiv.symm_apply_apply, Sum.elim_inr, implies_true]
  have hv' : ∀ a, v (finSumFinEquiv (Sum.inl a)) = v (finSumFinEquiv (Sum.inr a)) := by
    simpa only [diagSub, LinearMap.mem_eqLocus, funext_iff, LinearMap.funLeft_apply, Function.comp_apply] using hv
  have hl : ∀ a, (rat (Tm A μ) *ᵥ w) (finSumFinEquiv (Sum.inl a)) = x a := fun a => by
    have h1 : rat (A.gram⁻¹) * rat A.gram = (1 : Mx D A.rank A.rank) := by
      rw [rat, rat, ← Matrix.map_mul, nonsing_inv_mul _ hG, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrFun (congrArg (· *ᵥ x) h1) a
    simp only [← mulVec_mulVec, one_mulVec] at h2
    rw [← h2, mulVec, dotProduct, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    simp only [w, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, mulVec, dotProduct, rat, map_apply, Tm, submatrix_apply, id,
      fromCols_apply_inl, GlobalTheory.Core.Rk.SWLaw.dblDec, GlobalTheory.Core.Rk.SWLaw.stackRows, fromRows_apply_inl]
  refine ⟨w, hw, funext fun k => ?_⟩
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  rcases s with a | a
  · exact hl a
  · have h3 := (rat_Tm_mulVec_mem_diagSub_iff A hμ w).2 hw
    simp only [diagSub, LinearMap.mem_eqLocus, funext_iff, LinearMap.funLeft_apply, Function.comp_apply] at h3
    rw [← h3 a, hl a, ← hv' a]

theorem mem_siegel_iff_chart_mem_P : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ →
    ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g, g ∈ siegel A ↔ κ g ∈ P D A.rank := by
  intro D A μ hμ κ hκ g
  have hT : ∀ w, rat (Tm A μ) *ᵥ (mat (κ g) *ᵥ w) = mt (dblSp A) g *ᵥ (rat (Tm A μ) *ᵥ w) := fun w => by
    rw [mulVec_mulVec, mulVec_mulVec, hκ g]
  have hP : κ g ∈ P D A.rank ↔ ∀ w, w ∈ upperHalf D A.rank ↔ mat (κ g) *ᵥ w ∈ upperHalf D A.rank := Iff.rfl
  have hS : g ∈ siegel A ↔ ∀ v, v ∈ diagSub (AE D) finSumFinEquiv ↔
      mt (dblSp A) g *ᵥ v ∈ diagSub (AE D) finSumFinEquiv := Iff.rfl
  rw [hP]
  constructor
  · intro h w
    rw [← rat_Tm_mulVec_mem_diagSub_iff A hμ, ← rat_Tm_mulVec_mem_diagSub_iff A hμ, hT]
    exact hS.1 h _
  · intro h
    refine Subgroup.mem_comap.2 (mem_stabGL_diagSub.2 (keepsDiag_of_mulVec fun v hv => ?_))
    obtain ⟨w, hw, rfl⟩ := exists_rat_Tm_mulVec_eq A hμ v hv
    change mt (dblSp A) g *ᵥ _ ∈ _
    rw [← hT, rat_Tm_mulVec_mem_diagSub_iff A hμ]
    exact (h w).1 hw

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalIffSecondModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.SBesFlagTie

open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

variable {D : D7}

theorem unip_joint {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂] (f : A →+* R₁) (g : A →+* R₂)
    (hinj : ∀ y, f y = 0 → g y = 0 → y = 0) (hsurj : ∀ a b, ∃ y, f y = a ∧ g y = b) {n ρ : ℕ}
    (E : Matrix (Fin n) (Fin ρ) A) (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A) :
    Unip E K M ↔ Unip (E.map f) (K.map f) (M.map f) ∧ Unip (E.map g) (K.map g) (M.map g) :=
  GlobalTheory.T.isFlagUnipotentMatrix_iff_jointlyBijective_pair f g hinj hsurj E K M

theorem unip_pi {ι S : Type} [Fintype ι] [DecidableEq ι] [CommRing S] {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) (ι → S))
    (K : Matrix (Fin ρ) (Fin n) (ι → S)) (M : Matrix (Fin n) (Fin n) (ι → S)) :
    Unip E K M ↔ ∀ i, Unip (E.map (Pi.evalRingHom (fun _ => S) i)) (K.map (Pi.evalRingHom (fun _ => S) i))
      (M.map (Pi.evalRingHom (fun _ => S) i)) :=
  GlobalTheory.T.isFlagUnipotentMatrix_pi_iff_forall_eval E K M

theorem unip_real (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)
    (z : Fin I.n → I.E) (hc : ∀ a, c a ≠ 0) (hz : ∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0)
    (N : Matrix (Fin I.n) (Fin I.n) ℂ) :
    Unip ((Matrix.of fun k a => c a * x a k).map (I.φ v))
      ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) N ↔
    InN (I.ε v) (fun a => rv I v (x a)) (rv I v z) ((I.P v)⁻¹ * N * I.P v) :=
  GlobalTheory.T.isFlagUnipotent_realPlace_iff_frame_unipotentRadical I v x c z hc hz N

theorem unip_fin (I : Formalism.MainNotions.S.AutInst) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)
    (z : Fin I.n → I.E) (hc : ∀ a, c a ≠ 0) (hz : ∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0)
    (N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    Unip ((Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)))
      ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) N ↔
    ((∀ a : Fin ρ, (N - 1) *ᵥ incl I (x a) ∈
        Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => incl I (x b)) '' {b | b.1 < a.1})) ∧
    (N - 1) *ᵥ incl I z ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => incl I (x b)) ∧
    ∀ y : VA I, (∀ a, hA I (incl I (x a)) y = 0) →
      (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => incl I (x b))) :=
  GlobalTheory.T.isFlagUnipotent_finiteAdeles_iff_frame_unipotentRadical I x c z hc hz N

theorem eM_linIndep (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E) (ht : t ≠ 0)
    (hl : lam ≠ 0) : LinearIndependent D.host.E (GlobalTheory.Core.SBesEx.eM X h t lam).transpose :=
  GlobalTheory.T.linearIndependent_scaledBasisColumnsMatrix_transpose X h t lam ht hl

theorem unip_congr {R : Type} [CommRing R] {n ρ : ℕ} {E E' : Matrix (Fin n) (Fin ρ) R}
    {K K' : Matrix (Fin ρ) (Fin n) R} {M M' : Matrix (Fin n) (Fin n) R} (hE : E = E') (hK : K = K') (hM : M = M') :
    Unip E K M ↔ Unip E' K' M' := by
  subst hE hK hM; rfl

theorem castGA_self {I : Formalism.MainNotions.S.AutInst} (e : I = I) (x : I.GA) : castGA e x = x := rfl

theorem thetaV_incA (v : InfinitePlace (Formalism.L2.SG.InstExistsPf.instOf D).F) (y : D.host.E) :
    thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v (incA D y) = (Formalism.L2.SG.InstExistsPf.instOf D).φ v y := by
  have := thetaV_tmul (Formalism.L2.SG.InstExistsPf.instOf D) v 1 y
  rw [map_one, one_mul] at this
  exact this

theorem tauF_incA (y : D.host.E) :
    tauF (Formalism.L2.SG.InstExistsPf.instOf D) (incA D y) = Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) y := by
  exact tauF_tmul (Formalism.L2.SG.InstExistsPf.instOf D) 1 y

theorem core (D : D7) {ρ : ℕ} (x : Fin ρ → Fin (D.sp.Y 0).rank → D.host.E) (c : Fin ρ → D.host.E)
    (z : Fin (D.sp.Y 0).rank → D.host.E) (hc : ∀ a, c a ≠ 0)
    (hz : ∀ a, Formalism.UG.hform (starRingEnd D.host.E) (Formalism.L2.SG.InstExistsPf.instOf D).J (x a) z = 0)
    (hLI : LinearIndependent D.host.E (Matrix.of fun k a => c a * x a k).transpose) (g : GA D (D.sp.Y 0)) :
    g ∈ NFlag (D.sp.Y 0) (Matrix.of fun k a => c a * x a k) ↔
      (Formalism.IndefR.RationalEmbedding.iota D g).1 ∈ Ninf (Formalism.L2.SG.InstExistsPf.instOf D) x z ∧
        (Formalism.IndefR.RationalEmbedding.iota D g).2 ∈ Nfin (Formalism.L2.SG.InstExistsPf.instOf D) x z := by
  have hb := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  have hb1 : ∀ v, uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) = ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) g v :=
    fun v => (hb.1 v).trans (congrArg (fun q => ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) q v) key)
  have hb2 : (Formalism.IndefR.RationalEmbedding.inst D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) g :=
    hb.2.trans (congrArg (fun q => ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) q) key)
  refine (GlobalTheory.BesselChar.mem_NFlag_iff _ _ hLI g).trans ?_
  refine (unip_joint (A := AF D.host.F ⊗[D.host.F] D.host.E) (Pi.ringHom fun v => thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v)
      (tauF (Formalism.L2.SG.InstExistsPf.instOf D))
      (fun y h1 h2 => Formalism.L2.SG.Pf.TT_ext _ y (fun v => congr_fun h1 v) h2)
      (fun a b => by
        obtain ⟨y, h1, h2⟩ := Formalism.L2.SG.Pf.TT_surj (Formalism.L2.SG.InstExistsPf.instOf D) a b
        exact ⟨y, funext h1, h2⟩) _ _ _).trans ?_
  refine (and_congr_left' (unip_pi _ _ _)).trans ?_
  refine and_congr (forall_congr' fun v => ?_) ?_
  · have hR := unip_real (Formalism.L2.SG.InstExistsPf.instOf D) v x c z hc hz
      ((hmat (Formalism.IndefR.RationalEmbedding.inst D) g).map (thetaV (Formalism.IndefR.RationalEmbedding.inst D) v))
    refine (unip_congr (Matrix.ext fun k a => thetaV_incA v _) (Matrix.ext fun k a => thetaV_incA v _)
      (Matrix.ext fun k a => rfl)).trans (hR.trans ?_)
    show _ ↔ InN _ _ _ (uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v))
    rw [hb1 v]
    rfl
  · have hF := unip_fin (Formalism.L2.SG.InstExistsPf.instOf D) x c z hc hz
      ((hmat (Formalism.IndefR.RationalEmbedding.inst D) g).map (tauF (Formalism.IndefR.RationalEmbedding.inst D)))
    refine (unip_congr (Matrix.ext fun k a => tauF_incA _) (Matrix.ext fun k a => tauF_incA _)
      (Matrix.ext fun k a => rfl)).trans (hF.trans ?_)
    show _ ↔ (_ ∧ _ ∧ _)
    rw [hb2]
    rfl

theorem transport (D : D7) (I : Formalism.MainNotions.S.AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n) {ρ : ℕ} (eR : Fin ρ → Fin I.n → I.E)
    (zR : Fin I.n → I.E) (s : (Formalism.L2.SG.InstExistsPf.instOf D).GA) :
    ((castGA hI.symm s).1 ∈ Ninf I eR zR ↔ s.1 ∈ Ninf (Formalism.L2.SG.InstExistsPf.instOf D)
      (fun a k => ιE (eR a (Fin.cast hr k))) (fun k => ιE (zR (Fin.cast hr k)))) ∧
    ((castGA hI.symm s).2 ∈ Nfin I eR zR ↔ s.2 ∈ Nfin (Formalism.L2.SG.InstExistsPf.instOf D)
      (fun a k => ιE (eR a (Fin.cast hr k))) (fun k => ιE (zR (Fin.cast hr k)))) ∧
    ∀ p q : Fin I.n → I.E, Formalism.UG.hform (starRingEnd D.host.E) (Formalism.L2.SG.InstExistsPf.instOf D).J
      (fun k => ιE (p (Fin.cast hr k))) (fun k => ιE (q (Fin.cast hr k))) =
        ιE (Formalism.UG.hform (starRingEnd I.E) I.J p q) := by
  generalize hI.symm = e
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hv : ∀ p : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E,
      (fun k => ιE (p (Fin.cast hr k))) = p := fun p => funext fun k => by rw [hid]; rfl
  have hx : (fun a k => ιE (eR a (Fin.cast hr k))) = eR := funext fun a => hv (eR a)
  refine ⟨?_, ?_, fun p q => ?_⟩
  · rw [castGA_self]
    exact Iff.of_eq (congrArg₂ (fun A B => s.1 ∈ Ninf (Formalism.L2.SG.InstExistsPf.instOf D) A B) hx.symm (hv zR).symm)
  · rw [castGA_self]
    exact Iff.of_eq (congrArg₂ (fun A B => s.2 ∈ Nfin (Formalism.L2.SG.InstExistsPf.instOf D) A B) hx.symm (hv zR).symm)
  · exact (congrArg₂ (fun A B => Formalism.UG.hform (starRingEnd D.host.E) (Formalism.L2.SG.InstExistsPf.instOf D).J A B)
      (hv p) (hv q)).trans (hid _).symm

theorem mem_flagN_iff : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → IdE X → ∀ (V₀ : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS), d.e = GlobalTheory.Core.SBesEx.eM X h t lam → ∀ n, n ∈ flagN d ↔ (iotaX X h n).1 ∈ X.NinfU u ∧ (iotaX X h n).2 ∈ X.NfinU u := by
  intro D X h u t lam ht hl hId V₀ d hd n
  have hLI := eM_linIndep X h t lam ht hl
  have hsc : ∀ a, GlobalTheory.Core.SBesEx.scl t lam a ≠ 0 := fun a => mul_ne_zero ht (pow_ne_zero _ hl)
  have horth : ∀ a, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR a) (X.zR u) = 0 := by
    intro a
    apply X.ιE.injective
    show X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd (X.eX a)) (X.crd (X.zu u))) = X.ιE 0
    rw [Formalism.L2.SG.PoincareInHH.Cut.hform_crd X, map_zero]
    exact (X.zu_orth u a).1
  have hT := transport D X.B.I X.ιE hId h (rank_eq X h) X.eR (X.zR u) (Formalism.IndefR.RationalEmbedding.iota D n)
  have hz : ∀ a, Formalism.UG.hform (starRingEnd D.host.E) (Formalism.L2.SG.InstExistsPf.instOf D).J
      (fun k => X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) (fun k => X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) = 0 :=
    fun a => by rw [hT.2.2, horth a, map_zero]
  have hcore := core D (fun a k => X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) (GlobalTheory.Core.SBesEx.scl t lam)
    (fun k => X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) hsc hz hLI n
  show n ∈ NFlag (D.sp.Y 0) d.e ↔ _
  rw [hd]
  exact hcore.trans (and_congr hT.1.symm hT.2.1.symm)

end GlobalTheory.Core.SBesFlagTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeStabilizerIffScaledFrameConj
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.StabFin

section General

variable {A R n : Type} [CommRing A] [CommRing R] [Algebra R A] [Fintype n] [DecidableEq n]

theorem mem_stab_conj {L S : Submodule R (n → A)} {b : GL n A} (h : ∀ y, y ∈ S ↔ b.1 *ᵥ y ∈ L) (x : GL n A) :
    x ∈ Formalism.UG.stabGL L ↔ b⁻¹ * x * b ∈ Formalism.UG.stabGL S := by
  have key : ∀ y, (b⁻¹ * x * b).1 *ᵥ y ∈ S ↔ x.1 *ᵥ (b.1 *ᵥ y) ∈ L := fun y => by
    rw [h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel, one_mul]
  constructor
  · intro hx y
    rw [key, h]
    exact hx _
  · intro hx y
    have h1 := hx ((b⁻¹).1 *ᵥ y)
    rw [key, h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
    exact h1

omit [CommRing R] [Algebra R A] in

theorem conj_eq_of_smul {m m' : GL n A} {w : A} (h : m.1 = w • m'.1) (z : GL n A) :
    m⁻¹ * z * m = m'⁻¹ * z * m' := by
  have hc : m * m'⁻¹ * z = z * (m * m'⁻¹) := by
    apply Units.ext
    have e : (m * m'⁻¹).1 = w • (1 : Matrix n n A) := by
      rw [Units.val_mul, h, Matrix.smul_mul, Units.mul_inv]
    rw [Units.val_mul _ z, Units.val_mul z, e, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  calc m⁻¹ * z * m = m⁻¹ * (z * (m * m'⁻¹)) * m' := by group
    _ = m⁻¹ * (m * m'⁻¹ * z) * m' := by rw [hc]
    _ = m'⁻¹ * z * m' := by group

end General

theorem mem_stab_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {m : GL (Fin N) (Fv F v ⊗[F] E)} (h : ∀ i j, m.1 i j ∈ intLoc F E v)
    (h' : ∀ i j, (m⁻¹).1 i j ∈ intLoc F E v) : m ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
  have key : ∀ (M : Matrix (Fin N) (Fin N) (Fv F v ⊗[F] E)), (∀ i j, M i j ∈ intLoc F E v) →
      ∀ y, y ∈ latLoc F (stdLattice E N) v → M *ᵥ y ∈ latLoc F (stdLattice E N) v := fun M hM y hy =>
    mem_latLoc_stdLattice.2 fun i => show ∑ j, M i j * y j ∈ _ from
      sum_mem fun j _ => mul_mem (hM i j) (mem_latLoc_stdLattice.1 hy j)
  intro y
  refine ⟨key _ h y, fun hy => ?_⟩
  have h1 := key _ h' _ hy
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1

theorem mem_stab_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)) (b M M' : GL (Fin N) (AF F ⊗[F] E)) (u : (AF F ⊗[F] E)ˣ), IsLatticeFrame Λ b → (∀ v i j, compFin F E v (M'.1 i j) ∈ intLoc F E v ∧ compFin F E v ((M'⁻¹).1 i j) ∈ intLoc F E v) → M.1 = (u : AF F ⊗[F] E) • M'.1 → ∀ (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (Fv F v ⊗[F] E)), x ∈ Formalism.UG.stabGL (latLoc F Λ v) ↔ (Formalism.UG.bc (compFin F E v) (b * M))⁻¹ * x * Formalism.UG.bc (compFin F E v) (b * M) ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
  intro F E _ _ _ _ _ N Λ b M M' u hb hM' hM v x
  have hs : Formalism.UG.bc (compFin F E v) M' ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
    refine mem_stab_std (fun i j => (hM' v i j).1) (fun i j => ?_)
    rw [← map_inv]
    exact (hM' v i j).2
  have he : (Formalism.UG.bc (compFin F E v) M).1 =
      compFin F E v (u : AF F ⊗[F] E) • (Formalism.UG.bc (compFin F E v) M').1 := by
    ext i j
    change compFin F E v (M.1 i j) = compFin F E v (u : AF F ⊗[F] E) * compFin F E v (M'.1 i j)
    rw [hM, ← map_mul]
    rfl
  rw [mem_stab_conj (S := latLoc F (stdLattice E N) v) (b := Formalism.UG.bc (compFin F E v) b)
    (fun y => mem_latLoc_stdLattice.trans (hb v y)) x, map_mul, mul_inv_rev]
  set β := Formalism.UG.bc (compFin F E v) b
  have e : (Formalism.UG.bc (compFin F E v) M)⁻¹ * β⁻¹ * x * (β * Formalism.UG.bc (compFin F E v) M) =
      (Formalism.UG.bc (compFin F E v) M)⁻¹ * (β⁻¹ * x * β) * Formalism.UG.bc (compFin F E v) M := by group
  rw [e, conj_eq_of_smul he, Subgroup.mul_mem_cancel_right _ hs, Subgroup.mul_mem_cancel_left _ (inv_mem hs)]

end GlobalTheory.StdUnn.StabFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpanFullSphericalHeckeEigenpartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpace_span_fullSphericalHecke_eigenparts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → LevFacts D → ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e} = ⊤ := by
  first | exact @GlobalTheory.OntoDecomp.multT_span_partFull | exact GlobalTheory.OntoDecomp.multT_span_partFull | (intros; apply GlobalTheory.OntoDecomp.multT_span_partFull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthDecSumLatticeSelfDualStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthDecSumLattice_selfDual : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (LW : Lat W) (LH : Lat H), IsSelfDualC W LW → IsSelfDualC H LH → IsSelfDualC B (sumLatO o LW LH) := by
  first | exact @GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO | exact GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO | (intros; apply GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChartIntegralGLEqLatticeStabilizerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_chart_integral_GL_eq_lattice_stabilizer : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _ := by
  first | exact @GlobalTheory.ChartStab.chart_stab | exact GlobalTheory.ChartStab.chart_stab | (intros; apply GlobalTheory.ChartStab.chart_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiQEqZeroOfNotMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

def suppQ {D : D7} (v : FinPl D) {a b : ℕ} (r : ℕ) : Set (Matrix (Fin b) (Fin a) (Fv D.host.F v)) :=
  {x | IsUnit (topL r x).det ∧ Valued.v (topL r x).det = 1 ∧ (∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F) ∧
      ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1}

theorem phiQ_eq_zero_of_not_mem {D : D7} (v : FinPl D) {a b : ℕ} (r : ℕ) (mu : (Fv D.host.F v)ˣ →* ℂˣ)
    (x : Matrix (Fin b) (Fin a) (Fv D.host.F v)) (hx : x ∉ suppQ v r) : phiQ v r mu x = 0 := by
  unfold phiQ
  rw [dif_neg]
  exact hx

end GlobalTheory.NrmVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PushforwardHaarRealPointsTimesLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_haar_realPoints_times_level : ∀ D : D7, LevFacts D → ForStage D fun c _ s => MeasurableSet (intOff c s) ∧ MeasurableSet {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ∧ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ⊆ intOff c s ∧ (∀ g : GA D s.V, Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L → ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} s.ν ∧ ∫ g in {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}, F g ∂s.ν = ∫ b, f b ∂mR := by
  first | exact @GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real | exact GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real | (intros; apply GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealFormsRangeMultiplicityOfScalarHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

namespace GlobalTheory.ChainTw

theorem rangeX_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RangeX R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG t
  have hm := hG.core.models
  exact GlobalTheory.DefiniteMult.range_top R hm.inf hm.cX hm.prX hm.HX t

end GlobalTheory.ChainTw
end

