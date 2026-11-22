import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceFockDsUniqueness
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0059
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0060
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0112
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0101

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerZeroUpperBlockIndicatorSqSumEqCard
section
open Classical

namespace GlobalTheory.LevelVecNorm

theorem finsum_indicator_one_eq_ncard' {α : Type} (s : Set α) :
    (∑ᶠ x, s.indicator (fun _ => (1:ℝ)) x) = (s.ncard : ℝ) := by
  by_cases hs : s.Finite
  · rw [← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]
    simp
  · have hsupp : Function.support (s.indicator (fun _ => (1:ℝ))) = s := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [finsum_of_infinite_support (by rw [hsupp]; exact hs), Set.Infinite.ncard hs]
    simp

theorem suppInd_sq_sum_eq_card : ∀ {k : Type} [CommRing k] {b a : ℕ} (r t : ℕ), b = r + t → a = r → ∀ H : Subgroup (GL (Fin r) k),
    ∑ᶠ z : Matrix (Fin b) (Fin a) k, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = (Nat.card H : ℝ) := by
  intro k _ b a r t hb ha H
  subst hb; subst a
  let f : GL (Fin r) k → Matrix (Fin (r + t)) (Fin r) k := fun g i j =>
    if h : i.val < r then (g : Matrix (Fin r) (Fin r) k) ⟨i.val, h⟩ j else 0
  have htop : ∀ g, Formalism.IndefR.Datum.topL r (f g) = (g : Matrix (Fin r) (Fin r) k) := by
    intro g; ext i j
    simp [Formalism.IndefR.Datum.topL, f, i.isLt, j.isLt, show i.val < r + t by omega]
  have hlow : ∀ g, Formalism.IndefR.Datum.LowZero r (f g) := by
    intro g i j hi _
    simp [f, show ¬ i.val < r by omega]
  have hinj : Function.Injective f := by
    intro g g' h
    apply Units.ext
    rw [← htop g, ← htop g', h]
  let S : Set (Matrix (Fin (r + t)) (Fin r) k) :=
    {z | Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z}
  have hS : S = f '' (H : Set (GL (Fin r) k)) := by
    ext z
    constructor
    · rintro ⟨hz, g, hg, hgz⟩
      refine ⟨g, hg, ?_⟩
      ext i j
      by_cases hi : i.val < r
      · have := congrFun (congrFun hgz ⟨i.val, hi⟩) j
        simp only [Formalism.IndefR.Datum.topL, j.isLt, show i.val < r + t by omega] at this
        simpa [f, hi] using this
      · simp [f, hi, hz i j (by omega) j.isLt]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hlow g, g, hg, (htop g).symm⟩
  have hfun : ∀ z, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = S.indicator (fun _ => (1:ℝ)) z := by
    intro z
    unfold GlobalTheory.LevelVecNorm.suppInd
    by_cases hz : z ∈ S
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_pos hz', Set.indicator_of_mem hz]; norm_num
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_neg hz', Set.indicator_of_notMem hz]; norm_num
  simp_rw [hfun]
  rw [finsum_indicator_one_eq_ncard', hS, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
  rfl

end GlobalTheory.LevelVecNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeriesStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_intertwiner_smaller_fock_to_discrete_series : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFifth X := by
  first | exact @GlobalTheory.SmallerSource.no_map_smaller_source | exact GlobalTheory.SmallerSource.no_map_smaller_source | (intros; apply GlobalTheory.SmallerSource.no_map_smaller_source <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevChiFlagLEqOne
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem norm_residueChar_eq_one {E : Type} [Field E] [NumberField E] (PP : Pl E) (f : (kP PP)ˣ →* ℂˣ) (x : (kP PP)ˣ) :
    ‖((f x : ℂˣ) : ℂ)‖ = 1 := by

  have hx : IsOfFinOrder x := isOfFinOrder_of_finite x
  have hpow : ((f x : ℂˣ) : ℂ) ^ orderOf x = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow hx.orderOf_pos.ne'

theorem norm_levChi_flagL_eq_one :
    ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank),
      ∀ κ ∈ levG V β (flagL L), ‖levChi V β (flagL L) κ‖ = 1 := by
  intro D V β L κ _

  have hP : ∀ x, ext1 (flagL L).P.H (flagL L).P.chi x = 1 := by
    intro x
    unfold ext1
    split_ifs
    · rfl
    · rfl

  rw [levChi, levFn, hP, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod,
    norm_prod, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_residueChar_eq_one PP _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_residueChar_eq_one PP _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceFockDsUniquenessStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_correspondence_fock_ds_uniqueness : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → admQ7 → admQ8 → ArchimedeanRallisFirst X → ArchimedeanRallisSecond X → ArchimedeanRallisUpDownLine X := by
  first | exact @GlobalTheory.ThetaUnique.theta_unique | exact GlobalTheory.ThetaUnique.theta_unique | (intros; apply GlobalTheory.ThetaUnique.theta_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaKO_continuous_and_rat_invariant : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → Continuous (fun p : GA D S × GA D T => thetaKO om p.1 p.2 f) ∧ ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h, thetaKO om (γ * g) (γ' * h) f = thetaKO om g h f := by
  intro D ψ S T χS χT om H f hf
  refine ⟨H.om_cont f hf 0, ?_⟩
  intro γ hγ γ' hγ' g h
  have h1 : om (γ * g, γ' * h) = om (γ, γ') * om (g, h) := by
    rw [← map_mul]; rfl
  unfold thetaKO
  rw [h1]
  exact H.om_aut γ hγ γ' hγ' _ (H.om_pres (g, h) f hf)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKORatLeftAndEigenRight
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaKO_rat_left_and_eigen_right : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h, thetaKO om (γ * g) (γ' * h) f = thetaKO om g h f) ∧ ∀ k k' (c : ℂ), om (k, k') f = c • f → ∀ g h, thetaKO om (g * k) (h * k') f = c * thetaKO om g h f := by
  intro D ψ S T χS χT om hω f hf
  refine ⟨fun γ hγ γ' hγ' g h => ?_, fun k k' c hc g h => ?_⟩
  ·

    have hprod : ((γ * g, γ' * h) : GA D S × GA D T) = (γ, γ') * (g, h) := rfl
    unfold thetaKO
    rw [hprod, map_mul, Module.End.mul_apply]
    exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres (g, h) f hf)
  ·
    have hprod : ((g * k, h * k') : GA D S × GA D T) = (g, h) * (k, k') := rfl
    unfold thetaKO
    rw [hprod, map_mul, Module.End.mul_apply, hc, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftTranslateOfKernelFixed
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open NumberField IsDedekindDomain MeasureTheory in
open scoped TensorProduct InnerProductSpace in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in

theorem _root_.GlobalTheory.thetaLift_translate_of_kernel_fixed : ∀ {G H S Sinf Ds Dt : Type} [Group G] [Group H]
    [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds]
    [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (pt : Sinf → S)
    (It : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (io : CCs →ₗ[ℂ] CCt),
    _root_.Formalism.IndefR.Lift.IsIo ν 𝓕 th pt It CCs CCt io →
    (∀ u : CCt, (∀ φ v, (u : Dt →ₗ[ℂ] (G → ℂ)) (It φ v) = 0) → u = 0) →
    ∀ (k : G) (k' : H) (a a' : ℂ), (∀ g h φ, a * th (g * k) (h * k') (pt φ) = a' * th g h (pt φ)) →
    (∀ (F : CCs) φ v g, ∫ h in 𝓕, th g (h * k') (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k') ∂ν =
      ∫ h in 𝓕, th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h ∂ν) →
    ∀ (F F' : CCs) (u : CCt), (∀ v h, (F' : Ds →ₗ[ℂ] (H → ℂ)) v h = a' * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k')) →
    (∀ v g, (u : Dt →ₗ[ℂ] (G → ℂ)) v g = a * ((io F : CCt) : Dt →ₗ[ℂ] (G → ℂ)) v (g * k)) →
    io F' = u := by
  intro G H S Sinf Ds Dt _ _ _ _ _ _ _ _ _ ν 𝓕 th pt It CCs CCt io hio hker k k' a a' hth hinv
    F F' u hF' hu
  refine sub_eq_zero.mp (hker (io F' - u) fun φ v => ?_)
  funext g
  simp only [Submodule.coe_sub, LinearMap.sub_apply, Pi.sub_apply, Pi.zero_apply]
  rw [sub_eq_zero, ← hio.eq F' φ v g, hu, ← hio.eq F φ v (g * k)]
  unfold _root_.Formalism.IndefR.Lift.liftInt
  rw [← hinv F φ v (g * k), ← integral_const_mul]
  congr 1
  funext h
  rw [hF', show a * (th (g * k) (h * k') (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k')) =
    (a * th (g * k) (h * k') (pt φ)) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k') from
    (_root_.mul_assoc _ _ _).symm, hth]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedPlaceDoubleCosetVolumeAndDisjoint
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainCells

theorem vol_dcell_and_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)]
    (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 →
  ∀ [MeasurableSpace (GL (Fin (l * t)) k)] [BorelSpace (GL (Fin (l * t)) k)] (μK : Measure (GL (Fin (l * t)) k))
    [μK.IsHaarMeasure], μK (KO k (Fin (l * t))) = 1 →
  (∀ e : Fin (l * t) → ℤ, m.real (dcell ϖ (e ∘ (blkEquiv l t).symm)) =
    (resCard k : ℝ) ^ ((r : ℤ) * sumAbs e) * μK.real (cell k (Fin (l * t)) ϖ e)) ∧
  Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
    (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  intro k _ _ _ _ ϖ hϖ r l t _ _ m _ hm _ _ μK _ hμK
  refine ⟨fun e => ?_, GlobalTheory.T.pairwise_disjoint_parahoricTorusDoubleCoset_antitone k ϖ hϖ r l t⟩
  obtain ⟨ho, hc⟩ := GlobalTheory.T.isOpen_isCompact_twoBlockParahoricSubgroup k (Fin r) (Blocks l t)
  have h1 := GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul m _ ho hc (mtor (A := Fin r) ϖ (e ∘ (blkEquiv l t).symm))
  have h2 := GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul μK (KO k (Fin (l * t))) SplitFlip.isOpen_KO SplitFlip.isCompact_KO (torusElt k _ ϖ e)
  have hs : sumAbs (e ∘ (blkEquiv l t).symm) = sumAbs e := by
    unfold sumAbs; exact Equiv.sum_comp (blkEquiv l t).symm (fun i => |e i|)
  have hm1 : m.real (parahoric k (Fin r) (Blocks l t) : Set _) = 1 := by simp [Measure.real, hm]
  have hK1 : μK.real (KO k (Fin (l * t)) : Set _) = 1 := by simp [Measure.real, hμK]
  rw [dcell, h1, cell, h2, hm1, hK1, GlobalTheory.T.relIndex_twoBlockParahoric_conj_torusDiagElement k ϖ hϖ, GlobalTheory.T.relIndex_conj_uniformizerPowerDiagonalGL_reindex k ϖ _ _ (blkEquiv l t), hs]
  simp

end GlobalTheory.ChainCells
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrrepCompConjIsoDual
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

open GlobalTheory.ValCmp

theorem sqAct_eq_rnd_invTranspose (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) (g : GL (Fin n) K) (f : MP K n) :
    sqAct K n lam g f = rnd K lam.detShift ((g : Matrix (Fin n) (Fin n) K)⁻¹).transpose f := by
  have hdet : IsUnit (g : Matrix (Fin n) (Fin n) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)
  have hinv : (((g : Matrix (Fin n) (Fin n) K)⁻¹).transpose)⁻¹ = (g : Matrix (Fin n) (Fin n) K).transpose := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hdet]
  have hpow : (((g : Matrix (Fin n) (Fin n) K)⁻¹).transpose).det ^ (-lam.detShift) =
      (g : Matrix (Fin n) (Fin n) K).det ^ lam.detShift := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_zpow', neg_neg]
  simp only [GlobalTheory.ValCmp.rnd, LinearMap.smul_apply, AlgHom.toLinearMap_apply, hinv, hpow, sqAct, detPow,
    Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

private lemma detShift_eq_w_last {m : ℕ} (lam : DomWeight (m + 1)) : lam.detShift = lam.w (Fin.last m) := by
  unfold DomWeight.detShift
  rw [dif_pos (Nat.succ_pos m)]
  rfl

private lemma natW_antitone_succ {m : ℕ} (lam : DomWeight (m + 1)) : Antitone lam.natW := by
  intro i j hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)

private lemma natW_last_eq_zero {m : ℕ} (lam : DomWeight (m + 1)) : lam.natW (Fin.last m) = 0 := by
  unfold DomWeight.natW
  rw [detShift_eq_w_last, sub_self, Int.toNat_zero]

private lemma dual_detShift_eq_neg_w_zero {m : ℕ} (lam : DomWeight (m + 1)) : lam.dual.detShift = -lam.w 0 := by
  rw [detShift_eq_w_last]
  show -lam.w (Fin.rev (Fin.last m)) = -lam.w 0
  rw [Fin.rev_last]

private lemma natW_dual_eq_nuDual {m : ℕ} (lam : DomWeight (m + 1)) :
    lam.dual.natW = GlobalTheory.ValCmp.nuDual lam.natW := by
  funext i
  have h0 : lam.w (Fin.rev i) ≤ lam.w 0 := lam.anti (Fin.zero_le _)
  have h1 : lam.w (Fin.last m) ≤ lam.w (Fin.rev i) := lam.anti (Fin.le_last _)
  have h2 : lam.dual.w i = -lam.w (Fin.rev i) := rfl
  show (lam.dual.w i - lam.dual.detShift).toNat =
    (lam.w 0 - lam.detShift).toNat - (lam.w (Fin.rev i) - lam.detShift).toNat
  rw [dual_detShift_eq_neg_w_zero, h2, detShift_eq_w_last]
  omega

private lemma neg_detShift_add_natW_zero_eq_dual_detShift {m : ℕ} (lam : DomWeight (m + 1)) :
    -(lam.detShift + ((lam.natW 0 : ℕ) : ℤ) + 0) = lam.dual.detShift := by
  have h0 : lam.w (Fin.last m) ≤ lam.w 0 := lam.anti (Fin.zero_le _)
  rw [dual_detShift_eq_neg_w_zero, detShift_eq_w_last]
  simp only [DomWeight.natW, detShift_eq_w_last]
  omega

theorem iso_irr_comp_conjU : ∀ (n : ℕ), 0 < n → ∀ lam : DomWeight n,
    Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam.dual) := by
  intro n hn lam
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨Ψ, hinj, hmap, hact, -, -⟩ := GlobalTheory.ValCmp.exists_posOk_dual ℂ ℂ m lam.natW
    (natW_antitone_succ lam) (natW_last_eq_zero lam) lam.detShift 0
  have hmem : ∀ f : nablaSq ℂ (m + 1) lam, Ψ f ∈ nablaSq ℂ (m + 1) lam.dual := by
    intro f
    change Ψ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ (m + 1) (m + 1) lam.dual.natW
    rw [natW_dual_eq_nuDual, ← hmap]
    exact Submodule.mem_map_of_mem f.2
  let L : nablaSq ℂ (m + 1) lam →ₗ[ℂ] nablaSq ℂ (m + 1) lam.dual :=
    (Ψ ∘ₗ (nablaSq ℂ (m + 1) lam).subtype).codRestrict _ hmem
  have hL : Function.Bijective L := by
    constructor
    · intro f f' h
      have h1 : Ψ ((f : MP ℂ (m + 1)) - f') = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val h
      exact Subtype.ext (sub_eq_zero.mp (hinj _ (Submodule.sub_mem _ f.2 f'.2) h1))
    · rintro ⟨y, hy⟩
      have hy' : y ∈ (Formalism.GradedWeylDivisibility.dualWeyl ℂ (m + 1) (m + 1) lam.natW).map Ψ := by
        rw [hmap, ← natW_dual_eq_nuDual]
        exact hy
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy'
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  refine ⟨LinearEquiv.ofBijective L hL, fun g x => Subtype.ext ?_⟩
  have hu : IsUnit (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det := by
    have hdet := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.mp g.2)
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact isUnit_iff_exists_inv.mpr ⟨_, hdet⟩
  have hg : ((((star (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).transpose)⁻¹).transpose) =
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
    exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff.mp g.2)
  change Ψ (sqAct ℂ (m + 1) lam (unitaryIncl (m + 1) (conjU (m + 1) g)) (x : MP ℂ (m + 1))) =
    sqAct ℂ (m + 1) lam.dual (unitaryIncl (m + 1) g) (Ψ x)
  rw [sqAct_eq_rnd_invTranspose, sqAct_eq_rnd_invTranspose]
  simp only [GlobalTheory.Branching.unitaryIncl_coe, conjU_coe]
  rw [hg, hact _ hu _ x.2, zpow_zero, one_smul, neg_detShift_add_natW_zero_eq_dual_detShift]

end GlobalTheory.OneFunctional
end

