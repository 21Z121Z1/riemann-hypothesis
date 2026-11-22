import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0588
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0587
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateTwistMultiplicationIntertwines
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineEvalRingHomFrobeniusTaylor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0591
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleAtGoodPointsOfCoefRingTakenAtLive
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem GlobalTheory.AdmissibleCore.main : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (X : KillingConditions.HubData D), GlobalTheory.CoefDuty.TakenAll D → GlobalTheory.PtCore.ResAbsIrr D → GlobalTheory.PtCore.PtFam D X.r X.ρ → ∀ i : D.nd.Loc, ∀ π ∈ D.nd.Zgood i, LargeLevelLemmas.adm51 (D := D) i (X.r i) (X.ρ i) π := by
  intro hC D X hT hA hX i π hπ
  intro hZ
  obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (X.r i π) (X.ρ i π) (D.nd.chi i) e := ⟨e, fun g u => he g u⟩
  have hHG : IsHeckeGalois D.nd i π (X.r i π) := hX.good i π
  have hpt : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D i π (X.ρ i π) := ⟨hX.cont i π, X.r i π, hHG, e, fun g u => he g u⟩
  have hirr := hA i π hπ (X.ρ i π) hpt
  have hLive : GlobalTheory.CoefDuty.Live D.nd i := ⟨π, hZ, X.r i π, X.ρ i π, hHG, hdec, hirr⟩
  obtain ⟨r₀, ρ₀, hg₀, hw₀⟩ := hT i hLive
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hg₀ hw₀ (X.r i) (X.ρ i) (hX.good i) π hZ hdec
  exact ⟨S, hS⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BernsteinZelevinskyDerivativeHarishChandraProducStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bernsteinZelevinskyDerivative_harishChandraProduct : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (L : List (Pc g)) (n i : ℕ), degL L = n → i ≤ n → (∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) → wh ψ (der ψ i (hcL L n)) = (((Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i)).card : ℂ) ∧ wh ψ (hcL L n) = 1 := by
  first | exact @GlobalTheory.GLq.Leibniz.main | exact GlobalTheory.GLq.Leibniz.main | (intros; apply GlobalTheory.GLq.Leibniz.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosingAtRecord
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.Closing

theorem closing_at_record : ∀ D : D7, DualJumpL D.loc ∧ PotDRL D.loc ∧ PcrisTensorL D.loc ∧
    PairedCharacterCondition.tieBr (D := D) ∧ InertEq D := by
  intro D
  have hT : ∀ (l : ℕ) [Fact (Nat.Prime l)], Nonempty (LocTied l (D.loc l) (D.locA l)) :=
    fun l _ => ⟨D.locT l⟩
  refine ⟨GlobalTheory.DualJump.dualJumpL D.loc D.locA hT, GlobalTheory.Pass.potDRL_of_tied D.loc D.locA hT,
    GlobalTheory.PcrisTwist.pcrisTensorL_of_tied D.loc D.locA hT, ?_, GlobalTheory.BridgeInertia.inertEq D⟩
  intro i w hw
  exact GlobalTheory.bridge_degW D.nbr i w hw

end GlobalTheory.Closing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryBcrisOfDualExponentialZeroStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_bcris_of_dualExponential_zero : ∀ (D : Formalism.BasicNotions.D7), adm2 D → ArchimedeanSignatureMatching D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (z : GQ l → ℚ_[l]), ExpStar D.loc (Gj K s) e z 0 → ∃ x : (D.loc l).R.B, ∀ σ ∈ Gj K s, algebraMap ℚ_[l] (D.loc l).R.B (z σ) = (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) • (D.loc l).actQ σ x - x := by
  first | exact @GlobalTheory.KerExpCrys.cob_cris_of_expStar_zero | exact GlobalTheory.KerExpCrys.cob_cris_of_expStar_zero | (intros; apply GlobalTheory.KerExpCrys.cob_cris_of_expStar_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColumnWhittakerTransformKeepsLaterLaw
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

noncomputable section

namespace GlobalTheory.CuspGeneric

section Mat

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_blk_apply {r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) (i l : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) x i l =
      if h : (i : ℕ) < r ∧ r ≤ (l : ℕ) ∧ (l : ℕ) ≤ m then x ⟨(i, l), h⟩ else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, l), h⟩]
    · simp
    · rintro ⟨⟨i', l'⟩, h'⟩ _ hne
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact hne rfl
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    rw [← e1, ← e2]
    exact t.2

theorem posM_mul_posM_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ] {p : ι → Fin a × Fin a}
    {q : κ → Fin a × Fin a} (h : ∀ s t, (p s).2 ≠ (q t).1) (x : ι → R) (y : κ → R) :
    posM p x * posM q y = 0 := by
  simp only [posM, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  exact Matrix.single_mul_single_of_ne _ _ _ _ (h _ _) _

theorem blk_mul_support {j k : ℕ} (x : UnipotentBlockColumnIndex a j j → R) (y : UnipotentBlockColumnIndex a k k → R) (i l : Fin a)
    (h : (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
      posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) i l ≠ 0) :
    (i : ℕ) < j ∧ (l : ℕ) = k ∧ j < k := by
  rw [Matrix.mul_apply] at h
  obtain ⟨n, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  simp only [posM_blk_apply] at hn
  split_ifs at hn with h1 h2
  all_goals first
    | (refine ⟨?_, ?_, ?_⟩ <;> omega)
    | simp at hn

theorem posM_blk_of_support {r m : ℕ} (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ i l, M i l ≠ 0 → (i : ℕ) < r ∧ r ≤ (l : ℕ) ∧ (l : ℕ) ≤ m) :
    posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) (fun t => M t.1.1 t.1.2) = M := by
  ext i l
  rw [posM_blk_apply]
  split_ifs with h
  · rfl
  · by_contra h'
    exact h (hM i l fun e => h' e.symm)

theorem blkU_mul_blkU {j k : ℕ} (hjk : j < k) (x : UnipotentBlockColumnIndex a j j → R) (y : UnipotentBlockColumnIndex a k k → R) :
    (blkU x : GL (Fin a) R) * blkU y =
      blkU (fun t : UnipotentBlockColumnIndex a k k => y t + (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
        posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2) * blkU x := by
  have key : ∀ X Y Y' : Matrix (Fin a) (Fin a) R, Y' = Y + X * Y → Y' * X = 0 →
      (1 + X) * (1 + Y) = (1 + Y') * (1 + X) := by
    intro X Y Y' h1 h2
    have e : (1 + Y') * (1 + X) = 1 + X + Y' + Y' * X := by noncomm_ring
    rw [e, h2, h1]
    noncomm_ring
  apply Units.ext
  refine key _ _ _ ?_ ?_
  · change posM _ (y + fun t : UnipotentBlockColumnIndex a k k => _) = _
    rw [posM_add, posM_blk_of_support]
    intro i l hne
    obtain ⟨h1, h2, h3⟩ := blk_mul_support x y i l hne
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · refine posM_mul_posM_eq_zero (fun s t e => ?_) _ _
    have h1 := s.2.2.1
    have h2 := t.2.1
    have h3 := congrArg Fin.val e
    omega

end Mat

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem dot_eLast_shift {j k : ℕ} (hjk : j < k) (x : UnipotentBlockColumnIndex a j j → Ad E) (y : UnipotentBlockColumnIndex a k k → Ad E) :
    dot (eLast a k) (fun t : UnipotentBlockColumnIndex a k k => y t + (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
        posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2) = dot (eLast a k) y := by
  have h0 : ∀ t : UnipotentBlockColumnIndex a k k, algebraMap E (Ad E) (eLast a k t) *
      (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
        posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2 = 0 := by
    intro t
    unfold eLast
    split_ifs with h
    · have hz : (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
          posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2 = 0 := by
        by_contra hne
        have := (blk_mul_support x y _ _ hne).1
        omega
      rw [hz, mul_zero]
    · simp
  simp only [dot, mul_add, Finset.sum_add_distrib, h0, Finset.sum_const_zero, add_zero]

theorem colT_law_of_good (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (m : ℕ)
    (f : GA E a → ℂ) (hf : Good ψ (m + 1) f) (k : ℕ) (hk : m + 1 < k) (y : UnipotentBlockColumnIndex a k k → Ad E)
    (g : GA E a) : colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a k) y) * colT ψ (m + 1) f g := by
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  have e1 : f (blkU x * (blkU y * g)) = ψ (dot (eLast a k) y) * f (blkU x * g) := by
    rw [← mul_assoc, blkU_mul_blkU hk x y, mul_assoc, hf.law k hk, dot_eLast_shift hk x y]
  rw [e1]
  ring

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.JSW.WhitCont

open GroundTheory.Automorphic.FourierWhittaker

theorem continuous_whit : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → Continuous (GlobalTheory.JSW.whit F) := by
  intro E _ _ a F hF ⟨C, hC⟩
  set μ := (vecMeasure E (Pos a)).restrict (vecDomain E (Pos a)) with hμ
  haveI : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hψ : Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)
  have hj : Continuous fun p : GA E a × (Pos a → Ad E) =>
      F (uGL p.2 * p.1) * (GroundTheory.Global.adelicChar E (-supSum 0 p.2) : ℂ) :=
    (hF.comp ((continuous_uGL.comp continuous_snd).mul continuous_fst)).mul (hψ.comp continuous_snd)
  have e : GlobalTheory.JSW.whit F = fun g => ∫ X, F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂μ := rfl
  rw [e]
  refine continuous_of_dominated (bound := fun _ => C) (fun g => ?_) (fun g => ?_) (integrable_const C) ?_
  · have h1 : Continuous fun X : Pos a → Ad E => (g, X) := continuous_const.prodMk continuous_id
    exact (hj.comp h1).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun X => ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
    exact hC _
  · refine Filter.Eventually.of_forall fun X => ?_
    exact (hF.comp (continuous_const.mul continuous_id)).mul continuous_const

end GlobalTheory.JSW.WhitCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordEPowBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_E_pow_basis_alt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (ε δ : OCb l), IsEps ε → δ ^ l = ε → ∀ j : ι, ∃ c : ι → OA l O, inclL t ϖ D.toPhiMod c = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) ∧ ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η)) • R.jB (fun i => toB l O (c i)) = TWincl (toB l O) T (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H • z) := by
  first | exact @GlobalTheory.BKGal.HatVal.coord_E_pow_basis | exact GlobalTheory.BKGal.HatVal.coord_E_pow_basis | (intros; apply GlobalTheory.BKGal.HatVal.coord_E_pow_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodModuleIsClosedLAdic
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem norm_toDisc_natPow_mul_le {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (n : ℕ)
    (w : A) : ‖toDisc l u ρ ((l : A) ^ n * w)‖ ≤ ((l : ℝ)⁻¹) ^ n := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hm : algebraMap A (PreDisc l u ρ) ((l : A) ^ n * u ^ 0) * IsLocalization.Away.invSelf (l : A) ^ 0 ∈
      ball l u ρ (((l : ℝ)⁻¹) ^ n) :=
    Submodule.subset_span ⟨n, 0, 0, by rw [pow_zero, pow_zero, mul_one, ← mul_pow, inv_mul_cancel₀ hl0.ne', one_pow], rfl⟩
  have e : algebraMap A (PreDisc l u ρ) ((l : A) ^ n * w) =
      w • (algebraMap A (PreDisc l u ρ) ((l : A) ^ n * u ^ 0) * IsLocalization.Away.invSelf (l : A) ^ 0) := by
    rw [Algebra.smul_def, pow_zero, pow_zero, mul_one, mul_one, ← map_mul, mul_comm]
  show ‖ofPre l u ρ (algebraMap A _ _)‖ ≤ _
  rw [norm_ofPre, e]
  exact gauge_le l u ρ (by positivity) (Submodule.smul_mem _ w hm)

theorem BK.ρ₀_mem_Ioo_zero_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  refine ⟨NNReal.rpow_pos (by exact_mod_cast hl.out.pos), ?_⟩
  apply NNReal.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hl.out.one_lt
  · have : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
    rw [neg_lt_zero]; positivity

theorem seed_module_lAdic_closed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y : ℕ → Fin d → Ainf l, (∀ n, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) z := by
  intro l _ K bk τ hτ d ρ hρ s y hy _hcau z hz
  beta_reduce at hy ⊢
  obtain ⟨hρ0, hρ1⟩ := bk.ρ₀_mem_Ioo_zero_one
  have hX : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  set j₀ : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev hX with hj₀
  have hj₀d : IsDiscMap bk.ev j₀ := isDiscMap_map bk.ev hX
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨cD, hc_to, hc_mul, hc_norm, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j₀ hj₀d
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (2 * s.N * d)
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hr

  set V : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀) := s.W'.det • adjugate s.W with hV
  have hVW : V * s.W = bk.iA (τ ^ (2 * s.N * d)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have hd : s.W.det * s.W'.det = bk.iA (τ ^ (2 * s.N * d)) := by
      rw [← det_mul, s.W_mul, det_smul, det_one, mul_one, Fintype.card_fin, map_pow]
      ring
    rw [hV, smul_mul, adjugate_mul, smul_smul, mul_comm, hd]

  let Φ : bk.DA bk.ρ₀ → bk.DS bk.ρ₀ := fun w => ∑ i ∈ f.support, toDisc l (X : bk.S) bk.ρ₀ (f i) * cD i w
  have key : ∀ (x : Fin d → bk.DS bk.ρ₀) (a : Fin d),
      (l : bk.DS bk.ρ₀) ^ r * x a = Φ ((V *ᵥ (s.W *ᵥ fun b => j₀ (x b))) a) := by
    intro x a
    have hsm : ∀ (c : bk.DA bk.ρ₀) (v : Fin d → bk.DA bk.ρ₀), (c • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))) *ᵥ v = c • v := by
      intro c v; ext b; simp [mulVec, dotProduct, Matrix.one_apply]
    rw [mulVec_mulVec, hVW, hsm]
    have h1 : ∀ i, cD i ((bk.iA (τ ^ (2 * s.N * d)) • fun b => j₀ (x b)) a) =
        x a * toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
      intro i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, hc_mul, hc_to]
    simp only [Φ, h1]
    have h2 := congrArg (toDisc l (X : bk.S) bk.ρ₀) hf
    rw [Finsupp.sum, map_sum, map_pow, map_natCast] at h2
    rw [← h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, map_mul]; ring
  obtain ⟨u, hu⟩ : IsUnit ((l : bk.DS bk.ρ₀) ^ r) := (isUnit_l_disc l (X : bk.S) bk.ρ₀).pow r
  have hsol : ∀ (x : Fin d → bk.DS bk.ρ₀) (a : Fin d),
      x a = ↑u⁻¹ * Φ ((V *ᵥ (s.W *ᵥ fun b => j₀ (x b))) a) := by
    intro x a
    rw [← key, ← hu, Units.inv_mul_cancel_left]

  have hcont : ∀ {F : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀}, IsDiscMap bk.ev F → Continuous F := fun hF =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => (hF.norm_le x).trans (one_mul _).ge
  have hcDc : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => (hc_norm i x).trans (one_mul _).ge
  let G : (Fin d → bk.DA bk.ρ₀) → (Fin d → bk.DA bk.ρ₀) := fun v =>
    s.W *ᵥ fun a => j₀ (↑u⁻¹ * Φ ((V *ᵥ v) a))
  have hGc : Continuous G := by
    refine continuous_const.matrix_mulVec (continuous_pi fun a => (hcont hj₀d).comp (continuous_const.mul ?_))
    exact continuous_finsetSum _ fun i _ => continuous_const.mul
      ((hcDc i).comp ((continuous_apply a).comp (continuous_const.matrix_mulVec continuous_id)))
  have hGy : ∀ n, G (fun a => bk.iA (y n a)) = fun a => bk.iA (y n a) := by
    intro n
    obtain ⟨x, hx⟩ := hy n
    have hxe := hx j₀ hj₀d
    have h3 : G (s.W *ᵥ fun b => j₀ (x b)) = s.W *ᵥ fun b => j₀ (x b) := by
      dsimp only [G]; congr 1; funext a; rw [← hsol x a]
    rwa [hxe] at h3

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have ht : Filter.Tendsto (fun n => fun a => bk.iA (y n a)) Filter.atTop (nhds fun a => bk.iA (z a)) := by
    rw [tendsto_pi_nhds]; intro a
    have h0 : Filter.Tendsto (fun n => bk.iA (z a - y n a)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl1))
      obtain ⟨w, hw⟩ := hz n a
      rw [hw]; exact norm_toDisc_natPow_mul_le _ _ n w
    have h4 := (tendsto_const_nhds (x := bk.iA (z a))).sub h0
    simpa only [sub_zero, map_sub, sub_sub_cancel] using h4
  have hfix : G (fun a => bk.iA (z a)) = fun a => bk.iA (z a) :=
    (isClosed_eq hGc continuous_id).mem_of_tendsto ht (Filter.Eventually.of_forall hGy)
  refine ⟨fun a => ↑u⁻¹ * Φ ((V *ᵥ fun b => bk.iA (z b)) a), fun j hj => ?_⟩
  rw [hj.unique hj₀d]
  exact hfix

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineEvalRingHomFrobeniusTaylorStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineEval_ringHom_frobenius_taylor : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ g : ↥(GK (ϖ.field a)), ∃ E : ↥(PPd t K e) →+* Per.Acris l, (∀ (x : (Wq l a)⟦X⟧) (hx : constP a K (inclS t K (frobS l a x)) ∈ PPd t K e), E ⟨_, hx⟩ = ainfToAcris l (WittVector.frobenius (ϖ.ev a x))) ∧ (∀ (x : (Wq l a)⟦X⟧) (hx : shP a sh (inclS t K (frobS l a x)) ∈ PPd t K e), E ⟨_, hx⟩ = ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a x)))) ∧ (∀ (F : ZMod a → K⟦X⟧⟦X⟧) (hF : F ∈ PPd t K e) (hF' : frob2 φ₂ F ∈ PPd t K e), E ⟨_, hF'⟩ = frobC l (E ⟨F, hF⟩)) ∧ ∀ (F : ZMod a → K⟦X⟧⟦X⟧) (hF : F ∈ PPd t K e) (hS : ∀ (τ : ZMod a) (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (F τ)) ∈ S O K e) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] E ⟨F, hF⟩ - ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hS τ i⟩) := by
  first | exact @GlobalTheory.CrysEval.evalPP | exact GlobalTheory.CrysEval.evalPP | (intros; apply GlobalTheory.CrysEval.evalPP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineQuotientTensorDual
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.RegularRing

theorem quot_tensor_dual_crys : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    GlobalTheory.Per.IsStd P AI → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocQuotCrys l P ∧ GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocTensorCrys l P ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocDualCrys l P := by
  intro l _ P AI hs
  have h := fontaineFormalism_of_regular l P AI
    (fun C => ⟨GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C, GlobalTheory.T.bcris_regular_of_tensorInj l C (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C)⟩) hs
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

end GlobalTheory.RegularRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
section
noncomputable section

namespace GlobalTheory.TwistRepCrys

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_fildR_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ' τ a) := by
  rw [GlobalTheory.HTW.FildR_eq_comap PD ρ ρ' e.toLinearMap e.injective he τ a]
  exact (LinearEquiv.ofSubmodule'
    (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)) (FildR PD ρ' τ a)).finrank_eq

theorem multV_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = multV PD ρ' τ a := by
  rw [multV, multV, finrank_fildR_of_equiv PD e he, finrank_fildR_of_equiv PD e he]

theorem multV_of_le_one (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL (DdRE PD ρ τ)] (h1 : finrank LL (DdRE PD ρ τ) ≤ 1) {b : ℤ}
    (hb : IsJumpV PD ρ τ b) (a : ℤ) : multV PD ρ τ a = if a = b then 1 else 0 := by
  haveI : ∀ a, FiniteDimensional LL (FildR PD ρ τ a) := fun a =>
    Submodule.finiteDimensional_of_le (S₂ := DdRE PD ρ τ) inf_le_left
  have anti : Antitone (FildR PD ρ τ) := fun a a' haa =>
    inf_le_inf_left _ (GlobalTheory.Cmp.SmallJumps.filV_anti PD haa)
  have mono : ∀ a a', a ≤ a' → finrank LL (FildR PD ρ τ a') ≤ finrank LL (FildR PD ρ τ a) :=
    fun a a' h => Submodule.finrank_mono (anti h)
  have le1 : ∀ a, finrank LL (FildR PD ρ τ a) ≤ 1 := fun a =>
    (Submodule.finrank_mono (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ)).trans h1
  have lt : finrank LL (FildR PD ρ τ (b + 1)) < finrank LL (FildR PD ρ τ b) :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (anti (by omega)) hb)
  have := le1 a
  have := le1 b
  rw [multV]
  rcases lt_trichotomy a b with h | h | h
  · have := mono (a + 1) b (by omega)
    have := mono a (a + 1) (by omega)
    rw [if_neg h.ne]
    omega
  · subst h
    rw [if_pos rfl]
    omega
  · have := mono (b + 1) a (by omega)
    have := mono a (a + 1) (by omega)
    rw [if_neg h.ne']
    omega

def transport (e : V ≃ₗ[LL] V') (ρ' : Representation LL G V') : Representation LL G V where
  toFun g := e.symm.toLinearMap ∘ₗ ρ' g ∘ₗ e.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

omit [Module Qp V] [IsScalarTower Qp LL V] [Module Qp V'] [IsScalarTower Qp LL V'] in
theorem transport_apply (e : V ≃ₗ[LL] V') (ρ' : Representation LL G V') (g : G) (x : V) :
    e (transport e ρ' g x) = ρ' g (e x) := by
  simp [transport]

end Generic

theorem isCrys_and_multV_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (χ : ↥(GK K) →* (↥LL.1)ˣ), IsTwistRep χ ρ ρ' → IsCrys (P.PD K) (charRep χ) → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a b : ℤ), IsJumpV (P.PD K) (charRep χ) τ b → multV (P.PD K) ρ' τ (a + b) = multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' χ ⟨e, he⟩ cχ cρ
  let f : (Fin 1 → ↥LL.1) ≃ₗ[↥LL.1] ↥LL.1 := LinearEquiv.funUnique (Fin 1) ↥LL.1 ↥LL.1
  let ν := transport f (charRep χ)
  have hν : ∀ g x, ν g x = ((χ g : (↥LL.1)ˣ) : ↥LL.1) • x := fun g x => by
    apply f.injective
    rw [transport_apply, map_smul]
    rfl
  have hρ : ∀ g x, transport e ρ' g x = ((χ g : (↥LL.1)ˣ) : ↥LL.1) • ρ g x := fun g x => by
    apply e.injective
    rw [transport_apply, he, map_smul]
  have cν : IsCrys (P.PD K) ν :=
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K) f.symm (fun g x => by
      apply f.injective
      rw [transport_apply, f.apply_symm_apply, f.apply_symm_apply]) cχ
  refine ⟨GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K) e (transport_apply e ρ')
    ((GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T K LL V ρ _ ν _ hν hρ cν).1 cρ),
    fun τ a b hb => ?_⟩
  obtain ⟨hfin, hle, -⟩ := (GlobalTheory.T.deRhamComponents_crystallineLetters_finrank l P AI T K LL ↥LL.1 (charRep χ)).1 τ
  rw [finrank_self] at hle
  rw [← multV_of_equiv (P.PD K) e (transport_apply e ρ')]
  refine GlobalTheory.TwistJump.multV_twist_char l P AI T K LL V ρ _ ν _ hν hρ
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL _ ν cν).1 τ b (fun c => ?_) a
  rw [multV_of_equiv (P.PD K) f (transport_apply f (charRep χ))]
  exact multV_of_le_one (P.PD K) (charRep χ) τ hle hb c

end GlobalTheory.TwistRepCrys
end
end

