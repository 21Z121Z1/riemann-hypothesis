import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicLevelCharacterEqTwistLevelCharacter
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0947
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0054
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0858
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0927
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0452
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0916
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0928
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0762
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0387
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0918
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0917
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0914
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0948
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReading
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0949
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0099
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0950
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicLevelCharacterEqTwistLevelCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicLevelCharacter_eq_twistLevelCharacter : ∀ (D : D7) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i (j.1 + 1) b k Q ψ e W₀ ρ₀ τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) (t : Twist D Circle) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi (Vc D j) D.R.nV), IdFrame hF P → B.F.βS = 1 → (∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv) → Function.Injective (NX.pG D) → t.Q = M.QP → B.de.Q = M.DP → ∀ (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)) (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank), (∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c = iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c))) → (∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U) → D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r → Disjoint M.QP M.DP → ∀ (e₀ : FractionRing (D.ntw.O i) →+* ℂ) (ek : NX.Kk D i k →+* ℂ), (∀ x, ek (NX.toKk D i k x) = e₀ x) → NX.IsStdGeneric (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r (D.nexp.psiU i b) → (∀ (u : D.nexp.U) hu, ((B.G.P.chi ⟨eG u, hu⟩ : ℂˣ) : ℂ) = e₀ (D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ)) → (∀ kv (x : (ZMod (D.host.g kv.1))ˣ) (z : (kP (NX.pG D kv))ˣ), (z : kP (NX.pG D kv)) = iso kv x → ((B.G.muC (NX.pG D kv) z : ℂˣ) : ℂ) = e₀ (τ kv x : (FractionRing (D.ntw.O i))ˣ)) → (∀ PP ∈ M.QP, ∀ u : 𝓞 D.host.E, u ∉ PP.asIdeal → ∀ z : (kP PP)ˣ, (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((t.resC PP z : ℂˣ) : ℂ) = ek (NX.ofOk D i k (NX.tameVal ψ PP e u).1)) → (∀ PP ∈ M.DP, ∀ u : 𝓞 D.host.E, u ∉ PP.asIdeal → ∀ z : (kP PP)ˣ, (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((B.de.resC PP z : ℂˣ) : ℂ) = ek (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) PP (if b then e else -e) u).1)) → ∀ g (h : g ∈ M.J) (h' : frameEquiv P g ∈ B.levJ t), ek ((M.χ ⟨g, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) = ((B.levLam t ⟨frameEquiv P g, h'⟩ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.LevChiRead.levChi_read | exact GlobalTheory.LevChiRead.levChi_read | (intros; apply GlobalTheory.LevChiRead.levChi_read <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseLevelCharacterMemCoefficientRingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLevelCharacter_mem_coefficientRing : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)), (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  first | exact @GlobalTheory.LamVal.levLam_mem_coef | exact GlobalTheory.LamVal.levLam_mem_coef | (intros; apply GlobalTheory.LamVal.levLam_mem_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAtPlaceOfIntegralCoverReading
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLocInt

theorem rd_sum {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {m : ℕ} (s : Fin m → C.d.c₂.F) (g : Fin m → Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (∑ b, s b • g b) = ∑ b, C.σ₂ (s b) • C.rd a (g b) := by
  unfold Cover.rd
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smulₛₗ, map_smul, smul_comm]

theorem rd_sub {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (g h : Rul C.d.Xo₂ C.d.c₂) : C.rd a (g - h) = C.rd a g - C.rd a h := by
  unfold Cover.rd
  rw [map_sub, map_sub, smul_sub]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem bddAll_of_mem_intForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (la' : HeightOneSpectrum (𝓞 C.c'.F)), (∀ y : C.c'.F, la'.valuation C.c'.F y = la.valuation C.d.c₂.F (C.d.eF y)) → ∀ (m : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → (∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b)) ∈ C.intForms a n {la} → GlobalTheory.GoodPts.BddAll (T.Q.Xo j) C.c' la' 1 (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) := by
  intro D T hL j hj σ hσ C hU a n hdom hPin la la' hval m x f hf hmem
  obtain ⟨g₂, ⟨hcs, hint⟩, hrd⟩ := hmem
  choose f₂ hf₂ using fun b => GlobalTheory.T.exists_pullback_section_to_levelCover D T hL j hj σ hσ C hU.1 a n (f b) (hf b)
  have hpin : ∀ b, C.rd a (f₂ b) = T.phiJ j σ a (f b) := fun b => hPin.2 (f b) (hf b) (f₂ b) (hf₂ b).1 (hf₂ b).2
  have hG : g₂ = ∑ b, C.d.eF (x b) • f₂ b := by
    by_contra hne
    have h0 : g₂ - ∑ b, C.d.eF (x b) • f₂ b ≠ 0 := sub_ne_zero.2 hne
    have hsec : g₂ - ∑ b, C.d.eF (x b) • f₂ b ∈ sec C.d.Xo₂ C.d.c₂ a n :=
      sub_mem hcs.1 (sum_mem fun b _ => Submodule.smul_mem _ _ (hf₂ b).1)
    have hli : LinearIndependent C.d.c₂.F ![g₂ - ∑ b, C.d.eF (x b) • f₂ b] :=
      linearIndependent_unique_iff.2 h0
    have hli2 := GlobalTheory.T.coverSections_linearIndependent_adelicReadings D T hL j hj σ hσ C hU hPin.1 a n hdom 1 ![g₂ - ∑ b, C.d.eF (x b) • f₂ b]
      (fun i => by fin_cases i; exact hsec) hli
    have hz : C.rd a (g₂ - ∑ b, C.d.eF (x b) • f₂ b) = 0 := by
      rw [rd_sub, rd_sum, hrd]
      simp only [hpin, sub_self]
    exact hli2.ne_zero 0 (by simpa using hz)
  intro Tv io e ho y hy
  obtain ⟨T', iT, e', y', io₂, y₂, hext, hfin', hio₂, hover⟩ :=
    GlobalTheory.CoverPoint.exists_ext_lift_to_cover _ _ _ _ (T.Q.Xo j) C.c' 0 C.d hU.1 Tv io y hy
  have ho₂ : OverLa la T'.V io₂ (e' * e) := by
    refine ⟨Nat.mul_pos hext.1 ho.1, fun z => ?_⟩
    have h1 := hio₂ (C.d.eF.symm z)
    rw [C.d.eF.apply_symm_apply] at h1
    have h2 : vLa la z = vLa la' (C.d.eF.symm z) := by
      simp only [vLa, hval, C.d.eF.apply_symm_apply]
    rw [h1, hext.2.1, ho.2, h2]
    push_cast
    ring
  have hB := (GlobalTheory.T.integral_values_algebraic_points_iff_value_nonneg _ _ _ _ C.d.Xo₂ C.d.c₂ la g₂).2 (hint la (Set.mem_singleton la)) T' io₂ (e' * e) ho₂
    y₂ hfin'
  rw [map_one, one_mul] at hB
  have laws := GlobalTheory.firstFiveLaws.1
  letI a1 : Algebra C.c'.F T'.Fr := (iT.comp io).toAlgebra
  letI a2 : Algebra C.d.c₂.F T'.Fr := io₂.toAlgebra
  letI a0 : Algebra T.Q.c.F T'.Fr := ((iT.comp io).comp (incF T.Q.c C.c' C.hle)).toAlgebra
  have hAO : AlgOver T.Q.c C.c' C.hle T'.Fr := fun _ => rfl
  have hcomp : ∀ z : C.c'.F, algebraMap C.d.c₂.F T'.Fr (C.d.eF z) = algebraMap C.c'.F T'.Fr z := hio₂
  have e1 : ∀ b, evI y₂ (f₂ b) = evR (T.Q.Xo j) T.Q.c (f b) (y'.1.res C.hle hAO) := fun b =>
    (hf₂ b).2 T'.Fr hAO hcomp y₂.1 y'.1 hover
  have e2 : ∀ b, evI y' (GlobalTheory.FieldBC.rulBC C.hle (f b)) = evR (T.Q.Xo j) T.Q.c (f b) (y'.1.res C.hle hAO) := fun b =>
    GlobalTheory.FieldBCModel.evR_rulBC C.hle (hf b).1 hAO y'.1
  have e3 : evI y₂ g₂ = evI y' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) := by
    rw [hG, GlobalTheory.GalSup.evI_sum, GlobalTheory.GalSup.evI_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [e1, e2, hio₂]
    rfl
  have hgs : (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) ∈ sec (T.Q.Xo j) C.c' a n :=
    sum_mem fun b _ => Submodule.smul_mem _ _ (GlobalTheory.FieldBCModel.rulBC_mem_sec C.hle (hf b))
  obtain ⟨φ, hφ, hm⟩ := hext.2.2
  letI a3 : Algebra C.c'.F Tv.Fr := io.toAlgebra
  have e4 : evI y' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) =
      iT (evI y (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b))) := by
    have := GlobalTheory.PlaceInt.evR_of_frMap_fromTest
      (GlobalTheory.Frames.algebraic_laws laws.secBaseChange _ _ _ _ (T.Q.Xo j) C.c').2.2.1 _ hgs.1 φ y.1 y.2.1 y'.1 hm
    exact this.trans (congrArg (fun r : Tv.Fr →+* T'.Fr => r (evR (T.Q.Xo j) C.c' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) y.1)) hφ)
  rw [map_one, one_mul, ← GlobalTheory.CoverBound.inV_map_iff iT hext.1 hext.2.1, ← e4, ← e3]
  exact hB

end GlobalTheory.CoverLocInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundLarge
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

private theorem admPar_large {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (a : Fm.Ix x), AdmissibleParameterJ.AdmPar (Fm.L x a) := by
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have h := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at h
  obtain ⟨x0, hx0⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) heps
  refine ⟨x0, fun x hxx hx a => ?_⟩
  have hC : (Fm.params x hx a).CLw ≤ Fm.PK.getD 7 0 := by
    have h := congrArg (fun l : List ℝ => l.getD 7 0) (Fm.params_K x hx a)
    simp only [parConsts] at h
    exact le_of_eq (by simpa using h)
  exact (hx0 (Fm.D x a) (Fm.L x a) (Fm.params x hx a) (Fm.L_eps x a) hC
    (by rw [Fm.L_x x a hx]; exact hxx)).1

theorem GlobalTheory.NLinkE.main : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), GlobalTheory.NFacts.Facts (Fm.D x i) (Fm.ex x hx i).nch → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at (Fm.D x i) (Fm.L x i) := by
  intro hP eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.T.exists_localPositionData_off_exceptional_primes Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.T.jump_bound_family_large Fm
  obtain ⟨x3, h3⟩ := admPar_large Fm
  refine ⟨max (max x1 x2) x3, fun x hx' hx1 a hF => ?_⟩
  have hx : max x1 x2 ≤ x := le_trans (le_max_left _ _) hx'
  have hA := h3 x (le_trans (le_max_right _ _) hx') hx1 a
  have hJ := h2 x (le_trans (le_max_right _ _) hx) hx1 a hF
  intro k hl hg hexc _hW hHG r hr π hπ ρ hρ
  have hlp : (Fm.D x a).nd.l k |>.Prime := ((Fm.D x a).nd.lPrime k).out
  obtain ⟨⟨h5, ht, hq, hd, hsm⟩, hposition⟩ := h1 x (le_trans (le_max_left _ _) hx) hx1 a hJ _ hlp hl
  have hur := GlobalTheory.TripleGal.host_ramificationIdx_eq_one (Fm.D x a) _ hlp hsm hq hd
  have heps := GlobalTheory.AdmissibleDictionary.main (Fm.D x a) k
  obtain ⟨g1, gc, gss⟩ := GlobalTheory.T.image_conditions_of_rank_part _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have g3 := GlobalTheory.T.big_image_third_condition _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have g2 := GlobalTheory.T.big_image_second_condition hP.font _ _ _ k r π ρ hF hA hl hg hHG hr hπ hρ
  obtain ⟨gno, gunr⟩ := GlobalTheory.T.no_character_offset_unramified _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gS := GlobalTheory.T.quadratic_unit_at_ramified_place _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gQ := GlobalTheory.T.quadratic_zeta_ne_one_at_place _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition k r (fun _ => ρ) π := hρ.2
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_globalStep_objects_of_cyclotomic_generator_inertia _ k r (fun _ => ρ) π hr g1 g3 gc gss gdec heps g3.2.2 hπ hur ht
  obtain ⟨HW, F, ⟨Cm⟩⟩ := GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze hP.bs (Fm.D x a)
  have hTOP := GlobalTheory.T.blochKatoTop_of_localTateDuality_eulerChar hP.bk hP.tate hP.euler (Fm.D x a) HW F Cm
  have hloc := GlobalTheory.UseLoc.main (Fm.D x a) HW F k r (fun _ => ρ) π hTOP (GlobalTheory.T.crystalline_characters_given_jumps_unramified_twists _ HW F) hJ.1 hr hπ g2 g3 gc gdec heps h5 hsm hq hd
    (fun n _ up τ => hposition hexc _ ((Fm.D x a).nd.j_range k).1 ((Fm.D x a).nd.j_range k).2 n up τ)
  exact GlobalTheory.T.congruenceBound_extended_of_rationalBound _ k π ρ hπ (fun v hv => (gQ v hv).2)
    (fun hs hsha => GlobalTheory.T.globalCongruenceCount_of_rootDifference_unit hP.artin _ k r _ π S hr hS hπ gno gunr gS gQ hloc hs hsha)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateDefiniteFormsDescendNumberFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_definiteForms_descend_numberField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∀ a b : Tp, ConjTup R τ (tup a) (tup b) → ∀ (y : (R.HV i (tup a)).H) (y' : (R.HV i (tup b)).H), ConjForm R i τ c (tup a) (tup b) y y' → ∃ (n : ℕ) (α : Fin n → ℂ) (ys : Fin n → (R.HV i (tup a)).H) (ys' : Fin n → (R.HV i (tup b)).H), y = ∑ k, α k • ys k ∧ y' = ∑ k, τ (α k) • ys' k ∧ ∀ k (h : GA D (Vc D i)), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i (tup a)).e (ys k) (fin _ h) = M.c0' x ∧ (R.HV i (tup b)).e (ys' k) (fin _ h) = M.c0' x' := by
  first | exact @GlobalTheory.ConjDesc.conj_desc | exact GlobalTheory.ConjDesc.conj_desc | (intros; apply GlobalTheory.ConjDesc.conj_desc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFramedPointOverMovedBaseFrame
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverFrameOver

open GlobalTheory.CoverFrameRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem un_over : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ (x : Frame (C.U₂.X (C.dict₂ h).1).Ψ D.R.r) (x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r) (hx : x ∈ (C.U₂.X (C.dict₂ h).1).dom) (hx' : x' ∈ ((T.U j σ).X (T.dict j σ h).1).dom), (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → CategoryTheory.CategoryStruct.comp ((C.U₂.un (C.dict₂ h).1 ⟨x, hx⟩).x : Sp ℂ ⟶ C.d.Xo₂.X) C.d.r = (((T.U j σ).un (T.dict j σ h).1 ⟨x', hx'⟩).x : Sp ℂ ⟶ (T.Q.Xo j).X) ∧ ∀ (τ : D.host.E →+* ℂ) (i : Fin ((T.Q.Dw j).mult τ)), CategoryTheory.CategoryStruct.comp ((C.U₂.un (C.dict₂ h).1 ⟨x, hx⟩).u τ i : Sp (DualNumber ℂ) ⟶ C.d.Xo₂.univ.t.G.left) C.d.m.φ = (((T.U j σ).un (T.dict j σ h).1 ⟨x', hx'⟩).u τ i : Sp (DualNumber ℂ) ⟶ (T.Q.Xo j).univ.t.G.left) := by
  intro D T hT j hj σ hσ C hC h γ hlat hiso hfr x x' hx hx' hxx
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, ⟨hEF₁, hper₁⟩, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨hlev, hA₂, hσ₂, hU₂, hdom, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, ⟨hEF₂, hper₂⟩, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  have hU₁ := hT.unf j hj σ hσ
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  obtain ⟨-, hpq, -, hq⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hT.pins j hj
  obtain ⟨γ₁, hγ₁, hL₁, hm₁, hf₁⟩ := hd₁ h
  obtain ⟨γ₂, hγ₂, -, hm₂, hf₂⟩ := hd₂ h
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := fun τ =>
    ((hU₁.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  obtain ⟨δ, hδf, hδm⟩ := move_mark (T.V j σ) hr₁ h γ₁ γ₂ hγ₁ hγ₂ _ hL₁
  have hγδ : (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = δ := by
    obtain ⟨τ, t₂⟩ : ∃ τ, τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := by
      by_cases h0 : D.host.φ₀ ∈ (C.U₂.X (C.dict₂ h).1).Ψ
      · exact ⟨_, h0⟩
      · exact ⟨_, not_not.1 (mt ((C.U₂.X (C.dict₂ h).1).cmType _).2 h0)⟩
    have t₁ := (hΨ τ).2 t₂
    have a₂ := hf₂ ⟨τ, t₂⟩
    have a₁ := hf₁ ⟨τ, t₁⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
    have a₃ := a₁.trans ((hδf τ _ (hth₁ _ ⟨τ, t₁⟩) _).trans (congrArg (_ * ·) a₂.symm))
    have a₄ := (hfr τ t₂ t₁).symm.trans a₃
    have hu : IsUnit (mat (C.dict₂ h).2 ⟨τ, t₂⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (hdom h ⟨τ, t₂⟩).1)
    exact Matrix.map_injective τ.injective (hu.mul_right_cancel a₄)
  obtain ⟨f, hf⟩ := exists_latEquiv _ _ γ hlat
  let gam := (φ₂ (C.dict₂ h).1).trans (f.trans (φ₁ (T.dict j σ h).1).symm)
  have hgam : ∀ a, (φ₁ (T.dict j σ h).1 (gam a) : Fin D.R.r → D.host.E) =
      (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (φ₂ (C.dict₂ h).1 a : Fin D.R.r → D.host.E) := fun a =>
    (congrArg Subtype.val ((φ₁ (T.dict j σ h).1).apply_symm_apply _)).trans (hf _)
  obtain ⟨P₁, hP₁, hp₁, hu₁, hv₁⟩ := hper₁ _ ⟨x', hx'⟩
  obtain ⟨P₂, hP₂, hp₂, hu₂, hv₂⟩ := hper₂ _ ⟨x, hx⟩
  have hle : KA T.Q.l ≤ KA C.d.l₂ := by rw [KA, KA, hA, hA₂]
  have hrel : ∀ τ : D.host.E →+* ℂ, relab T.Q.c σ τ = relab C.d.c₂ C.σ₂ τ := fun τ => by
    ext a
    exact (RingHom.congr_fun hσ₂ _).symm.trans (congrArg C.σ₂ (Subtype.ext rfl))
  obtain ⟨k₁, k₂⟩ := point_over C.d hlev (by omega) hA hle
    (RingHom.ext fun a => (congrArg C.σ₂ (Subtype.ext rfl)).trans
      (RingHom.congr_fun hσ₂ ((IntermediateField.inclusion T.Q.c.le).toRingHom a)))
    e₁ e₂ F₁ F₂ _ _ hp₁ hp₂ gam
    (fun a b => by
      have := (hEF₁ _ (gam a) (gam b)).trans (Eq.trans (by rw [hgam, hgam, hiso, (hW₁ _).2, (hW₂ _).2])
        (hEF₂ _ a b).symm)
      exact_mod_cast this)
    (fun a ha => by
      have b₂ := hm₂ a ha
      rw [hlev.2.1] at b₂
      obtain ⟨u, hu, e⟩ := hδm T.Q.l.M C.d.pd (by have := T.Q.l.three_le; omega) _ _ _
        (hm₁ a (Submodule.smul_mono_left (Ideal.map_mono hlev.1.2.1) ha)) b₂
      refine ⟨(φ₁ _).symm ⟨u, hu⟩, (φ₁ (T.dict j σ h).1).injective (Subtype.ext ?_)⟩
      rw [hgam, hγδ, e, map_add, map_nsmul, LinearEquiv.apply_symm_apply]
      rfl)
    (fun a i => by
      rw [hP₁, hP₂, hgam, Equiv.apply_symm_apply, hrel]
      exact perFr_move _ _ hΨ ((hU₁.2.1 _).1.trans (hU₂.2.1 _).1.symm) ((hW₁ _).1.trans (hW₂ _).1.symm) γ hiso x x'
        hxx _ _ _)
  exact ⟨by rw [hu₁, hu₂]; exact k₁, fun τ i => k₂ ⟨τ, i⟩ _ _ (hv₁ τ i) (hv₂ τ i)⟩

end GlobalTheory.CoverFrameOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReadingStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverReading_eq_pow_mul_movedFrameReading : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ (x : Frame (C.U₂.X (C.dict₂ h).1).Ψ D.R.r) (x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r), x ∈ (C.U₂.X (C.dict₂ h).1).dom → x' ∈ ((T.U j σ).X (T.dict j σ h).1).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → ∃ t : ℂ, t ≠ 0 ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ (C.dict₂ h).1 x = t ^ n * rdU (T.U j σ) f (T.dict j σ h).1 x' := by
  first | exact @GlobalTheory.CoverFrameRead.rdU_cover_eq | exact GlobalTheory.CoverFrameRead.rdU_cover_eq | (intros; apply GlobalTheory.CoverFrameRead.rdU_cover_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralValuesEqualCharacteristic
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqCharCusp

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem exists_goodAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ∃ p : ℕ, p.Prime ∧ l.GoodAt p := by
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (l.M + 1)
  refine ⟨p, hp, ?_⟩
  have h3 := l.three_le
  have hM : ¬ p ∣ l.M := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  unfold Level.GoodAt
  rw [Nat.factorization_eq_zero_of_not_dvd hM]
  simpa using h3

theorem exists_place (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ la : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ la.asIdeal := by
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨Q, -, hQ, hQl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) ⊥
    (by rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have : ((p : ℤ)) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQl ▸ Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hpQ⟩
  rw [h, Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int] at hQl
  have : ((p : ℤ)) ∈ (⊥ : Ideal ℤ) := hQl ▸ Ideal.mem_span_singleton_self _
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 this))

theorem integral_of_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, evI y f ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H Dw l Xo c r U hU a n f hd hf T hcnt io hint y
  obtain ⟨p, hp, hg⟩ := exists_goodAt l
  obtain ⟨la, hpl⟩ := exists_place c.F p hp
  let _ := io.toAlgebra
  obtain ⟨b, hb⟩ := exists_factor T (io.comp (la.valuation c.F).valuationSubring.subtype) (fun x => hint _)
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift y.1.x (spMap io) (y.1.x_over.trans (sp_comp _ _).symm)
  have hz₁ : z ≫ pullback.fst _ _ = y.1.x := pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hA : ∀ Y : Model Xo c (la.valuation c.F).valuationSubring.subtype, PushInvertible Y.t.G Y.t.PP.L →
      ∀ y' : Sp T.V ⟶ Y.X, z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → Set.range y' ⊆ abLocus Y.t.G →
      evI y f ∈ (algebraMap T.V T.Fr).range := fun Y hP y' h3 hr =>
    GlobalTheory.T.section_integral_equalChar_abelianLocus E H Dw l Xo c a n f hf.1 la Y hP T io hint y ⟨y', z, hz₁, hz₂, h3, hr⟩
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hD | hD
  · obtain ⟨Y, hP⟩ := GlobalTheory.SupFinite.exists_model_rank_zero Xo c hD (la.valuation c.F).valuationSubring.subtype
    obtain ⟨⟨y', ⟨-, hz₃⟩, -⟩, -⟩ :=
      GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c _ _ Y T.V T.Fr b io z hb hz₂
    refine hA Y hP y' hz₃.symm ?_
    rw [GlobalTheory.DefiniteAbelian.abLocus_eq_univ (by omega) _ Y]
    exact Set.subset_univ _
  obtain ⟨Y, hP, hop, hS, h3, h4⟩ := exists_model (by omega) Xo c la p hp hpl hg
  obtain ⟨⟨y', ⟨hy', hz₃⟩, -⟩, -⟩ :=
    GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c _ _ Y T.V T.Fr b io z hb hz₂
  by_cases hr : Set.range y' ⊆ abLocus Y.t.G
  · exact hA Y hP y' hz₃.symm hr
  obtain ⟨T', g, ϖ, a₀, hg₁, hg₂, hϖ, hA'⟩ := GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension E H Dw l Xo c _ Y h3 hS T io b y' z hb hy' hz₂ hz₃.symm hr
  obtain ⟨i, ρ, hρ, hi, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' g hg₁ hg₂
  obtain ⟨y₁, φ, hφ, hy₁⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i ρ hρ
    (fun x _ => hv x)
  let _ := (i.comp io).toAlgebra
  have e₁ : (algebraMap T'.V T'.Fr).comp g = i.comp (algebraMap T.V T.Fr) := RingHom.ext fun x => (hi x).symm
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_complex_embedding_fractionField_finite_over_cdvr c.F c.F.val.toRingHom T T' g hg₁ hg₂ hcnt (i.comp io)
  have hint' : ∀ k : c.F, (i.comp io) k ∈ (algebraMap T'.V T'.Fr).range := fun k => by
    obtain ⟨v, hv'⟩ := hint k
    exact ⟨g v, by rw [RingHom.comp_apply, ← hv', hi]⟩
  have key := GlobalTheory.T.cuspForm_integral_arc_section_equalChar E H Dw l Xo c r U hU la Y hP hop h4 a n f hd hf
    (fun T₁ io₁ h₁ y₂ hy₂ => GlobalTheory.T.section_integral_equalChar_abelianLocus E H Dw l Xo c a n f hf.1 la Y hP T₁ io₁ h₁ y₂ hy₂)
    T' (i.comp io) hint' ⟨κ, hκ⟩ (g.comp b)
    (by rw [← RingHom.comp_assoc, e₁, RingHom.comp_assoc, hb]; rfl) ϖ hϖ a₀ (spMap g ≫ y')
    (by rw [Category.assoc, hy', sp_comp]) hA' y₁ (spMap i ≫ z)
    (by rw [Category.assoc, hz₁, hy₁.1, hφ]) (by rw [Category.assoc, hz₂, sp_comp])
    (by rw [Category.assoc, ← hz₃, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, e₁])
  obtain ⟨hE, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have e₂ : evI y₁ f = φ (evI y f) :=
    (GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hf.1 T.Fr).1 _ φ _ _ hy₁
  have e₃ : φ (evI y f) = i (evI y f) := RingHom.congr_fun hφ _
  have key' : InV T' (i (evI y f)) := by rw [← e₃, ← e₂]; exact key
  rw [inV_iff, hv] at key'
  show InV T (evI y f)
  rw [inV_iff]
  exact nonneg_of_mul_nonneg_right key' (by exact_mod_cast hρ)

end GlobalTheory.EqCharCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisRationalFormsLocalUnitBallStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_rationalForms_local_unit_ball : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) → ∃ (n : ℕ) (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))), (∀ s, B s ∈ locBall YS fw iC b j) ∧ ∀ g ∈ locBall YS fw iC b j, ∀ s, ‖embS S iC b (B.repr g s)‖ ≤ 1 := by
  first | exact @GlobalTheory.GeoTie.locBall_basis_exists | exact GlobalTheory.GeoTie.locBall_basis_exists | (intros; apply GlobalTheory.GeoTie.locBall_basis_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityCoverFunctionReferenceTupleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rootOfUnity_coverFunction_reference_tuple : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → Normal ℚ M.c'.F → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) → (∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e) → ∃ c₀ : M.c'.F, IsRoot1 ((c₀ : M.c'.F) : ℂ) ∧ ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (x x' : M.Cl' A.μ0 → VsV D i M.c'.F), (∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k))) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M A.μ0 x f → (ta c₀ * c₀⁻¹)⁻¹ • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M A.μ0 x' ((ta c₀ * c₀⁻¹)⁻¹ • galRul hf f) := by
  first | exact @GlobalTheory.GalRef.exists_root_galRul_isSum | exact GlobalTheory.GalRef.exists_root_galRul_isSum | (intros; apply GlobalTheory.GalRef.exists_root_galRul_isSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjCoverFunctionEqConstMulConjTupleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisConj_coverFunction_eq_const_mul_conjTuple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∃ k0 : ℂ, IsRoot1 k0 ∧ ∀ (a b : Tp) (cx : Rul (M.dδ a).Xo₂ (M.dδ a).c₂), M.dδ b = { M.dδ a with cδ := cx } → HEq (M.U₂ b) (M.U₂ a) → HEq (M.dict₂ b) (M.dict₂ a) → ConjTup R τ (tup a) (tup b) → ∃ (h₂ : Fixes (M.dδ a).c₂ (covAut (M.dδ a) ta)) (ka : M.c'.F) (s : (AE D)ˣ), (ka : ℂ) = k0 * ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (M.dδ a).c₂.F k] (y₂ : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ k), evR (M.dδ a).Xo₂ (M.dδ a).c₂ (galRul h₂ (M.dδ a).cδ) y₂ = algebraMap (M.dδ a).c₂.F k ((M.dδ a).eF ka) * evR (M.dδ a).Xo₂ (M.dδ a).c₂ cx y₂ := by
  first | exact @GlobalTheory.CoverConj.conj_cover_const | exact GlobalTheory.CoverConj.conj_cover_const | (intros; apply GlobalTheory.CoverConj.conj_cover_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisLinearOrbitalIntegralDescentStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_linear_orbitalIntegral_descent : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (r : ℕ) (M : Meas r F E) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → ∀ f' : Gl r F → ℂ, IsTest f' → ∃ (φ' : A.K × A.K → ℂ) (κ : ℂ), IsTest φ' ∧ ∀ a : A.K, IsUnit a → orbG M f' (sec (A.invK τ p lam a)) = κ * A.orbK m.μK φ' a ∧ orbG M (fourG M ψ f') (sec (A.invK τ p lam a)) = κ * A.orbK m.μK (A.fourK m.μK ψ φ') a := by
  first | exact @GlobalTheory.JR.LinDesc.descent | exact GlobalTheory.JR.LinDesc.descent | (intros; apply GlobalTheory.JR.LinDesc.descent <;> assumption)
end

