import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastSideLogBound
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
import ReciprocityTheory.Hypotheses.GalCoh
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.Bundle0003
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastSideLogBoundStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_side_log_bound : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.OrthNormLogBound → ∀ (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), WeightTie N W pl u δ → Sizes Pr W N.sc.a → SizeRows N δ (Pr.T u) → 1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R → LastSide R 25 (lastLog W u) := by
  first | exact @GlobalTheory.ColRows.LastSideProof.lastSide | exact GlobalTheory.ColRows.LastSideProof.lastSide | (intros; apply GlobalTheory.ColRows.LastSideProof.lastSide <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCombinationInHodgeFiltrationStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_combination_in_hodge_filtration : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g)
    (P : u.Λ →+ HdR A), LieExact A → (∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) →
    ∀ c : u.Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ Fil A ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0 := by
  first | exact @GlobalTheory.HodgeUnif.sum_smul_mem_fil_iff | exact GlobalTheory.HodgeUnif.sum_smul_mem_fil_iff | (intros; apply GlobalTheory.HodgeUnif.sum_smul_mem_fil_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfSymmetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymFirstOrder
open GlobalTheory.CechPic

theorem lbIso_of_symmetric : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A']
    (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left),
    IsAbelianScheme A →
    IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i →
    IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → i ≫ q = 𝟙 _ →
    ∀ (L M : LB A'.left), L.IsLB → M.IsLB →
      LBIso (L.pull (GrpObj.inv : A' ⟶ A').left) L → LBIso (M.pull (GrpObj.inv : A' ⟶ A').left) M →
      LBIso (L.pull i) (M.pull i) → LBIso L M := by
  intro K _ _ A _ A' _ i q hA hi hq e L M hL hM hLs hMs hLM
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hA hq
  set c := cls L hL - cls M hM with hc
  have h0 : pull i c = 0 := by
    rw [hc, map_sub, ← cls_pull hL i (pull_isLB hL i), ← cls_pull hM i (pull_isLB hM i),
      (cls_eq_iff (pull_isLB hL i) (pull_isLB hM i)).2 hLM, sub_self]
  have hinv : pull (GrpObj.inv : A' ⟶ A').left c = c := by
    rw [hc, map_sub, ← cls_pull hL _ (pull_isLB hL _), ← cls_pull hM _ (pull_isLB hM _),
      (cls_eq_iff _ hL).2 hLs, (cls_eq_iff _ hM).2 hMs]
  have hlam := ConstTheta.lam_eq_zero GlobalTheory.laws_without_cohomology.1 hA' hi.1 c h0 (𝟙 A') (𝟙 A')⁻¹
  have einv : (𝟙 A')⁻¹ = (GrpObj.inv : A' ⟶ A') := by simp [Hom.inv_def]
  have hone : pull (1 : A' ⟶ A').left c = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨Q, hQ, hQc⟩ := cls_surj (pull (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left c)
    rw [← hQc, (cls_eq_zero_iff hQ).2 (LB.exists_isGen_of_isLocalRing hQ), map_zero]
  have htwo : 2 • c = 0 := by
    unfold lam at hlam
    rw [mul_inv_cancel, einv, hinv, hone, Over.id_left, pull_id] at hlam
    rw [two_nsmul, ← neg_eq_zero, neg_add]
    simpa [sub_eq_add_neg, add_assoc] using hlam

  have hsurj : Surjective i := by
    have : Surjective (GlobalTheory.DeRham.epsRed K) := ⟨fun x => by
      haveI := ConstTheta.subsingleton_sp (K := K)
      obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
      exact ⟨t, Subsingleton.elim _ _⟩⟩
    exact MorphismProperty.of_isPullback (P := @Surjective) hi.1.flip this
  have hiq : ∀ x, i (q x) = x := fun x => by
    obtain ⟨y, rfl⟩ := hsurj.surj x
    rw [← Scheme.Hom.comp_apply i q, e]; rfl
  have h2 : IsUnit (2 : Γ(A'.left, ⊤)) := by
    have u : IsUnit (2 : DualNumber K) := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [show TrivSqZeroExt.fst (2 : DualNumber K) = 2 from rfl]; exact isUnit_iff_ne_zero.2 two_ne_zero)
    have u' := (u.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom).map A'.hom.appTop.hom
    rwa [map_ofNat, map_ofNat] at u'
  have hsq : ∀ (W : A'.left.Opens) (f g : Γ(A'.left, W)), (i.app W).hom f = 0 → (i.app W).hom g = 0 → f * g = 0 := by
    refine SquareZero.mul_eq_zero_of_app_eq_zero (DualNumber K) K (TrivSqZeroExt.fstHom K K K).toRingHom
      TrivSqZeroExt.fst_surjective ?_ A'.left A.left A'.hom A.hom i hi.1
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro r hr s hs
    have hr' : r.fst = 0 := hr
    have hs' : s.fst = 0 := hs
    rw [Ideal.mem_bot]
    ext <;> simp [hr', hs']
  have hc0 := GlobalTheory.T.cechPicardClass_eq_zero_of_squareZero_retraction i q e hiq h2 hsq c h0 htwo
  exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 hc0)

end GlobalTheory.SymFirstOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickeningStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_quasiLogarithm_along_pdThickening : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (g : MvPowerSeries (Fin d) C) (w : Fin d → B), QL (fun i => map θ (μ i)) ⊤ g → (∀ i, lin g i = algebraMap O C (θ (w i))) → ∃ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f ∧ map Θ f = g ∧ ∀ i, lin f i = algebraMap B Q (w i) := by
  first | exact @GlobalTheory.QLog.KLift.lift_quasiLog | exact GlobalTheory.QLog.KLift.lift_quasiLog | (intros; apply GlobalTheory.QLog.KLift.lift_quasiLog <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearNormalisationClosedSubschemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearNormalisation_closed_subscheme : ∀ (Rg : Type) [CommRing Rg] (mA mB : ℕ) (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤)), ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (GlobalTheory.HomFixUniv.Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  first | (exact @GlobalTheory.HomFixUniv.normal_closed) | (exact GlobalTheory.HomFixUniv.normal_closed) | (intros; apply GlobalTheory.HomFixUniv.normal_closed  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralExpRhoEqSetLIntegralUnitBallDomainStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_expRho_eq_setLIntegral_unitBallDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Base X) (s : ℝ), ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) ∂muF X x0.1 = ∫⁻ z in Om X, ENNReal.ofReal (density X x0 z) * ENNReal.ofReal (Real.exp (-(s * rho X z))) := by
  first | exact @GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om | exact GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om | (intros; apply GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocfinHolds
section
namespace GlobalTheory.Laid

theorem locfin_holds : ReciprocityTheory.Gal.LocalFiniteness := GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness

end GlobalTheory.Laid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogClassNumberAtLe
section
noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnClassLog

theorem log_le_of_count (h f n N g₀ g₁ T : ℕ) (rd L : ℝ) (hf : 1 ≤ f) (hn : 1 ≤ n) (hnN : n ≤ N) (hT : 1 ≤ T) (hrd : 0 < rd)
    (hL : 1 ≤ L) (hrdL : Real.log rd ≤ L) (hfN : (f : ℝ) * N ≤ Real.exp L) (hg₀ : Real.exp L ≤ g₀) (hg₁ : 1 ≤ g₁)
    (hh : (h : ℝ) ≤ (3 * (((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * rd ^ 2)) ^ (3 * (2 * f) * n ^ 2) *
      ((g₀ : ℝ) * g₁ * T) ^ (f * (n * n))) :
    Real.log h ≤ 55 * (f : ℝ) * (N : ℝ) ^ 2 * Real.log ((g₀ : ℝ) * g₁ * T) := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hg₁' : (1 : ℝ) ≤ g₁ := by exact_mod_cast hg₁
  have he : 0 < Real.exp L := Real.exp_pos L
  have hg0 : (0 : ℝ) < g₀ := lt_of_lt_of_le he hg₀
  have hG : Real.exp L ≤ (g₀ : ℝ) * g₁ * T := by
    calc Real.exp L ≤ g₀ := hg₀
      _ = (g₀ : ℝ) * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  set G : ℝ := (g₀ : ℝ) * g₁ * T with hGd
  have hGp : 0 < G := lt_of_lt_of_le he hG
  have hLG : L ≤ Real.log G := (Real.le_log_iff_exp_le hGp).2 hG
  have hlG : 0 ≤ Real.log G := by linarith
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp only [Nat.cast_zero, Real.log_zero]
    positivity
  have hrd' : rd ≤ Real.exp L := (Real.log_le_iff_le_exp hrd).1 hrdL
  have hfn : (f : ℝ) * n ≤ Real.exp L := le_trans (by gcongr) hfN
  have hn2 : (n : ℝ) ≤ Real.exp L := le_trans (by nlinarith) hfn
  have h12 : (12 : ℝ) ≤ Real.exp L ^ 3 := by
    have h1 : Real.exp 1 ≤ Real.exp L := Real.exp_le_exp.2 hL
    have h2 : (2.7 : ℝ) ≤ Real.exp L := by linarith [Real.exp_one_gt_d9]
    calc (12 : ℝ) ≤ 2.7 ^ 3 := by norm_num
      _ ≤ _ := by gcongr
  set A : ℝ := 3 * (((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * rd ^ 2) with hA
  have hAp : 0 < A := by rw [hA]; push_cast; positivity
  have hA9 : A ≤ G ^ 9 := by
    calc A = 12 * ((f : ℝ) * n) ^ 2 * (n : ℝ) ^ 2 * rd ^ 2 := by rw [hA]; push_cast; ring
      _ ≤ Real.exp L ^ 3 * Real.exp L ^ 2 * Real.exp L ^ 2 * Real.exp L ^ 2 := by gcongr
      _ = Real.exp L ^ 9 := by ring
      _ ≤ G ^ 9 := by gcongr
  have hfin : (h : ℝ) ≤ G ^ (55 * f * n ^ 2) := by
    calc (h : ℝ) ≤ A ^ (3 * (2 * f) * n ^ 2) * G ^ (f * (n * n)) := hh
      _ ≤ (G ^ 9) ^ (3 * (2 * f) * n ^ 2) * G ^ (f * (n * n)) := by gcongr
      _ = G ^ (55 * f * n ^ 2) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  calc Real.log h ≤ Real.log (G ^ (55 * f * n ^ 2)) := Real.log_le_log (by exact_mod_cast hpos) hfin
    _ = 55 * (f : ℝ) * (n : ℝ) ^ 2 * Real.log G := by rw [Real.log_pow]; push_cast; ring
    _ ≤ _ := by gcongr

theorem fibre_bound_le {X : Fields} {Pr : Primes X} (hP : Pr.Ok) (u : Pr.Word) (n : ℕ) (hn : 1 ≤ n)
    (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (hSG : SG = Pr.vGs) :
    (∏ P ∈ Pr.vT u, Ideal.absNorm P.asIdeal ^ n) * ∏ w ∈ SG, Ideal.absNorm w.asIdeal ^ (n * n) ≤
      (Pr.g 0 * Pr.g 1 * Pr.T u) ^ (X.f * (n * n)) := by
  classical
  subst hSG
  have hT : ∏ P ∈ Pr.vT u, Ideal.absNorm P.asIdeal ^ n ≤ Pr.T u ^ (X.f * (n * n)) := by
    rw [Finset.prod_congr rfl (fun P hP' => by rw [hP.vT_norm u P hP']), Finset.prod_const, hP.vT_card, ← pow_mul]
    exact Nat.pow_le_pow_right (hP.T_prime u).pos (by rw [mul_comm]; exact Nat.mul_le_mul_left _ (Nat.le_mul_self n))
  have hg : ∀ i, ∏ w ∈ Pr.vG i, Ideal.absNorm w.asIdeal ^ (n * n) = Pr.g i ^ (X.f * (n * n)) := by
    intro i
    rw [Finset.prod_congr rfl (fun P hP' => by rw [hP.vG_norm i P hP']), Finset.prod_const, hP.vG_card, ← pow_mul, mul_comm]
  have hd : Disjoint (Pr.vG 0) (Pr.vG 1) := by
    rw [Finset.disjoint_left]
    intro w h0 h1
    exact hP.g_ne ((hP.vG_norm 0 w h0).symm.trans (hP.vG_norm 1 w h1))
  have hU : ∏ w ∈ Pr.vGs, Ideal.absNorm w.asIdeal ^ (n * n) = Pr.g 0 ^ (X.f * (n * n)) * Pr.g 1 ^ (X.f * (n * n)) := by
    rw [← hg 0, ← hg 1, ← Finset.prod_union hd]
    unfold Primes.vGs
    congr
  rw [hU, mul_pow, mul_pow, mul_comm]
  exact Nat.mul_le_mul_left _ hT

end GlobalTheory.ColumnClassLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LubinTatePeriodFiltrationExact
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK

namespace GlobalTheory.PMC.PeriodVector

theorem exists_casimir (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Algebra.IsSeparable F K] :
    ∃ (n : ℕ) (b d : Fin n → K), (∑ j, Algebra.trace F K (d j) • b j = 1) ∧
      ∀ (M : Type) [AddCommGroup M] [Module F M] (β : K →ₗ[F] K →ₗ[F] M) (c : K),
        ∑ j, β (c * b j) (d j) = ∑ j, β (b j) (c * d j) := by
  classical
  let b := Module.finBasis F K
  let B := Algebra.traceForm F K
  let d := B.dualBasis (traceForm_nondegenerate F K) b
  have h1 : ∀ x, ∑ k, Algebra.trace F K (x * b k) • d k = x := fun x => by
    conv_rhs => rw [← d.sum_repr x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply]
    rfl
  have h2 : ∀ x, ∑ k, Algebra.trace F K (d k * x) • b k = x := fun x => by
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have : B (d k) = b.coord k := b.ext fun j => by
      rw [LinearMap.BilinForm.apply_dualBasis_left]
      simp [Finsupp.single_apply]
    exact LinearMap.congr_fun this x
  refine ⟨_, b, d, by simpa using h2 1, fun M _ _ β c => ?_⟩
  calc ∑ j, β (c * b j) (d j) = ∑ j, ∑ k, Algebra.trace F K (d k * (c * b j)) • β (b k) (d j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [← h2 (c * b j)]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ k, ∑ j, Algebra.trace F K (c * d k * b j) • β (b k) (d j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [show d k * (c * b j) = c * d k * b j by ring]
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        conv_rhs => rw [← h1 (c * d k)]
        simp only [map_sum, map_smul]

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

theorem exists_vector [Algebra.IsSeparable Qp K] (χ : G →* Kˣ) (τ : K →ₐ[Qp] LL)
    (ρ : Representation LL G (Fin 1 → LL)) (hρ : ∀ g v, ρ g v = (τ (χ g : K))⁻¹ • v) (Y : BdR)
    (hY : ∀ g, PD.actdR g Y = algebraMap K BdR (χ g : K) * Y) (h1 : Y ∈ PD.Fil 1) (h2 : Y ∉ PD.Fil 2) :
    ∃ x ∈ DdRE PD ρ τ, x ∈ FilV PD (LL := LL) (V := Fin 1 → LL) 1 ∧
      x ∉ FilV PD (LL := LL) (V := Fin 1 → LL) 2 := by
  have := PD.finK
  obtain ⟨n, b, d, hbd, hcas⟩ := exists_casimir Qp K
  let e : Fin 1 → LL := fun _ => 1
  let β : K →ₗ[Qp] K →ₗ[Qp] ((Fin 1 → LL) ⊗[Qp] BdR) :=
    (TensorProduct.mk Qp (Fin 1 → LL) BdR).compl₁₂
      (((LinearMap.toSpanSingleton LL _ e).restrictScalars Qp) ∘ₗ τ.toLinearMap)
      ((LinearMap.toSpanSingleton K _ Y).restrictScalars Qp)
  have hβ : ∀ u v, β u v = (τ u • e) ⊗ₜ[Qp] (v • Y) := fun _ _ => rfl
  have hmul : ∀ c : K, mulVdR (K := K) (BdR := BdR) (V := Fin 1 → LL) (LL := LL) c (∑ j, β (b j) (d j)) =
      τ c • ∑ j, β (b j) (d j) := fun c => by
    have hl : ∀ j, mulVdR (K := K) (BdR := BdR) (V := Fin 1 → LL) (LL := LL) c (β (b j) (d j)) =
        β (b j) (c * d j) := fun j => by
      rw [hβ, hβ, mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply,
        ← Algebra.smul_def, smul_smul]
    rw [map_sum, Finset.smul_sum]
    simp only [hl]
    rw [← hcas]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hβ, hβ, map_mul, mul_smul, TensorProduct.smul_tmul']
  refine ⟨∑ j, β (b j) (d j), ⟨?_, ?_⟩, ?_, ?_⟩
  · refine (Submodule.mem_iInf _).2 fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    have hne : τ (χ g : K) ≠ 0 := (map_ne_zero τ).2 (χ g).ne_zero
    have : actVdR PD ρ g (∑ j, β (b j) (d j)) = (τ (χ g : K))⁻¹ •
        mulVdR (K := K) (BdR := BdR) (V := Fin 1 → LL) (LL := LL) (χ g : K) (∑ j, β (b j) (d j)) := by
      rw [map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hβ, actVdR, mulVdR, AlgebraTensorModule.map_tmul, AlgebraTensorModule.map_tmul, hρ,
        ← TensorProduct.smul_tmul', LinearMap.id_apply, LinearMap.mulLeft_apply]
      congr 2
      change PD.actdR g (d j • Y) = _
      rw [map_smul, hY, mul_smul_comm]
    rw [this, hmul, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · refine (Submodule.mem_iInf _).2 fun c => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hmul, sub_self]
  · refine Submodule.sum_mem _ fun j _ => ?_
    exact ⟨(τ (b j) • e) ⊗ₜ[Qp] ⟨d j • Y, (PD.Fil 1).smul_mem _ h1⟩, rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨lam, hlam⟩ : ∃ lam : LL →ₗ[Qp] Qp, lam 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff Qp (1 : LL)).1 h)
    let Λ : ((Fin 1 → LL) ⊗[Qp] BdR) →ₗ[Qp] BdR :=
      TensorProduct.lift ((LinearMap.lsmul Qp BdR) ∘ₗ lam ∘ₗ LinearMap.proj 0)
    have hΛ : ∀ v y, Λ (v ⊗ₜ[Qp] y) = lam (v 0) • y := fun _ _ => rfl
    have hmem : ∀ z, Λ (AlgebraTensorModule.map (LinearMap.id : (Fin 1 → LL) →ₗ[LL] (Fin 1 → LL))
        ((PD.Fil 2).restrictScalars Qp).subtype z) ∈ PD.Fil 2 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul v y =>
        rw [AlgebraTensorModule.map_tmul, hΛ]
        exact ((PD.Fil 2).restrictScalars Qp).smul_mem _ y.2
      | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
    have hx := hmem z
    rw [hz] at hx
    have hκ : Λ (∑ j, β (b j) (d j)) = (∑ j, lam (τ (b j)) • d j) • Y := by
      rw [map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hβ, hΛ, smul_assoc]
      simp [e]
    have hκ0 : (∑ j, lam (τ (b j)) • d j) ≠ 0 := fun h => hlam (by
      have h' := congrArg (Algebra.trace Qp K) h
      have h'' := congrArg (fun u => lam (τ u)) hbd
      simp only [map_sum, map_smul, map_zero, map_one, smul_eq_mul] at h' h''
      rw [← h'', ← h']
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _)
    rw [hκ] at hx
    exact h2 (((PD.Fil 2).smul_mem_iff hκ0).1 hx)

end General

theorem exists_degree_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (Y : P.R.BdR),
    (∀ g : ↥(GK K), (P.PD K).actdR g Y = algebraMap ↥K.1 P.R.BdR (χ g : ↥K.1) * Y) →
    Y ∈ (P.PD K).Fil 1 → Y ∉ (P.PD K).Fil 2 →
    ∃ x ∈ DdRE (P.PD K) (lineRep (K := K) (LL := LL) (ltChar τ₀ χ⁻¹)) τ₀,
      x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 1 ∧
      x ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 2 := by
  intro l _ P K LL χ τ₀ Y hY h1 h2
  have := (P.PD K).finK
  refine exists_vector (P.PD K) χ τ₀ _ (fun g v => ?_) Y hY h1 h2
  simp [lineRep, ltChar]

end GlobalTheory.PMC.PeriodVector

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqLeOfNoShortVector
section
open NumberField GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.SlopeMink

theorem sum_embeddings_eq_two_mul {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (g : (K →+* ℂ) → ℝ) (hg : ∀ σ, g ((starRingEnd ℂ).comp σ) = g σ) :
    ∑ σ : K →+* ℂ, g σ = 2 * ∑ v : InfinitePlace K, g v.embedding := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun σ => InfinitePlace.mk σ) g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hc : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w), g σ = g w.embedding := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [← hσ.2]
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ := by
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [this, hg]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two, nsmul_eq_mul]
  norm_num

theorem slopeMax_sq_le_of_no_short : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V)
    (La : ℝ), HasGram N → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → L.FG → L ≠ ⊥ →
    (∀ x ∈ L, x ≠ 0 → -La ≤ (∑ σ : K →+* ℂ, Real.log (N σ x)) / (Module.finrank ℚ K : ℝ)) →
    slopeMax_sq N L ≤ 2 * La + Real.log (Module.finrank K V : ℝ) +
      Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  intro K V _ _ _ _ _ _ _ N L La hG hconj hfg h0 hshort
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, hX⟩ := hG.some
  rw [(slopeMax_slopeMin_eq hX hfg h0).1]
  have hXu : ∀ v, IsUnit (X v).det := fun v => (hX v).1
  have hnf : Module.finrank ℚ K = 2 * Formalism.HN.nPl K := Formalism.HN.sizeMu_finrank_eq K
  have hf : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have : 0 < Formalism.HN.nPl K := Fintype.card_pos
    exact_mod_cast this
  have hmink := Formalism.ExtensionFiltration.muMaxMinkowski K V (Fin n) b X hXu L La hfg h0 (by
    intro x hx hx0
    have h1 := hshort x hx hx0
    rw [sum_embeddings_eq_two_mul (fun σ => Real.log (N σ x)) (fun σ => by simp only [hconj])] at h1
    have e : ∀ v : InfinitePlace K, Real.log (N v.embedding x) = Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) :=
      fun v => by rw [(hX v).2 x]
    simp only [e] at h1
    rw [hnf] at h1
    push_cast at h1
    have : (2 * ∑ v : InfinitePlace K, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x)) / (2 * (Formalism.HN.nPl K : ℝ)) =
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) := by
      field_simp
    linarith)
  haveI : Module.Finite K V := Module.Finite.of_basis b
  have hj : 0 < Formalism.HN.rkK L := by
    have h : Submodule.span K (L : Set V) ≠ ⊥ := by
      intro h
      apply h0
      rw [Submodule.span_eq_bot] at h
      exact (Submodule.eq_bot_iff _).2 (fun x hx => h x hx)
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)
  have hle : (Formalism.HN.rkK L : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast Submodule.finrank_le _
  have hlog : Real.log (Formalism.HN.rkK L : ℝ) ≤ Real.log (Module.finrank K V : ℝ) :=
    Real.log_le_log (by exact_mod_cast hj) hle
  have hd : Formalism.HN.logDisc K = Real.log |(discr K : ℝ)| := rfl
  rw [hd] at hmink
  linarith

end GlobalTheory.SlopeMink
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanDetSetIffAdelicLatticeValuationStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_detSet_iff_adelicLattice_valuation : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x : Fin n → E, x ∈ L ↔ ∀ (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)), Valued.v (((g⁻¹).1.mulVec (fun j => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x j)) i) Q) ≤ 1) → ∀ x : E, x ∈ Submodule.span (𝓞 E) (detSet L) ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ Valued.v (g.1.det Q) := by
  first | exact @GlobalTheory.AdelicDetSpan.mem_span_detSet_iff | exact GlobalTheory.AdelicDetSpan.mem_span_detSet_iff | (intros; apply GlobalTheory.AdelicDetSpan.mem_span_detSet_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtensionStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modF_finiteIdeleUpToExtension : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ), modF (upIdele K E t) = modF t ^ Module.finrank K E := by
  first | exact @GlobalTheory.UpIdeleMod.modF_upIdele | exact GlobalTheory.UpIdeleMod.modF_upIdele | (intros; apply GlobalTheory.UpIdeleMod.modF_upIdele <;> assumption)
end

