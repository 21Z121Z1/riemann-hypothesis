import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0716
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationDataNormalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0718
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0464
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
import Formalism.LocalToGlobal.IndefiniteReal.FWCentral

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityGrassmannRelationOriginZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open scoped Matrix

namespace GlobalTheory.PointChernRel

open GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointChern GlobalTheory.GrassModel MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

theorem chernPoly_reindex {n m p : ℕ} (h : p = m) (K : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin p) (Fin p) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    chernPoly (fun u => Matrix.reindex (finCongr h) (finCongr h) (K u)) v k = chernPoly K v k := by
  subst h
  simp

theorem curvPoly_model {n r s : ℕ} (f g : Fin r → Fin s → Fin n) :
    curvPoly (fun u : ReciprocityTheory.L2DbarEstimates.V n =>
      (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 =
      -Matrix.of fun i j => ∑ c, X (g i c, f j c) := by
  refine Matrix.ext fun i j => ?_
  simp only [curvPoly, Matrix.of_apply, GlobalTheory.T.chernCurvature_inv_one_sub_conj_mul_transpose_at_zero, Matrix.neg_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    coordVec, PiLp.single_apply, apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero, map_neg, map_sum,
    neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, neg_inj]
  have h (x y : Fin n) (c : Fin s) : C (if f j c = y then if g i c = x then (1 : ℂ) else 0 else 0) * X (x, y) =
      if (g i c, f j c) = (x, y) then X (g i c, f j c) else (0 : MvPolynomial (Fin n × Fin n) ℂ) := by
    by_cases h1 : f j c = y <;> by_cases h2 : g i c = x <;> simp [h1, h2]
  simp only [h]
  rw [← Fintype.sum_prod_type' (f := fun x y => ∑ c, if (g i c, f j c) = (x, y) then X (g i c, f j c) else 0), Finset.sum_comm]
  simp

theorem coeff_comp_neg_X' {R : Type} [CommRing R] (p : Polynomial R) (b : ℕ) :
    (p.comp (-Polynomial.X)).coeff b = (-1) ^ b * p.coeff b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.add_comp, hp, hq, mul_add]
  | monomial m a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, neg_pow,
      ← mul_assoc, show ((-1 : Polynomial R)) ^ m = Polynomial.C ((-1) ^ m) by simp, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

theorem coeff_neg_charpolyRev {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (b : ℕ) :
    (-M).charpolyRev.coeff b = (-1) ^ b * M.charpolyRev.coeff b := by
  have h : (-M).charpolyRev = M.charpolyRev.comp (-Polynomial.X) := by
    rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
    congr 1
    ext a c : 2
    by_cases h : a = c <;> simp [h]
  rw [h, coeff_comp_neg_X']

theorem charpolyRev_map' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem relation_top_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, chernTop (relPoly τ k * P) (fun u => modelGram H Dw (coordOf ix u)) 0 = 0 := by
  intro E _ _ _ H Dw n ix τ k hk P
  set e : Fin Dw.p × Fin Dw.q → Fin n := fun x => ix.symm (τ, x.1, x.2) with he
  have hL : ∀ j, chernPoly (fun u => modelGram H Dw (coordOf ix u) τ.1) 0 j = (blockPoly e).charpolyRev.coeff j := by
    intro j
    have h1 : (fun u => modelGram H Dw (coordOf ix u) τ.1) = fun u =>
        Matrix.reindex (finCongr (mult_of_mem Dw τ.2).symm) (finCongr (mult_of_mem Dw τ.2).symm)
          ((1 - (Matrix.of fun i c => u (e (i, c))).map (starRingEnd ℂ) * (Matrix.of fun i c => u (e (i, c)))ᵀ)⁻¹) := by
      funext u
      simp only [modelGram, dif_pos τ.2]
      rfl
    rw [h1, chernPoly_reindex, chernPoly, curvPoly_model (fun i c => e (i, c)) (fun i c => e (i, c)), neg_neg]
    rfl
  have hc1 : ¬ conjEmb τ.1 (H.rt : E) = H.rt0 := GlobalTheory.AllWt.conj_not_mem τ
  have hc2 : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  have hD : ∀ j, chernPoly (fun u => modelGram H Dw (coordOf ix u) (conjEmb τ.1)) 0 j =
      (blockPolyBar e).charpolyRev.coeff j := by
    intro j
    have hτ : (⟨conjEmb (conjEmb τ.1), hc2⟩ : GlobalTheory.AllWt.Psi H) = τ := Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
    have h1 : (fun u => modelGram H Dw (coordOf ix u) (conjEmb τ.1)) = fun u =>
        Matrix.reindex (finCongr (mult_of_not_mem Dw hc1).symm) (finCongr (mult_of_not_mem Dw hc1).symm)
          ((1 - (Matrix.of fun b i => u (e (i, b))).map (starRingEnd ℂ) * (Matrix.of fun b i => u (e (i, b)))ᵀ)⁻¹) := by
      funext u
      simp only [modelGram, dif_neg hc1, dif_pos hc2, hτ]
      rfl
    rw [h1, chernPoly_reindex, chernPoly, curvPoly_model (fun b i => e (i, b)) (fun b i => e (i, b)), neg_neg]
    rfl
  have hrel : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) (relPoly τ k) =
      ((blockPoly e).charpolyRev * (-blockPolyBar e).charpolyRev).coeff k := by
    simp only [relPoly, map_sum, map_mul, aeval_X, aeval_C, hL, hD, Polynomial.coeff_mul, coeff_neg_charpolyRev]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [map_pow, map_neg, map_one]
    ring
  have hzero : toEven n (((blockPoly e).charpolyRev * (-blockPolyBar e).charpolyRev).coeff k) = 0 := by
    have h2 := GlobalTheory.T.charpolyRev_mul_eq_one_of_trace_pow_add_eq_zero (K := ℂ) _ _ (GlobalTheory.T.trace_pow_grassmannBlockCurvature_supertrace_zero e)
    have e1 : ((blockPoly e).map (toEven n)).charpolyRev = (blockPoly e).charpolyRev.map (toEven n).toRingHom :=
      (charpolyRev_map' _ _).symm
    have e2 : ((-blockPolyBar e).map (toEven n)).charpolyRev =
        (-blockPolyBar e).charpolyRev.map (toEven n).toRingHom := (charpolyRev_map' _ _).symm
    rw [e1, e2, ← Polynomial.map_mul] at h2
    have h3 := congrArg (fun f => Polynomial.coeff f k) h2
    simp only [Polynomial.coeff_map, Polynomial.coeff_one, if_neg (show k ≠ 0 by omega)] at h3
    exact h3
  rw [chernTop, map_mul, hrel, GlobalTheory.T.topDegreeFormCoeff_eq_tensorSquareTopCoefficient, map_mul, hzero, zero_mul]
  simp

end GlobalTheory.PointChernRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationFibreArithmeticGroupRelatStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentUniformisation_fibre_arithmeticGroup_related : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ψ v = ψ w → ∃ γ ∈ gammaU (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ), moebI γ (unflat v) = unflat w := by
  first | exact @GlobalTheory.UnifFibre.fibre_gamma | exact GlobalTheory.UnifFibre.fibre_gamma | (intros; apply GlobalTheory.UnifFibre.fibre_gamma <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConcreteSplitPrimeAutomorphicDataDivisionLatticeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.concreteSplitPrimeAutomorphicData_divisionLatticeChange : ∀ (sc : Scale) (D : D7) (Gt : GatTies D) (c : LatCmp D) (H : Formalism.L2.Herm.Herm0 D) (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), IsRecG sc D Gt c H F → IsRecG sc (setDiv D N h) (gatTr N h Gt) (cmpTr N h c) (DivTr.herm0S N h H) (fun u => DivTr.forms0S N h (F u)) := by
  first | exact @GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv | exact GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv | (intros; apply GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorPrimesInLowSetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_primes_in_low_set : ∀ (D : D7) (Z : GlobalTheory.LamTie.LamDat D), Z.Ok → Z.q0 = AbsolutelyIrreducibleSpan.q0 D → ∀ P : HeightOneSpectrum (𝓞 D.host.E), (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → ∃ p ∈ lowAll D, P ∈ placesOver D.host.E p := by
  first | exact @GlobalTheory.LamTie.cond0_primes_lowAll | exact GlobalTheory.LamTie.cond0_primes_lowAll | (intros; apply GlobalTheory.LamTie.cond0_primes_lowAll <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysOfLinearIndependentIntFormsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coneMatch_rays_of_linearIndependent_intForms : ∀ {X : Type} [AddCommGroup X] {k m : ℕ} (p : Fin k → LinearMap.BilinForm ℤ X) (δ : Fin m → LinearMap.BilinForm ℤ X),
  LinearIndependent ℤ p → LinearIndependent ℤ δ →
  ∀ (t : Fin k → ℝ) (c : Fin m → ℝ), (∀ i, 0 < t i) → (∀ j, 0 ≤ c j) → ∑ i, t i • toReal (p i) = ∑ j, c j • toReal (δ j) →
    (∀ i, InRCone δ (p i)) → (∀ j, 0 < c j → InRCone p (δ j)) →
    (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
    (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  first | exact @GlobalTheory.PolFan.cone_match_rays | exact GlobalTheory.PolFan.cone_match_rays | (intros; apply GlobalTheory.PolFan.cone_match_rays <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationDataNormalRingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneration_data_normal_ring : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left), IsGrpPullback F.univ.A G j e → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (I : Ideal R) (ξ : Sp R ⟶ S) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : Unif I D A G'), IsUnifOf F j e ξ π U → ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R) (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (β : B.left ⟶ G'.left) (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), y ≫ j = x ≫ ξ → IsGrpPullback B G' x β → IsGrpPullback B F.univ.A y α → α ≫ e = β ≫ π → IsSquare α α₂ → LBIso (abelian₂ B (U.LG.L.pull β)) (F.univ.P.pull α₂) := by
  first | exact @GlobalTheory.UnifLamFibre.lam_pull_eq_univ | exact GlobalTheory.UnifLamFibre.lam_pull_eq_univ | (intros; apply GlobalTheory.UnifLamFibre.lam_pull_eq_univ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimOpenlyImmersedVarietyEqCmTypeCardMulPqStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dim_openly_immersed_variety_eq_cmType_card_mul_pq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), (∃ y, y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j)) → ∀ k : U.Comp, X.dim = (U.X k).Ψ.card * (Dw.p * Dw.q) := by
  first | exact @GlobalTheory.OpenBaseDim.dim_eq | exact GlobalTheory.OpenBaseDim.dim_eq | (intros; apply GlobalTheory.OpenBaseDim.dim_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionLocalDataPreservedDivisionLatticeChangeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisionLocalData_preserved_divisionLatticeChange : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (Y : DivX (w.D Z)) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), DivT n Y → Nonempty (DivT (nchTTr w Z N h n) (divTr (D := w.D Z) N h Y)) := by
  first | exact @GlobalTheory.Mem.Top.Bl.WitTr.divT_setDiv | exact GlobalTheory.Mem.Top.Bl.WitTr.divT_setDiv | (intros; apply GlobalTheory.Mem.Top.Bl.WitTr.divT_setDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdjointOfReadRelation
section
noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

section Gen

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

variable (R) in

def EigVec (i : Fin D.R.m) (k : ℕ) (Q : PlE D.host) (Rr : Finset (GA D (Wc D i))) (c : ↥D.LL0) (v : (R.HW i (sg0 D A3.A)).H) : Prop :=
  hkNorm R i k Q • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e v) =
    D.what₂.embLL ((c : ↥D.LL0) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e v

theorem eigAd_iff_eigVec (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : EigAd Y Sb eig ↔
    ∀ (i : Fin D.R.m) σ k Q α Rr, HkDat R Sb i k Q α Rr → D.nd.goodRow σ → ∀ y ∈ D.what₂.isot (i.1 + 1) σ,
      EigVec R i k Q Rr (eig (i.1 + 1) σ k Q) (Y.mj.eW i y) := Iff.rfl

theorem EigVec.congr {i : Fin D.R.m} {k : ℕ} {Q : PlE D.host} {Rr : Finset (GA D (Wc D i))} {c : ↥D.LL0}
    {v v' : (R.HW i (sg0 D A3.A)).H} (h : EigVec R i k Q Rr c v) (e : HEq v' v) : EigVec R i k Q Rr c v' := eq_of_heq e ▸ h

end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (L : LocAll (lay0 (Dof x)))

theorem eig_hkDat_back (l : LC hL x) {i k Q α Rr} (h : HkDat (datL x L).R (sbD L l) i k Q α Rr) :
    HkDat x.m.z.R l.rat.In.Sb ((i)) k ((Q)) ((α)) ((Rr)) :=
  ⟨(by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.offS :)), (by with_unfolding_all exact (h.odd :)), (by with_unfolding_all exact (h.le :)), (by with_unfolding_all exact (h.elt :)), (by with_unfolding_all exact (h.reps :))⟩

theorem eigVec_loc {i k Q Rr c v} (h : EigVec x.m.z.R i k Q Rr c v) :
    EigVec (datL x L).R ((i)) k ((Q)) ((Rr)) ((c)) ((v)) := (h)

theorem eigVec_state (l : LC hL x) (i σ k Q α Rr) (hd : HkDat x.m.z.R l.rat.In.Sb i k Q α Rr) (hσ : (Dof x).nd.goodRow σ) (y)
    (hy : y ∈ (Dof x).what₂.isot (i.1 + 1) σ) : EigVec x.m.z.R i k Q Rr (l.rat.In.eig (i.1 + 1) σ k Q) (x.r.Y.mj.eW i y) :=
  (by with_unfolding_all exact (((eigAd_iff_eigVec _ _ _).1 l.rat.rat.eig i σ k Q α Rr hd hσ y hy) :))

theorem eigAd_loc (l : LC hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y) :
    EigAd Y (sbD L l) (eigD L l) :=
  (eigAd_iff_eigVec _ _ _).2 fun i σ k Q α Rr hd hσ y hy =>
    (by with_unfolding_all exact ((EigVec.congr (v' := ((Y.mj.eW i y))) (eigVec_loc L (eigVec_state l ((i)) ((σ)) k ((Q)) ((α)) ((Rr)) (((eig_hkDat_back L l hd))) ((hσ)) ((y)) ((hy))))
      (((hY.eW i y)))) : _))

end GlobalTheory.HeightCounting.Fin3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenSpanInclusionInjective
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem iotaR_injective_of (R : RealDat3 D A3 Ks) (hM : R.toRealDat.IsModels) (hU : R.toRealDat.LUnif) (i : Fin D.R.m) :
    Function.Injective (iotaR R i) := by
  have hj : Function.Injective ((R.FW i).j (sg0 D A3.A)) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    by_contra hne
    exact ((hU i _).1 1 (fun _ => v) (linearIndependent_unique_iff.2 hne)).ne_zero 0 hv
  exact (hM.HW i _).1.comp hj

end Gen

theorem iotaR_injective_states : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ i : Fin (Dof x).R.m, Function.Injective (GlobalTheory.EigSpanDesc.iotaR x.m.z.R i) := by
  intro hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x _ i
  exact iotaR_injective_of x.m.z.R x.m.z.pins.char.base.models x.m.intersectionNumber_baseChange.prim.unif i

end GlobalTheory.EigSpanDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGramNearPointStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenframe_gram_near_point : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (V : (gen s.T.Z).affineOpens) (φ : κ.c.F →+* Γ(gen s.T.Z, V.1)) (F : EigFrame s.T.Z φ (LogKS.chart V ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) (a b : Fin (S.Dw.mult τ)), LogKS.chart V ≫ genStr s.T.Z = spMap φ → ∀ y₀ : CxPts (genStr s.T.Z) σ, ¬ LiesIn y₀ (genBd s.T.Z) → y₀ ∈ ptsIn (genStr s.T.Z) σ V.1 → ∃ (T : Set (CxPts (genStr s.T.Z) σ)) (g : CxPts (genStr s.T.Z) σ → ℂ), IsOpen T ∧ y₀ ∈ T ∧ (manifold s.T.Z σ).SmoothOn T (fun y => (g y).re) ∧ (manifold s.T.Z σ).SmoothOn T (fun y => (g y).im) ∧ ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr s.T.Z) σ V.1) (f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)), F.IsMap (evHom hy) f → (x.hodge σ).gram y f τ a b = g y := by
  first | exact @GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_smooth_near | exact GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_smooth_near | (intros; apply GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_smooth_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef

namespace GlobalTheory.Mem.R3.Rw.WeilExt

section Defs

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
  {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}

def LevSame (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (R'.toLevCh.mu (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ((i' : ℕ) + 1)) (z.R.toLevCh.mu (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((i : ℕ) + 1)) ∧
    ∀ PP' PP, HEq PP' PP → PP ∈ z.R.Pg → HEq (R'.chi ((i' : ℕ) + 1) PP') (z.R.chi ((i : ℕ) + 1) PP)) ∧
  HEq R'.eta z.R.eta ∧ R'.Q (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) = ∅ ∧ z.R.Q (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) = ∅

def IdemSame (z : Dat (w.st Z) w.I hX T Wt) (Xg : Finset (Gc B' w'.px → B'.LL)) : Prop :=
  ∀ (g' : Gc B' w'.px) (g : Gc B w.px), HEq g' g → B'.embLL ((idemOf Xg).coeff g') = B.embLL ((idemOf z.Xg).coeff g)

set_option maxHeartbeats 1000000 in

def JSpan (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ x' : (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.fam.amb.FL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))),
      ∃ (n : ℕ) (a : Fin n → (w'.st Z').toD7.what₂.LL)
        (x : Fin n → (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))),
        HEq (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) x') (∑ k, (w'.st Z').toD7.what₂.embLL (a k) • z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) (x k))

end Defs

theorem ratAt_of_geo {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] (R : RealDat3 D A3 C.Q.c.F)
    (F : Face3 D A3) (hch : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (hI : GlobalTheory.RealGeo.InGeo geo) (hU : R.toRealDat.LUnif) :
    RatAt R.toRealDat A3.A.μ0 := by
  intro i x v hv
  have hio := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A3.A _ R.toRealDat hch.base.lev hch.base.fam hch.base.models
    (RealDat.thP_of_weak hch.base.thP hEx)
  have hM := GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation _ _ _ _ _ _ C R F geo.κ geo.v₀ geo.O (fun _ => 1) hn hch hEx ⟨geo.fw⟩ hio i
    (geo.pins i) (geo.phase i hU)
  have e : v = R.jV i A3.A.μ0 x := (hch.base.models.HV i _).1 (hv.trans (hch.base.models.jV i _ x).symm)
  subst e
  obt ⟨y, hy⟩ := (Formalism.IndefR.FWT.phase_of_oneMap geo.fw hU
    (hI.evInj i _ (Formalism.IndefR.FWT.base_embedding_good C R.toRealDat geo.fw.alg_eq geo.fw.laws.pins.2.2.1)) (geo.O i) (geo.phase i hU hM.1)).2 x
  exact ⟨y, hy.trans (one_smul ℂ _)⟩

theorem eq_cj_one_smul {H : Type} [AddCommGroup H] [Module ℂ H] (s : Bool) (v : H) : v = Formalism.IndefR.Links.cj s (1 : ℂ) • v := by
  rw [map_one, one_smul]

local macro "qmove " h:term : tactic => `(tactic| (
  obtain ⟨i, u, a, l, e, m, w, b, x, k⟩ := $h
  refine ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨u.mu_off, u.mu_used, u.mu_ne, u.mu_conj, u.mu_on⟩, a, l, e, m, w, b, x, fun c hc => ?_⟩
  have kv := k c hc
  exact ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩))

set_option maxHeartbeats 8000000 in

theorem charW_keep (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL]
    (R₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (hI : Inputs X.toD7)
    (hXi : IdemClass (D := X.toD7) (famR X I hX U Xg tr₀).A)
    (hEx : ∀ R : RealDat X.toD7 (famR X I hX U Xg tr₀).A Ks, R.Pre1 (face0 X I hX U Xg tr₀).lv2 → R.IsChainW → R.IsThPW → R.ExAt)
    (S : RealDat X.toD7 (famR X I hX U Xg tr₀).A Ks → Prop)
    (hSM : ∀ R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG, S R →
      S (updM R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG))
    (hS3 : ∀ R ωY ωX vac vacX vY vX ItY ItX ioY ioX Th, S R → S (R.upd3 ωY ωX vac vacX vY vX ItY ItX ioY ioX Th))
    (hS6 : ∀ R kap lam, S R → S (R.upd6 kap lam)) (s0 : S R₀.toRealDat)
    (p0 : R₀.toRealDat.Pre0 (face0 X I hX U Xg tr₀).lv2) (i0 : R₀.IsInert) (t0 : R₀.IsTup) (a0 : R₀.AllPlaces)
    (k0 : Keep R₀.toRealDat (face0 X I hX U Xg tr₀).lv2 cG) (b0 : BrgStd X I hX U Xg tr₀ R₀.toRealDat) (x0 : R₀.toRealDat.grp_chiW)
    (hW : ModW R₀.toRealDat) (hω : WeilAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0) (hV : ModVAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0)
    (hl : LiftAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0) (hr : RatAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0) :
    ∃ (tr : TrI X.B px) (R : RealDat3 X.toD7 (famR X I hX U Xg tr) Ks) (cG' : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd),
      Pins R (face0 X I hX U Xg tr) cG' ∧ R.toRealDat.ExAt ∧ R.toRealDat.toLevCh = R₀.toRealDat.toLevCh ∧ HEq R.eG R₀.eG ∧ HEq cG' cG ∧
      R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧ BrgStd X I hX U Xg tr R.toRealDat ∧ S R.toRealDat ∧
      SameAt (A := (famR X I hX U Xg tr₀).A) R₀.toRealDat R.toRealDat (famR X I hX U Xg tr₀).A.μ0 := by
  classical
  obt ⟨hL, hF⟩ := GlobalTheory.HeckeCharacterRestriction.liftsAt_and_seedFacts X.toD7 _ _ _ (famR X I hX U Xg tr₀).A Ks (face0 X I hX U Xg tr₀).lv2
  obt ⟨R1, p1, c1, t1, f1, g1, ⟨q1, s1⟩, m1, hrat⟩ := exists_weak_keep hI hXi hL hF
    (fun R => (RealDat3.IsInert (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) ∧
      RealDat3.IsTup (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) ∧
      RealDat3.AllPlaces (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) ∧
      R.toLevCh = R₀.toLevCh ∧ HEq R.eG R₀.eG ∧ R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧
      BrgStd X I hX U Xg tr₀ R ∧ R.grp_chiW ∧
      ∀ c : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG → Keep (A3 := (famR X I hX U Xg tr₀)) R (face0 X I hX U Xg tr₀).lv2 c) ∧ S R)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 ⟨h, s⟩ => ⟨by qmove h, hSM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s⟩)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 ⟨h, s⟩ => ⟨by qmove h, hS3 _ _ _ _ _ _ _ _ _ _ _ _ s⟩)
    R₀.toRealDat p0 ⟨⟨⟨i0.tie, i0.onto, i0.hR, i0.hL, i0.SF⟩, ⟨t0.mu_off, t0.mu_used, t0.mu_ne, t0.mu_conj, t0.mu_on⟩, a0, rfl, HEq.rfl,
      rfl, rfl, b0, x0, fun c hc => by cases eq_of_heq hc; exact k0⟩, s0⟩ hW hω hV hl hr
  obtain ⟨i1, u1, a1, l1, e1, mu1, w1, b1, x1, k1⟩ := q1
  have hc : ∃ c : G0 R1.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG := by
    rw [show R1.Pg = R₀.Pg from congrArg (fun L => L.Pg) l1]
    exact ⟨cG, HEq.rfl⟩
  obtain ⟨cutoffDeriv, hcG1⟩ := hc
  let R2₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks := ⟨R1, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  have htr : ∃ tr : TrI X.B px, (∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t') →
      R2₀.TrISem (face0 X I hX U Xg tr₀) tr ∧ SepWith (famR X I hX U Xg tr₀) tr := by
    by_cases h : ∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t'
    · obtain ⟨t', h'⟩ := h
      exact ⟨t', fun _ => h'⟩
    · exact ⟨tr₀, fun h' => absurd h' h⟩
  obtain ⟨tr, htr⟩ := htr
  let R2 : RealDat3 X.toD7 (famR X I hX U Xg tr) Ks := ⟨R1, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  obt ⟨kap, lam, hs⟩ := scalars_exist (F := face0 X I hX U Xg tr) R2
  have p6 := RealDat.preliminary_of_scalar_update p1 kap R2.lam
  have f6 := RealDat.full_Y_of_scalar_update f1 kap R2.lam
  have c6 := RealDat.weak_chain_of_scalar_update c1 kap R2.lam
  have t6 := RealDat.weak_theta_props_of_scalar_update t1 kap R2.lam
  have g6 := RealDat.full_P_of_scalar_update g1 kap R2.lam
  have hphs : (R2.updS kap lam).phase := by
    intro i
    refine ⟨show ‖(1 : ℂ)‖ = 1 from norm_one, fun _ x => ?_⟩
    obt ⟨y, hy⟩ := hrat i x
    refine ⟨y, ?_⟩
    exact (by with_unfolding_all exact (hy.trans (eq_cj_one_smul (twAt X.toD7.what₂.embLL (famR X I hX U Xg tr₀).A.v0) _) :))
  have kv := k1 cutoffDeriv hcG1
  exact ⟨tr, R2.updS kap lam, cutoffDeriv, ⟨⟨⟨p6.1.lev, ⟨p6.1.red_R, p6.1.red_L, p6.1.levels, p6.1.record, x1⟩,
      p6.1.fam, p6.2, c6, t6⟩, ⟨⟨i1.tie.plI_inj, i1.tie.okI⟩, i1.onto, i1.hR, i1.hL, i1.SF⟩, f6.1, f6.2, g6, hs,
      ⟨u1.mu_off, u1.mu_used, u1.mu_ne, u1.mu_conj, u1.mu_on⟩, hphs, a1⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩,
    fun _ => rfl, fun h => htr h⟩, hEx _ p6 c6 t6, l1, e1, hcG1, mu1, w1, b1, hS6 _ kap R2.lam s1, m1⟩

end GlobalTheory.Mem.R3.Rw.WeilExt

end
end

