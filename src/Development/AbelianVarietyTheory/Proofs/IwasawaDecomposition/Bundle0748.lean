import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0119
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefEqConjTransposeMulSelfOfIsUnitDet
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory

open scoped MatrixOrder in

theorem posDef_eq_conjTranspose_mul_self_of_isUnit_det :
    ∀ {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ), P.PosDef →
      ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := by
  intro p P hP
  have h0 : (0 : Matrix (Fin p) (Fin p) ℂ) ≤ P := Matrix.nonneg_iff_posSemidef.mpr hP.posSemidef
  have hB : star (CFC.sqrt P) * CFC.sqrt P = P := by
    rw [(CFC.sqrt_nonneg P).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self P h0]
  refine ⟨CFC.sqrt P, ?_, hB⟩
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  rw [← hB, Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefOneSubMulConjTransposeOfPosDefSwap
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.PosDefSwap

open scoped Matrix.Norms.L2Operator in

theorem one_sub_mul_conjTranspose_posDef {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ)
    (h : (1 - zᴴ * z).PosDef) : (1 - z * zᴴ).PosDef := by
  have h1 : ‖z‖ < 1 := (GlobalTheory.MatrixBall.posDef_iff_norm_lt_one z).mp h
  have h2 : ‖zᴴ‖ < 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  have h3 := (GlobalTheory.MatrixBall.posDef_iff_norm_lt_one zᴴ).mpr h2
  rwa [Matrix.conjTranspose_conjTranspose] at h3

theorem main : ∀ {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ), (1 - zᴴ * z).PosDef → (1 - z * zᴴ).PosDef :=
  fun z h => one_sub_mul_conjTranspose_posDef z h

end GlobalTheory.PosDefSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdXSubCScaleMemLifts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistLift

open Polynomial

theorem prod_X_sub_C_scale_mem_lifts {K : Type} [Field K] (f : K →+* ℂ) (M : Multiset ℂ) (y : K)
    (hy : f y ≠ 0) (h : (M.map (fun α => X - C α)).prod ∈ Polynomial.lifts f) :
    ((M.map (fun x => x * f y)).map (fun α => X - C α)).prod ∈ Polynomial.lifts f := by
  set q : ℂ[X] := C (f y)⁻¹ * X with hq
  have key : ((M.map (fun x => x * f y)).map (fun α => X - C α)).prod =
      C (f y) ^ Multiset.card M * ((M.map (fun α => X - C α)).prod).comp q := by
    clear h
    induction M using Multiset.induction_on with
    | empty => simp
    | cons a M ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, ih, mul_comp]
      have e1 : (X - C a).comp q = C (f y)⁻¹ * X - C a := by simp [hq]
      have e2 : X - C (a * f y) = C (f y) * (C (f y)⁻¹ * X - C a) := by
        rw [mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hy, C_1, one_mul, ← C_mul, mul_comm (f y) a]
      rw [e1, e2]; ring
  rw [key]
  refine mul_mem (pow_mem (Polynomial.C_mem_lifts f y) _) ?_
  rw [Polynomial.lifts_iff_set_range] at h ⊢
  obtain ⟨p, hp⟩ := h
  refine ⟨p.comp (C y⁻¹ * X), ?_⟩
  rw [Polynomial.map_comp, hp, hq]
  simp [map_inv₀]

end GlobalTheory.TwistLift

namespace GlobalTheory.TwistLift

open Polynomial

theorem galPol_lifts_tw_etaTinv : ∀ (D : D7) (cf : CharFrame D), GlobalTheory.HeightCounting.CharSide D cf → ValLL0 D cf → ∀ π : D.naut.CG D.R.r, (∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D)) → ∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D) := by
  intro D cf hC hV π hπ
  obtain ⟨k, hk⟩ := D.R.t_odd
  filter_upwards [hπ, D.naut.locG_unr_ae π] with w hw hu
  have hUe : cf.eta.UnrAt w := by
    have h1 := (hC.unr_iff D.naut.etaT w).1 (D.naut.etaT_unr w)
    rwa [hC.etaT] at h1
  have hFe : D.naut.frobEig (D.naut.locG D.naut.etaT w) = {((cf.eta.val w : ℂ))⁻¹} := by
    have h1 := hC.frob D.naut.etaT w (by rw [hC.etaT]; exact hUe)
    rw [h1, hC.etaT]; simp
  have hFi : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {(cf.eta.val w : ℂ)} := by
    rw [(D.naut.etaTinv_def w).2, hFe]; simp
  have hUi : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hD1 : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  obtain ⟨y, hy⟩ := hV.eta w hUe
  have hNv : Formalism.ConjugateSelfDual.normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hN : ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ≠ 0 := by
    rw [hNv, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  set N : ℂ := ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) with hNdef
  set lam : D.LL0 := y * (((Formalism.ConjugateSelfDual.normV w : ℕ) : D.LL0) ^ k)⁻¹ with hlamdef
  have hlam : embLL0 D lam = (cf.eta.val w : ℂ) * N ^ (-(1 / 2 : ℂ)) * (N ^ k)⁻¹ := by
    rw [hlamdef, map_mul, map_inv₀, map_pow, map_natCast, hy, Formalism.L2.Host.HChar.valTw, hNdef, hNv]
    push_cast; ring
  have hlam0 : embLL0 D lam ≠ 0 := by
    rw [hlam]
    refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) (inv_ne_zero (pow_ne_zero _ hN))
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hmul : D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2)) =
      (D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map (fun x => x * embLL0 D lam) := by
    rw [D.naut.locG_tw, D.naut.frobEig_tw _ _ (D.naut.unr_char _ _ hD1 hu hUi),
      D.naut.frobEig_char _ _ _ hu hUi hD1 hFi, D.naut.frobEig_tw _ _ hu, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun x _ => ?_)
    simp only [Function.comp_apply]
    have hs : (((1 - (D.R.nV : ℝ)) / 2 : ℝ) : ℂ) = (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) + (-(1 / 2 : ℂ)) + (-(k : ℂ)) := by
      have e : D.R.nV = D.R.r + D.R.t := rfl
      rw [e, hk]; push_cast; ring
    rw [hlam, ← hNdef, hs, Complex.cpow_add _ _ hN, Complex.cpow_add _ _ hN, Complex.cpow_neg (x := N) (y := (k : ℂ)),
      Complex.cpow_natCast]
    ring
  have hw' := hw
  simp only [galPol] at hw' ⊢
  rw [hmul]
  exact prod_X_sub_C_scale_mem_lifts (embLL0 D) _ lam hlam0 hw'

end GlobalTheory.TwistLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcTorusStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_model_arc_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ χ : Sp (PowerSeries O') ⟶ Z.X, Out.jK (PowerSeries O') ≫ χ = x₀ ≫ Z.j := by
  first | exact @GlobalTheory.PolArcExtend.extend | exact GlobalTheory.PolArcExtend.extend | (intros; apply GlobalTheory.PolArcExtend.extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatioAgreeOnOverlapStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratio_agree_on_overlap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) st (V V' : Z.X.Opens) (A B : Γ(Z.X, V)) (A' B' : Γ(Z.X, V')), IsAffineOpen (V ⊓ V') → RatioAt Z st V ![A] ![B] → RatioAt Z st V' ![A'] ![B'] → ∃ u : Γ(Z.X, V ⊓ V')ˣ, u.val * ((Z.X.presheaf.map (homOfLE (inf_le_right : V ⊓ V' ≤ V')).op).hom A' * (Z.X.presheaf.map (homOfLE (inf_le_left : V ⊓ V' ≤ V)).op).hom B) = (Z.X.presheaf.map (homOfLE (inf_le_right : V ⊓ V' ≤ V')).op).hom B' * (Z.X.presheaf.map (homOfLE (inf_le_left : V ⊓ V' ≤ V)).op).hom A := by
  first | exact @GlobalTheory.HTLine.Overlap.ratioAt_overlap_unit | exact GlobalTheory.HTLine.Overlap.ratioAt_overlap_unit | (intros; apply GlobalTheory.HTLine.Overlap.ratioAt_overlap_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalHeckeAtLevelsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_hecke_at_levels : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ i : Fin (Dof x).R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke x.m.z.R.toRealDat i := by
  first | exact @GlobalTheory.HeckeFamRead.rationalHecke_allSt | exact GlobalTheory.HeckeFamRead.rationalHecke_allSt | (intros; apply GlobalTheory.HeckeFamRead.rationalHecke_allSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RawPackEqPow
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Rigid

theorem exists_frob (hc : GlobalTheory.TwSys.Cheb) (D : D7) (i : D.ntw.Tw) (Q : Finset (PlE D.host)) {p : ℕ} (hp : p ≠ 0)
    (γ : D.ntw.RCG i Q) :
    ∃ w, w ∉ Q ∧ w ∉ placesOver D.host.E p ∧ ∃ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      Formalism.ConjugateSelfDual.IsPlaceOver B w ∧ Formalism.ConjugateSelfDual.IsFrob B (Formalism.ConjugateSelfDual.normV w) σ ∧ D.ntw.art i Q σ = γ := by
  classical
  obtain ⟨g, rfl⟩ := D.ntw.art_surj i Q γ
  obtain ⟨w, hwA, -, -, B, hB, -, σ, hσ, hU⟩ := hc D.host.E D.nd.Om (D.ntw.art i Q).ker (D.ntw.art_cont i Q) inferInstance g
    (Q ∪ (placesOver_finite_av D.host.E p hp).toFinset)
  refine ⟨w, fun h => hwA (Finset.mem_union_left _ h),
    fun h => hwA (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)), B, σ, hB, hσ, ?_⟩
  rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hU

theorem pow_of_tied (hc : GlobalTheory.TwSys.Cheb) {D : D7} (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C)
    (v : D.what₂.places.Pl) (ψ : D.ntw.RCG (C.twI v) (C.Q v) →* (D.ntw.Ok (C.twI v) (C.k' v))ˣ)
    (ι : TwChar.RootIso D (C.twI v) (C.k' v))
    (hF : TwChar.FrobPick (C.twI v) (C.Q v) (C.k' v) ψ ι (tp.psi v)) (hT : PsiChoiceCompatible D cf C tp)
    (htw : TwistedAt D v) (hk : 1 ≤ C.k' v)
    (hL : ∀ z : ℂ, z ^ D.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D.what₂.LL, D.what₂.embLL x = z) :
    ∃ a : ℕ, a.Coprime (D.ntw.l (C.twI v)) ∧ C.psi' v = ψ ^ a := by
  haveI : NeZero (D.ntw.l (C.twI v) ^ C.k' v) := ⟨pow_ne_zero _ (D.ntw.lPrime _).out.ne_zero⟩
  have hL' : ∀ z : ℂ, z ^ (D.ntw.l (C.twI v) ^ C.k' v) = 1 → ∃ x : D.what₂.LL, D.what₂.embLL x = z := fun z hz =>
    hL z (by rw [← C.twI_l v]; exact hz)
  let j : D.ntw.Ok (C.twI v) (C.k' v) →+* FractionRing (C.Oe v) :=
    (algebraMap (C.Oe v) (FractionRing (C.Oe v))).comp (algebraMap (D.ntw.Ok (C.twI v) (C.k' v)) (C.Oe v))
  have hj : Function.Injective j := (IsFractionRing.injective (C.Oe v) (FractionRing (C.Oe v))).comp (C.Oe_inj v)
  obtain ⟨a, ha, hax⟩ := TwChar.exists_exponent ι (D.ntw.zk_prim _ _) D.what₂.embLL hL' (C.embW v) j hj
  refine ⟨a, Nat.Coprime.coprime_dvd_right (dvd_pow_self _ (by omega)) ha, MonoidHom.ext fun γ => Units.ext ?_⟩
  have hp : D.what₂.places.resChar v ≠ 0 := by rw [← C.twI_l v]; exact (D.ntw.lPrime _).out.ne_zero
  obtain ⟨w, hwQ, hwl, B, σ, hB, hσ, rfl⟩ := exists_frob hc D (C.twI v) (C.Q v) hp γ
  obtain ⟨u, hu, hχ⟩ := hF w hwQ B hB σ hσ
  obtain ⟨x, hx⟩ := hL' ((ι u : ℂˣ) : ℂ) (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 (ι u).2, Units.val_one])
  have h1 := hT v htw w hwQ hwl B σ hB hσ x (by rw [hχ, inv_inv]; exact hx)
  have h2 := hax u x hx
  have h3 := hj (h1.symm.trans h2)
  rw [MonoidHom.pow_apply, ← hu]
  exact h3

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem transfer {D₁ D₂ : D7} (h : SameExport D₁ D₂) (p : TwPack D₁) (A : Finset (PlE D₁.host))
    (ι : TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (hO : BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2)
    (hF : TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ) (i₂ : D₂.ntw.Tw) (Q₂ : Finset (PlE D₂.host)) (k₂ : ℕ)
    (χ₂ : HChar D₂.host.E) (hi : HEq i₂ p.1) (hQ : HEq Q₂ p.2.1) (hk : k₂ = p.2.2.1) (hχ : HEq χ₂ χ) :
    ∃ (ψ₂ : D₂.ntw.RCG i₂ Q₂ →* (D₂.ntw.Ok i₂ k₂)ˣ) (ι₂ : TwChar.RootIso D₂ i₂ k₂) (A₂ : Finset (PlE D₂.host)),
      BlochKatoReduction.Gen.PsiOk i₂ A₂ Q₂ k₂ ψ₂ ∧ TwChar.FrobPick i₂ Q₂ k₂ ψ₂ ι₂ χ₂ ∧ D₂.ntw.l i₂ = D₁.ntw.l p.1 ∧
      ∀ a : ℤ, HEq (⟨i₂, Q₂, k₂, ψ₂ ^ a⟩ : TwPack D₂) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  obtain ⟨h1, h2, -, -, -⟩ := h
  obtain ⟨i, Q, k, ψ⟩ := p
  dsimp only at hi hQ hk hO hF ι ⊢
  subst hk
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  cases D₁; cases D₂
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases ‹NData _ _ _›; cases ‹NData _ _ _›
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases ‹@NTw _ _ _ _ _ _ _›; cases ‹@NTw _ _ _ _ _ _ _›
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hi; subst hQ; subst hχ
  exact ⟨ψ, ι, A, hO, hF, rfl, fun _ => HEq.rfl⟩

theorem rawPack_eq_pow : PrN → ∀ (D₁ D₂ : D7) (p : TwPack D₁) (A : Finset (PlE D₁.host)) (ι : GlobalTheory.Mem.Top.TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (cf : CharFrame D₂) (C : NChoice D₂) (tp : TupTied D₂ cf C) (v : D₂.what₂.places.Pl), SameExport D₁ D₂ → BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2 → GlobalTheory.Mem.Top.TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ → PsiChoiceCompatible D₂ cf C tp → TwistedAt D₂ v → HEq (C.twI v) p.1 → HEq (C.Q v) p.2.1 → C.k' v = p.2.2.1 → HEq (tp.psi v) χ → (∀ z : ℂ, z ^ D₂.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D₂.what₂.LL, D₂.what₂.embLL x = z) → ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l p.1) ∧ HEq (rawPack C v) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  intro hc D₁ D₂ p A ι χ cf C tp v h hO hF hT htw hi hQ hk hχ hL
  obtain ⟨ψ₂, ι₂, A₂, hO₂, hF₂, hl, hpow⟩ := transfer h p A ι χ hO hF (C.twI v) (C.Q v) (C.k' v) (tp.psi v) hi hQ hk hχ
  obtain ⟨a, ha, hψ⟩ := pow_of_tied hc.cheb cf C tp v ψ₂ ι₂ hF₂ hT htw hO₂.2.2.1 hL
  refine ⟨a, by rw [Int.natAbs_natCast, ← hl]; exact ha, ?_⟩
  have e : rawPack C v = (⟨C.twI v, C.Q v, C.k' v, ψ₂ ^ (a : ℤ)⟩ : TwPack D₂) := by
    rw [zpow_natCast, ← hψ]
    rfl
  rw [e]
  exact hpow a

end GlobalTheory.HeightCounting.Rigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadTw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def ReadTw (D : D7) (a : D.nd.Loc) : Prop :=
  ∃ (φ : FractionRing (D.ntw.O0 (D.ntw.twOf a)) →+* Qbar (D.ntw.l (D.ntw.twOf a)))
    (ι : Qbar (D.ntw.l (D.ntw.twOf a)) ≃+* ℂ),
    (∀ z : ℤ_[D.ntw.l (D.ntw.twOf a)], φ (algebraMap (D.ntw.O0 (D.ntw.twOf a)) _
        (algebraMap ℤ_[D.ntw.l (D.ntw.twOf a)] (D.ntw.O0 (D.ntw.twOf a)) z)) =
      algebraMap ℚ_[D.ntw.l (D.ntw.twOf a)] (Qbar (D.ntw.l (D.ntw.twOf a))) (z : ℚ_[D.ntw.l (D.ntw.twOf a)])) ∧
    (∀ x : ↥D.LL0, ι (φ ((if D.ntw.twSide a then D.ntw.emb0 (D.ntw.twOf a) else D.ntw.emb0b (D.ntw.twOf a)) x)) =
      embLL0 D x) ∧
    ∀ y : D.ntw.O0 (D.ntw.twOf a), ι (φ (algebraMap _ (FractionRing (D.ntw.O0 (D.ntw.twOf a))) y)) =
      iotaO D.nd D.naut a (D.ntw.twist₂ a y)

end GlobalTheory.RowTriple

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsAtOfPlUnder
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.Mem.Top.TwChar (plUnder incl embLL_incl mem_plUnder)

theorem readsAt_of_plUnder (X X' : Stages) (h : Enl X.B X'.B) (hc : Carried X.toD7 X'.toD7) (v' : X'.B.places.Pl)
    (i : X.toD7.ntw.Tw) (i' : X'.toD7.ntw.Tw) (b : Bool) (hi : HEq i i')
    (hr : ReadsAt (D := X.toD7) i b (plUnder h v')) : ReadsAt (D := X'.toD7) i' b v' := by
  intro x'

  have hx : X'.B.embLL ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) ∈ X'.B.embLL '' (X'.B.LL0 : Set X'.B.LL) :=
    ⟨_, (x' : ↥X'.toD7.LL0).2, rfl⟩
  rw [h.2.2.1] at hx
  obtain ⟨y, hy, hye⟩ := hx
  have hint' : IsIntegral ℤ (X.B.embLL y) := by
    rw [hye]
    exact (RingOfIntegers.isIntegral_coe x').map
      ((X'.toD7.what₂.embLL.comp (algebraMap ↥X'.toD7.LL0 X'.toD7.what₂.LL)).toIntAlgHom)
  have hint : IsIntegral ℤ (⟨y, hy⟩ : ↥X.toD7.LL0) := by
    refine (isIntegral_algHom_iff ((X.toD7.what₂.embLL.comp (algebraMap ↥X.toD7.LL0 X.toD7.what₂.LL)).toIntAlgHom) ?_).1 (by exact hint')
    exact X.toD7.what₂.embLL.injective.comp (algebraMap ↥X.toD7.LL0 X.toD7.what₂.LL).injective
  let x : 𝓞 ↥X.toD7.LL0 := ⟨⟨y, hy⟩, hint⟩
  have e : X.toD7.what₂.embLL ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL) =
      X'.toD7.what₂.embLL ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) := hye

  obtain ⟨h1, h2⟩ := hc.emb i i' hi x x' e
  have hside : HEq (sideEmb i b (x : ↥X.toD7.LL0)) (sideEmb i' b (x' : ↥X'.toD7.LL0)) := by
    cases b
    · simpa [sideEmb] using h2
    · simpa [sideEmb] using h1
  have hleft := ((same_basic hc.exp.gal hc.exp.set hc.exp.frm).2.2.2.2 i i' hi).2.2 _ _ hside

  have hmap : RingOfIntegers.mapRingHom (incl h) (algebraMap (𝓞 ↥X.toD7.LL0) (𝓞 X.toD7.what₂.LL) x) =
      algebraMap (𝓞 ↥X'.toD7.LL0) (𝓞 X'.toD7.what₂.LL) x' := by
    apply RingOfIntegers.ext
    apply X'.B.embLL.injective
    exact (embLL_incl h ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL)).trans e
  have hright : 0 < X.toD7.what₂.places.val (plUnder h v') ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL) ↔
      0 < X'.toD7.what₂.places.val v' ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) := by
    refine (TwistChoice.val_pos_iff_mem X.toD7 (plUnder h v') x).trans
      (Iff.trans ?_ (TwistChoice.val_pos_iff_mem X'.toD7 v' x').symm)
    have hm := mem_plUnder h v' (algebraMap (𝓞 ↥X.toD7.LL0) (𝓞 X.toD7.what₂.LL) x)
    rw [hmap] at hm
    exact hm
  exact hleft.symm.trans ((hr x).trans hright)

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadOfPolarizedFiber
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolNearAmple

theorem relAmple_near_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (t : SAB H (Sp R)), IsProper t.G.hom → ∀ (C : Type) [Field C] (g : R →+* C), GlobalTheory.LN.PolAt t (spMap g) → ∃ s : R, g s ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (h : R →+* R'), IsUnit (h s) → ∀ (t' : SAB H (Sp R')), SABMap t' t (spMap h) → RelAmple t'.G t'.PP.L := by
  intro E _ _ _ H R _ _ t hprop C _ g hpol
  have : Smooth t.G.hom := t.semi.smooth
  have : Flat t.G.hom := inferInstance
  have hL := t.PP.isLB
  let p : Ideal R := RingHom.ker g
  haveI : p.IsPrime := RingHom.ker_isPrime g
  let g₀ := algebraMap R p.ResidueField
  have hf₂ : p.primeCompl ≤ (IsUnit.submonoid C).comap g := fun x hx =>
    show IsUnit (g x) from isUnit_iff_ne_zero.2 fun h0 => hx (RingHom.mem_ker.2 h0)
  let i : p.ResidueField →+* C := Ideal.ResidueField.lift p g le_rfl hf₂
  have hcomp : i.comp g₀ = g := RingHom.ext fun r => Ideal.ResidueField.lift_algebraMap p g le_rfl hf₂ r
  have hsp : spMap i ≫ spMap g₀ = spMap g := by
    rw [← hcomp]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have h₂ : IsPullback (pullback.fst t.G.hom (spMap g)) (pullback.snd t.G.hom (spMap g)) t.G.hom
      (spMap i ≫ spMap g₀) := by
    rw [hsp]; exact IsPullback.of_hasPullback _ _
  have hA₁ : RelAmple ((Over.pullback (spMap g₀)).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom (spMap g₀))) :=
    FibreAmple.relAmple_of_fieldExtension (f := t.G.hom) hL i (IsPullback.of_hasPullback t.G.hom (spMap g₀)) h₂
      (pull_isLB hL _) (GlobalTheory.lbIso_refl (pull_isLB hL _)) hpol.2.1
  obtain ⟨s, hs, hAs⟩ := ProperFinite.relAmple_near_fibre t.G hL g₀ (FibreAmple.residueField_fraction p) hA₁
  refine ⟨s, fun h0 => hs (Ideal.algebraMap_residueField_eq_zero.2 (RingHom.mem_ker.2 h0)), ?_⟩
  intro R' _ h hu t' m
  let D : (Sp R).Opens := PrimeSpectrum.basicOpen s
  have : IsAffine D.toScheme := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) s
  have hrange : Set.range (spMap h) ⊆ Set.range D.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    show s ∉ Ideal.comap h y.asIdeal
    exact fun hy => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy hu)
  let u : Sp R' ⟶ D.toScheme := IsOpenImmersion.lift D.ι (spMap h) hrange
  have hu' : u ≫ D.ι = spMap h := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ, Hp⟩ := FibreAmple.exists_isPullback (IsPullback.of_hasPullback t.G.hom D.ι) m.cart.1 u hu'
  have e₀ : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := (isPullCubical_iff m.cm t.cub t'.cub).1 m.lin
    exact ⟨w, (isGen_iff w).2 hw⟩
  obtain ⟨w, hw⟩ : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom D.ι)).pull φ) :=
    LBIso.trans t'.PP.isLB (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) e₀
      (FibreAmple.lbIso_pull_comp hφ (GlobalTheory.lbIso_refl (pull_isLB hL _)))
  exact relAmple_pull (A := (Over.pullback D.ι).obj t.G) (A' := t'.G) Hp (pull_isLB hL _) t'.PP.isLB
    ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hAs

end GlobalTheory.PolNearAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersAutCommHostConjugationStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringOfIntegers_aut_comm_hostConjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E), τ (H.bar a) = H.bar (τ a) := by
  first | exact @GlobalTheory.ringOfIntegers_equiv_bar_comm | exact GlobalTheory.ringOfIntegers_equiv_bar_comm | (intros; apply GlobalTheory.ringOfIntegers_equiv_bar_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersEmbeddingFixedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_of_integers_embedding_fixed : PrN → AllSt fun _ _ _ _ _ _ x => Function.Injective (Dof x).what₂.OtoLL ∧ ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y := by
  first | exact @GlobalTheory.HeightCounting.Up.rows_O_integers | exact GlobalTheory.HeightCounting.Up.rows_O_integers | (intros; apply GlobalTheory.HeightCounting.Up.rows_O_integers <;> assumption)
end

