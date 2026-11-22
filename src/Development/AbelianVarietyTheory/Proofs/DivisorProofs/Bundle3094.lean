import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3032
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3033
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2958
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2994
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataFactorPairingPullback
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensPair

theorem pair_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), (∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb D.toPre.P.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j)) → ∀ (i₀ : Fin r), letI := T.mod (symUnitOf W h); ∃ w : LB.Iso (abelian₂ D.toPre.P.A D.toPre.P.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good D.toPre.P.L z J' → val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b)).left z J J' * val (D'.toPre.tau (T.xi i₀ a) (TensO.binv (symUnitOf W h) • T.xi i₀ b)) (𝟙 _) z J := by
  intro R _ _ _ _ D D' r W h _ T hw i₀
  obtain ⟨w₁, hw₁, hv₁⟩ := hw
  have hsum : ∑ j, (W + W.transpose) i₀ j * TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ = 1 := by
    have hb : (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose :=
      IsUnit.unit_spec _
    have key := congrFun (congrFun (Units.mul_inv (symUnitOf W h).1) i₀) i₀
    rw [hb, Matrix.mul_apply, Matrix.one_apply_eq] at key
    exact key
  obtain ⟨u₀, hu₀, hv₀⟩ := GlobalTheory.T.exists_biextension_generator_bezout_combination D.toPre D.tau_bimult (fun j => (W + W.transpose) i₀ j)
    (fun j => TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀) hsum
  obtain ⟨u, hu, hvu⟩ := exists_gen D.toPre.P.isLB
    (φ' := Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun I : ULift (Finset (Fin 2)) => (psum D.toPre.P.A (x2 D.toPre.P.A) I.down).left))
    (ε' := Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun I : ULift (Finset (Fin 2)) => -((-1) ^ (2 - I.down.card))))
    (fun U _ hh => by
      clear hv₀ hv₁ hu₀ u₀ hw₁ w₁
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      refine congrArg (· * _) ?_
      simp only [Sum.elim_inl, GlobalTheory.TensPair.lamPts_pull, Fintype.prod_prod_type]
      symm
      rw [Finset.prod_eq_single i₀ ?_ (by simp)]
      · exact Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun l _ => by rw [if_pos rfl]
      · intro i _ hi
        refine Finset.prod_eq_one fun j _ => ?_
        rw [Fin.prod_univ_four, if_neg hi]
        simp only [GlobalTheory.PolDeg.lamPts, Oε, _root_.one_mul]
        simp [zpow_mul, zpow_neg]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        module)
    u₀ hu₀
  obtain ⟨w, hw, hvw⟩ := GlobalTheory.T.exists_iso_glued_from_linComb_pullback D.toPre.P.isLB (LB.isLB_linComb D'.toPre.P.isLB _ _) _ _ _ _ _ w₁ hw₁ u hu
  refine ⟨w, hw, fun a b z J J' hJ hJ' => ?_⟩

  suffices key : ∀ b' : D'.toPre.X, (∀ j, T.xe b' j = TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ • b) →
      val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J J' *
        val (D'.toPre.tau (T.xi i₀ a) b') (𝟙 _) z J by
    exact key _ (fun j => (Tens.xe_smul T (symUnitOf W h) (TensO.binv _) (T.xi i₀ b) j).trans (by
      rw [Finset.sum_eq_single i₀ (fun k _ hk => by rw [GlobalTheory.TensPair.xe_xi, if_neg hk, smul_zero]) (by simp),
        GlobalTheory.TensPair.xe_xi, if_pos rfl]))
  intro b' hb'
  have hPl : (lift (toUnit (TK R) ≫ D'.toPre.c (T.xi i₀ a)) (toUnit (TK R) ≫ D'.toPre.c b') : TK R ⟶ G2 D'.toPre.P.A).left =
      (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫
        (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left := by
    rw [GlobalTheory.TensPair.pt_pull T i₀ _ a b _ b' (GlobalTheory.TensPair.xe_xi T i₀ · a) hb']; rfl
  have t0 : ∀ x, val (D.toPre.tau 0 x) (𝟙 _) z J' = 1 := fun x => by
    have e := GlobalTheory.TauTwist.val_tau_nsmul (𝟙 (TK R)) hJ' D.tau_bimult 0 x x
    rw [zero_smul] at e
    simpa [cubN] using e
  have hPi : ∏ i, ∏ j, val (D.toPre.tau (T.xe (T.xi i₀ a) i) (T.xe b' j)) (𝟙 _) z J' ^ ((W + W.transpose) i j) =
      ∏ j, val (D.toPre.tau a (TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ • b)) (𝟙 _) z J' ^ ((W + W.transpose) i₀ j) := by
    rw [Finset.prod_eq_single i₀ (fun i _ hi => Finset.prod_eq_one fun j _ => by
      rw [GlobalTheory.TensPair.xe_xi, if_neg hi, t0, one_zpow]) (by simp)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [GlobalTheory.TensPair.xe_xi, if_pos rfl, hb']
  have e1 := hv₁ (T.xi i₀ a) b' z J' J hJ' hJ
  rw [hPi, hPl] at e1
  have e2 := hvw _ (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J' hJ'
    (fun I => J (((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫
        (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left) ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))
    (hJ.mem _ _)
  have e3 := hv₀ a b z J' hJ'
  have e4 := hvu _ (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J' hJ'
  clear hv₀ hvu hvw hv₁ hPi
  change val _ _ z J = gv w₁ _ z _ _ * _ at e1
  have hj : (fun I : ULift (Finset (Fin 2)) => J ((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left)) =
      (fun I => J (((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left) ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left)) :=
    funext fun I => by rw [Category.assoc]
  have e5 : GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J J' = gw w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z (fun I : ULift (Finset (Fin 2)) => J ((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))
      (fun I => J' ((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (psum D.toPre.P.A (x2 D.toPre.P.A) I.down).left)) := rfl
  rw [e5, hj, e2, e1, e3, e4]
  have key : ∀ {G : Type} [CommGroup G] (A P X : G), A * P = X⁻¹ * A * (X * P) := fun A P X => by
    rw [_root_.mul_comm X⁻¹ A, _root_.mul_assoc, inv_mul_cancel_left]
  exact key (G := ((TK R).left.presheaf.stalk z)ˣ) _ _ _

end GlobalTheory.TensPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataScalarsMemMaximalIdealTendstoZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_scalars_mem_maximalIdeal_tendsto_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X → X → (FractionRing R)ˣ), (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) → (∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b)) → (∀ y, y ≠ 0 → ∃ s ∈ maximalIdeal R, (k y y : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (a' : (Fin r → X) → (FractionRing R)ˣ), (∀ z, ∃ u ∈ unitsK R, a' z = u * ∏ i, ∏ j, k (z i) (z j) ^ W i j) → (∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (a' z : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {z | ¬ ∃ s ∈ maximalIdeal R ^ n, (a' z : FractionRing R) = algebraMap R _ s}.Finite := by
  first | exact @GlobalTheory.Mum.TensPolScal.scalars_tens | exact GlobalTheory.Mum.TensPolScal.scalars_tens | (intros; apply GlobalTheory.Mum.TensPolScal.scalars_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSectionsZerosMultiplicitiesNorms
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

theorem nonzeroLocus_prodSec {X : Scheme.{0}} {A B : LB X} (s : A.Sec) (t : B.Sec) :
    nonzeroLocus (EffBound.tensSec s t) = nonzeroLocus s ⊓ nonzeroLocus t := by
  have e (c : A.ι × B.ι) : X.basicOpen ((EffBound.tensSec s t).f c) =
      (A.U c.1 ⊓ B.U c.2) ⊓ X.basicOpen (s.f c.1) ⊓ ((A.U c.1 ⊓ B.U c.2) ⊓ X.basicOpen (t.f c.2)) :=
    (X.basicOpen_mul _ _).trans (congrArg₂ (· ⊓ ·) (X.basicOpen_res _ _) (X.basicOpen_res _ _))
  refine le_antisymm (iSup_le fun c => (e c).le.trans (inf_le_inf
    (inf_le_right.trans (le_iSup (fun i => X.basicOpen (s.f i)) c.1))
    (inf_le_right.trans (le_iSup (fun i => X.basicOpen (t.f i)) c.2)))) fun x hx => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx.1
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hx.2
  have h : x ∈ A.U i ⊓ B.U j := ⟨X.basicOpen_le _ hi, X.basicOpen_le _ hj⟩
  exact Opens.mem_iSup.2 ⟨(i, j), (e (i, j)).ge ⟨⟨h, hi⟩, h, hj⟩⟩

theorem secVal_prodSec {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (σ : k →+* ℂ) {A B : LB X}
    (s : A.Sec) (t : B.Sec) :
    secVal p σ (EffBound.tensSec s t) = secTens (secVal p σ s) (secVal p σ t) := by
  funext c y
  by_cases h : y ∈ ptsIn p σ (A.U c.1 ⊓ B.U c.2)
  · exact (ev_mul _ _ y).trans (congrArg₂ (· * ·) (ev_res inf_le_left h _) (ev_res inf_le_right h _))
  · exact (ev_of_notMem h _).trans ((secTens_mem (secVal_mem s) (secVal_mem t)).2 c y h).symm

theorem mult_prodSec {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {A B : LB X} (hA : A.IsLB)
    (hB : B.IsLB) (hAB : (tens A B).IsLB) (s : A.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : B.Sec)
    (ht : genericPoint X ∈ nonzeroLocus t) (h : genericPoint X ∈ nonzeroLocus (EffBound.tensSec s t)) (z : X) :
    (divOfSec hAB _ h).mult z = (divOfSec hA s hs).mult z + (divOfSec hB t ht).mult z := by
  obtain ⟨i, hi⟩ := Geo.Tor.exists_chart hA z
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hB z
  have hij : z ∈ (tens A B).U (i, j) := ⟨hi, hj⟩
  rw [((presents_divOfRatSec hAB _).isEqn (i, j) z hij).mult_eq,
    ((presents_divOfRatSec hA _).isEqn i z hi).mult_eq, ((presents_divOfRatSec hB _).isEqn j z hj).mult_eq,
    val_ratOfSec (gen_mem hij), val_ratOfSec (gen_mem hi), val_ratOfSec (gen_mem hj),
    ← Scheme.ord_mul (fnOf_sec_ne_zero hs (gen_mem hi)) (fnOf_sec_ne_zero ht (gen_mem hj))]
  exact congrArg (Scheme.ord · z) ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (fnOf_resG inf_le_left _ _) (fnOf_resG inf_le_right _ _)))

theorem exists_sec_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (M A : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a), ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ (∀ z, (divOfSec (M.tens A).φ.isLB s₁ h₁).mult z = (divOfSec M.φ.isLB s hs).mult z + (divOfSec A.φ.isLB a ha).mult z) ∧ ∀ y ∈ ptsIn p σ (nonzeroLocus s₁), (M.tens A).logSec s₁ y = M.logSec s y + A.logSec a y := by
  intro k _ X _ _ p σ M A s hs a ha
  have e := nonzeroLocus_prodSec s a
  refine ⟨EffBound.tensSec s a, e.ge ⟨hs, ha⟩, e, mult_prodSec _ _ _ s hs a ha _, fun y hy => ?_⟩
  have hy' : y ∈ ptsIn p σ (nonzeroLocus s ⊓ nonzeroLocus a) := ptsIn_mono e.le hy
  have h0 (N : MLine p σ) (u : N.B.Sec) (hu : y ∈ ptsIn p σ (nonzeroLocus u)) : N.φ.nsq (secVal p σ u) y ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 ((secVal_ne_zero_iff u (mem_pick _ y)).2 hu)))
      (Real.exp_ne_zero _)
  have h : (M.φ.tens A.φ).nsq (secVal p σ (EffBound.tensSec s a)) y =
      M.φ.nsq (secVal p σ s) y * A.φ.nsq (secVal p σ a) y := by
    rw [secVal_prodSec]
    exact Weight.nsq_tens _ _ (secVal_mem s) (secVal_mem a) y
  refine (congrArg (Real.log · / 2) h).trans ?_
  rw [Real.log_mul (h0 M s (mem_ptsIn_inf.1 hy').1) (h0 A a (mem_ptsIn_inf.1 hy').2), add_div]
  rfl

end GlobalTheory.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionAddComponentwise
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

theorem GlobalTheory.Mum.TensTor.qkAdd_of_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (p' q' s' : QkPt D'.toPre F k) (ps qs ss : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs → PtRel T ν ν' s' ss → (∀ i, QkAdd (ps i) (qs i) (ss i)) → QkAdd p' q' s' := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' k p' q' s' ps qs ss hp hq hs hadd
  have gt : GlobalTheory.Ex.BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  obtain ⟨-, -, gAdd, -, gQ⟩ := gt R D.toPre D.psi_even D.tau_bimult F N ν
  obtain ⟨-, -, gAdd', -, gQ'⟩ := gt R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  have hF := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  obtain ⟨-, -, he, hebij, -, -, -, -⟩ := hF
  obtain ⟨P', Ps, hP', hPs, hPy, hPg⟩ := hp
  obtain ⟨Q', Qs, hQ', hQs, hQy, hQg⟩ := hq
  obtain ⟨S', Ss, hS', hSs, hSy, hSg⟩ := hs
  have hz : ∀ i, N.QEq (Ps i * Qs i) (Ss i) := by
    intro i
    obtain ⟨x, hxy, hxg, hxe⟩ := hadd i
    obtain ⟨X, hX⟩ := ((gQ k).1 x).exists
    have hXeq : X = Ps i * Qs i := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · apply Multiplicative.toAdd.injective
        apply ν.eX.injective
        rw [hX.1, hxy, ← (hPs i).1, ← (hQs i).1, ← map_add]
        rfl
      · exact (gAdd _ _ _ _ _ _ (hPs i).2 (hQs i).2 hX.2).1 hxg
    rw [← hXeq]
    exact ((gQ k).2.2 x (ss i) X (Ss i) hX (hSs i)).1 hxe
  choose z hz1 hz2 using hz
  obtain ⟨z', hz'⟩ := hebij.2 z
  have he0 : ∀ i, chi T ν ν' 0 i = 0 := fun i => by
    have := he 0 0 i
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have hensmul : ∀ (n : ℕ) χ i, chi T ν ν' (n • χ) i = n • chi T ν ν' χ i := by
    intro n χ i
    induction n with
    | zero => rw [zero_smul, zero_smul, he0]
    | succ n ih => rw [succ_nsmul, he, ih, succ_nsmul]
  obtain ⟨x', hx'⟩ := (gQ' k).2.1 (P' * Q')
  refine ⟨x', ?_, ?_, ?_⟩
  · rw [← hx'.1, ← hP'.1, ← hQ'.1, ← map_add]
    rfl
  · exact (gAdd' _ _ _ _ _ _ hP'.2 hQ'.2 hx'.2).2 rfl
  · refine ((gQ' k).2.2 x' s' (P' * Q') S' hx' hS').2 ⟨z', ?_, ?_⟩
    · apply hebij.1
      funext i
      have e1 : (P' * Q').1.1.toAdd = P'.1.1.toAdd + Q'.1.1.toAdd := rfl
      have e2 : (Ps i * Qs i).1.1.toAdd = (Ps i).1.1.toAdd + (Qs i).1.1.toAdd := rfl
      rw [hSy i, hz1 i, he, hensmul, hz', e1, he, hPy i, hQy i, e2]
    · have m1 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν')
        P'.1.2 Q'.1.2 _ _ hPg hQg
      have m2 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν') z'
      have m3 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν')
        _ _ _ _ m1 m2
      have e3 : ((fun j => (Ps j).1.2) * (fun j => (Qs j).1.2)) * (fun j => N.io (chi T ν ν' z' j)) =
          fun j => (Ss j).1.2 := by
        funext j
        rw [hz2 j, hz']
        rfl
      rw [e3] at m3
      exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν')
        _ _ _ hSg m3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPointEquivIffComponentsEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem comp_nsmul {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {e : N'.X → Fin r → N.X}
    (he : ∀ χ χ' i, e (χ + χ') i = e χ i + e χ' i) (k : ℕ) (z : N'.X) (i : Fin r) : e (k • z) i = k • e z i := by
  induction k with
  | zero =>
    have h := he 0 0 i
    rw [add_zero] at h
    simpa using h
  | succ k ih => rw [succ_nsmul, he, ih, succ_nsmul]

theorem qEq_iff_of_rel {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (hT : TensFacts W φ e wv)
    (hW : IsUnit (W + W.transpose).det) {k : ℕ} {a' b' : N'.QT k} {as bs : Fin r → N.QT k}
    (ha : QRelV W φ e wv a' as) (hb : QRelV W φ e wv b' bs) : N'.QEq a' b' ↔ ∀ i, N.QEq (as i) (bs i) := by
  have hadd := hT.2.2.1
  have he := hT.2.2.2.1
  constructor
  · rintro ⟨z, hy, hg⟩ i
    refine ⟨e z i, ?_, ?_⟩
    · rw [← hb.1 i, hy, hadd, comp_nsmul hadd, ha.1 i]
    · have h1 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hT _ _ _ _ ha.2 (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hT z)
      rw [← hg] at h1
      have h2 := congrFun (GlobalTheory.T.tensorTorusValueCorrespondence_unique_components F N N' W φ e wv hT hW _ _ _ hb.2 h1) i
      simpa using h2
  · intro h
    choose z hz using h
    obtain ⟨z', hz'⟩ := he.2 z
    refine ⟨z', ?_, ?_⟩
    · apply he.1
      funext i
      rw [hadd, comp_nsmul hadd, hz', ha.1 i, hb.1 i]
      exact (hz i).1
    · have h1 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hT _ _ _ _ ha.2 (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hT z')
      have h2 : ((fun j => (as j).1.2) * fun j => N.io (e z' j)) = fun j => (bs j).1.2 :=
        funext fun j => by rw [Pi.mul_apply, hz']; exact ((hz j).2).symm
      rw [h2] at h1
      exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W φ e wv hT _ _ _ hb.2 h1

theorem qkPt_equiv_iff_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N)
    (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' q' : QkPt D'.toPre F k)
    (ps qs : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs →
    (QkPt.Equiv D'.toPre F p' q' ↔ ∀ i, QkPt.Equiv D.toPre F (ps i) (qs i)) := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' hW k p' q' ps qs hp hq
  obtain ⟨a', as, ha', has, ha⟩ := hp
  obtain ⟨b', bs, hb', hbs, hb⟩ := hq
  have hT := GlobalTheory.T.tensorData_values_facts R hB D D' W T F N N' ν ν'
  have G := GlobalTheory.Ex.GtValues.points_correspond
  rw [((G R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 k).2.2 p' q' a' b' ha' hb', qEq_iff_of_rel hT hW ha hb]
  exact forall_congr' fun i =>
    (((G R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 k).2.2 _ _ _ _ (has i) (hbs i)).symm

end GlobalTheory.Mum.TensTor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionTowerNsmulComponentwise
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTower

section Values
variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ} {φ : N'.A → Fin r → N.A}
  {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem comp_nsmul (h : TensFacts W φ e wv) (k : ℕ) (χ : N'.X) (i : Fin r) : e (k • χ) i = k • e χ i :=
  (AddMonoidHom.mk' (fun χ => e χ i) fun a b => h.2.2.1 a b i).map_nsmul k χ

theorem rel_pow (h : TensFacts W φ e wv) {v' : N'.Gt} {vs : Fin r → N.Gt} (hv : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv h 0
    have e0 : ∀ j, e 0 j = 0 := fun j => by simpa using comp_nsmul h 0 0 j
    simp only [e0, NumD.io_zero] at h0
    rw [pow_zero, pow_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv h _ _ _ _ ih hv

theorem tower_val (h : TensFacts W φ e wv) {n m : ℕ} {p' : N'.QT (n * m)} {ps : Fin r → N.QT (n * m)} {t' : N'.QT n}
    {ts : Fin r → N.QT n} (hp : QRelV W φ e wv p' ps) (ht : QRelV W φ e wv t' ts)
    (hz : ∀ i, ∃ z : N.X, (ts i).1.1.toAdd = (ps i).1.1.toAdd + n • z ∧ (ts i).1.2 = (ps i).1.2 ^ m * N.io z) :
    ∃ z' : N'.X, t'.1.1.toAdd = p'.1.1.toAdd + n • z' ∧ t'.1.2 = p'.1.2 ^ m * N'.io z' := by
  choose z hz1 hz2 using hz
  obtain ⟨z', rfl⟩ := h.2.2.2.1.2 z
  refine ⟨z', h.2.2.2.1.1 (funext fun i => ?_), ?_⟩
  · rw [h.2.2.1, comp_nsmul h, ht.1, hp.1, hz1]
  · refine GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W φ e wv h _ _ _ ht.2 ?_
    have := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv h _ _ _ _ (rel_pow h hp.2 m) (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv h z')
    have e1 : (fun j => (ts j).1.2) = (fun j => (ps j).1.2) ^ m * fun j => N.io (e z' j) := funext hz2
    rw [e1]
    exact this

end Values

theorem tower : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (n m : ℕ), 0 < n → 0 < m → ∀ (p' : QkPt D'.toPre F (n * m)) (ps : Fin r → QkPt D.toPre F (n * m)) (t' : QkPt D'.toPre F n) (ts : Fin r → QkPt D.toPre F n), PtRel T ν ν' p' ps → PtRel T ν ν' t' ts → (∀ i, ∃ q : QkPt D.toPre F n, q.y = (ps i).y ∧ GtPtF.IsNsmul m (ps i).g q.g ∧ QkPt.Equiv D.toPre F q (ts i)) → ∃ q' : QkPt D'.toPre F n, q'.y = p'.y ∧ GtPtF.IsNsmul m p'.g q'.g ∧ QkPt.Equiv D'.toPre F q' t' := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' n m _ _ p' ps t' ts ⟨a', as, ha', has, ha⟩ ⟨b', bs, hb', hbs, hb⟩ H
  have hF := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  have B := (GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 n
  have B' := (GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 n
  obtain ⟨z', hz1, hz2⟩ := tower_val hF ha hb fun i => by
    obtain ⟨q, hy, hn, he⟩ := H i
    obtain ⟨c, hc⟩ := (B.1 q).exists
    obtain ⟨z, h1, h2⟩ := (B.2.2 q (ts i) c (bs i) hc (hbs i)).1 he
    refine ⟨z, ?_, ?_⟩
    · rw [h1, ν.eX.injective (hc.1.trans (hy.trans (has i).1.symm))]
    · rw [h2, (GtValues.isNsmul_val ν m (has i).2 hc.2).1 hn]
  let c' : N'.QT n := ⟨(a'.1.1, a'.1.2 ^ m), by
    rw [NumD.mem_QT, ← pow_mul, mul_comm m n]
    exact a'.2⟩
  obtain ⟨q', hq'⟩ := B'.2.1 c'
  exact ⟨q', hq'.1.symm.trans ha'.1, (GtValues.isNsmul_val ν' m ha'.2 hq'.2).2 rfl,
    (B'.2.2 q' t' c' b' hq' hb').2 ⟨z', hz1, hz2⟩⟩

end GlobalTheory.Mum.TensTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListRealisedSystemUpToRootsOfUnityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A)) (c : Fin N → K), ThList ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (spMap i ≫ 𝟙 (Sp S.R)) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) pt c → (∀ x, ∃ b, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  first | exact @GlobalTheory.UMin.thList_real | exact GlobalTheory.UMin.thList_real | (intros; apply GlobalTheory.UMin.thList_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListsUniqueUpToPermScalarStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstantLists_unique_up_to_perm_scalar : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m m' N N' : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S), Odd m → (m : K) ≠ 0 → Odd m' → (m' : K) ≠ 0 → PolFib G L g x → (∀ (θ : SecAt G L x) (pt pt' : Fin N → (Over.mk x ⟶ G)) (c d : Fin N → K), ThList G L ρ m x θ pt c → ThList G L ρ m x θ pt' d → ∃ σ : Equiv.Perm (Fin N), ∀ b, d b = c (σ b)) ∧ ∀ (c d : Fin N → K) (c' d' : Fin N' → K), HasTh₂ G L ρ m m' x c c' → HasTh₂ G L ρ m m' x d d' → ∃ (a : K) (σ : Equiv.Perm (Fin N)) (σ' : Equiv.Perm (Fin N')), a ≠ 0 ∧ (∀ b, d b = a * c (σ b)) ∧ ∀ b, d' b = a * c' (σ' b) := by
  first | exact @GlobalTheory.UMin.ThUniq.theta_lists_unique | exact GlobalTheory.UMin.ThUniq.theta_lists_unique | (intros; apply GlobalTheory.UMin.ThUniq.theta_lists_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFunctionsFiniteFlatCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem thList_cover : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (c : Fin N → R₁), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ ∀ (K : Type) [Field K] (i : R →+* K) (i₁ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i → ∃ pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun a => i₁ (c a)) := by
  intro S G _ _ L ρ hL hρ g m N R _ _ x θ hm hu hN hP
  obtain ⟨R₁, _, _, q, hfin, hff, hq, hpts⟩ := GlobalTheory.T.exists_finite_flat_cover_m_sq_torsion_sections S G L g m N R x hm hu hN hP
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R R₁
  have hcomp : ∀ {K : Type} [Field K] (i₁ : R₁ →+* K),
      spMap i₁ ≫ spMap (algebraMap R R₁) = spMap (i₁.comp (algebraMap R R₁)) := by
    intro K _ i₁; simp [spMap]
  let pt₀ : ∀ {K : Type} [Field K] (i₁ : R₁ →+* K) (a : Fin N), Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G :=
    fun i₁ a => Over.homMk (spMap i₁ ≫ (q a).left) (by
      have h := Over.w (q a)
      simp only [Over.mk_hom] at h ⊢
      rw [Category.assoc, h, ← Category.assoc, hcomp])
  have key : ∀ a : Fin N, ∃ c : R₁, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K)
      (pt : Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap i₁ ≫ (q a).left →
        ThG G L ρ m (SecAt.pull G L θ (i₁.comp (algebraMap R R₁))) pt (fn (i₁ c)) := by
    intro a
    refine GlobalTheory.T.exists_ring_element_of_local_field_point_values R₁ (fun K _ i₁ v => ∀ (pt : Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G),
        pt.left = spMap i₁ ≫ (q a).left →
        ThG G L ρ m (SecAt.pull G L θ (i₁.comp (algebraMap R R₁))) pt (fn v)) ?_ ?_
    · intro K _ i₁ u v hu' hv'
      exact GlobalTheory.T.thetaConstant_unique_field_point_polarisedFibre S G L ρ hL hρ g m R x K (i₁.comp (algebraMap R R₁)) hm hu hP _ (pt₀ i₁ a) u v
        (hu' _ rfl) (hv' _ rfl)
    · intro p hp
      obtain ⟨f, hf, c, hc⟩ := GlobalTheory.T.exists_local_thetaConstants_localisation S G L ρ hL hρ g m R x θ R₁ N q hm hu hP hq p hp
      exact ⟨f, hf, c a, fun K _ j pt hpt => hc K j a pt hpt⟩
  choose c hc using key
  refine ⟨R₁, inferInstance, inferInstance, c, hfin, hff, fun K _ i i₁ hi => ?_⟩
  subst hi
  obtain ⟨hinj, hcov⟩ := hpts K i₁ (pt₀ i₁) (fun a => rfl)
  exact ⟨pt₀ i₁, hinj, fun a => hc a K i₁ _ rfl, hcov⟩

end GlobalTheory.UMin
end

