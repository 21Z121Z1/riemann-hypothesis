import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0199
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2846
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveIsAffineAndFiniteIntStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmeticCurve_isAffine_and_finite_int : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsArithVar q 0 → IsAffine Y ∧ Module.Finite ℤ Γ(Y, ⊤) := by
  first | exact @GlobalTheory.ArithCurve.isAffine_and_finite | exact GlobalTheory.ArithCurve.isAffine_and_finite | (intros; apply GlobalTheory.ArithCurve.isAffine_and_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BearsFlagUnitriangularIffMemCell
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.BearsCell

variable {ι : Type} {m : ι → ℕ}

theorem upM_map {K K' : Type} [Field K] [Field K'] (v : K → K') (h0 : v 0 = 0) (h1 : v 1 = 1) (u : Cell m → K) :
    (upM u).map v = upM fun j => v (u j) := by
  funext τ
  ext a b
  simp only [Mat.map, upM, upU, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp [h0, h1]

theorem det_upM {K : Type} [Field K] (u : Cell m → K) (τ : ι) : (upM u τ).det = 1 :=
  (GlobalTheory.FlagCell2.lowMul_upU_leadMinor_ne_zero K (m τ) _ 1 (fun _ _ h => Matrix.one_apply_ne h.ne) (by simp)).1

theorem exists_lu {K K' : Type} [Field K] [Field K'] {O : Subring K} (v : K → K') (ψ : O →+* K')
    (hv : ∀ x : O, v x = ψ x) (hu : ∀ x : O, ψ x ≠ 0 → (x : K) ≠ 0 ∧ (x : K)⁻¹ ∈ O) {g : Mat m K} (hg : Par 0 O g)
    {y₀ : Cell m → K'} (hP : Par m ⊤ (upM y₀ * (g.map v)⁻¹)) :
    ∃ (u : Cell m → K) (b : Mat m K), Par m O b ∧ g = b * upM u ∧ ∀ j, v (u j) = y₀ j := by
  have hgv := hg.map_of v ψ hv
  have hy : ∀ τ, (upM y₀ τ).det ≠ 0 := fun τ => (det_upM y₀ τ).trans_ne one_ne_zero
  have e : g.map v = (upM y₀ * (g.map v)⁻¹)⁻¹ * upM y₀ := by
    rw [Mat.mul_inv_rev, Mat.inv_inv hgv.det_ne, mul_assoc, Mat.inv_mul hy, mul_one]
  have hmin : ∀ τ (k : ℕ), ((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det ≠ 0 ∧
      (((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det)⁻¹ ∈ O := fun τ k => by
    let N : Matrix {a : Fin (m τ) // (a : ℕ) < k} {a : Fin (m τ) // (a : ℕ) < k} O := fun a b => ⟨_, (hg τ).1 a.1 b.1⟩
    have e1 : (N.det : K) = ((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det :=
      O.subtype.map_det N
    have e2 : ψ.mapMatrix N =
        (g.map v τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val := by
      ext a b
      exact (hv (N a b)).symm
    rw [← e1]
    refine hu _ ?_
    rw [ψ.map_det, e2, e]
    exact (GlobalTheory.FlagCell2.lowMul_upU_leadMinor_ne_zero K' (m τ) _ _ (fun i j h => (hP.inv τ).2.2.2 i j i.2 h) (hP.inv.det_ne τ)).2 k
  choose y b h1 h2 h3 h4 using fun τ => GlobalTheory.FlagLU.exists_lu_subring K O (m τ) (g τ) (hg τ).1 (hmin τ)
  have hgb : g = b * upM (fun j : Cell m => y j.1 j.2) := funext h4
  have hd : ∀ τ, (b τ).det = (g τ).det := fun τ => by
    rw [hgb, Pi.mul_apply, Matrix.det_mul, det_upM, mul_one]
  have hb : Par m O b := fun τ => ⟨h2 τ, hd τ ▸ (hg τ).2.1, hd τ ▸ (hg τ).2.2.1, fun i j _ h => h3 τ i j h⟩
  have hU : Par 0 O (upM fun j : Cell m => y j.1 j.2) := by
    have := (hb.inv.mono (k' := 0) (fun _ => Nat.zero_le _) le_rfl).mul hg
    rwa [hgb, ← mul_assoc, Mat.inv_mul hb.det_ne, one_mul] at this
  refine ⟨_, b, hb, hgb, fun j => ?_⟩
  have e3 : g.map v = Mat.map b v * upM fun j : Cell m => v (y j.1 j.2) := by
    rw [← upM_map v ((hv 0).trans (map_zero ψ)) ((hv 1).trans (map_one ψ)), ← Par.map_mul_of hb hU v ψ hv, ← hgb]
  have e4 : upM y₀ = (upM y₀ * (g.map v)⁻¹ * Mat.map b v) * upM fun j : Cell m => v (y j.1 j.2) := by
    rw [mul_assoc, ← e3, mul_assoc, Mat.inv_mul hgv.det_ne, mul_one]
  have hc := hP.mul (hb.map_of v ψ hv)
  exact (congrFun (GlobalTheory.FlagCell2.upU_unique_of_lower K' (m j.1) _ _ _ (fun i k h => (hc j.1).2.2.2 i k i.2 h) (congrFun e4 j.1)) j.2).symm

theorem bears_iff : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (K : Type) [Field K] (p : Sp K ⟶ Y.X), A ∈ E.S (f (p (IsLocalRing.closedPoint K))) → ∀ y₀ : Cell m → K, Bears E' φ A (upM y₀) p ↔ ∃ u : Cell m → Y.Fn, upM u * A.map φ ∈ E'.S (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  intro F _ X Y ι _ m E E' φ f hf A K _ p hA y₀
  have hd : ∀ σ, (A.map φ σ).det ≠ 0 := fun σ =>
    (Mat.det_map A (φ : X.Fn →+* Y.Fn) σ).trans_ne ((map_ne_zero _).2 (Fr.det_ne hA σ))
  have hr := GlobalTheory.ZH.RatModel.range_eq_singleton (M := ratOf Y) p (IsLocalRing.closedPoint K)
  constructor
  · rintro ⟨A', hA', hP⟩
    obtain ⟨u, b, hb, hg, hu⟩ := exists_lu ((ratOf Y).val p) (GlobalTheory.ZH.RatModel.valHom (M := ratOf Y) p _ hr)
      (fun _ => rfl) (fun x hx => (GlobalTheory.ZH.RatModel.isUnit_O_iff x).1
        ((GlobalTheory.ZH.RatModel.val_ne_zero_iff (M := ratOf Y) hr x).1 hx)) (hf.sub _ A' hA' A hA) hP
    refine ⟨u, (Fr.mem_iff hA').2 ?_, hu⟩
    have e : upM u * A.map φ * A'⁻¹ = b⁻¹ := by
      have e1 : upM u = b⁻¹ * (A' * (A.map φ)⁻¹) := by
        rw [hg, ← mul_assoc, Mat.inv_mul hb.det_ne, one_mul]
      rw [e1, mul_assoc b⁻¹, mul_assoc A', Mat.inv_mul hd, mul_one, mul_assoc, Mat.mul_inv (Fr.det_ne hA'), mul_one]
    rw [e]
    exact hb.inv
  · rintro ⟨u, hu, hy⟩
    refine ⟨_, hu, ?_⟩
    rw [mul_assoc, Mat.mul_inv hd, mul_one,
      upM_map ((ratOf Y).val p) (GlobalTheory.ZH.RatModel.val_zero (M := ratOf Y) p)
        (GlobalTheory.ZH.RatModel.val_one (M := ratOf Y) p), show (fun j => (ratOf Y).val p (u j)) = y₀ from funext hy,
      Mat.mul_inv fun τ => (det_upM y₀ τ).trans_ne one_ne_zero]
    exact Par.one

end GlobalTheory.FlagCell2.BearsCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleIsoOfWeilPairingEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem GlobalTheory.biIso_of_weil : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P P' : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → P'.IsLB → (∃ t : (P'.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A A) (fst A A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P'.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → LBIso P P' := by
  intro A _ _ g hA hs P P' hP hP1 hP2 hPs hP' hP'1 hP'2 hP's e La _ Q EF he hQ hker hW hW'
  obtain ⟨Λ, hd, hf, hk⟩ := GlobalTheory.T.complexFibreExponential_kernel_full_lattice (Sp ℂ) A g hA hs (𝟙 _) e he
  obtain ⟨L₀, u₀, hu₀⟩ := GlobalTheory.T.exists_holomorphic_uniformisation_of_exponential_lattice A g e Λ he hd hf hk
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hs P hP hP1 hP2 hPs
  obtain ⟨M', hM', hPM'⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hs P' hP' hP'1 hP'2 hP's
  obtain ⟨u, Hm, χ, hue, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  obtain ⟨u', Hm', χ', hue', hF'⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M' hM'
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hL' : (abelian₂ A M').IsLB := LB.isLB_linComb hM' _ _

  have key : ∀ (M : LB A.left) (P : LB (G2 A).left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ), M.IsLB → P.IsLB → u.ex = e → GlobalTheory.TorusRM.IsFactorAH u Hm χ →
      LBIso P (cubeLB A ![fst A A, snd A A] M) →
      (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
        Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) →
      ∀ a b : La, ((Q a) ⬝ᵥ ((2 : ℂ) • Hm).mulVec (star (Q b))).im = (EF a b : ℝ) := by
    intro M P u Hm χ hM hP hue hF hPM hW a b
    have hLM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
    obtain ⟨ud, χd, hude, hFd⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u Hm χ hM hF
    have mem : ∀ x : La, Q x ∈ ud.Λ := fun x => (ud.ker _).1 (by rw [hude, hue]; exact (hker _).2 ⟨x, rfl⟩)
    refine GlobalTheory.T.eq_of_forall_cexp_neg_two_pi_I_mul_div_eq _ _ fun k hk => ?_
    have h1 := hW k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have h2 := GlobalTheory.T.weilPairing_eq_exp_riemannForm_appellHumbert_frame A hA _ (pull_isLB hLM _) g ud _ χd hFd k (Q a) (Q b)
      (Units.mk0 _ (Complex.exp_ne_zero _)) hk (mem a) (mem b) rfl
    rw [hude, hue] at h2
    have hiso : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left)
        (((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).pull (𝟙 A : A ⟶ A).left) := by
      refine LBIso.trans (pull_isLB hP _) (pull_isLB hLM _) (pull_isLB (pull_isLB hLM _) _)
        (GlobalTheory.RigidBundleGlue.LBIso.pull hPM _) ?_
      exact GlobalTheory.ThetaAffineGlue.lbIso_pull_id (pull_isLB hLM _)
    have h3 := GlobalTheory.PeriodObject.weilIs_of_lbIso GlobalTheory.globalFns_holds hA (pull_isLB hP _)
      (pull_isLB hLM _) hiso h2
    have := GlobalTheory.weilIs_unique_fieldPoint (Sp ℂ) A _ (pull_isLB hP _) ℂ (𝟙 _) k _ _ _ _ h1 h3
    have := congrArg Units.val this
    simpa using this.symm
  have hH : Hm = Hm' := by
    have e2 := GlobalTheory.T.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span' g ((2 : ℂ) • Hm) ((2 : ℂ) • Hm') (Set.range Q) ?_ ?_
    · have := congrArg (fun X => (1 / 2 : ℂ) • X) e2
      simpa [smul_smul] using this
    · have hR : Set.range Q = (Λ : Set (Fin g → ℂ)) := by
        ext z
        rw [SetLike.mem_coe, ← hk, hker]
        rfl
      rw [hR]; exact hf
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [key M P u Hm χ hM hP (hue.trans hu₀) hF hPM hW a b,
        key M' P' u' Hm' χ' hM' hP' (hue'.trans hu₀) hF' hPM' hW' a b]
  subst hH
  have hlam := GlobalTheory.T.mumfordBundleIso_of_same_appellHumbert_form g A hA hp M M' u u' Hm χ χ' hM hM' (hue'.trans hue.symm) hF hF'
  exact LBIso.trans hP hL hP' hPM (LBIso.trans hL hL' hP' hlam (LBIso.symm hPM'))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleKernelKilledOfComplexPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BiKill

open GlobalTheory.CechPic

theorem lam_lam_diag {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB)
    (hΘ : ∃ t : LB.Gen (Theta A M), t.IsGen) (a b : T ⟶ A) :
    lam (lam (cls M hM) (𝟙 A) (𝟙 A)) a b = 2 • lam (cls M hM) a b := by
  have e : ∀ h : T ⟶ A, pull h.left (lam (cls M hM) (𝟙 A) (𝟙 A)) = lam (cls M hM) h h := fun h =>
    by rw [pull_lam, Category.comp_id]
  have hr : ∀ x y z : T ⟶ A, lam (cls M hM) x (y * z) = lam (cls M hM) x y + lam (cls M hM) x z := by
    intro x y z
    rw [lam_comm, lam_mul_left hM hΘ, lam_comm _ y, lam_comm _ z]
  change pull (a * b).left _ - pull a.left _ - pull b.left _ + pull (1 : T ⟶ A).left _ = _
  rw [e, e, e, e, lam_mul_left hM hΘ, hr, hr, lam_one_left, lam_comm _ b a, two_smul]
  abel

theorem kernel_pow_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) → x ^ n = 1) → ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ n = 1 := by
  intro A _ _ g hA hg P hP h1 h2 hsw hamp n hn T x hx
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hg P hP h1 h2 hsw
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ A hA M hM
  have hcube : (cubeLB A ![fst A A, snd A A] M).IsLB := LB.isLB_linComb hM _ _
  have hcP : cls P hP = lam (cls M hM) (fst A A) (snd A A) :=
    ((cls_eq_iff hP hcube).2 hPM).trans (cls_cube_two hM _ _ hcube)
  have hpullP : ∀ {Y : Over (Sp ℂ)} (a b : Y ⟶ A) (h : (P.pull (lift a b).left).IsLB),
      cls _ h = lam (cls M hM) a b := by
    intro Y a b h
    rw [cls_pull hP, hcP, pull_lam, lift_fst, lift_snd]
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hcL : cls _ hL = lam (cls M hM) (𝟙 A) (𝟙 A) := hpullP _ _ hL
  obtain ⟨L₀, ⟨u₀⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨u, Hm, χ, -, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ _ hL
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hamp g u Hm χ hF.1 hF.2.1 hF.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hF hpos
  obtain ⟨Q, ψ, ρ, N, hN, hψ, hρ, e₁, e₂, e₃⟩ :=
    GlobalTheory.PosAHIsog.exists_isog_principal_lam g A hA _ u Hm χ hL hAH
  have hlamM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hlamL : (abelian₂ A (P.pull (lift (𝟙 A) (𝟙 A)).left)).IsLB := LB.isLB_linComb hL _ _
  have hker : ∀ {Y : Over (Sp ℂ)} (y : Y ⟶ A),
      (∃ t : (P.pull (lift (snd A Y ≫ y) (fst A Y)).left).Gen, t.IsGen) →
      GlobalTheory.RealMult.HasGen ((abelian₂ A M).pull (lift (fst A Y) (snd A Y ≫ y)).left) ∧
      GlobalTheory.RealMult.HasGen ((abelian₂ A (P.pull (lift (𝟙 A) (𝟙 A)).left)).pull (lift (fst A Y) (snd A Y ≫ y)).left) := by
    intro Y y ht
    have h0 : lam (cls M hM) (fst A Y) (snd A Y ≫ y) = 0 := by
      rw [lam_comm, ← hpullP _ _ (pull_isLB hP _)]
      exact (cls_eq_zero_iff _).2 ht
    refine ⟨(cls_eq_zero_iff (pull_isLB hlamM _)).1 ?_, (cls_eq_zero_iff (pull_isLB hlamL _)).1 ?_⟩
    · rw [GlobalTheory.RealMult.Elliptic.cls_pull_lam hM]
      exact h0
    · rw [GlobalTheory.RealMult.Elliptic.cls_pull_lam hL, hcL, lam_lam_diag hM hΘ, h0, smul_zero]
  have hk : x ^ (N * N) = 1 :=
    GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial A hA _ hL Q ψ ρ N hψ hρ e₁ e₂ e₃ T x (hker x hx).2
  have key := GlobalTheory.torsion_point_comp_eq_one A hA M ((𝟙 A) ^ n) (N * N) hM (Nat.mul_pos hN hN) (fun y hy => ?_)
    T x hk (hker x hx).1
  · rwa [MonObj.comp_pow, Category.comp_id] at key
  · rw [MonObj.comp_pow, Category.comp_id]
    refine hn y ((cls_eq_zero_iff (pull_isLB hP _)).1 ?_)
    rw [hpullP, lam_comm, ← GlobalTheory.RealMult.Elliptic.cls_pull_lam hM _ _ (pull_isLB hlamM _)]
    exact (cls_eq_zero_iff _).2 hy

end GlobalTheory.BiKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleExistsNonzeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triangle_exists_nonzero : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ v : ℂ, v ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (g : GA D WW) (pt : GA D P.a → GA D A),
          (∀ x, GlobalTheory.BotFormula.IsFinPt A (pt x) x) → ∀ T : Tup D P.a P.d P.n,
            X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
              v * ∑ᶠ x : GlobalTheory.NormSum.Cls D P.a (GlobalTheory.NormSum.intG D P.a),
                ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g (pt x.out) := by
  first | exact @GlobalTheory.BotFormula.theta_integral_classSum | exact GlobalTheory.BotFormula.theta_integral_classSum | (intros; apply GlobalTheory.BotFormula.theta_integral_classSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyLinearIndependentProductDegeneration
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdIndep

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep GlobalTheory.BoxFamIndep

theorem tensor_indep (F O₁ O₂ : Type) [Field F] [CommRing O₁] [Algebra F O₁] [CommRing O₂] [Algebra F O₂]
    {A₁ A₂ : Type} {m n : ℕ} (β₁ : A₁ → Fin m → O₁) (β₂ : A₂ → Fin n → O₂)
    (h₁ : ∀ c : Fin m → F, (∀ α, ∑ l, c l • β₁ α l = 0) → c = 0)
    (h₂ : ∀ c : Fin n → F, (∀ α, ∑ l, c l • β₂ α l = 0) → c = 0) (c : Fin m × Fin n → F)
    (hc : ∀ α₁ α₂, ∑ a, c a • (β₁ α₁ a.1 ⊗ₜ[F] β₂ α₂ a.2) = 0) : c = 0 := by
  have key : ∀ α₁ α₂, ∑ l : Fin m, β₁ α₁ l ⊗ₜ[F] (∑ a : Fin n, c (l, a) • β₂ α₂ a) = 0 := by
    intro α₁ α₂
    rw [← hc α₁ α₂, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun a _ => TensorProduct.tmul_smul _ _ _
  have key2 : ∀ l, (fun a : Fin n => c (l, a)) = 0 := fun l => h₂ _ fun α => by
    refine (Module.forall_dual_apply_eq_zero_iff F _).1 fun φ => ?_
    refine congrFun (h₁ (fun l => φ (∑ a : Fin n, c (l, a) • β₂ α a)) fun α₀ => ?_) l
    have := congrArg (fun t => TensorProduct.rid F O₁ (LinearMap.lTensor O₁ φ t)) (key α₀ α)
    simpa only [map_sum (LinearMap.lTensor O₁ φ), map_sum (TensorProduct.rid F O₁), LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul, map_zero] using this
  funext a
  exact congrFun (key2 a.1) a.2

theorem exists_test₂ {F : Type} [Field F] {X₁ X₂ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of F))
    (p₂ : X₂ ⟶ Spec (CommRingCat.of F)) (x₁ : X₁) (x₂ : X₂) {A₁ A₂ : Type} {U₁ : A₁ → X₁.Opens}
    {U₂ : A₂ → X₂.Opens} (hx₁ : ∀ α, x₁ ∈ U₁ α) (hx₂ : ∀ α, x₂ ∈ U₂ α) {m n : ℕ}
    (s₁ : ∀ α, Fin m → Γ(X₁, U₁ α)) (s₂ : ∀ α, Fin n → Γ(X₂, U₂ α))
    (hs₁ : ∀ c : Fin m → F, (∀ α, ∑ l, germOf p₁ x₁ (c l) * gs (𝟙 X₁) x₁ (U₁ α) (s₁ α l) = 0) → c = 0)
    (hs₂ : ∀ c : Fin n → F, (∀ α, ∑ l, germOf p₂ x₂ (c l) * gs (𝟙 X₂) x₂ (U₂ α) (s₂ α l) = 0) → c = 0) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r₁ : Z ⟶ X₁) (r₂ : Z ⟶ X₂), r₁ ≫ p₁ = q ∧ r₂ ≫ p₂ = q ∧
      (∀ z α, r₁ z ∈ U₁ α) ∧ (∀ z α, r₂ z ∈ U₂ α) ∧ ∀ c : Fin m × Fin n → F,
        (∀ α₁ α₂ z, ∑ a, germOf q z (c a) * (gs r₁ z (U₁ α₁) (s₁ α₁ a.1) * gs r₂ z (U₂ α₂) (s₂ α₂ a.2)) = 0) →
          c = 0 := by
  let : Algebra F (X₁.presheaf.stalk x₁) := (germOf p₁ x₁).toAlgebra
  let : Algebra F (X₂.presheaf.stalk x₂) := (germOf p₂ x₂).toAlgebra
  have h := tensor_indep F _ _ (fun α l => gs (𝟙 X₁) x₁ (U₁ α) (s₁ α l)) (fun α l => gs (𝟙 X₂) x₂ (U₂ α) (s₂ α l))
    (fun c hc => hs₁ c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this)
    (fun c hc => hs₂ c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this)
  obtain ⟨B, _, _, e₁, e₂, h⟩ : ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (e₁ : X₁.presheaf.stalk x₁ →ₐ[F] B)
      (e₂ : X₂.presheaf.stalk x₂ →ₐ[F] B), ∀ c : Fin m × Fin n → F, (∀ α₁ α₂, ∑ a, c a •
        (e₁ (gs (𝟙 X₁) x₁ (U₁ α₁) (s₁ α₁ a.1)) * e₂ (gs (𝟙 X₂) x₂ (U₂ α₂) (s₂ α₂ a.2))) = 0) → c = 0 :=
    ⟨TensorProduct F (X₁.presheaf.stalk x₁) (X₂.presheaf.stalk x₂), inferInstance, inferInstance,
      Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight, fun c hc => h c fun α₁ α₂ => by
        rw [← hc α₁ α₂]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]⟩
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    (Spec.map (CommRingCat.ofHom e₁.toRingHom) : _ ⟶ Spec (X₁.presheaf.stalk x₁)) ≫ X₁.fromSpecStalk x₁,
    (Spec.map (CommRingCat.ofHom e₂.toRingHom) : _ ⟶ Spec (X₂.presheaf.stalk x₂)) ≫ X₂.fromSpecStalk x₂,
    ?_, ?_, fun z α => fromSpecStalk_mem x₁ (hx₁ α) _, fun z α => fromSpecStalk_mem x₂ (hx₂ α) _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact e₁.commutes a
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact e₂.commutes a
  · refine h c fun α₁ α₂ => eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_
    rw [← hc α₁ α₂ z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_mul]
    refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ ?_)
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · rw [gs_fromSpecStalk x₁ (hx₁ _)]
      exact (germOf_map (B := X₁.presheaf.stalk x₁) (𝟙 _) (CommRingCat.ofHom e₁.toRingHom) z _).symm
    · rw [gs_fromSpecStalk x₂ (hx₂ _)]
      exact (germOf_map (B := X₂.presheaf.stalk x₂) (𝟙 _) (CommRingCat.ofHom e₂.toRingHom) z _).symm

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem exists_pt {D : DegPre R} {m : ℕ} (b : Fin m → Fam D F k) (hb : LinearIndependent F b) :
    ∃ (x : (DegPre.BF D F).left) (jj : D.X → Fin 4 → D.P.L.ι),
      (∀ α, x ∈ LB.wchart D.P.L (DegPre.famφ D F α) (jj α)) ∧ ∀ c : Fin m → F,
      (∀ α, ∑ l, germOf (B := CommRingCat.of F) (fst (TF (R := R) F) D.P.A).left x (c l) *
        gs (𝟙 _) x (LB.wchart D.P.L (DegPre.famφ D F α) (jj α)) (((b l).s α).f (jj α)) = 0) → c = 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.P.A.hom
  have hint : IsIntegral (DegPre.BF D F).left :=
    hg.geometrically_isIntegral (TF (R := R) F).hom _ _ (IsPullback.of_hasPullback (TF (R := R) F).hom D.P.A.hom).flip
  choose J₀ hJ₀ using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left =>
    exists_chart D.P.isLB (χ (genericPoint (DegPre.BF D F).left))
  have hx : ∀ α, genericPoint (DegPre.BF D F).left ∈
      LB.wchart D.P.L (DegPre.famφ D F α) (fun a => J₀ (DegPre.famφ D F α a)) :=
    fun α => Set.mem_iInter.2 fun a => hJ₀ _
  refine ⟨_, _, hx, fun c hc => funext <| Fintype.linearIndependent_iff.1 hb c <| fam_ext fun α jj => ?_⟩
  refine fn_ext fun y hy => congrArg _ ?_
  have hy' : genericPoint (DegPre.BF D F).left ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj :=
    ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
  apply germ_injective_of_isIntegral _ _ hy'
  refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
  refine (sec_trans _ (𝟙 _) _ hy' (hx α)).trans ?_
  refine (congrArg _ ((gs_comb c b α _ (𝟙 _) _ (hx α)).trans ?_)).trans (mul_zero _)
  rw [Category.id_comp]
  exact hc α

theorem exists_pair {D D₁ D₂ : DegPre R} (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) [IsIso (lift p₁ p₂)]
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of F)) (r₁ : Z ⟶ (DegPre.BF D₁ F).left)
    (r₂ : Z ⟶ (DegPre.BF D₂ F).left) (h₁ : r₁ ≫ (fst (TF (R := R) F) D₁.P.A).left = q)
    (h₂ : r₂ ≫ (fst (TF (R := R) F) D₂.P.A).left = q) :
    ∃ ρ : Z ⟶ (DegPre.BF D F).left, ρ ≫ (TF (R := R) F ◁ p₁).left = r₁ ∧ ρ ≫ (TF (R := R) F ◁ p₂).left = r₂ ∧
      ρ ≫ (fst (TF (R := R) F) D.P.A).left = q := by
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ (TF (R := R) F).hom)
  let q' : T ⟶ TF (R := R) F := Over.homMk q rfl
  let r₁' : T ⟶ DegPre.BF D₁ F := Over.homMk r₁ (by
    rw [← Over.w (fst (TF (R := R) F) D₁.P.A), ← Category.assoc, h₁]; rfl)
  let r₂' : T ⟶ DegPre.BF D₂ F := Over.homMk r₂ (by
    rw [← Over.w (fst (TF (R := R) F) D₂.P.A), ← Category.assoc, h₂]; rfl)
  let ρ : T ⟶ DegPre.BF D F := lift q' (SumDeg.pairPt p₁ p₂ (r₁' ≫ snd _ _) (r₂' ≫ snd _ _))
  have hρ₁ : ρ ≫ TF (R := R) F ◁ p₁ = r₁' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext h₁.symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact SumDeg.pairPt_fst _ _ _ _
  have hρ₂ : ρ ≫ TF (R := R) F ◁ p₂ = r₂' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext h₂.symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact SumDeg.pairPt_snd _ _ _ _
  exact ⟨ρ.left, congrArg (fun g => g.left) hρ₁, congrArg (fun g => g.left) hρ₂,
    congrArg (fun g => g.left) (lift_fst q' (SumDeg.pairPt p₁ p₂ (r₁' ≫ snd _ _) (r₂' ≫ snd _ _)))⟩

theorem boxFam₂_linearIndependent : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k m n : ℕ) (b₁ : Fin m → Fam D₁ F k) (b₂ : Fin n → Fam D₂ F k) (b : Fin m × Fin n → Fam D F k), LinearIndependent F b₁ → LinearIndependent F b₂ → (∀ a, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k (b a) (b₁ a.1) (b₂ a.2)) → LinearIndependent F b := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w F _ _ k m n b₁ b₂ b hb₁ hb₂ hb
  refine Fintype.linearIndependent_iff.2 fun c hc => congrFun (?_ : c = 0)
  have := hS.lim
  obtain ⟨x₁, j₁, hx₁, H₁⟩ := exists_pt b₁ hb₁
  obtain ⟨x₂, j₂, hx₂, H₂⟩ := exists_pt b₂ hb₂
  obtain ⟨Z, q, r₁, r₂, hq₁, hq₂, hr₁, hr₂, H⟩ := exists_test₂ (F := F) (fst (TF (R := R) F) D₁.P.A).left
    (fst (TF (R := R) F) D₂.P.A).left x₁ x₂ hx₁ hx₂ (fun α l => ((b₁ l).s α).f (j₁ α))
    (fun α l => ((b₂ l).s α).f (j₂ α)) H₁ H₂
  obtain ⟨ρ, hρ₁, hρ₂, hρq⟩ := exists_pair p₁ p₂ q r₁ r₂ hq₁ hq₂
  refine H c fun α₁ α₂ z => ?_
  obtain ⟨α, rfl, rfl⟩ : ∃ α, q₁ α = α₁ ∧ q₂ α = α₂ := by
    obtain ⟨α, h⟩ := hS.xsum.2 (α₁, α₂)
    exact ⟨α, congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.P.isLB z
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB z
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB z
  have hm := hJ.mem (DegPre.famφ D F α) ρ
  have E := (gs_comb c b α _ ρ z hm).symm.trans
    ((congrArg (fun s : Fam D F k => gs (Y := Z) ρ z _ ((s.s α).f _)) hc).trans (gs_zero _ _ _ hm))
  rw [hρq] at E
  have E' := fun a => hb a α Z ρ z J₁ J₂ J hJ₁ hJ₂ hJ
  rw [hρ₁, hρ₂] at E'
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a, u * sval (Z := Z) ((b a).s α) ρ z J =
      sval ((b₁ a.1).s (q₁ α)) r₁ z J₁ * sval ((b₂ a.2).s (q₂ α)) r₂ z J₂ := ⟨_, E'⟩
  obtain ⟨v₁, hv₁⟩ : ∃ v : Z.presheaf.stalk z, ∀ l,
      gs r₁ z (LB.wchart D₁.P.L (DegPre.famφ D₁ F (q₁ α)) (j₁ (q₁ α))) (((b₁ l).s (q₁ α)).f (j₁ (q₁ α))) =
      v * sval ((b₁ l).s (q₁ α)) r₁ z J₁ :=
    ⟨_, fun l => sec_trans _ r₁ z (hr₁ z _) (hJ₁.mem _ r₁)⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v : Z.presheaf.stalk z, ∀ l,
      gs r₂ z (LB.wchart D₂.P.L (DegPre.famφ D₂ F (q₂ α)) (j₂ (q₂ α))) (((b₂ l).s (q₂ α)).f (j₂ (q₂ α))) =
      v * sval ((b₂ l).s (q₂ α)) r₂ z J₂ :=
    ⟨_, fun l => sec_trans _ r₂ z (hr₂ z _) (hJ₂.mem _ r₂)⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ ((v₁ * v₂) * u)).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ (((congrArg₂ (· * ·) (hv₁ a.1) (hv₂ a.2)).trans (_root_.mul_mul_mul_comm _ _ _ _)).trans
    (congrArg _ (hu a).symm))) ?_
  exact (congrArg _ (_root_.mul_assoc _ _ _).symm).trans (mul_left_comm _ _ _)

end GlobalTheory.ProdIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionOfFrameCarriedAlongLiftsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carried_section_of_frame_carried_along_lifts : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X) (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)), φ ≫ f = f → (∀ f' : (pullback f (spMap ρ₁)) ⟶ (pullback f (spMap ρ₁)), f' ≫ (pullback.fst f (spMap ρ₁)) = (pullback.fst f (spMap ρ₁)) ≫ φ → f' ≫ (pullback.snd f (spMap ρ₁)) = (pullback.snd f (spMap ρ₁)) → FrameCarriedAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ φ w f') → ∀ l, SecCarriedOver L O (s l) φ w := by
  first | exact @GlobalTheory.Mum.secCarriedOver_of_frameCarriedAlong | exact GlobalTheory.Mum.secCarriedOver_of_frameCarriedAlong | (intros; apply GlobalTheory.Mum.secCarriedOver_of_frameCarriedAlong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeStatementStatement
section
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CovolumeStatement : CovolSt := by
  first | exact @GlobalTheory.DetHT.Covol.covol | exact GlobalTheory.DetHT.Covol.covol | (intros; apply GlobalTheory.DetHT.Covol.covol <;> assumption)
end

