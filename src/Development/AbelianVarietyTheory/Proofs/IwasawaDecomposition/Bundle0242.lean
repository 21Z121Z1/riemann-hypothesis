import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeSum.GrowthAtPlace

open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace

variable {n : ℕ} {ε : Fin n → Bool} {P G : Mx n}

theorem norm_entry_le (A : Mx n) (i j : Fin n) : ‖A i j‖ ≤ 1 + hs A := by
  have h : ‖A i j‖ ^ 2 ≤ hs A :=
    (Finset.single_le_sum (f := fun b => ‖A i b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, ‖A a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))
  nlinarith [norm_nonneg (A i j)]

theorem one_add_hs_conj_le (Q y P : Mx n) : 1 + hs (Q * y * P) ≤ (1 + hs Q) * (1 + hs P) * (1 + hs y) := by
  have h1 := one_add_hs_mul_le (Q * y) P
  have h2 := mul_le_mul_of_nonneg_right (one_add_hs_mul_le Q y) (show 0 ≤ 1 + hs P by linarith [hs_nonneg P])
  nlinarith

theorem conj_mul (hP : IsUnit P) (a b : Mx n) : P⁻¹ * (a * b) * P = (P⁻¹ * a * P) * (P⁻¹ * b * P) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  calc P⁻¹ * (a * b) * P = P⁻¹ * a * (P * P⁻¹) * b * P := by
        rw [Matrix.mul_nonsing_inv _ hd]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem conj_exp (hP : IsUnit P) (X : Mx n) (t : ℝ) :
    P⁻¹ * NormedSpace.exp (t • X) * P = NormedSpace.exp (t • (P⁻¹ * X * P)) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  rw [Matrix.mul_assoc, exp_mul_eq hP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

theorem conj_lie (hP : IsUnit P) (h : Pᴴ * Jm ε * P = G) {X : Mx n} (hX : X ∈ lieSet ε) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * Xᴴ * (P * P⁻¹)ᴴ * Jm ε * P + Pᴴ * Jm ε * (P * P⁻¹) * X * P := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * (Xᴴ * Jm ε + Jm ε * X) * P := by
        rw [Matrix.mul_nonsing_inv _ hd]
        simp only [conjTranspose_one, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [h1, Matrix.mul_zero, Matrix.zero_mul]

theorem normInf_atTau_le {D : D7} {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {ε : Fin V.rank → Bool} {P : Mx V.rank} (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ) :
    ∃ c : ℝ, ∀ y ∈ UJset ε, normInf θ V (atTau θ V τ (P⁻¹ * y * P)) ≤ c * (1 + hs y) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  set K : ℝ := (1 + hs P⁻¹) * (1 + hs P) + (1 + hs (1 : Mx V.rank)) with hK
  refine ⟨∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (K + K), fun y hy => ?_⟩
  have hs1 := hs_nonneg (1 : Mx V.rank)
  have hsy := hs_nonneg y
  have hPP : 0 ≤ (1 + hs P⁻¹) * (1 + hs P) := mul_nonneg (by linarith [hs_nonneg P⁻¹]) (by linarith [hs_nonneg P])
  have b1 : ∀ z : Mx V.rank, hs z = hs y → 1 + hs (P⁻¹ * z * P) ≤ K * (1 + hs y) := fun z hz => by
    have := one_add_hs_conj_le P⁻¹ z P
    rw [hz] at this
    nlinarith
  have b2 : 1 + hs (1 : Mx V.rank) ≤ K * (1 + hs y) := by nlinarith
  have sp := atTau_spec hθ V τ (conj_inv_mem hP h hy)
  unfold normInf
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun τ' _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have e := infMat_mul_inv θ V τ' (atTau θ V τ (P⁻¹ * y * P))
  rw [add_mul]
  refine add_le_add ((norm_entry_le _ i j).trans ?_) ((norm_entry_le _ i j).trans ?_)
  · by_cases c : τ' = τ
    · subst c
      rw [sp.2.1]
      exact b1 y rfl
    · rw [sp.2.2 τ' c]
      exact b2
  · by_cases c : τ' = τ
    · subst c
      rw [sp.2.1] at e
      have e2 : (P⁻¹ * y⁻¹ * P) * (P⁻¹ * y * P) = 1 := by
        rw [← conj_mul hP, inv_mul_UJ hy, Matrix.mul_one, Matrix.nonsing_inv_mul _ hd]
      rw [← left_inv_eq_right_inv e2 e]
      exact b1 _ (hs_inv hy)
    · rw [sp.2.2 τ' c, Matrix.one_mul] at e
      rw [e]
      exact b2

theorem umg_atTau : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ (ε : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ → ∀ x : GA D V, GlobalTheory.TypeSum.UMG ε (fun y => φ (x * atTau θ V τ (P⁻¹ * y * P))) := by
  intro D θ hθ V τ φ hφ ε P hP h x
  obtain ⟨N, hN⟩ := hφ.growth
  obtain ⟨c, hc⟩ := normInf_atTau_le hθ V τ hP h
  have hl : ∀ l : List (Mx V.rank), (∀ Y ∈ l, Y ∈ lieSet ε) →
      ∀ p ∈ l.map fun X => (τ, P⁻¹ * X * P), p.2 ∈ lieAt V p.1 := fun l hl p hp => by
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hp
    exact conj_lie hP h (hl Y hY)
  refine ⟨N, fun l y => ((l.map fun X => (τ, P⁻¹ * X * P)).foldr (fun p f => Rder θ V p.1 p.2 f) φ)
    (x * atTau θ V τ (P⁻¹ * y * P)), fun _ _ => rfl, fun l hl' X hX g hg => ?_, fun l hl' => ?_⟩
  · have hs := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Mx V.rank => Rder θ V p.1 p.2) _
      fun p hp => linOnSm_Rder (hl l hl' p hp)).mem φ hφ.smooth
    have hd := (differentiable_oneP hs (τ := τ) (conj_lie hP h hX) (x * atTau θ V τ (P⁻¹ * g * P)) 0).hasDerivAt
    refine HasDerivAt.congr_of_eventuallyEq hd (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hg) (conj_inv_mem hP h (exp_mem_UJ hX t)), conj_exp hP,
      ← mul_assoc]
    rfl
  · obtain ⟨C, hC⟩ := hN _ (hl l hl') x
    refine ⟨|C| * c ^ N, fun g hg => (hC _ (atTau_mem V τ _)).trans ?_⟩
    have h0 := normInf_nonneg (θ := θ) (atTau θ V τ (P⁻¹ * g * P))
    rw [mul_assoc |C|, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ h0 (hc g hg) N) (pow_nonneg h0 _) (abs_nonneg _)

end GlobalTheory.TypeSum.GrowthAtPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalNegFirstFamilyFrameCartanMove
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

noncomputable section

namespace GlobalTheory.OneMapRef.Frames

open GlobalTheory.Ker.ONBasis

variable {D : D7} {T : HSp D}

theorem negM_sq (T : HSp D) (q : ℕ) : negM T q * negM T q = 1 := by
  unfold negM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  unfold sgn
  split_ifs <;> simp

theorem negM_herm (T : HSp D) (q : ℕ) : (negM T q)ᴴ = negM T q := by
  unfold negM
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp

theorem compAt_eq (θ : InfFam D) (ρ : D.what₂.Tau) (h : GA D T) :
    compAt θ ρ (Formalism.L2.Theta.mt T h) = infMat D.sp.cm.sig T.gram (θ ρ) h := rfl

theorem compAt_unitary' {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (g : GA D T) :
    (compAt θ ρ (Formalism.L2.Theta.mt T g))ᴴ * gramAt D T ρ * compAt θ ρ (Formalism.L2.Theta.mt T g) = gramAt D T ρ := by
  rw [GlobalTheory.FockCompare.RealAction.gramAt_eq hθ]
  exact GlobalTheory.FockCompare.RealAction.unitary_map (cA D) ((θ ρ).comp (infPart D))
    (GlobalTheory.FockCompare.comp_cA hθ ρ) _ _ (mt_rel T g)

theorem isONeg_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) (g : GA D T) :
    IsONeg T q (mvZ θ g Z) := by
  intro τ
  unfold mvZ
  rw [Matrix.conjTranspose_mul, ← hZ τ]
  conv_rhs => rw [← compAt_unitary' hθ τ g]
  simp only [Matrix.mul_assoc]

theorem mvZ_mul (θ : InfFam D) (Z : Fam T) (g g' : GA D T) : mvZ θ (g' * g) Z = mvZ θ g' (mvZ θ g Z) := by
  funext τ
  unfold mvZ
  have e : Formalism.L2.Theta.mt T (g' * g) = Formalism.L2.Theta.mt T g' * Formalism.L2.Theta.mt T g := by simp [Formalism.L2.Theta.mt]
  rw [e, ← Matrix.mul_assoc]
  congr 1
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem mvZ_fin (θ : InfFam D) (Z : Fam T) {g : GA D T} (hg : g ∈ GfC T) : mvZ θ g Z = Z := by
  funext τ
  have h1 : (Formalism.L2.Theta.mt T g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt T g) = ((Formalism.L2.Theta.mt T g).map (infPart D)).map (θ τ) := rfl
  unfold mvZ
  rw [h2, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem cartZ_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) (g : GA D T)
    (τ : D.what₂.Tau) :
    cartZ T q (mvZ θ g Z) τ * compAt θ τ (Formalism.L2.Theta.mt T g) = compAt θ τ (Formalism.L2.Theta.mt T g) * cartZ T q Z τ := by
  have hu' := isUnit_det (negM_sq T q) (isONeg_mvZ hθ hZ g τ)
  have e : (mvZ θ g Z τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T g) = (Z τ)⁻¹ := by
    symm
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ hu'
  unfold cartZ
  rw [Matrix.mul_assoc, e]
  unfold mvZ
  simp only [Matrix.mul_assoc]

theorem fin_of_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) {g : GA D T}
    (h : mvZ θ g Z = Z) : g ∈ GfC T := by
  refine (GlobalTheory.SmoothForms.RealPts.glue θ hθ T).1 g fun τ => ?_
  have hu := isUnit_det (negM_sq T q) (hZ τ)
  have h1 : compAt θ τ (Formalism.L2.Theta.mt T g) * Z τ = Z τ := congrFun h τ
  rw [← compAt_eq]
  calc _ = compAt θ τ (Formalism.L2.Theta.mt T g) * Z τ * (Z τ)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hu]

theorem exists_move {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z Z' : Fam T} (hZ : IsONeg T q Z)
    (hZ' : IsONeg T q Z') : ∃ a ∈ GinfC T, Z' = mvZ θ a Z := by
  have hu := fun τ => isUnit_det (negM_sq T q) (hZ τ)
  obtain ⟨a, ha, h⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ T).2 (fun τ => Z' τ * (Z τ)⁻¹) (fun τ => by
    show (Z' τ * (Z τ)⁻¹)ᴴ * gramAt D T τ * (Z' τ * (Z τ)⁻¹) = gramAt D T τ
    have h2 := Matrix.mul_nonsing_inv _ (hu τ)
    calc _ = (Z τ)⁻¹ᴴ * ((Z' τ)ᴴ * gramAt D T τ * Z' τ) * (Z τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Z τ * (Z τ)⁻¹)ᴴ * gramAt D T τ * (Z τ * (Z τ)⁻¹) := by
          rw [hZ' τ, ← hZ τ]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one])
  refine ⟨a, ha, funext fun τ => ?_⟩
  unfold mvZ
  rw [compAt_eq, h τ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu τ), Matrix.mul_one]

theorem isOrtho_frOf {X : Data D.host.E T.rank} (eT : D.what₂.Tau ≃ X.Ψ) (hM : ModelW T rfl X)
    (he : ∀ ρ, (eT ρ).1 = tauE D ρ) {Z : Fam T} (hZ : IsONeg T X.p0 Z) : X.IsOrtho (frOf rfl eT Z) := by
  intro σ
  obtain ⟨τ, rfl⟩ := eT.surjective σ
  have hm : mat (frOf rfl eT Z) (eT τ) = Z τ := by
    ext a b
    simp [mat, frOf]
  have hG : ∀ a b, tauE D τ (X.Gm a b) = -gramAt D T τ b a := fun a b => by
    rw [hM.1]
    simp [gramAt]
  rw [hm, he]
  ext a b
  have h1 := congrFun (congrFun (hZ τ) b) a
  have h2 : FD.gram (tauE D τ) X.Gm (Z τ) a b = -((Z τ)ᴴ * gramAt D T τ * Z τ) b a := by
    simp only [FD.gram, hermC, FD.col, Matrix.of_apply, hG, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.sum_mul, ← Finset.sum_neg_distrib, RCLike.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, h1, negM]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), neg_zero]

theorem isUnitFr_of_isOrtho {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i
  unfold dmin
  have h : FD.gram τ.1 X.Gm (mat x τ) = sgnM X := hx τ
  rw [h, GlobalTheory.SW.Slab.lminor_sgnM]
  rcases GlobalTheory.SW.Slab.psgn_sq X.p0 i with h | h <;> rw [h] <;> norm_num

end GlobalTheory.OneMapRef.Frames

open GlobalTheory.OneMapRef.Frames GlobalTheory.Ker.ONBasis in

theorem GlobalTheory.OneMapRef.oneg_frames : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ Z : Fam T, IsONeg T X.p0 Z → frOf hr eT Z ∈ X.dom ∧ IsUnitFr X (frOf hr eT Z) ∧ X.IsOrtho (frOf hr eT Z) ∧ (∀ ρ, IsCartanInv (gramAt D T ρ) (cartZ T X.p0 Z ρ)) ∧ ∀ h : GA D T, IsONeg T X.p0 (mvZ θ h Z) ∧ (∀ ρ, cartZ T X.p0 (mvZ θ h Z) ρ * compAt θ ρ (Formalism.L2.Theta.mt T h) = compAt θ ρ (Formalism.L2.Theta.mt T h) * cartZ T X.p0 Z ρ) ∧ (∀ h', mvZ θ (h' * h) Z = mvZ θ h' (mvZ θ h Z)) ∧ (h ∈ GfC T → mvZ θ h Z = Z) ∧ (mvZ θ h Z = Z → h ∈ GfC T) ∧ ∀ Z', IsONeg T X.p0 Z' → ∃ a ∈ GinfC T, Z' = mvZ θ a Z := by
  intro D S T r g hr ψ θ X eT bas idx hS Z hZ
  subst hr
  obtain ⟨-, hθ, -, -, hM, -, he, -⟩ := hS
  have ho := isOrtho_frOf eT hM he hZ
  exact ⟨mem_dom X ho, isUnitFr_of_isOrtho X ho, ho,
    fun ρ => isCartanInv (negM_sq T _) (negM_herm T _) (hZ ρ),
    fun h => ⟨isONeg_mvZ hθ hZ h, cartZ_mvZ hθ hZ h, mvZ_mul θ Z h, mvZ_fin θ Z, fin_of_mvZ hθ hZ,
      fun _ hZ' => exists_move hθ hZ hZ'⟩⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairIntegral

theorem sum_mem_intAf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → E)
    (hu : ∀ y ∈ Λ, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = ∑ k, u k * y k)
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ∑ k, (u k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * z k ∈ Formalism.L2.Herm.intAf F E := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨c, hc⟩ := hu y hy
    have hm : (algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.intAf F E :=
      Subring.subset_closure (Or.inl ⟨⟨_, c, rfl⟩, rfl⟩)
    convert hm using 1
    rw [hc, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (u k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (y k ⊗ₜ[F] 1) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; exact add_mem hx hy
  | smul c x _ hx =>
    have := mul_mem c.2 hx
    convert this using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ * (c.1 * x k) = _
    ring

theorem pair_mem_intAf : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ v : Fin W.rank → D.host.E, finVec W v ∈ gLat W 1 → ∀ a : Fin W.rank, ∑ k, eToEAf D (∑ l, D.sp.cm.sig (v l) * W.gram l k) * β.val k a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D W β Λ hβ v hv a
  have hΛ := GlobalTheory.PrincInLevel.eq_latC hβ
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hβ; exact h
  obtain ⟨h1, -, hfg, hsp, -, -, -, -, -, -, hsd⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D W
  have hv' : v ∈ GlobalTheory.Member.latC W := by
    obtain ⟨z, hz, e⟩ := hv
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    subst e
    rw [h1] at hz
    exact ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E W.rank _ hfg hsp).1 v).1 hz
  have hcol : (fun k => β.val k a) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    refine (hfr _).2 fun i => ?_
    have e : ((β⁻¹).val *ᵥ fun k => β.val k a) i = ((β⁻¹).val * β.val) i a := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine sum_mem_intAf Λ (fun k => ∑ l, D.sp.cm.sig (v l) * W.gram l k) (fun y hy => ?_) _ hcol
  rw [hΛ] at hy
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 ((hsd y).2 hy v hv')
  refine ⟨c, hc.trans (Finset.sum_congr rfl fun k _ => ?_)⟩
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  change y k * W.gram l k * D.sp.cm.sig (v l) = _
  ring

end GlobalTheory.PairIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormSumLieWordInner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem exists_factor_of_bound {V E : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Φ : V →ₗ[ℂ] E) (ℓ : V →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ w, ‖ℓ w‖ ≤ C * ‖Φ w‖) :
    ∃ Λ : E →L[ℂ] ℂ, ∀ w, Λ (Φ w) = ℓ w := by
  have hk : LinearMap.ker Φ ≤ LinearMap.ker ℓ := fun w hw => by
    have := h w
    rw [LinearMap.mem_ker.1 hw, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let f₀ : LinearMap.range Φ →ₗ[ℂ] ℂ := (LinearMap.ker Φ).liftQ ℓ hk ∘ₗ Φ.quotKerEquivRange.symm.toLinearMap
  have hf : ∀ w, f₀ ⟨Φ w, LinearMap.mem_range_self Φ w⟩ = ℓ w := fun w => by
    simp only [f₀, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hb : ∀ x, ‖f₀ x‖ ≤ C * ‖x‖ := by
    rintro ⟨_, w, rfl⟩
    exact (congrArg norm (hf w)).le.trans (h w)
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range Φ) (f₀.mkContinuous C hb)
  exact ⟨g, fun w => (hg ⟨Φ w, LinearMap.mem_range_self Φ w⟩).trans (hf w)⟩

theorem exists_inner_of_pi {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {m : ℕ}
    (Λ : (Fin m → H) →L[ℂ] ℂ) : ∃ a : Fin m → H, ∀ x, Λ x = ∑ i, ⟪a i, x i⟫_ℂ := by
  refine ⟨fun i => (InnerProductSpace.toDual ℂ H).symm (Λ.comp (ContinuousLinearMap.single ℂ (fun _ => H) i)),
    fun x => ?_⟩
  simp only [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  rw [← map_sum, Finset.univ_sum_single]

theorem sobCont_repr : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → ∃ (m : ℕ) (ls : Fin m → List (Matrix (Fin n) (Fin n) ℂ)) (a : Fin m → H), (∀ i, ∀ X ∈ ls i, X ∈ lieG G) ∧ ∀ w ∈ smSub G (trRep σ P), ℓ w = ∑ i, ⟪a i, word (trRep σ P) (ls i) w⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP h hσ ℓ ⟨S, C, hS, hC⟩
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have hl : ∀ i : Fin S.length, ∀ X ∈ S.get i, X ∈ lieG G := fun i => hS _ (List.get_mem S i)
  let Φ : smSub G (trRep σ P) →ₗ[ℂ] (Fin S.length → H) :=
    { toFun := fun w i => word (trRep σ P) (S.get i) w
      map_add' := fun v w => funext fun i => word_add hG hπ (hl i) v.2 w.2
      map_smul' := fun c w => funext fun i => word_smul hG hπ (hl i) c w.2 }
  have hb : ∀ w, ‖(ℓ ∘ₗ (smSub G (trRep σ P)).subtype) w‖ ≤ (|C| * S.length) * ‖Φ w‖ := fun w => by
    refine (hC w w.2).trans ?_
    have h1 : (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖).sum ≤ S.length * ‖Φ w‖ := by
      have := List.sum_le_card_nsmul (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖) ‖Φ w‖ (by
        intro x hx
        obtain ⟨l, hl', rfl⟩ := List.mem_map.1 hx
        obtain ⟨i, rfl⟩ := List.get_of_mem hl'
        exact norm_le_pi_norm (Φ w) i)
      simpa using this
    have h0 : 0 ≤ (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    rw [mul_assoc]
    exact mul_le_mul (le_abs_self C) h1 h0 (abs_nonneg C)
  obtain ⟨Λ, hΛ⟩ := exists_factor_of_bound Φ _ _ hb
  obtain ⟨a, ha⟩ := exists_inner_of_pi Λ
  exact ⟨S.length, S.get, a, hl, fun w hw => (hΛ ⟨w, hw⟩).symm.trans (ha _)⟩

end GlobalTheory.SmVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompact
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct RestrictedProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitAnnihilator

open GlobalTheory.IdemModTwo

open Classical in

theorem continuous_singleV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem trace_split {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} (he : SplitAt D v e)
    (x y : Fv D.host.F v) :
    Algebra.trace (AF D.host.F) (AE D) (fj D (singleV D.host.F v x) * e * (fj D (singleV D.host.F v y) * e)) =
      pairA D.host.F 0 (singleV D.host.F v (x * y)) := by
  have h1 : fj D (singleV D.host.F v x) * e * (fj D (singleV D.host.F v y) * e) =
      fj D (singleV D.host.F v (x * y)) * e := by
    rw [mul_mul_mul_comm, he.1, ← map_mul, singleV_mul, GlobalTheory.SplitIdem.evalV_singleV_same]
  have h2 := GlobalTheory.FockCompare.SymplVal.trace_AE D (fj D (singleV D.host.F v (x * y)) * e)
  rw [map_mul (cA D), cA_fj, ← mul_add, he.2.2, ← map_mul (fj D), singleV_mul, GlobalTheory.SplitIdem.evalV_singleV_same, mul_one] at h2
  rw [h1]
  exact tmul_one_inj (F := D.host.F) (E := D.host.E) h2

theorem annihilator_subset_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1) → ∀ ε : AE D, IsSplitIdem D ε → ∀ V ∈ nhds (0 : AE D), ∃ C : Set (AE D), IsCompact C ∧ ∀ a, ε * a = a → (∀ s ∈ V, ε * s = s → ψ (Algebra.trace (AF D.host.F) (AE D) (a * s)) = 1) → a ∈ C := by
  intro D ψ hψ e hε V hV
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hε
  obtain ⟨y, hy⟩ := hψ v
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : ProperSpace (Fv D.host.F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  let j : Fv D.host.F v → AE D := fun x => fj D (singleV D.host.F v x) * e
  have hj : Continuous j := by
    have h1 : Continuous (algebraMap (AF D.host.F) (AE D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))
    have h2 : Continuous fun x : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v x) :=
      Continuous.prodMk continuous_const (continuous_singleV D.host.F v)
    exact (h1.comp h2).mul continuous_const
  have hj0 : j 0 = 0 := by
    have h0 : singleV D.host.F v 0 = 0 := by
      rw [← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self]
    simp only [j, h0, map_zero, zero_mul]
  have hV' : j ⁻¹' V ∈ nhds (0 : Fv D.host.F v) := hj.continuousAt.preimage_mem_nhds (by rwa [hj0])
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV'
  refine ⟨j '' Metric.closedBall 0 (‖y‖ / r), (isCompact_closedBall _ _).image hj, fun a ha hs => ?_⟩
  obtain ⟨x, hx⟩ := he.exists_scalar a
  rw [ha] at hx
  refine ⟨x, ?_, hx.symm⟩
  by_contra hn
  rw [mem_closedBall_zero_iff, not_le] at hn
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hr.le) hn
  have hx0 : x ≠ 0 := norm_pos_iff.1 hxpos
  have hmem : y / x ∈ Metric.ball (0 : Fv D.host.F v) r := by
    rw [mem_ball_zero_iff, norm_div, div_lt_iff₀ hxpos]
    rw [div_lt_iff₀ hr] at hn
    linarith
  have h := hs (j (y / x)) (hball hmem) (by
    show e * (_ * e) = _ * e
    rw [mul_left_comm, he.1])
  rw [hx] at h
  change ψ (Algebra.trace _ _ (_ * (_ * e))) = 1 at h
  rw [trace_split he, mul_div_cancel₀ _ hx0] at h
  exact hy h

end GlobalTheory.SplitAnnihilator

end
end

