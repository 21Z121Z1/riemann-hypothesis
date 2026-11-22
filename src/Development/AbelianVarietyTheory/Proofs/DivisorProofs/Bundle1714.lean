import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFinPartILocFEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoreIsometryOfFixesIsotropicFrame
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.CoreIsom

theorem cT_add' {A : Type} [CommRing A] (s : A →+* A) {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) A) :
    cT s (X + Y) = cT s X + cT s Y := by
  ext i k; simp [cT]

theorem unitary_core {A : Type} [CommRing A] (s : A →+* A) {n j m : ℕ} {J : Matrix (Fin n) (Fin n) A}
    {J₀ : Matrix (Fin m) (Fin m) A} {C : Matrix (Fin n) (Fin j) A} {Z : Matrix (Fin n) (Fin m) A}
    {G : Matrix (Fin n) (Fin n) A} {M : Matrix (Fin m) (Fin m) A} {b : Matrix (Fin j) (Fin m) A}
    (hG : cT s G * J * G = J) (hcz : cT s C * J * Z = 0) (hzc : cT s Z * J * C = 0)
    (hcc : cT s C * J * C = 0) (hzz : cT s Z * J * Z = J₀) (hGZ : G * Z = Z * M + C * b) :
    cT s M * J₀ * M = J₀ := by
  have e : cT s (G * Z) * J * (G * Z) = J₀ := by
    calc cT s (G * Z) * J * (G * Z) = cT s Z * (cT s G * J * G) * Z := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J₀ := by rw [hG, hzz]
  rw [hGZ, cT_add', Formalism.UG.cT_mul, Formalism.UG.cT_mul] at e
  have h : (cT s M * cT s Z + cT s b * cT s C) * J * (Z * M + C * b) =
      cT s M * (cT s Z * J * Z) * M + cT s M * (cT s Z * J * C) * b +
        (cT s b * (cT s C * J * Z) * M + cT s b * (cT s C * J * C) * b) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
  rw [h, hzz, hzc, hcz, hcc] at e
  simpa using e

theorem isUnit_of_form {A : Type} [CommRing A] (s : A →+* A) {m : ℕ} {J₀ M : Matrix (Fin m) (Fin m) A}
    (h : cT s M * J₀ * M = J₀) (hJ : IsUnit J₀.det) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at e
  rw [← e] at hJ
  exact isUnit_of_mul_isUnit_right hJ

end GlobalTheory.SphEis.CoreIsom

open GlobalTheory.SphEis.CoreIsom in

theorem GlobalTheory.SphEis.core_isom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g ∈ fixG σ J C, ∃ (g₀ : GAd σ J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)), (matHom _ σ J g).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g₀).1 + adMat F C * b ∧ b = adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z ∧ (matHom _ σ J₀ g₀).1 = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z ∧ (g ∈ ratPts σ J → g₀ ∈ ratPts σ J₀) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g hg
  have hmap : ∀ {a b c d : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin a) (Fin c) E)
      (W : Matrix (Fin c) (Fin d) E), cT (sigR (AF F) σ) (adMat F X) * adMat F Y * adMat F W =
        adMat F (cT (σ : E →+* E) X * Y * W) := by
    intro a b c d X Y W
    rw [adMat, adMat, adMat, GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul]
  have hgC : (matHom _ σ J g).1 * adMat F C = adMat F C := hg
  have hCJ : adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J) := by
    have h1 : (matHom _ σ J g⁻¹).1 * adMat F C = adMat F C * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]
      conv_lhs => rw [← hgC]
      rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]
    have h2 := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at h2
  have hsum : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
    simp only [adMat]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _),
      ← Matrix.map_add _ (map_add _), hF.sum, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨M, hM⟩ : ∃ M, M = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z := ⟨_, rfl⟩
  have hZ : (matHom _ σ J g).1 * adMat F Z = adMat F Z * M + adMat F C * b := by
    calc (matHom _ σ J g).1 * adMat F Z = (adMat F C * adMat F (cT (σ : E →+* E) D * J) +
          adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + adMat F D * adMat F (cT (σ : E →+* E) C * J)) *
          ((matHom _ σ J g).1 * adMat F Z) := by rw [hsum, Matrix.one_mul]
      _ = adMat F C * (adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z) +
          adMat F Z * (adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z) +
          adMat F D * (adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 * adMat F Z) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = adMat F Z * M + adMat F C * b := by
        rw [hCJ, ← hM, ← hb]
        have h0 : adMat F (cT (σ : E →+* E) C * J) * adMat F Z = 0 := by
          simp only [adMat]; rw [← Matrix.map_mul, hF.cz]; simp
        rw [h0, Matrix.mul_zero, add_zero, add_comm]
  have hG : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have hMu : cT (sigR (AF F) σ) M * adMat F J₀ * M = adMat F J₀ :=
    unitary_core (sigR (AF F) σ) hG (by rw [hmap, hF.cz]; simp) (by rw [hmap, hF.zc]; simp)
      (by rw [hmap, hF.cc]; simp) (by rw [hmap, hF.zz]) hZ
  have hdet : IsUnit (adMat F J₀).det := by
    rw [adMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Ne.isUnit hF.herm₀.2).map _
  have hMU := isUnit_of_form _ hMu hdet
  let g₀ : GAd σ J₀ := ⟨hMU.unit, by
    show cT (sigR (AF F) σ) (hMU.unit : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) * adMat F J₀ * hMU.unit = adMat F J₀
    rw [hMU.unit_spec]; exact hMu⟩
  have hg₀ : (matHom _ σ J₀ g₀).1 = M := hMU.unit_spec
  refine ⟨g₀, b, ?_, hb, ?_, ?_⟩
  · rw [hg₀]; exact hZ
  · rw [hg₀]; exact hM
  · intro hr
    have hr' : (show HR (AF F) σ J from g).1 ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (bc (inclR (F := F) (AF F))) := hr
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 hr'
    have hGx : (matHom _ σ J g).1 = adMat F (x : Matrix (Fin n) (Fin n) E) := by
      exact (congrArg Units.val hxg).symm
    have hMM : M = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) := by
      rw [hM, hGx]; simp only [adMat, Matrix.map_mul]
    have inj : Function.Injective (inclR (F := F) (E := E) (AF F)) := fun a c h =>
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F) h
    have hM₀ : cT (σ : E →+* E) (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) * J₀ *
        (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) = J₀ := by
      apply Matrix.map_injective inj
      show adMat F _ = adMat F _
      rw [← hmap, ← hMM]; exact hMu
    have hM₀U := isUnit_of_form _ hM₀ (Ne.isUnit hF.herm₀.2)
    show (show HR (AF F) σ J₀ from g₀).1 ∈ (Formalism.UG.UJ (σ : E →+* E) J₀).map (bc (inclR (F := F) (AF F)))
    refine Subgroup.mem_map.2 ⟨hM₀U.unit, ?_, Units.ext ?_⟩
    · show cT (σ : E →+* E) (hM₀U.unit : Matrix (Fin m) (Fin m) E) * J₀ * hM₀U.unit = J₀
      rw [hM₀U.unit_spec]; exact hM₀
    · show (hM₀U.unit : Matrix (Fin m) (Fin m) E).map (inclR (F := F) (AF F)) = (matHom _ σ J₀ g₀).1
      rw [hM₀U.unit_spec, hg₀, hMM]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroEvalFrNeZero
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj GlobalTheory.LamT

namespace GlobalTheory.LatFull.CMInt

theorem exists_denom {K : Type} [Field K] [NumberField K] (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (c : K) :
    ∃ N : 𝓞 K, N ≠ 0 ∧ ∀ x ∈ J, IsIntegral ℤ ((N : K) * (x * c)) := by
  obtain ⟨a, ha, h⟩ := (J * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c).isFractional
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun x hx => ?_⟩
  obtain ⟨w, hw⟩ := h (x * c) (FractionalIdeal.mul_mem_mul hx (FractionalIdeal.mem_spanSingleton_self _ _))
  rw [Algebra.smul_def] at hw
  have : (a : K) * (x * c) = (w : K) := hw.symm
  rw [this]
  exact w.isIntegral_coe

theorem exists_denom_eval {K σ : Type} [Field K] [NumberField K] [Finite σ]
    (J : (σ →₀ ℕ) → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (x : σ → K) (d : ℕ) :
    ∃ N : K, N ≠ 0 ∧ ∀ G : MvPolynomial σ K, G.IsHomogeneous d → (∀ μ, MvPolynomial.coeff μ G ∈ J μ) →
      IsIntegral ℤ (N * MvPolynomial.eval x G) := by
  classical
  choose M hM0 hM using fun μ : σ →₀ ℕ => exists_denom (J μ) (∏ i ∈ μ.support, x i ^ μ i)
  let S := (Finsupp.finite_of_degree_le (σ := σ) d).toFinset
  refine ⟨((∏ μ ∈ S, M μ : 𝓞 K) : K), ?_, fun G hG hJ => ?_⟩
  · have : (∏ μ ∈ S, M μ : 𝓞 K) ≠ 0 := Finset.prod_ne_zero_iff.2 fun μ _ => hM0 μ
    exact fun h => this (RingOfIntegers.coe_eq_zero_iff.1 h)
  · rw [MvPolynomial.eval_eq, Finset.mul_sum]
    refine IsIntegral.sum _ fun μ hμ => ?_
    have hS : μ ∈ S := by
      simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      have := hG (MvPolynomial.mem_support_iff.1 hμ)
      rw [Finsupp.degree_eq_weight_one]
      exact this.le
    rw [← Finset.prod_erase_mul _ _ hS]
    have e : (((∏ ν ∈ S.erase μ, M ν) * M μ : 𝓞 K) : K) = ((∏ ν ∈ S.erase μ, M ν : 𝓞 K) : K) * (M μ : K) :=
      map_mul (algebraMap (𝓞 K) K) _ _
    rw [e, mul_assoc]
    exact (RingOfIntegers.isIntegral_coe _).mul (hM μ _ (hJ μ))

theorem coeff_mem_of_loc {K : Type} [Field K] [NumberField K] {g : ℕ} {B : Type} [Fintype B] {m : B → ℕ}
    (e : (Σ b, Fin (m b)) ≃ Fin g) (T abelian₂ : MLine K) (ℓ : Fin g → MLine K) (U : Matrix (Fin g) (Fin g) K)
    (G : MvPolynomial (FrVar m) K) (n : ℕ) (hT : T.Good) (hℓ : ∀ j, (ℓ j).Good)
    (hloc : ∀ p, Step5Loc e T abelian₂ ℓ U G n p) (μ : FrVar m →₀ ℕ) :
    MvPolynomial.coeff μ G ∈ (lineNN T ℓ (fun v : FrVar m => e ⟨v.1, v.2.2⟩) μ n).I := by
  classical
  refine coeff_mem_of_local K g ℓ T (FrVar m) _ μ n _ hT hℓ fun p => ?_
  obtain ⟨t, cd, cl, ht, hcd, hcl, hv, V, K', _, _, _, _, _, _, f, Ub, hVc, hfin, hind, hUb, hclUb, hW⟩ := hloc p
  refine ⟨t, cl, ht, hcl, ?_⟩
  have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.1
  have hftn : f (t ^ n) ≠ 0 := (map_ne_zero f).mpr htn
  obtain ⟨w, hw⟩ := coeff_integral_local V K' B m (MvPolynomial.map f G) Ub (fun b j => f (cl (e ⟨b, j⟩)))
    (f (t ^ n)) hVc hfin hftn hUb hclUb hW μ
  have hrange : f (MvPolynomial.coeff μ G * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) ∈
      Set.range (algebraMap V K') := by
    refine ⟨w, ?_⟩
    rw [map_div₀, map_mul, map_prod]
    simp only [map_pow]
    rw [← map_pow f t n, ← MvPolynomial.coeff_map, hw, mul_div_cancel_left₀ _ hftn]
  have h1 := (hind _).mp hrange
  calc p.valuation K (MvPolynomial.coeff μ G * ∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v)
      = p.valuation K (MvPolynomial.coeff μ G * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) *
          p.valuation K (t ^ n) := by
        rw [← map_mul, div_mul_cancel₀ _ htn]
    _ ≤ p.valuation K (t ^ n) := mul_le_of_le_one_left' h1

theorem exists_det_ne_zero_evalFr_ne_zero {K : Type} [Field K] [Infinite K] {B : Type} [Fintype B] {m : B → ℕ}
    (G : MvPolynomial (FrVar m) K) (hG : G ≠ 0) :
    ∃ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K, (∀ b, (Y b).det ≠ 0) ∧ evalFr G Y ≠ 0 := by
  classical
  have hev : ∀ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K,
      evalFr (∏ b, FieldPoly.blockDetPoly K m b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← FieldPoly.evalFr_blockDetPoly m _ Y]
    simp only [evalFr, map_prod]
  have hD : (∏ b, FieldPoly.blockDetPoly K m b) ≠ 0 := fun h0 => by
    have h1 := hev fun _ => 1
    rw [h0] at h1
    simp [evalFr] at h1
  have hP := mul_ne_zero hD hG
  obtain ⟨x, hx⟩ : ∃ x : FrVar m → K, MvPolynomial.eval x ((∏ b, FieldPoly.blockDetPoly K m b) * G) ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (MvPolynomial.funext fun x => by rw [h x, map_zero])
  rw [map_mul] at hx
  let X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
  refine ⟨X, fun b => ?_, right_ne_zero_of_mul hx⟩
  have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hev X]; exact left_ne_zero_of_mul hx
  exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)

theorem exists_frame_bounded_denom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F₀ ∈ sec Xo c a n, (∀ G, IsFrPoly F₀ z.y G → G ≠ 0) → ∃ (y : FrPt Xo c z.K) (N : z.K), N * evR Xo c F₀ y ≠ 0 ∧ ∀ F ∈ sec Xo c a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → IsIntegral ℤ (N * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz a n F₀ hF₀ hne
  classical
  obtain ⟨G₀, hG₀, -⟩ := FieldPoly.exists_isFrPoly_isHomogeneous E H Dw l Xo c z.K z.y a n F₀ hF₀
  obtain ⟨Y, hY, hY0⟩ := exists_det_ne_zero_evalFr_ne_zero G₀ (hne G₀ hG₀)
  obtain ⟨y, hy, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c z.K z.y (fun b => (Y b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact (hY b).isUnit)
  rw [Units.val_one] at hy
  have hval : ∀ (F : Rul Xo c) (G : MvPolynomial (FrVar Dw.mult) z.K), IsFrPoly F z.y G →
      evR Xo c F y = evalFr G Y := fun F G hG => by
    have h1 := hG z.K (AlgHom.id c.F z.K) z.y y Y (fun b => (hY b).isUnit) (GlobalTheory.Frames.frMapUniq_refl z.y) hy
    have h2 : MvPolynomial.map (AlgHom.id c.F z.K).toRingHom G = G := MvPolynomial.map_id G
    rwa [h2] at h1
  have hgood : z.Tl.dual.Good ∧ ∀ k, (z.ℓ k).Good := by
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvΨ, hv', hT, -⟩, ⟨-, -, -, hℓ⟩, -⟩ := hz
    refine ⟨(degree_algebraic z.K z.Tl z.Tl hT hT).2.2.1, fun k => ?_⟩
    have h := hℓ k
    change (z.letters.ℓ k).Good
    generalize z.letters = L at h
    revert h
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact (hvΨ q.2).1
    | inr q => intro h1; rw [h1]; exact (hv' q.2).1
  obtain ⟨N, hN, hint⟩ := exists_denom_eval
    (fun μ : FrVar Dw.mult →₀ ℕ => (lineNN z.Tl.dual z.ℓ (fun v : FrVar Dw.mult => z.e ⟨v.1, v.2.2⟩) μ n).I)
    (fun v : FrVar Dw.mult => Y v.1 v.2.2 v.2.1) (∑ τ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ)))
  refine ⟨y, N, by rw [hval F₀ G₀ hG₀]; exact mul_ne_zero hN hY0, fun F hF hv => ?_⟩
  obtain ⟨G, hG, hh⟩ := FieldPoly.exists_isFrPoly_isHomogeneous E H Dw l Xo c z.K z.y a n F hF
  rw [hval F G hG]
  exact hint G hh (coeff_mem_of_loc z.e z.Tl.dual z.LamL z.ℓ z.U G n hgood.1 hgood.2
    (LocClause.step5Loc_cmPt E H Dw l Xo c z f La hz a n F hF hv G hG))

end GlobalTheory.LatFull.CMInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledPairWeilDatumSchrodingerTransportStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubledPairWeilDatum_schrodingerTransport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∃ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd ∧
          ∃ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ := by
  first | exact @GlobalTheory.DblSchr.exists_dbl_weilDatum_transport | exact GlobalTheory.DblSchr.exists_dbl_weilDatum_transport | (intros; apply GlobalTheory.DblSchr.exists_dbl_weilDatum_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberDeformationLiftModificationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualNumber_deformation_lift_modification : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q) (zw : Sp (DualNumber K) ⟶ M.X) (hw : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ zw = z), ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ zw ≫ toFlag M = X.ptY w := by
  first | exact @GlobalTheory.CompHS.exists_isDef_lift_dualNumber | exact GlobalTheory.CompHS.exists_isDef_lift_dualNumber | (intros; apply GlobalTheory.CompHS.exists_isDef_lift_dualNumber <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped Classical

namespace GlobalTheory.PureFactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mulSupport_finite (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (x : κ → AF F) : (Function.mulSupport fun v => φ v fun i => evFin F v (x i)).Finite := by
  have hx : ∀ᶠ v in Filter.cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F := by
    rw [Filter.eventually_all]
    intro i
    exact (x i).2.2
  refine Set.Finite.subset (Filter.eventually_cofinite.1 (hφ.and hx)) ?_
  intro v hv hv'
  apply hv
  obtain ⟨h1, h2⟩ := hv'
  simp only [h1]
  rw [Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h2)]
  rfl

theorem update_eventually (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (g : (κ → Fv F v₁) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∀ᶠ v in Filter.cofinite, Function.update φ v₁ g v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hφ, Filter.eventually_cofinite_ne v₁] with v hv hne
  rw [Function.update_of_ne hne]; exact hv

theorem finprod_update (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (g : (κ → Fv F v₁) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (x : κ → AF F) :
    (∏ᶠ v, Function.update φ v₁ g v fun i => evFin F v (x i)) =
      g (fun i => evFin F v₁ (x i)) * ∏ᶠ v, Function.update φ v₁ (fun _ => 1) v fun i => evFin F v (x i) := by
  rw [← mul_finprod_cond_ne v₁ (mulSupport_finite _ (update_eventually φ v₁ g hφ) x),
    ← mul_finprod_cond_ne v₁ (mulSupport_finite _ (update_eventually φ v₁ (fun _ => 1) hφ) x)]
  simp only [Function.update_self, one_mul]
  congr 1
  refine finprod_congr fun v => finprod_congr fun hv => ?_
  rw [Function.update_of_ne hv, Function.update_of_ne hv]

theorem comp_add_of_at (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (z : κ → AF F) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v₁) z) (i : κ) :
    (z i).1 = 0 ∧ ∀ v, v ≠ v₁ → evFin F v (z i) = 0 := by
  set u : AF F := 1 - GlobalTheory.EmbChart.atPlace v₁ 1 with hu
  have h0 : evFin F v₁ u = 0 := by
    rw [hu, map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have hzi : u * z i = 0 := by
    have := congrFun (hz u h0) i
    simpa using this
  refine ⟨?_, fun v hv => ?_⟩
  · have h1 : (u * z i).1 = (z i).1 := by
      have : u.1 = 1 := by
        rw [hu]
        show (1 : Ainf F) - (0 : Ainf F) = 1
        exact sub_zero 1
      show u.1 * (z i).1 = (z i).1
      rw [this, one_mul]
    rw [← h1, hzi]; rfl
  · have h2 : evFin F v u = 1 := by
      rw [hu, map_sub, map_one]
      have : evFin F v (GlobalTheory.EmbChart.atPlace v₁ 1) = 0 := evalV_singleFin_ne hv 1
      rw [this, sub_zero]
    have := congrArg (evFin F v) hzi
    rwa [map_mul, h2, one_mul, map_zero] at this

end GlobalTheory.PureFactor

open GlobalTheory.PureFactor in

theorem GlobalTheory.PureFactor.exists_rest_factor : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ),
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∃ r : (κ → AF F) → ℂ, (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v₁) z → r (x + z) = r x) ∧
      ∀ ψ₀ : (κ → Fv F v₁) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) ψ₀ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v₁ ψ₀) := by
  intro F _ _ κ _ v₁ f φ hφ
  refine ⟨fun x => f (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)) *
    ∏ᶠ v, Function.update φ v₁ (fun _ => 1) v fun i => evFin F v (x i), ?_, ?_⟩
  · intro x z hz
    have hI : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x + z) i)) = fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i) := by
      funext i
      have h := (comp_add_of_at v₁ z hz i).1
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((x i).1 + (z i).1) = (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1
      rw [h, add_zero]
    simp only
    rw [hI]
    congr 1
    refine finprod_congr fun v => ?_
    by_cases hv : v = v₁
    · subst hv; simp only [Function.update_self]
    · rw [Function.update_of_ne hv]
      congr 1
      funext i
      rw [Pi.add_apply, map_add, (comp_add_of_at v₁ z hz i).2 v hv, add_zero]
  · intro ψ₀
    funext x
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    rw [finprod_update φ v₁ ψ₀ hφ x]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeUnitStalkDataStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_groupSchemeUnitStalkData : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ s : S, ∃ π ε m, StalkData G s π ε m ∧ ε.comp π = RingHom.id _ ∧ m.comp π = π ∧ ε.comp m = ε := by
  first | exact @GlobalTheory.Nef.stalkData_exists | exact GlobalTheory.Nef.stalkData_exists | (intros; apply GlobalTheory.Nef.stalkData_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUAlphaH
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
noncomputable section

namespace GlobalTheory.FunObj.SqNum

theorem exists_heckeU_alphaH : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ →
    ∀ (G : GridData L sc) (i j : Fin D.R.m), ∃ χ : HeckeU D (botSmall D i j),
      ∀ x, χ.f x = (alphaH L μ₀ i j).1 (finIdl D x) := by
  intro D T L sc μ₀ hL _ i j
  obtain ⟨χ₁, h1, -⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_of_isMu0 (N := 0) ⟨0, rfl⟩ (L.C.isMu0 j) fun g => (D.hc _).e_int j
  have hr := (ranks_exact D i j).2.1
  rcases Nat.mod_two_eq_zero_or_one (rankV D i j) with h | h
  · refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₁ (GlobalTheory.Mem.Col2.SplitChar.trivial D (N := 0) ⟨0, rfl⟩)
      (Int.even_iff.2 (by omega)), fun x => ?_⟩
    rw [GlobalTheory.AlphaSplit.mulU_f, h1]
    simp [alphaH, h, hL.xi_base, GlobalTheory.Mem.Col2.SplitChar.trivial]
  · refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₁ (GlobalTheory.AlphaSplit.etaU L.C.isEta) (Int.even_iff.2 (by omega)), fun x => ?_⟩
    rw [GlobalTheory.AlphaSplit.mulU_f, h1, GlobalTheory.AlphaSplit.etaU_f]
    simp [alphaH, h, hL.xi_base]

end GlobalTheory.FunObj.SqNum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory

theorem exists_int_add_conj_eq_one_of_base_good : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ B hB
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hB.unram
  exact exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianEvalRingPointNeZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jacobian_evalRingPoint_ne_zero : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] (K : GlobalTheory.CanonLB p D) (i : K.bundle.ι) {F : Type} [Field F] (z : Sp F ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ K.bundle.U i), ∃ g : Fin D → Γ(Y, K.bundle.U i), evalPt z _ hz (K.jacobian i le_rfl g) ≠ 0 := by
  first | exact @GlobalTheory.CanonLB.exists_jacobian_evalPt_ne_zero | exact GlobalTheory.CanonLB.exists_jacobian_evalPt_ne_zero | (intros; apply GlobalTheory.CanonLB.exists_jacobian_evalPt_ne_zero <;> assumption)
end

