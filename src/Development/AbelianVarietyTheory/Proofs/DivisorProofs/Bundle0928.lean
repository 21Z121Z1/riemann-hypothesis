import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0884
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0034
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerCoordExists
section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open GlobalTheory.PELU
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj det_ne_zero_of_pos colMat exists_finset_of_mem_nhds)

namespace GlobalTheory.PerCoordU

noncomputable section

variable {g : ℕ}

theorem coords_sum {d : ℕ} (π : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] (Fin d → ℂ)) (S : Matrix (Fin g) (Fin g) ℂ) (k : Fin d) :
    π S k = ∑ i, ∑ j, S i j * π (Matrix.single i j 1) k := by
  conv_lhs => rw [matrix_eq_sum_single S]
  simp only [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (S i j) = S i j • Matrix.single i j (1 : ℂ) by rw [smul_single, smul_eq_mul, mul_one],
    map_smul, Pi.smul_apply, smul_eq_mul]

theorem perCoord_exists : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D : PLat O bar), ∃ d, PerCoord D ρ d := by
  intro O _ bar g ρ D
  classical
  refine ⟨Module.finrank ℂ (Tsp bar ρ), fun P₀ hP₀ => ?_⟩
  set d := Module.finrank ℂ (Tsp bar ρ)
  let bV := Module.finBasis ℂ (Tsp bar ρ)
  obtain ⟨p, hp⟩ := (Tsp bar ρ).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let ι : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ := (Tsp bar ρ).subtype ∘ₗ bV.equivFun.symm.toLinearMap
  let π : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] (Fin d → ℂ) := bV.equivFun.toLinearMap ∘ₗ p
  have hιeq : ∀ b, ι b = ((bV.equivFun.symm b : Tsp bar ρ) : Matrix (Fin g) (Fin g) ℂ) := fun b => rfl
  have hιT : ∀ b, ι b ∈ Tsp bar ρ := fun b => by rw [hιeq]; exact Submodule.coe_mem _
  have hpv : ∀ v : Tsp bar ρ, p ((Tsp bar ρ).subtype v) = v := fun v => LinearMap.congr_fun hp v
  have hπι : ∀ b, π (ι b) = b := fun b => by
    rw [hιeq]; simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show ((bV.equivFun.symm b : Tsp bar ρ) : Matrix (Fin g) (Fin g) ℂ) = (Tsp bar ρ).subtype (bV.equivFun.symm b) from rfl, hpv, LinearEquiv.apply_symm_apply]
  have hιπ : ∀ S ∈ Tsp bar ρ, ι (π S) = S := fun S hS => by
    rw [hιeq]; simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show S = (Tsp bar ρ).subtype ⟨S, hS⟩ from rfl, hpv, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨α, β, hαβ⟩ := exists_colMat_per hP₀
  obtain ⟨M₀, hM₀h, hpos₀, hM₀⟩ := hP₀.2.2.2.2
  have hdet₀ : M₀.det ≠ 0 := det_ne_zero_of_pos hpos₀
  have hu₀ : IsUnit M₀.det := isUnit_iff_ne_zero.2 hdet₀
  have hA₀ : colMat α P₀ = 1 ∧ colMat β P₀ = 0 :=
    realMap_inj (ext_per hP₀ fun x => by rw [← hαβ P₀ hP₀]; simp [realMap_apply])
  let Cf : (D.La → Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun f => (colMat α f)⁻¹ * colMat β f
  let Z : (D.La →+ (Fin g → ℂ)) → (Fin d → ℂ) := fun P => π ((Cf P)ᵀ * M₀)
  let Cof : (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => (ι b * M₀⁻¹)ᵀ
  let Q : (Fin d → ℂ) → (D.La →+ (Fin g → ℂ)) := fun b => (realMap 1 (Cof b)).toAddMonoidHom.comp P₀
  have hQ : ∀ b x, Q b x = realMap 1 (Cof b) (P₀ x) := fun b x => rfl
  have hCofT : ∀ b, (Cof b)ᵀ * M₀ = ι b := fun b => by
    simp only [Cof, transpose_transpose, nonsing_inv_mul_cancel_right _ _ hu₀]
  obtain ⟨U, hUg, hUo, hU0⟩ := mem_nhds_iff.1 (GlobalTheory.T.eventually_posDef_hermForm_near_zero_matrix M₀ hpos₀)
  have hQper : ∀ b, Cof b ∈ U → IsPeriod D ρ (Q b) := fun b hb => by
    obtain ⟨hY, hX, hpos⟩ := hUg hb
    have hT : (Cof b)ᵀ * M₀ ∈ Tsp bar ρ := by rw [hCofT]; exact hιT b
    obtain ⟨hMh, hMim⟩ := GlobalTheory.T.riemann_relation_converse_conjAffine M₀ (Cof b) hM₀h hdet₀ hT.1 hY
    refine GlobalTheory.T.isPeriodMap_comp_injective_realLinear D ρ P₀ (realMap 1 (Cof b)) _ hP₀ (realMap_one_injective hX) (fun a x => ?_) hMh hpos (fun x y => ?_)
    · rw [realMap_apply, realMap_apply, one_mulVec, one_mulVec, star_mulVec_map, mulVec_mulVec,
        ← comm_of_mem_Tsp hP₀ hM₀ hdet₀ hT a, ← mulVec_mulVec, mulVec_add]
    · rw [realMap_apply, realMap_apply, one_mulVec, one_mulVec, hMim, hM₀]
  have hCofc : Continuous Cof := by
    exact (Continuous.matrix_mul ι.continuous_of_finiteDimensional continuous_const).matrix_transpose
  have hCof0 : Cof 0 = 0 := by simp [Cof, ι]
  have hZ0 : Z P₀ = 0 := by simp [Z, Cf, hA₀]
  have hcol : ∀ γ : Fin g → (D.La →₀ ℂ), Continuous fun f : D.La → Fin g → ℂ => colMat γ f := fun γ =>
    continuous_matrix fun i j => by simp only [colMat, of_apply]; fun_prop
  have hCfc : ContinuousAt Cf ⇑P₀ := by
    refine ContinuousAt.mul ?_ (hcol β).continuousAt
    refine ContinuousAt.comp (f := fun f => colMat α f) ?_ (hcol α).continuousAt
    refine continuousAt_matrix_inv _ ?_
    rw [hA₀.1, det_one]
    exact (Ring.inverse_eq_inv' (G₀ := ℂ)) ▸ continuousAt_inv₀ one_ne_zero
  have hCf0 : Cf P₀ = 0 := by simp [Cf, hA₀]
  have hdetc : Continuous fun f : D.La → Fin g → ℂ => (colMat α f).det := (hcol α).matrix_det
  obtain ⟨s, ε, hε, hs⟩ := exists_finset_of_mem_nhds
    ((hdetc.continuousAt (x := ⇑P₀)).eventually_ne (show (colMat α P₀).det ≠ 0 by simp [hA₀.1]) |>.and
      (hCfc.preimage_mem_nhds (hUo.mem_nhds (by rw [hCf0]; exact hU0))))
  refine ⟨Cof ⁻¹' U, Q, Z, s, ε, hUo.preimage hCofc, hε, ⟨fun b hb => hQper b hb, fun x => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let F : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun b => Cof b *ᵥ star (P₀ x)
        map_add' := fun b b' => by simp only [Cof, map_add, Matrix.add_mul, transpose_add, add_mulVec]
        map_smul' := fun c b => by
          simp only [Cof, map_smul, Matrix.smul_mul, transpose_smul, smul_mulVec, RingHom.id_apply] }
    have hF : Differentiable ℂ (fun b => F b) := (LinearMap.toContinuousLinearMap F).differentiable
    refine ((differentiableOn_const (P₀ x)).add hF.differentiableOn).congr fun b _ => ?_
    rw [hQ, realMap_apply, one_mulVec]; rfl
  · show Cof (Z P₀) ∈ U
    rw [hZ0, hCof0]; exact hU0
  · ext x
    rw [hZ0, hQ, hCof0, realMap_apply, one_mulVec, zero_mulVec, add_zero]
  · intro b hb _
    have h1 := hαβ (Q b) (hQper b hb)
    have key : colMat α (Q b) = 1 ∧ colMat β (Q b) = Cof b :=
      realMap_inj (ext_per hP₀ fun x => by rw [← h1 x, hQ])
    show π (((colMat α (Q b))⁻¹ * colMat β (Q b))ᵀ * M₀) = b
    rw [key.1, key.2, inv_one, Matrix.one_mul, hCofT, hπι]
  · intro P hP hn
    obtain ⟨hdetA, hCU⟩ := hs _ hn
    have hu : IsUnit (colMat α P).det := isUnit_iff_ne_zero.2 hdetA
    have hT := mem_Tsp_of_period hP₀ hP hM₀ (hαβ P hP) hdetA
    have hCofZ : Cof (Z P) = Cf P := by
      show (ι (π ((Cf P)ᵀ * M₀)) * M₀⁻¹)ᵀ = Cf P
      rw [hιπ _ hT, mul_nonsing_inv_cancel_right _ _ hu₀, transpose_transpose]
    refine ⟨show Cof (Z P) ∈ U by rw [hCofZ]; exact hCU, Matrix.toLinearEquiv' _ (invertibleOfIsUnitDet _ hu),
      fun x => ?_⟩
    rw [hQ, hCofZ]
    change P x = colMat α P *ᵥ realMap 1 ((colMat α P)⁻¹ * colMat β P) (P₀ x)
    rw [hαβ P hP x, realMap_apply, realMap_apply, one_mulVec, mulVec_add, mulVec_mulVec,
      mul_nonsing_inv_cancel_left _ _ hu]
  · intro P P' hP hP' _ _ h hh
    let H := LinearMap.toMatrix' h.toLinearMap
    have hHv : ∀ v, h v = H *ᵥ v := fun v => (LinearMap.toMatrix'_mulVec _ v).symm
    have hHinv : LinearMap.toMatrix' h.symm.toLinearMap * H = 1 := by
      rw [← LinearMap.toMatrix'_comp, show h.symm.toLinearMap ∘ₗ h.toLinearMap = LinearMap.id from
        LinearMap.ext fun v => h.symm_apply_apply v, LinearMap.toMatrix'_id]
    have hHu : IsUnit H.det := isUnit_det_of_left_inverse hHinv
    have key : colMat α P' = H * colMat α P ∧ colMat β P' = H * colMat β P :=
      realMap_inj (ext_per hP₀ fun x => by
        rw [← hαβ P' hP' x, hh x, hαβ P hP x, hHv]
        simp only [realMap_apply, mulVec_add, mulVec_mulVec])
    show π (((colMat α P')⁻¹ * colMat β P')ᵀ * M₀) = π (((colMat α P)⁻¹ * colMat β P)ᵀ * M₀)
    rw [key.1, key.2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc H⁻¹ H, nonsing_inv_mul _ hHu,
      Matrix.one_mul]
  · intro m B' P _ hP hnear
    have hc : ∀ (γ : Fin g → (D.La →₀ ℂ)) i j, DifferentiableOn ℂ (fun b => colMat γ (P b) i j) B' :=
      fun γ i j => by
        simp only [colMat, of_apply]
        exact DifferentiableOn.fun_sum fun x _ => (differentiableOn_pi.1 (hP.2 x) i).const_mul _
    have hinv := RiemannRel.differentiableOn_left_inverse (fun b => colMat α (P b)) (fun b => (colMat α (P b))⁻¹)
      (hc α) (fun b hb => nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hs _ (hnear b hb)).1))
    refine differentiableOn_pi.2 fun k => ?_
    show DifferentiableOn ℂ (fun b => π (((colMat α (P b))⁻¹ * colMat β (P b))ᵀ * M₀) k) B'
    rw [show (fun b => π (((colMat α (P b))⁻¹ * colMat β (P b))ᵀ * M₀) k) = fun b => ∑ i, ∑ j,
      (((colMat α (P b))⁻¹ * colMat β (P b))ᵀ * M₀) i j * π (Matrix.single i j 1) k from
      funext fun b => coords_sum π _ k]
    simp only [mul_apply, transpose_apply]
    exact DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
      (DifferentiableOn.fun_sum fun l _ => (DifferentiableOn.fun_sum fun n _ =>
        (hinv _ _).mul (hc β _ _)).mul_const _).mul_const _

end

end GlobalTheory.PerCoordU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodBoundLastLog
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder Matrix

noncomputable section

namespace GlobalTheory.LastPeriod

open GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum GlobalTheory.ColNorms GlobalTheory.PeriodClassSum

theorem gramSum_one {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) :
    gramSum hN (1 : Matrix (Fin n) (Fin n) K) 1 = 1 := by
  ext a b
  have ha := a.2
  have hb := b.2
  simp only [gramSum, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff, Br.iL]
  split_ifs <;> first | rfl | omega

theorem coefOpLe_brAt (hL : LastMapNorm) {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι]
    {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (T : ℝ) (hT : 0 < T) (t : ι → K)
    (ht : ∀ τ, star (σ (t τ)) * σ (t τ) = (T : ℂ)) :
    CoefOpLe σ lam sg (Br.brAt hN lam sg t) (T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * orthNormSq hN lam sg) := by
  intro x
  have h := (hL ℂ (RingHom.id ℂ) (fun _ => rfl) ι N n hN lam sg hI hS (fun _ => 1)
    (fun _ => by simpa using Matrix.PosDef.one) T hT (fun _ => 1) (fun τ => σ (t τ))
    (fun τ => by simpa using ht τ)).2.2.1
    ⟨MvPolynomial.map σ (x : Pol K ι N), GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩
  simp only [gramSum_one] at h
  rw [GlobalTheory.JetBase.sqAt_eq σ lam x ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩ rfl]
  refine le_of_eq_of_le (GlobalTheory.JetBase.sqAt_eq σ sg _ _ ?_) h
  simp only [Br.brAt, Br.brStd, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    Submodule.coe_smul, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_prod σ]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (map_zpow₀ σ _ _).symm

theorem sqAt_eq_dot {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (x : Formalism.L2.DIV.VV K lam) :
    sqAt σ lam x = (star (fun i => σ ((bVV K lam).repr x i)) ⬝ᵥ (GlobalTheory.TestLat.Compare.gramB K lam).map σ *ᵥ
      fun i => σ ((bVV K lam).repr x i)).re := by
  simp only [sqAt, pairK_one_basis, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply,
    starRingEnd_apply, mul_assoc]

theorem sum_pair_le {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {N n : ℕ}
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (B : Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K sg) (t : ℝ)
    (hB : CoefOpLe σ lam sg B t) {C : Type} [Fintype C] (w : C → ℕ) (x : C → Formalism.L2.DIV.VV K lam)
    (y : C → Formalism.L2.DIV.VV K sg) :
    ‖σ (∑ c, ((w c : ℕ) : K)⁻¹ * pairBK sg (B (x c)) (y c))‖ ^ 2 ≤
      t * (∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ lam (x c)) * ∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ sg (y c) := by
  have hG := (gramB_posDef sg σ).posSemidef
  have hre : ∀ z : C → Formalism.L2.DIV.VV K sg, (wForm w ((GlobalTheory.TestLat.Compare.gramB K sg).map σ)
      (fun c i => σ ((bVV K sg).repr (z c) i)) (fun c i => σ ((bVV K sg).repr (z c) i))).re =
      ∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ sg (z c) := fun z => by
    rw [wForm, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sqAt_eq_dot, ← Complex.re_ofReal_mul]
    push_cast
    rfl
  have e3 : σ (∑ c, ((w c : ℕ) : K)⁻¹ * pairBK sg (B (x c)) (y c)) = wForm w ((GlobalTheory.TestLat.Compare.gramB K sg).map σ)
      (fun c => star fun i => σ ((bVV K sg).repr (B (x c)) i)) (fun c i => σ ((bVV K sg).repr (y c) i)) := by
    rw [map_sum, wForm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_inv₀, map_natCast, star_star, map_pairBK]
  have h := wForm_le w hG (fun c => star fun i => σ ((bVV K sg).repr (B (x c)) i)) (fun c i => σ ((bVV K sg).repr (y c) i))
  rw [wForm_star w (by rw [← Matrix.transpose_map, GlobalTheory.TestLat.Compare.gramB_transpose]), ← e3] at h
  have h0 := (Complex.nonneg_iff.1 (wForm_nonneg w hG (fun c i => σ ((bVV K sg).repr (y c) i)))).1
  rw [hre] at h0
  rw [hre fun c => B (x c), hre] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ h0)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

theorem sqAt_nonneg {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) : 0 ≤ sqAt σ lam x := by
  rw [sqAt_eq_dot]
  exact (Complex.nonneg_iff.1 ((gramB_posDef lam σ).posSemidef.dotProduct_mulVec_nonneg _)).1

theorem re_inv_mul (w : ℕ) (z : ℂ) : ((w : ℂ)⁻¹ * z).re = (w : ℝ)⁻¹ * z.re := by
  rw [← Complex.re_ofReal_mul]
  push_cast
  rfl

end GlobalTheory.LastPeriod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjAGphiEqSum
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VacProj

theorem mem_vset {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (Λ : Formalism.L2.Pj.GenLat E n) (hU : Λ.Unimod) (hfg : Λ.La.FG) : Λ.La ∈ Vset E n 1 := by
  have hU' := (GenLatCmp.unimod_iff Λ.La).1 hU
  obtain ⟨N, hN, h⟩ := TensLat.exists_mul_le (B := stdL E n) (B' := Λ.La)
    (Submodule.fg_span (Set.finite_range _)) (DualFamily.span_eq_top Λ.La hfg fun x => (hU' x).2)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {N}))
  have h4 : ∀ u ∈ stdL E n, ((Ideal.absNorm (Ideal.span {N}) : ℕ) : E) • u ∈ Λ.La := fun u hu => by
    have e : ((Ideal.absNorm (Ideal.span {N}) : ℕ) : E) = (a : E) * (N : E) := by
      have := congrArg (algebraMap (𝓞 E) E) ha
      rw [map_mul, map_natCast] at this
      exact this.symm
    rw [e, mul_smul]
    exact TensLat.int_smul_mem a.isIntegral_coe (h u hu)
  refine ⟨hfg, hU', _, Nat.pos_of_ne_zero ?_, Nat.coprime_one_right _,
    GenLatCmp.smul_mem_std hU' h4, h4⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hN

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {w : E} {A A' : AddSubgroup (Matrix (Fin n) (Fin r) E)}

theorem heisG_sum {ι : Type} (y : Matrix (Fin n) (Fin r) E) (s : Finset ι) (f : ι → TF n g) :
    heisG X bas y (∑ i ∈ s, f i) = ∑ i ∈ s, heisG X bas y (f i) := by
  funext x; simp [heisG, heisS, Finset.sum_mul]

theorem rho_eq_iff (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : TensVac.Good X w A) (hA' : TensVac.Good X w A') {v : TF n g} (hv : IsVac X bas w A' v)
    {a b : Matrix (Fin n) (Fin r) E} (ha : a ∈ A) (hb : b ∈ A) :
    epsW X w a • heisG X bas a v = epsW X w b • heisG X bas b v ↔ -a + b ∈ A' := by
  have hfix : ∀ y, epsW X w y • heisG X bas y v = v ↔ y ∈ A' := by
    refine fun y => ⟨fun h => ?_, hv.2.2 y⟩
    by_contra hy
    have := hA'.ip_eq_zero idx hs hn hv hy
    rw [h, hv.2.1] at this
    exact one_ne_zero this
  rw [← hfix, ← hA.rho_rho idx hs hn (A.neg_mem ha) hb hv.1]
  constructor
  · intro h
    rw [← h, hA.rho_rho idx hs hn (A.neg_mem ha) ha hv.1, neg_add_cancel,
      TensVac.rho_zero idx hs hn hv.1]
  · intro h
    conv_lhs => rw [← h]
    rw [hA.rho_rho idx hs hn ha (A.neg_mem ha) (TensVac.rho_sb idx hs hn b hv.1), add_neg_cancel,
      TensVac.rho_zero idx hs hn (TensVac.rho_sb idx hs hn b hv.1)]

theorem proj_eq (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : TensVac.Good X w A) (hA' : TensVac.Good X w A') {v : TF n g} (hv : IsVac X bas w A' v)
    (R : Finset (Matrix (Fin n) (Fin r) E)) (hR : ∀ y ∈ R, y ∈ A)
    (hR' : ∀ y ∈ A, ∃! y', y' ∈ R ∧ y - y' ∈ A') :
    R.card = A'.relIndex A ∧
      projA X bas w A v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X w y • heisG X bas y v ∧
      IsVac X bas w A ((Real.sqrt (R.card : ℝ) : ℂ) • projA X bas w A v) := by
  set f : Matrix (Fin n) (Fin r) E → TF n g := fun y => epsW X w y • heisG X bas y v with hf
  have hiff : ∀ a ∈ A, ∀ b ∈ A, f a = f b ↔ -a + b ∈ A' := fun a ha b hb =>
    rho_eq_iff idx hs hn hA hA' hv ha hb
  have hinj : Set.InjOn f R := fun a ha b hb h => by
    have h1 := (hiff a (hR a ha) b (hR b hb)).1 h
    rw [neg_add_eq_sub] at h1
    exact (hR' b (hR b hb)).unique ⟨ha, h1⟩ ⟨hb, by rw [sub_self]; exact A'.zero_mem⟩
  have him : f '' A = f '' R := by
    refine Set.Subset.antisymm ?_ (Set.image_mono fun y hy => hR y hy)
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, ⟨hb, h⟩, -⟩ := hR' a ha
    exact ⟨b, hb, (hiff b (hR b hb) a ha).2 (by rwa [neg_add_eq_sub])⟩
  have hc : (f '' A).ncard = R.card := by
    rw [him, hinj.ncard_image, Set.ncard_coe_finset]
  have hidx : R.card = A'.relIndex A := hc.symm.trans (TensVac.ncard_image_eq f hiff)
  refine ⟨hidx, ?_, ?_⟩
  · have h1 : ∑ᶠ ψ ∈ f '' R, ψ = ∑ y ∈ R, f y :=
      (finsum_mem_image (f := fun ψ : TF n g => ψ) hinj).trans (finsum_mem_coe_finset _ _)
    rw [projA, ← hf, hc, him, h1]
  · obtain ⟨u, hu, -⟩ := hA.vac hs
    have hov := hA.overlap idx hs hn hA' hu hv
    rw [(hA.proj idx hs hn hv.1 hu).2, smul_smul]
    set a := (Real.sqrt (R.card : ℝ) : ℂ) * SW.ip v u with ha
    have hn1 : ‖a‖ ^ 2 = 1 := by
      rw [ha, TensVac.ip_conj hu.1 hv.1, norm_mul, Complex.norm_conj, Complex.norm_real, mul_pow,
        Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _), hidx, hov]
    refine ⟨TensVac.sb_smul a hu.1, ?_, fun y hy => ?_⟩
    · rw [TensVac.ip_smul_left a hu.1 (TensVac.sb_smul a hu.1), TensVac.ip_smul_right a hu.1 hu.1,
        hu.2.1, _root_.mul_one, Complex.mul_conj']
      exact_mod_cast hn1
    · rw [TensVac.heisG_smul, smul_comm, hu.2.2 y hy]

end

theorem projA_gphi_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ (w : E), IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ (Λ₀ Λ : Formalism.L2.Pj.GenLat E n), Λ₀.Unimod → Λ.Unimod → Λ₀.La.FG → Λ.La.FG → ∀ v : TF n g, IsVac X bas w (tens Λ₀.La L) v → ∀ R : Finset (Matrix (Fin n) (Fin r) E), (∀ y ∈ R, y ∈ tens Λ.La L) → (∀ y ∈ tens Λ.La L, ∃! y', y' ∈ R ∧ y - y' ∈ tens Λ₀.La L) → R.card = ((Λ.La ⊓ Λ₀.La).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ^ r ∧ projA X bas w (tens Λ.La L) v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X w y • heisG X bas y v ∧ IsVac X bas w (tens Λ.La L) ((Real.sqrt (R.card : ℝ) : ℂ) • projA X bas w (tens Λ.La L) v) ∧ ∀ (Q : Type) [Fintype Q] (c : Q → ℂ) (Y : Q → Matrix (Fin n) (Fin r) E), gphi X bas w Λ.La L v c Y = ((R.card : ℂ))⁻¹ • ∑ q, ∑ y ∈ R, (c q * epsW X w y) • heisG X bas (Y q) (heisG X bas y v) := by
  intro E _ _ _ r g n X bas idx hs hn w hw hw1 L hL Λ₀ Λ hU₀ hU hf₀ hf v hv R hR hR'
  have h₀ := mem_vset Λ₀ hU₀ hf₀
  have h₁ := mem_vset Λ hU hf
  obtain ⟨a1, a2, a3, -, -, a4⟩ :=
    TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw1 L hL 1 _ h₁
  obtain ⟨b1, b2, b3, -⟩ :=
    TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw1 L hL 1 _ h₀
  obtain ⟨c1, c2, c3⟩ := proj_eq idx hs hn ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ hv R hR hR'
  refine ⟨?_, c2, c3, fun Q _ c Y => ?_⟩
  · rw [c1, a4 _ h₀, ← AddSubgroup.inf_relIndex_left]
    rfl
  · rw [gphi, finsum_eq_sum_of_fintype, c2]
    refine Eq.trans ?_ Finset.smul_sum.symm
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [TensVac.heisG_smul, heisG_sum, smul_comm]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [TensVac.heisG_smul, smul_smul]

end GlobalTheory.AdTh.VacProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalVectorMemIdealCompletedLatticeIff
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdealCap

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem closure_eq_hat (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 E)) :
    AddSubgroup.closure {u : Fin n → GlobalTheory.AdLat.RA F E | ∃ b ∈ I, ∃ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      u = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i} =
      GlobalTheory.AdLat.hat F ((I • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨b, hb, z, hz, rfl⟩
    rw [SetLike.mem_coe]
    induction hz using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨a, ha, b • x, Submodule.smul_mem_smul hb hx, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
    | zero =>
      convert AddSubgroup.zero_mem _ using 1
      funext i; simp
    | add w w' _ _ h h' =>
      convert add_mem h h' using 1
      funext i; simp [mul_add]
    | neg w _ h =>
      convert neg_mem h using 1
      funext i; simp
  · unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx ⊢
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro b hb y hy
      refine AddSubgroup.subset_closure ⟨b, hb, fun i => a ⊗ₜ y i,
        AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
    · intro y y' h h'
      convert add_mem h h' using 1
      funext i; simp [TensorProduct.tmul_add]

theorem span_smul_eq_top (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Submodule.span E ((I • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤ := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro x hx
  have hb1 : algebraMap (𝓞 E) E b ≠ 0 := by
    simpa using hb0
  have e : x = (algebraMap (𝓞 E) E b)⁻¹ • (b • x) := by
    rw [← algebraMap_smul E b x, smul_smul, inv_mul_cancel₀ hb1, one_smul]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.smul_mem_smul hb hx))

end General

theorem finVec_mem_closure_iff : ∀ (D : D7) (V : HSp D) (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ a : Fin V.rank → D.host.E, finVec V a ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z} ↔ a ∈ I • latG V 1 := by
  intro D V I hI a
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hfg' : (I • latG V 1).FG := Submodule.FG.smul (IsNoetherian.noetherian I) hfg
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg'
    (span_smul_eq_top _ I hI hsp)).1 a
  rw [hhat, ← key, ← closure_eq_hat]
  rfl

end GlobalTheory.IdealCap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCharacterEndOfTorusExtensionActionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_characterEnd_of_torusExtension_action : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (E : TorusExtension G) (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → letI := E.addCommGroup; ∃ ρ : O →+* Module.End ℤ E.X, ∀ a, ∃ τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X, τ ≫ E.i = E.i ≫ act a ∧ ∀ χ, chV τ χ = charUnit (Sp k) E.X (ρ a χ) := by
  first | exact @GlobalTheory.ringHom_charEnd_of_torusExtension | exact GlobalTheory.ringHom_charEnd_of_torusExtension | (intros; apply GlobalTheory.ringHom_charEnd_of_torusExtension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.JSW.MirPatch

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def cell (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a) : Set (GA E a) :=
  {p | ∃ u ∈ NA E a, ∃ k ∈ K, ∃ y : GL (Fin a) (Cinf E), p = u * q * finGL E a k * infGL E a y}

theorem self_mem_cell (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a) : q ∈ cell K q :=
  ⟨1, ⟨fun i j h => by simp [Matrix.one_apply_ne (Fin.ne_of_gt h)], fun i => by simp⟩, 1, K.one_mem, 1, by simp⟩

end GlobalTheory.JSW.MirPatch
end
end

