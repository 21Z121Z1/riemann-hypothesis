import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0724
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0550
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0734
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

theorem charpolyRev_conj_of_mul_eq_one {R : Type*} [CommRing R] {r : Type*} [Fintype r] [DecidableEq r]
    (M P Q : Matrix r r R) (hQP : Q * P = 1) : (Q * M * P).charpolyRev = M.charpolyRev := by
  have hQP' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : (1 : Matrix r r (Polynomial R)) - (Polynomial.X : Polynomial R) • (Q * M * P).map Polynomial.C =
      Q.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) * P.map Polynomial.C := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQP',
      Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
    ← Matrix.det_mul, hQP', Matrix.det_one, one_mul]

theorem curvPoly_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : curvPoly G v =
      ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) • (curv G v (coordVec a) (coordVec b)).map C := by
  ext i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

end GlobalTheory.PointChern

namespace GlobalTheory.PointChern

theorem gram_eq_changeFrame {r : Type} [Fintype r] (c : ℝ) (hc : 0 < c) (g K : Matrix r r ℂ) :
    (c : ℂ) • (g * K * gᴴ) = (((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᵀ * K * (((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᴴᵀ := by
  have h1 : ((((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᴴᵀ) = ((Real.sqrt c : ℝ) : ℂ) • gᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have h2 : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  rw [h1, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, h2]

theorem chernTop_changeFrame : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G K g : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (c : ι → ℝ) (v : ReciprocityTheory.L2DbarEstimates.V n), (∀ τ, 0 < c τ) → (∀ τ i j, AnalyticAt ℂ (fun w => g w τ i j) v) → (∀ τ, IsUnit (g v τ).det) → (∀ τ, MContDiffAt 2 (fun w => K w τ) v) → (∀ τ, IsUnit (K v τ).det) → (∀ᶠ w in 𝓝 v, ∀ τ, G w τ = (c τ : ℂ) • (g w τ * K w τ * (g w τ)ᴴ)) → chernTop R G v = chernTop R K v := by
  intro n ι m R G K g c v hc hg hgu hK hKu hG
  have key : ∀ τ, curvPoly (fun u => G u τ) v = ((((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ)⁻¹).map C *
      curvPoly (fun u => K u τ) v * ((((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ)).map C := by
    intro τ
    set A : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin (m τ)) ℂ :=
      fun u => ((Real.sqrt (c τ) : ℝ) : ℂ) • (g u τ)ᵀ with hAdef
    have hent : ∀ a b, (fun x => A x a b) = fun x => ((Real.sqrt (c τ) : ℝ) : ℂ) * g x τ b a := fun a b => rfl
    have hA : MContDiffAt 2 A v := fun a b => by
      rw [hent]
      exact contDiffAt_const.mul ((hg τ b a).contDiffAt.restrict_scalars ℝ)
    have hAu : IsUnit (A v).det := by
      simp only [hAdef, Matrix.det_smul, Matrix.det_transpose]
      refine IsUnit.mul (IsUnit.pow _ (Ne.isUnit ?_)) (hgu τ)
      exact_mod_cast (Real.sqrt_pos.2 (hc τ)).ne'
    have hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0 := by
      have hev : ∀ᶠ x in 𝓝 v, ∀ a b, AnalyticAt ℂ (fun w => g w τ b a) x :=
        eventually_all.2 fun a => eventually_all.2 fun b => (hg τ b a).eventually_analyticAt
      filter_upwards [hev] with x hx η
      ext a b
      rw [mdbar_apply, hent, GlobalTheory.dbar_eq_zero (((hx a b).differentiableAt).const_mul _)]
      rfl
    have hGe : (fun u => G u τ) =ᶠ[𝓝 v] fun u => (A u)ᵀ * K u τ * (A u)ᴴᵀ :=
      hG.mono fun u hu => by show G u τ = _; rw [hu τ]; exact gram_eq_changeFrame _ (hc τ) _ _
    have hcurv : ∀ ξ η, curv (fun u => G u τ) v ξ η = (A v)⁻¹ * curv (fun u => K u τ) v ξ η * A v :=
      fun ξ η => by rw [curv_congr hGe, curv_changeFrame (hK τ) (hKu τ) hA hAu hA0]
    clear_value A
    rw [curvPoly_eq_sum, curvPoly_eq_sum]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, hcurv]
    subst hAdef
    rfl
  have key2 : ∀ τ k, chernPoly (fun u => G u τ) v k = chernPoly (fun u => K u τ) v k := by
    intro τ k
    have hu : IsUnit (((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ).det := by
      simp only [Matrix.det_smul, Matrix.det_transpose]
      refine IsUnit.mul (IsUnit.pow _ (Ne.isUnit ?_)) (hgu τ)
      exact_mod_cast (Real.sqrt_pos.2 (hc τ)).ne'
    rw [chernPoly, chernPoly, key, show ∀ (Q M P : Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Fin n × Fin n) ℂ)), -(Q * M * P) = Q * (-M) * P from fun Q M P => by rw [Matrix.mul_neg, Matrix.neg_mul], charpolyRev_conj_of_mul_eq_one]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [chernTop, key2]

end GlobalTheory.PointChern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMul
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric

section Subst

variable {n : ℕ}

namespace LinSubst

def rowSel (c : Fin n → Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i => Pi.single (c i) 1

theorem topCoeff_add (P Q : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (P + Q) = topCoeff P + topCoeff Q := by
  simp [topCoeff, coeff_add, mul_add, Finset.sum_add_distrib]

theorem topCoeff_C_mul (a : ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) : topCoeff (C a * P) = a * topCoeff P := by
  simp only [topCoeff, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem topCoeff_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, topCoeff (f i) := by
  simp only [topCoeff, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem sum_apply_sum_single {k : ℕ} (f : Fin k → Fin n × Fin n) :
    ∑ x, (∑ i, Finsupp.single (f i) 1 : Fin n × Fin n →₀ ℕ) x = k := by
  simp only [Finsupp.finset_sum_apply]
  rw [Finset.sum_comm]
  simp [Finsupp.single_apply]

theorem prod_X_eq_monomial' {ι : Type} [Fintype ι] (f : ι → Fin n × Fin n) :
    (∏ i, X (f i) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ i, Finsupp.single (f i) 1) 1 := by
  rw [monomial_sum_one]
  rfl

theorem topCoeff_prod_X_of_ne {k : ℕ} (hk : k ≠ n) (f : Fin k → Fin n × Fin n) :
    topCoeff (∏ i, X (f i)) = 0 := by
  rw [topCoeff]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [prod_X_eq_monomial', coeff_monomial, if_neg, mul_zero]
  intro h
  have : ∑ x, (∑ i, Finsupp.single (f i) 1 : Fin n × Fin n →₀ ℕ) x =
      ∑ x, (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) x := by rw [h]
  rw [sum_apply_sum_single, sum_apply_sum_single (fun a => (a, w a))] at this
  exact hk this

theorem graph_apply (g : Fin n → Fin n) (x y : Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) (x, y) = if g x = y then 1 else 0 := by
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single x (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

theorem graph_eq_iff (g h : Fin n → Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) = ∑ a, Finsupp.single (a, h a) 1 ↔ g = h := by
  constructor
  · intro e
    funext x
    have := DFunLike.congr_fun e (x, g x)
    rw [graph_apply, graph_apply] at this
    by_contra hne
    rw [if_pos rfl, if_neg (Ne.symm hne)] at this
    exact one_ne_zero this
  · rintro rfl
    rfl

theorem det_rowSel_of_not_injective {c : Fin n → Fin n} (hc : ¬ Function.Injective c) : (rowSel c).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
    simp only [Function.Injective, not_forall] at hc
    obtain ⟨i, j, h, h'⟩ := hc
    exact ⟨i, j, h, h'⟩
  exact Matrix.det_zero_of_row_eq hne (by ext k; simp [rowSel, hij])

theorem det_rowSel_perm (σ : Equiv.Perm (Fin n)) : (rowSel σ).det = Equiv.Perm.sign σ := by
  have : rowSel σ = σ.permMatrix ℂ := by
    ext i j
    simp [rowSel, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_permutation]

theorem sum_prod_mul_det_rowSel (U : Matrix (Fin n) (Fin n) ℂ) :
    ∑ c : Fin n → Fin n, (∏ i, U i (c i)) * (rowSel c).det = U.det := by
  have h : (fun i => ∑ a, U i a • (Pi.single a 1 : Fin n → ℂ)) = U := by
    ext i j
    simp [Pi.single_apply]
  conv_rhs => rw [← h]
  change _ = (Matrix.detRowAlternating : AlternatingMap ℂ (Fin n → ℂ) ℂ (Fin n)) _
  rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem topCoeff_prod_X_pair (c d : Fin n → Fin n) :
    topCoeff (∏ i, X (c i, d i)) = (rowSel c).det * (rowSel d).det := by
  rw [topCoeff, prod_X_eq_monomial']
  simp only [coeff_monomial]
  by_cases hc : Function.Injective c
  · have hcb : Function.Bijective c := Finite.injective_iff_bijective.mp hc
    set σ := Equiv.ofBijective c hcb with hσ
    have e : (∑ i, Finsupp.single (c i, d i) 1 : Fin n × Fin n →₀ ℕ) =
        ∑ a, Finsupp.single (a, (d ∘ σ.symm) a) 1 := by
      conv_rhs => rw [← Equiv.sum_comp σ]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [σ]
    simp_rw [e, graph_eq_iff]
    have hcσ : rowSel c = rowSel ⇑σ := rfl
    rw [hcσ, det_rowSel_perm]
    by_cases hd : Function.Injective d
    · set τ := Equiv.ofBijective d (Finite.injective_iff_bijective.mp hd) with hτ
      have hdτ : d ∘ σ.symm = ⇑(σ.symm.trans τ) := by
        ext a
        simp [τ]
      have hdτ' : rowSel d = rowSel ⇑τ := rfl
      rw [hdτ, hdτ', det_rowSel_perm]
      simp only [DFunLike.coe_fn_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp [Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, mul_comm]
    · rw [det_rowSel_of_not_injective hd, mul_zero]
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [if_neg, mul_zero]
      intro h
      apply hd
      have : d = w ∘ σ := by
        rw [← h]
        ext a
        simp
      rw [this]
      exact w.injective.comp σ.injective
  · rw [det_rowSel_of_not_injective hc, zero_mul]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    intro h
    obtain ⟨x, hx⟩ : ∃ x, ∀ i, c i ≠ x := by
      have : ¬ Function.Surjective c := fun hs => hc (Finite.injective_iff_surjective.mpr hs)
      simpa [Function.Surjective] using this
    have h1 := DFunLike.congr_fun h (x, w x)
    rw [graph_apply, if_pos rfl, Finsupp.finset_sum_apply] at h1
    simp [Finsupp.single_apply, hx] at h1

theorem rowSel_mul_apply (c : Fin n → Fin n) (M : Matrix (Fin n) (Fin n) ℂ) (i b : Fin n) :
    (rowSel c * M) i b = M (c i) b := by
  simp [rowSel, Matrix.mul_apply, Pi.single_apply]

theorem exists_prod_X (u : Fin n × Fin n →₀ ℕ) :
    ∃ (k : ℕ) (f : Fin k → Fin n × Fin n), monomial u (1 : ℂ) = ∏ i, X (f i) := by
  induction u using Finsupp.induction with
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | single_add x m u _ _ ih =>
    obtain ⟨k, f, hf⟩ := ih
    refine ⟨m + k, Fin.append (fun _ => x) f, ?_⟩
    rw [Fin.prod_univ_add, monomial_single_add, hf]
    simp [Fin.append_left, Fin.append_right]

theorem topCoeff_subst_prod (J : Matrix (Fin n) (Fin n) ℂ) {k : ℕ} (f : Fin k → Fin n × Fin n) :
    topCoeff (aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
      (∏ i, X (f i) : MvPolynomial (Fin n × Fin n) ℂ)) = J.det * starRingEnd ℂ J.det * topCoeff (∏ i, X (f i)) := by
  rw [map_prod]
  simp only [aeval_X]
  have e : ∀ i, (∑ a, ∑ b, C (J (f i).1 a * starRingEnd ℂ (J (f i).2 b)) * X (a, b) :
      MvPolynomial (Fin n × Fin n) ℂ) =
      ∑ p : Fin n × Fin n, C (J (f i).1 p.1 * starRingEnd ℂ (J (f i).2 p.2)) * X p := fun i =>
    (Fintype.sum_prod_type' (fun a b => C (J (f i).1 a * starRingEnd ℂ (J (f i).2 b)) * X (a, b))).symm
  simp_rw [e]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
  simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
  by_cases hk : k = n
  · subst hk
    rw [← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin k) (fun _ => Fin k)).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    simp_rw [topCoeff_prod_X_pair]
    have key : ∀ (c d : Fin k → Fin k),
        (∏ i, J (f i).1 (c i) * starRingEnd ℂ (J (f i).2 (d i))) * ((rowSel c).det * (rowSel d).det) =
        ((∏ i, (rowSel (fun i => (f i).1) * J) i (c i)) * (rowSel c).det) *
        ((∏ i, (rowSel (fun i => (f i).2) * J.map (starRingEnd ℂ)) i (d i)) * (rowSel d).det) := by
      intro c d
      simp only [rowSel_mul_apply, Matrix.map_apply, Finset.prod_mul_distrib]
      ring
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => key c d, ← Finset.sum_mul_sum,
      sum_prod_mul_det_rowSel, sum_prod_mul_det_rowSel, Matrix.det_mul, Matrix.det_mul]
    have hc : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := by
      rw [RingHom.map_det]
      rfl
    rw [hc]
    ring
  · simp [topCoeff_prod_X_of_ne hk]

end LinSubst

open LinSubst

theorem topCoeff_subst_conj (J : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) P) =
      J.det * starRingEnd ℂ J.det * topCoeff P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u r =>
    obtain ⟨k, f, hf⟩ := exists_prod_X u
    have e : (monomial u r : MvPolynomial (Fin n × Fin n) ℂ) = C r * ∏ i, X (f i) := by
      rw [← hf, C_mul_monomial, mul_one]
    rw [e, map_mul, aeval_C, algebraMap_eq, topCoeff_C_mul, topCoeff_C_mul, topCoeff_subst_prod]
    ring
  | add p q hp hq =>
    rw [map_add, topCoeff_add, topCoeff_add, hp, hq, mul_add]

end Subst

end GlobalTheory.GoodMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricCharacterGridListKeptLocalizedStage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

noncomputable section
namespace GlobalTheory.HeightCounting.Fin3

theorem listPin_datL : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (L : LocAll (lay0 (Dof x))) (cDep : ℝ), ListSt cDep x → ListPin (DL x L) (datL x L).R.toRealDat.toLevCh cDep K.s.b := by
  intro K B f T w P x L cDep h
  obtain ⟨G, h1, h2⟩ := h
  exact ⟨(by with_unfolding_all exact ((GlobalTheory.Mem.GridMove.gdC (oL x L).Z G) :)), ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩, (by with_unfolding_all exact (h2 :))⟩

end GlobalTheory.HeightCounting.Fin3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionChar_extends_divisible_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q q' : ℕ), q' ≠ 0 → q ∣ q' → ∀ c : TorsChar t x q, ∃ c' : TorsChar t x q', ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B] (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 → c'.χ B w = c.χ B w := by
  first | exact @GlobalTheory.TorsCharExt.exists_extension | exact GlobalTheory.TorsCharExt.exists_extension | (intros; apply GlobalTheory.TorsCharExt.exists_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistOfPlaceInWeightSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.HeightCounting.InW1TwistAtMember

theorem inW1_twOf_atMem : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∀ a : (w.D Z).nd.Loc, (w.D Z).ntw.NonzeroIndexPlace ((w.D Z).ntw.twOf a) := by
  intro _ _ hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ => ?_
  intro a
  rw [n.tie.twOf_eq a]
  exact GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice (w.D Z) nch n.tie B.coeffGaloisSubfield_isGalois _ ((w.D Z).nd.w_tw a)

end GlobalTheory.HeightCounting.InW1TwistAtMember

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceWeightPositive
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.LamPosTw

theorem eigenvalue_twistedWeight_pos : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∀ v, TwistedAt (w.D Z) v → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ∀ σ, (w.D Z).what₂.isot j σ ≠ ⊥ → 0 < (w.D Z).what₂.lamP ((w.D Z).what₂.muTw v) j σ := by
  intro hP hL
  have e1 := evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  have e0 : EvLgG fun _ _ _ _ => True :=
    e1.imp fun K _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ _ => trivial⟩
  unfold AtMem
  refine (e0.inter e1).imp fun K _ _ _ _ H => ?_
  obtain ⟨hK, hH⟩ := H
  refine hK.imp fun B f T hO _ _ w Z Wt p0 t nch n xd c _ _ _ v hTw j hj1 hjm σ hne => ?_
  letI : Algebra (↥t.r.z.core.Q.c.F) (w.D Z).what₂.LL := t.r.z.alg
  have host : Formalism.IndefR.Links.HostHyp (w.D Z) := (hH (w.st Z) hO).1
  obtain ⟨p, hp⟩ := GlobalTheory.Mem.LamPosTw.hasLab_exists hP.decay (w.D Z) _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0
    t.r.Y t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange host σ
  have hi : j - 1 < (w.D Z).R.m := by omega
  have hj' : ((⟨j - 1, hi⟩ : Fin (w.D Z).R.m) : ℕ) + 1 = j := by simp only; omega
  have hmu : (w.D Z).what₂.muTw v = t.r.Y.tup (t.r.z.R.mu ((w.D Z).plEq v)) := by
    rcases (w.D Z).what₂.muAt_or v with h | h
    · exact absurd h hTw
    · rw [← h]; exact t.r.Y.muAt v
  have key := GlobalTheory.Mem.LamPosTw.eigenvalue_eq_of_label (w.D Z) _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0 t.r.Y t.r.Z t.r.z.pins
    t.r.intersectionNumber_baseChange host σ p ⟨j - 1, hi⟩ (t.r.z.R.mu ((w.D Z).plEq v)) hp (Or.inr ⟨v, (t.r.Y.muAt v).symm⟩) (by rw [hj']; exact hne)
  rw [hj'] at key
  rw [hmu, key]
  exact t.r.intersectionNumber_baseChange.prim.posScal.2 _ _ _ _

end GlobalTheory.Mem.LamPosTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLatticeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_fixed_lattice : PrN → AllSt fun _ _ _ _ _ _ x => ValLL0 (Dof x) (cfOf x) := by
  first | exact @GlobalTheory.HeightCounting.Up.valLL0_allSt | exact GlobalTheory.HeightCounting.Up.valLL0_allSt | (intros; apply GlobalTheory.HeightCounting.Up.valLL0_allSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneLabelsAllPlacesOfFixedAndConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.LabAllOf

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem labAll_of_labTrue_labConj : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), LabTrue D T → LabConj D T →
    GlobalTheory.PendOf.LabAll D T := by
  intro D T hT hC
  have key : ∀ (k : Fin 2) (w : PlE D.host), ∃ γ : G D.host.E D.nd.Om,
      (∀ v, w = D.naut.plGw k v → γ = D.ntypes.tg k v) ∧
      ∀ v, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
        (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
        (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ (∀ x, γ (c x) = c (D.ntypes.tg k v x)) ∧
        ∀ a : D.naut.LP w, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
          D.naut.items₂ k w a = GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ (T.e w a) := by
    intro k w
    by_cases h : ∃ v, IsConjPl D.host (D.naut.plGw k v) w
    · obtain ⟨v, hv⟩ := h
      obtain ⟨c, γ, h1, h2, h3, h4⟩ := hC k v w hv
      refine ⟨γ, fun v' e => absurd (e ▸ hv) (D.naut.plGw_nconj k v v'), fun v' hv' => ?_⟩
      obtain rfl : v = v' := D.naut.plGw_inj k (GlobalTheory.HeightCounting.LabConjModel.eq_of_isConjPl hv hv')
      exact ⟨c, h1, h2, h3, h4⟩
    · refine ⟨Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1) w, fun v e => ?_,
        fun v hv => absurd ⟨v, hv⟩ h⟩
      rw [e]; exact (D.naut.plGw_inj k).extend_apply _ _ v
  choose γ h1 h2 using key
  refine ⟨γ, fun k v => h1 k _ v rfl, fun k v w' hw' => ?_, fun k w hw a => ?_⟩
  · obtain ⟨c, hc1, hc2, hc3, -⟩ := h2 k w' v hw'
    exact ⟨c, hc1, hc2, hc3⟩
  · obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
    · rw [h1 k _ v rfl]; exact hT k v a
    · obtain ⟨c, -, -, -, h4⟩ := h2 k w v hv
      exact h4 a

end GlobalTheory.LabAllOf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZetaUniformOfExtensionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_uniform_of_extension : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ZeU (prmR N S Γ).s := by
  first | exact @GlobalTheory.Mem.Top.Bl.zeU_prmR_NEb | exact GlobalTheory.Mem.Top.Bl.zeU_prmR_NEb | (intros; apply GlobalTheory.Mem.Top.Bl.zeU_prmR_NEb <;> assumption)
end

