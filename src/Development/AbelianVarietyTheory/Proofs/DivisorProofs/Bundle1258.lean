import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalComponentMemIntegralGLCofini
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SuppFin

theorem cLoc_mem_KGL_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y : UA E n),
    ∀ᶠ w in cofinite, cLoc w y ∈ GlobalTheory.LFun.KGL w n := by
  intro E _ _ _ n y
  set P : GL (Fin n) (Af E) := GeneralLinearGroup.map (pFin E) (y : GA E n) with hP
  have h1 : ∀ᶠ w in cofinite, ∀ i j, (P.val i j) w ∈ HeightOneSpectrum.adicCompletionIntegers E w := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    exact (P.val i j).2
  have h2 : ∀ᶠ w in cofinite, ∀ i j, ((P⁻¹).val i j) w ∈ HeightOneSpectrum.adicCompletionIntegers E w := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    exact ((P⁻¹).val i j).2
  filter_upwards [h1, h2] with w hw1 hw2
  have hmul : ∀ (A B : GL (Fin n) (Af E)), A * B = 1 →
      (A.val.map (pLoc E w)) * (B.val.map (pLoc E w)) = 1 := by
    intro A B h
    rw [← Matrix.map_mul, ← Units.val_mul, h, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  let M : Matrix (Fin n) (Fin n) (Ov E w) := Matrix.of fun i j => ⟨(P.val i j) w, hw1 i j⟩
  let N : Matrix (Fin n) (Fin n) (Ov E w) := Matrix.of fun i j => ⟨((P⁻¹).val i j) w, hw2 i j⟩
  have hM : M.map (Ov E w).subtype = P.val.map (pLoc E w) := Matrix.ext fun i j => rfl
  have hN : N.map (Ov E w).subtype = (P⁻¹).val.map (pLoc E w) := Matrix.ext fun i j => rfl
  have hinj : Function.Injective (fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype) :=
    Matrix.map_injective Subtype.val_injective
  let k : GL (Fin n) (Ov E w) :=
    { val := M
      inv := N
      val_inv := hinj (by
        simp only
        rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _)]
        exact hmul _ _ (mul_inv_cancel P))
      inv_val := hinj (by
        simp only
        rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _)]
        exact hmul _ _ (inv_mul_cancel P)) }
  exact ⟨k, Units.ext (Matrix.ext fun i j => rfl)⟩

end GlobalTheory.BCT.SuppFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthEqChartValueAndSum
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

namespace GlobalTheory.FactorDepth

theorem nuFac_eq_nuFacC_and_nuProd_eq_nuP :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
      ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
        (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p),
        (∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k) ∧
          ∀ cx : Lt1 Dw → ℕ, nuProd p y cx = nuP p y cx := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X
  have hc : ∀ (Ch' : IntegralChartA3 Xo c T io y) (X' : ValExt T p) (f : Lt1 Dw) (k : ℕ),
      nuFacC Ch' X' f k = nuFacC Ch X f k := fun Ch' X' f k =>
    (GlobalTheory.T.detFactorDepthInChart_chart_independent E H Dw l Xo c p T io y Ch' Ch X' f k).trans
      (GlobalTheory.T.detFactorDepthInChart_independent_closedField E H Dw l Xo c p T io y Ch X' X f k)
  have h1 : ∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k := fun f k =>
    le_antisymm (nuFac_le Ch X f k) (le_nuFac fun Ch' X' => (hc Ch' X' f k).ge)
  refine ⟨h1, fun cx => ?_⟩
  have h2 : ∀ (Ch' : IntegralChartA3 Xo c T io y) (X' : ValExt T p), nuProdC Ch' X' cx = nuP p y cx := by
    intro Ch' X'
    rw [GlobalTheory.T.detProductDepthInChart_eq_sum_factorDepths E H Dw l Xo c p T io y Ch' X' cx, nuP]
    exact Finset.sum_congr rfl fun f _ => (hc Ch' X' f (cx f)).trans (h1 f (cx f)).symm
  exact le_antisymm (iInf_le_of_le Ch (iInf_le_of_le X (h2 Ch X).le))
    (le_iInf₂ fun Ch' X' => (h2 Ch' X').ge)

end GlobalTheory.FactorDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTwistedSylvesterSqMulDetPowEqResultantSq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

theorem sign_sq_eq_one_of_pow {k : Type} [Field k] (n : ℕ) : ((-1 : k) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem det_adL_sq_mul_det_pow : ∀ (k : Type) [Field k] (a b : ℕ) (A : GL (Fin a) k)
    (B : Matrix (Fin b) (Fin b) k),
    LinearMap.det (GlobalTheory.LeviDesc.adL A B) ^ 2 * A.val.det ^ (2 * b)
      = resultant A.val.charpoly B.charpoly ^ 2 := by
  intro k _ a b A B
  let e : Matrix (Fin a) (Fin b) k ≃ₗ[k] ((Fin b → k) →ₗ[k] (Fin a → k)) := Matrix.toLin'
  let F : ((Fin b → k) →ₗ[k] (Fin a → k)) →ₗ[k] ((Fin b → k) →ₗ[k] (Fin a → k)) :=
    LinearMap.llcomp k (Fin b → k) (Fin a → k) (Fin a → k) (Matrix.toLin' A.val)
  let G : ((Fin b → k) →ₗ[k] (Fin a → k)) →ₗ[k] ((Fin b → k) →ₗ[k] (Fin a → k)) :=
    LinearMap.lcomp k (Fin a → k) (Matrix.toLin' B)
  have hcomp : F ∘ₗ ((e : _ →ₗ[k] _) ∘ₗ GlobalTheory.LeviDesc.adL A B ∘ₗ (e.symm : _ →ₗ[k] _)) = F - G := by
    apply LinearMap.ext
    intro ψ
    obtain ⟨X, rfl⟩ := e.surjective ψ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.sub_apply, F, G, e, LinearMap.llcomp_apply, LinearMap.lcomp_apply,
      GlobalTheory.LeviDesc.adL, LinearMap.coe_mk, AddHom.coe_mk]
    change Matrix.toLin' A.val ∘ₗ Matrix.toLin' (X - (A⁻¹ : GL (Fin a) k).val * X * B)
      = Matrix.toLin' A.val ∘ₗ Matrix.toLin' X - Matrix.toLin' X ∘ₗ Matrix.toLin' B
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← map_sub]
    congr 1
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  have h1 := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_conj, GlobalTheory.DetAdResultant.det_ad_eq_resultant,
    Matrix.charpoly_toLin', Matrix.charpoly_toLin'] at h1
  have hz : (0 : (Fin b → k) →ₗ[k] (Fin b → k)).charpoly = X ^ b := by
    rw [← (Matrix.toLin' : Matrix (Fin b) (Fin b) k ≃ₗ[k] _).map_zero, Matrix.charpoly_toLin',
      Matrix.charpoly_zero, Fintype.card_fin]
  have hF0 : F - LinearMap.lcomp k (Fin a → k) (0 : (Fin b → k) →ₗ[k] (Fin b → k)) = F := by
    apply LinearMap.ext
    intro ψ
    apply LinearMap.ext
    intro v
    simp [F]
  have h0 : LinearMap.det F = (-1) ^ (a * b) * A.val.charpoly.coeff 0 ^ b := by
    have h := GlobalTheory.DetAdResultant.det_ad_eq_resultant k (Fin a → k) (Fin b → k) (Matrix.toLin' A.val) 0
    rw [hF0, Matrix.charpoly_toLin', hz] at h
    rw [h, natDegree_X_pow, resultant_X_pow_right _ _ _ le_rfl, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  rw [← h1, h0, pow_mul, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, mul_pow ((-1 : k) ^ a),
    sign_sq_eq_one_of_pow, one_mul]
  have hs := sign_sq_eq_one_of_pow (k := k) (a * b)
  linear_combination (-(LinearMap.det (GlobalTheory.LeviDesc.adL A B) ^ 2 * (A.val.charpoly.coeff 0 ^ b) ^ 2)) * hs

end GlobalTheory.LeviDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSpecAffineOpenFunctionsBijective
section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB

namespace GlobalTheory.LieVB

theorem bijective_add_mul_epsFn : ∀ (O : Type) [CommRing O] (V : (Sp O).Opens), IsAffineOpen V → Function.Bijective (fun ab : Γ(Sp O, V) × Γ(Sp O, V) => (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.1 + (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.2 * resG _ le_top (epsFn O)) := by
  intro O _ V hV
  have H : IsPullback (spMap (algebraMap O (DualNumber O))) (𝟙 _) (𝟙 _)
      (spMap (algebraMap O (DualNumber O))) := IsPullback.of_vert_isIso ⟨by simp⟩
  have h := GlobalTheory.EpsThick.comb_bijective_of_isAffineOpen H hV
  refine Eq.mpr (congrArg Function.Bijective (funext fun ab => ?_)) h
  rw [Scheme.Hom.appLE_eq_app, _root_.mul_comm]
  rfl

end GlobalTheory.LieVB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdIntegralMonicCoprimeDerivativeBezoutFactorStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_integral_monic_coprime_derivative_bezout_factor : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (P₀ : (w.adicCompletionIntegers E)[X]), P₀.Monic →
    IsCoprime P₀ (derivative P₀) → ∀ Q₁ : (w.adicCompletion E)[X],
    Q₁ ∣ P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∃ (Q₁₀ Q₂₀ A B : (w.adicCompletionIntegers E)[X]) (c : w.adicCompletion E), c ≠ 0 ∧ P₀ = Q₁₀ * Q₂₀ ∧
      A * Q₁₀ + B * Q₂₀ = 1 ∧ Q₁ = C c * Q₁₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
  first | exact @GlobalTheory.monic_dvd_integral_factor_bezout | exact GlobalTheory.monic_dvd_integral_factor_bezout | (intros; apply GlobalTheory.monic_dvd_integral_factor_bezout <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceCentreOnBaseOfEtaleTowerOverNormalLocalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvrPlace_centre_on_base_of_etaleTowerOverNormalLocal : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL),
  IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = 0) ∨
  ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0) := by
  first | exact @GlobalTheory.FieldPair.centre_of_isEtTower | exact GlobalTheory.FieldPair.centre_of_isEtTower | (intros; apply GlobalTheory.FieldPair.centre_of_isEtTower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbasisBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Matrix

namespace GlobalTheory.EigBasisExtend

theorem eig_rows_map {k K O : Type} [Field k] [Field K] (i : k →+* K) {m n : ℕ} {P : Matrix (Fin m) (Fin n) k}
    (hP : ∀ c, c ᵥ* P = 0 → c = 0) (A : O → Matrix (Fin n) (Fin n) k) (χ : O → k)
    (h : ∀ c, (∀ a, c ᵥ* A a = χ a • c) → ∃ d, d ᵥ* P = c) (c : Fin n → K)
    (hc : ∀ a, c ᵥ* (A a).map i = i (χ a) • c) : ∃ d, d ᵥ* P.map i = c := by
  obtain ⟨g, hg⟩ := (Matrix.vecMulLinear P).exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 hP)
  have h1 : P * LinearMap.toMatrixRight' g = 1 := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_one]
    change Matrix.toLinearMapRight' (LinearMap.toMatrixRight' g) ∘ₗ Matrix.vecMulLinear P = _
    simpa using hg
  set Q := LinearMap.toMatrixRight' g
  let := i.toAlgebra
  have key : ∀ (l : K →ₗ[k] k) {p q : ℕ} (M : Matrix (Fin p) (Fin q) k) (v : Fin p → K),
      (fun j => l ((v ᵥ* M.map i) j)) = (fun j => l (v j)) ᵥ* M := fun l p q M v => by
    funext j
    simp only [Matrix.vecMul, dotProduct, map_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [_root_.mul_comm (v s), _root_.mul_comm (l _), ← smul_eq_mul (M s j), ← map_smul, Algebra.smul_def]
    rfl
  refine ⟨c ᵥ* Q.map i, funext fun j => sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff k _).1 fun l => ?_)⟩
  obtain ⟨d, hd⟩ := h (fun j => l (c j)) fun a => by
    rw [← key, hc]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← smul_eq_mul (χ a), ← map_smul, Algebra.smul_def]
    rfl
  have e := congrFun (key l P (c ᵥ* Q.map i)) j
  rw [key, ← hd, Matrix.vecMul_vecMul d, h1, Matrix.vecMul_one, hd] at e
  rw [map_sub, e, sub_self]

theorem isEigVec_iff {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (act : OAct O G) (χ : O →+* R) {n : ℕ} {e : Fin n → (epsR R ⟶ G)} (he : IsLieBasis e)
    {A : O → Matrix (Fin n) (Fin n) R} (hA : ∀ a j, IsLieComb (A a j) e (e j ≫ act.act a))
    {c : Fin n → R} {w : epsR R ⟶ G} (hw : IsLieComb c e w) :
    EigenvectorLieDegree.IsEigVec act χ w ↔ ∀ a, c ᵥ* A a = χ a • c := by
  let b := Serre.Lie.basis act he
  have hb : (fun j => (b j).hom) = e := funext (Serre.Lie.hom_basis he)
  clear_value b
  subst hb
  obtain rfl := (Serre.Lie.isLieComb_iff c b w).1 hw
  have hA' : ∀ a j, a • b j = ∑ s, A a j s • b s := fun a j =>
    Serre.Lie.ext ((Serre.Lie.isLieComb_iff _ b _).1 (hA a j))
  have h1 : ∀ a, a • ∑ j, c j • b j = ∑ s, (c ᵥ* A a) s • b s := fun a => by
    simp only [Finset.smul_sum, smul_comm a, hA', Matrix.vecMul, dotProduct, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have h2 : ∀ a, χ a • ∑ j, c j • b j = ∑ s, (χ a • c) s • b s := fun a => by
    simp only [Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]
  refine (and_iff_right (Serre.Lie.isTangent _)).trans (Serre.Lie.mem_eig_iff_left.symm.trans ?_)
  rw [Serre.Lie.mem_eig_iff]
  refine forall_congr' fun a => ?_
  rw [h1, h2, ← b.equivFun_symm_apply, ← b.equivFun_symm_apply, EmbeddingLike.apply_eq_iff_eq]

theorem isEigBasis_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (χ : 𝓞 E →+* k), (∀ a, IsVecOver i n.φ (x a) (x' a)) → EigenvectorLieDegree.IsEigBasis t.act χ x → EigenvectorLieDegree.IsEigBasis t'.act (i.comp χ) x' := by
  intro E _ _ _ H k k' _ _ _ _ i t t' n m x x' χ hx' hx
  have hi := Indep.of_eigBasis hx
  have := t.semi.smooth
  obtain ⟨N, e, he⟩ := Chart.exists_isLieBasis t.G t.semi.smooth
  choose e' h _ using fun j => existsUnique_isVecOver n.cart.1 (e j)
  have he' := Chart.isLieBasis_baseChange i n.cart he h
  choose P hP _ using fun s => he.2 _ (hi.1 s)
  have hP' : ∀ s, IsLieComb ((Matrix.of P).map i s) e' (x' s) := fun s =>
    (lieComb_baseChange _ _ i t.G t'.G n.φ n.cart N e (x s) (P s) e' (x' s) h (hP s)).1 (hx' s)
  choose A hA _ using fun a j => he.2 (e j ≫ t.act.act a) (Serre.Lie.isTangent (a • Serre.Lie.mk t.act (e j) (he.1 j)))
  have hA' : ∀ a j, IsLieComb ((Matrix.of (A a)).map i j) e' (e' j ≫ t'.act.act a) := fun a j =>
    (lieComb_baseChange _ _ i t.G t'.G n.φ n.cart N e _ (A a j) e' _ h (hA a j)).1 (by
      have := h j
      simp only [IsVecOver] at this ⊢
      rw [Over.comp_left, Category.assoc, n.act a, ← Category.assoc, this, Category.assoc, Over.comp_left])
  have hinj := hi.vecMul_eq_zero (P := Matrix.of P) he.1 hP
  have E1 := fun c w => isEigVec_iff t.act χ he (A := fun a => Matrix.of (A a)) hA (c := c) (w := w)
  have E2 := fun c w => isEigVec_iff t'.act (i.comp χ) he' (A := fun a => (Matrix.of (A a)).map i) hA' (c := c) (w := w)
  have tx : ∀ s, IsTangent (x' s) := fun s => (hx' s).isTangent n.cart (hi.1 s)
  refine ⟨fun s => (E2 _ _ (hP' s)).2 fun a => ?_, fun w hw => ?_⟩
  · have := (E1 _ _ (hP s)).1 (hx.1 s) a
    funext j
    have := congrArg i (congrFun this j)
    simpa [Matrix.vecMul, dotProduct] using this
  · obtain ⟨c, hc, -⟩ := he'.2 w hw.1
    obtain ⟨d, hd⟩ := eig_rows_map i hinj (fun a => Matrix.of (A a)) χ (fun c hc => by
      obtain ⟨w, hw⟩ := ((LieComb.lieComb_algebra k t.G N e he.1).1 c).exists
      obtain ⟨d, hd, -⟩ := hx.2 w ((E1 _ _ hw).2 hc)
      exact ⟨d, (Indep.of_basis he).2 _ _ w ((comb_comb (P := Matrix.of P) he.1 hP _ _).1 hd) hw⟩) c
      ((E2 _ _ hc).1 hw)
    refine ⟨d, (comb_comb he'.1 hP' _ _).2 (hd ▸ hc), fun d' hd' => ?_⟩
    refine sub_eq_zero.1 (vecMul_map_eq_zero i hinj _ ?_)
    rw [Matrix.sub_vecMul, hd, (Indep.of_basis he').2 _ _ w ((comb_comb he'.1 hP' _ _).1 hd') hc, sub_self]

end GlobalTheory.EigBasisExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbasisSignatureExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.EigBasisExist

theorem exists_eigBasis_of_lieMult {k O : Type} [Field k] [CommRing O] {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    (act : OAct O G) (χ : O →+* k) {n : ℕ} (h : LieMult act (𝟙 (Sp k)) χ n) :
    ∃ x : Fin n → (epsR k ⟶ G), EigenvectorLieDegree.IsEigBasis act χ x := by
  obtain ⟨b⟩ := (Serre.Lie.lieMult_id_iff act χ n).1 h
  have hm : ∀ v : Serre.Lie act, v ∈ Serre.Lie.eig act χ ↔ EigenvectorLieDegree.IsEigVec act χ v.hom := fun v =>
    ⟨fun hv => ⟨v.isTangent, fun a => congrArg (fun z : Serre.Lie act => z.hom.left) (hv a)⟩,
      fun hv a => Serre.Lie.ext (Over.OverMorphism.ext (hv.2 a))⟩
  refine ⟨fun i => (b i : Serre.Lie act).hom, fun i => (hm _).1 (b i).2, fun w hw => ?_⟩
  let z : Serre.Lie.eig act χ := ⟨Serre.Lie.mk act w hw.1, (hm _).2 hw⟩
  have key : ∀ c : Fin n → k, IsLieComb c (fun i => (b i : Serre.Lie act).hom) w ↔ b.equivFun z = c := fun c => by
    rw [Serre.Lie.isLieComb_iff c (fun i => (b i : Serre.Lie act)) w, ← LinearEquiv.eq_symm_apply,
      Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact ⟨fun e => Serre.Lie.ext e, fun e => congrArg Serre.Lie.hom e⟩
  exact (existsUnique_congr key).2 existsUnique_eq'

theorem exists_eigBases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k) (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → (∃ x : Fin D.p → (epsR k ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act ((EigenvectorLieDegree.embIn c j τ).comp (algebraMap (𝓞 E) E)) x) ∧ ∃ x : Fin D.q → (epsR k ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act ((EigenvectorLieDegree.embIn c j (conjEmb τ)).comp (algebraMap (𝓞 E) E)) x := by
  intro E _ _ _ H D l c k _ _ j o τ hτ
  let φ : k →+* AlgebraicClosure k := algebraMap k _
  have := o.t.semi.smooth
  have d := (o.geom (AlgebraicClosure k) (spMap φ)
    (φ.comp (j.comp (IntermediateField.inclusion c.le).toRingHom))
    (by rw [spMap_comp_spMap, spMap_comp_spMap])).1
  have iff : ∀ σ : E →+* ℂ, (φ.comp ((EigenvectorLieDegree.embIn c j σ).comp (algebraMap (𝓞 E) E))) H.rt =
      (φ.comp (j.comp (IntermediateField.inclusion c.le).toRingHom)) (baseKA l).ρ ↔ σ (H.rt : E) = H.rt0 := fun σ =>
    (φ.injective.eq_iff.trans j.injective.eq_iff).trans Subtype.ext_iff
  have ne : conjEmb τ (H.rt : E) ≠ H.rt0 := fun e => by
    have e' : (starRingEnd ℂ) H.rt0 = H.rt0 := by rw [← hτ]; exact e.trans hτ.symm
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e'
    have h := H.sqrt_neg_disc_sq
    rw [hr] at h
    have h' : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h
    have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg r]
  exact ⟨exists_eigBasis_of_lieMult _ _ ((LieExt.lieMult_extend_iff φ _ _ _ _).1 ((d _).1 ((iff τ).2 hτ))),
    exists_eigBasis_of_lieMult _ _ ((LieExt.lieMult_extend_iff φ _ _ _ _).1 ((d _).2 fun e => ne ((iff _).1 e)))⟩

end GlobalTheory.EigBasisExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolynomialsBoundedFinite
section
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.GeoFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_coeff_le {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) (τ : E →+* ℂ) (i : ℕ) :
    ‖τ (P.coeff i)‖ ≤ n.choose i := by
  obtain ⟨hm, hd, -, hr⟩ := hP
  have h := Polynomial.coeff_le_of_roots_le (f := τ) (B := 1) i hm (IsAlgClosed.splits _)
    (fun z hz => (hr τ z hz).le)
  rw [one_pow, one_mul, hd, Polynomial.coeff_map] at h
  exact h

theorem valued_algebraMap (w : Pl E) (k : E) :
    Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
  Formalism.UG.P.levelaf_valued_algebraMap w k

theorem valuation_conjE (w : Pl E) (k : E) :
    w.valuation E (GlobalTheory.SplitPts.conjE E k) = (conjSrc (GlobalTheory.SplitPts.conjE E) w).valuation E k := by
  have h := (conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.2 (algebraMap E _ k)
  rw [(conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.1, valued_algebraMap, valued_algebraMap] at h
  exact h

theorem valuation_coeff_le {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) {γ : Pl E → WithZero (Multiplicative ℤ)} (hγ0 : ∀ w, γ w ≠ 0)
    {P : E[X]} (hP : P ∈ Ell E n) (hPS : ∀ w ∈ S, (∀ i, Valued.v ((atPl w P).coeff i) ≤ γ w) ∧
      (γ w)⁻¹ ≤ Valued.v ((atPl w P).coeff 0)) (w : Pl E) (i : ℕ) :
    w.valuation E (P.coeff i) ≤ if w ∈ S then γ w else γ (conjSrc (GlobalTheory.SplitPts.conjE E) w) ^ 2 := by
  have hv : ∀ u ∈ S, (∀ j, u.valuation E (P.coeff j) ≤ γ u) ∧ (γ u)⁻¹ ≤ u.valuation E (P.coeff 0) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hPS u hu
    refine ⟨fun j => ?_, ?_⟩
    · have := h1 j
      rwa [atPl, Polynomial.coeff_map, valued_algebraMap] at this
    · rwa [atPl, Polynomial.coeff_map, valued_algebraMap] at h2
  split_ifs with hw
  · exact (hv w hw).1 i
  obtain ⟨hm, hd, -, hr⟩ := hP
  have hrec := GlobalTheory.T.monic_coeff_natDegree_sub_eq_mul_cmConj E n P hm hd hr
  obtain ⟨u, ⟨hu, huw⟩, -⟩ := hS w
  rcases GlobLev.eq_or_eq_conjSrc huw with rfl | rfl
  · exact absurd hu hw
  set u := conjSrc (GlobalTheory.SplitPts.conjE E) w
  by_cases hi : i ≤ n
  swap
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Valuation.map_zero]
    exact zero_le'
  have hci : P.coeff i = P.coeff 0 * GlobalTheory.SplitPts.conjE E (P.coeff (n - i)) := by
    have := hrec (n - i) (Nat.sub_le n i)
    rwa [Nat.sub_sub_self hi] at this
  have hc0 : P.coeff 0 * GlobalTheory.SplitPts.conjE E (P.coeff 0) = 1 := by
    have := hrec 0 (Nat.zero_le n)
    rw [Nat.sub_zero, ← hd, ← Polynomial.leadingCoeff, hm.leadingCoeff] at this
    exact this.symm
  have hv0 : w.valuation E (P.coeff 0) * u.valuation E (P.coeff 0) = 1 := by
    rw [← valuation_conjE, ← Valuation.map_mul, hc0, Valuation.map_one]
  have hw0 : w.valuation E (P.coeff 0) ≤ γ u := by
    rw [eq_inv_of_mul_eq_one_left hv0]
    have hu0 : u.valuation E (P.coeff 0) ≠ 0 := right_ne_zero_of_mul_eq_one hv0
    exact (inv_le_comm₀ (zero_lt_iff.2 hu0) (zero_lt_iff.2 (hγ0 u))).2 (hv u hu).2
  rw [hci, Valuation.map_mul, valuation_conjE, sq]
  exact mul_le_mul' hw0 ((hv u hu).1 _)

theorem finite_ell_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S →
    ∀ γ : Pl E → WithZero (Multiplicative ℤ), (∀ w, γ w ≠ 0) → (∀ᶠ w in cofinite, γ w = 1) →
    {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, (∀ i, Valued.v ((atPl w P).coeff i) ≤ γ w) ∧
      (γ w)⁻¹ ≤ Valued.v ((atPl w P).coeff 0)}.Finite := by
  intro E _ _ _ n S hS γ hγ0 hγ1
  set σ := GlobalTheory.SplitPts.conjE E
  set β : Pl E → WithZero (Multiplicative ℤ) := fun w => if w ∈ S then γ w else γ (conjSrc σ w) ^ 2 with hβ
  have hβ1 : ∀ᶠ w in cofinite, β w ≤ 1 := by
    have h2 : ∀ᶠ w in cofinite, γ (conjSrc σ w) = 1 := (conjSrc_injective σ).tendsto_cofinite.eventually hγ1
    filter_upwards [hγ1, h2] with w h1 h2
    simp only [hβ]
    split_ifs
    · exact h1.le
    · rw [h2, one_pow]
  obtain ⟨D, hD0, hD⟩ := GlobalTheory.T.exists_common_denominator_of_valuation_le_cofinite E β hβ1
  have hD0' : (D : E) ≠ 0 := by exact_mod_cast hD0
  set r : ℕ → ℝ := fun i => (∑ τ : E →+* ℂ, ‖τ (D : E)‖) * n.choose i with hr
  set X : Fin (n + 1) → Set E := fun i => {x | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ r i} with hXd
  have hX : ∀ i, (X i).Finite := fun i => Embeddings.finite_of_norm_le E ℂ (r i)
  refine Set.Finite.of_finite_image (f := fun (P : E[X]) (i : Fin (n + 1)) => (D : E) * P.coeff i)
    ((Set.Finite.pi hX).subset ?_) ?_
  · rintro _ ⟨P, ⟨hP, hPS⟩, rfl⟩ i -
    refine ⟨hD _ fun w => valuation_coeff_le hS hγ0 hP hPS w i, fun φ => ?_⟩
    rw [map_mul, norm_mul]
    exact mul_le_mul (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (D : E)‖) (fun τ _ => norm_nonneg _)
      (Finset.mem_univ φ)) (norm_coeff_le hP φ i) (norm_nonneg _)
      (Finset.sum_nonneg fun τ _ => norm_nonneg _)
  · intro P hP Q hQ hPQ
    ext k
    by_cases hk : k ≤ n
    · exact mul_left_cancel₀ hD0' (congrFun hPQ ⟨k, Nat.lt_succ_of_le hk⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ.1.2.1]; omega)]

end GlobalTheory.BCT.GeoFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSumDegreeFormula
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory

theorem card_embeddings_restrict_eq_finrank (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k']
    [Algebra k k'] (τ : k →+* ℂ) :
    Nat.card {σ : k' →+* ℂ // σ.comp (algebraMap k k') = τ} = Module.finrank k k' := by
  letI : Algebra k ℂ := τ.toAlgebra
  haveI : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  rw [← AlgHom.card k k' ℂ, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr ⟨fun σ => { σ.1 with commutes' := fun x => RingHom.congr_fun σ.2 x },
    fun φ => ⟨φ.toRingHom, RingHom.ext fun x => φ.commutes x⟩, fun σ => rfl, fun φ => rfl⟩

theorem finrank_mul_sum_embeddings_comp (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k']
    (i : k →+* k') (f : (k →+* ℂ) → ℝ) :
    (Module.finrank ℚ k : ℝ) * ∑ σ : k' →+* ℂ, f (σ.comp i)
      = (Module.finrank ℚ k' : ℝ) * ∑ σ : k →+* ℂ, f σ := by
  classical
  letI : Algebra k k' := i.toAlgebra
  have h1 : ∑ σ : k' →+* ℂ, f (σ.comp i) = (Module.finrank k k' : ℝ) * ∑ σ : k →+* ℂ, f σ := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun σ : k' →+* ℂ => σ.comp i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f τ) (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]),
      Finset.sum_const, nsmul_eq_mul, ← card_embeddings_restrict_eq_finrank k k' τ,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [h1, ← _root_.mul_assoc, ← Module.finrank_mul_finrank ℚ k k', Nat.cast_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatGoodOfBlockExtensionTwistStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matGood_of_block_extension_twist : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (f n : ℕ) (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (ρ : ↥(GK K) →* GL (Fin 1) ↥(OL LL)) (r₂ : ↥(GK K) →* GL (Fin (n + 1)) ↥(OL LL)) (U U' : ZMod f → Multiset ℤ) (B : Mx ↥(OL LL) n (n + 1)) (C : Mx ↥(OL LL) 1 (n + 1)), MatGood P emb r U → MatGood P emb ρ U' → Tw r₂ r B → Tw r₂ ρ C → (∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) → MatGood P emb r₂ (fun i => U i + U' i) := by
  first | exact @GlobalTheory.WachPlace.FullRankSum.matGood_sum | exact GlobalTheory.WachPlace.FullRankSum.matGood_sum | (intros; apply GlobalTheory.WachPlace.FullRankSum.matGood_sum <;> assumption)
end

