import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0086
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDuality
import Formalism.LocalToGlobal.Columns.CoefModB
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralExpNegMulSumNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

namespace GlobalTheory.CartanInt

theorem integral_exp_neg_mul_norm_complex (b : ℝ) (hb : 0 < b) :
    ∫ z : ℂ, Real.exp (-(b * ‖z‖)) = 2 * Real.pi / b ^ 2 := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 1) (b := b) le_rfl hb
  simp only [Real.rpow_one, neg_mul, div_one] at h
  rw [h]
  have h3 : Real.Gamma (2 + 1) = 2 := by
    have := Real.Gamma_nat_eq_factorial 2
    simpa [Nat.factorial] using this
  rw [h3, Real.rpow_neg hb.le, Real.rpow_two]
  field_simp

theorem lintegral_exp_neg_mul_sum_norm (p q : ℕ) (b : ℝ) (hb : 0 < b) :
    ∫⁻ B : Fin p → Fin q → ℂ, ENNReal.ofReal (Real.exp (-(b * ∑ i, ∑ j, ‖B i j‖))) =
      ENNReal.ofReal ((2 * Real.pi / b ^ 2) ^ (p * q)) := by
  have h1 := integral_exp_neg_mul_norm_complex b hb
  have hne : (2 * Real.pi / b ^ 2) ≠ 0 := by positivity
  have hi : Integrable (fun z : ℂ => Real.exp (-(b * ‖z‖))) :=
    Integrable.of_integral_ne_zero (by rw [h1]; exact hne)
  have hprod : ∀ B : Fin p → Fin q → ℂ, Real.exp (-(b * ∑ i, ∑ j, ‖B i j‖)) =
      ∏ i, ∏ j, Real.exp (-(b * ‖B i j‖)) := by
    intro B
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  have hrow : Integrable (fun v : Fin q → ℂ => ∏ j, Real.exp (-(b * ‖v j‖))) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ (z : ℂ) => Real.exp (-(b * ‖z‖))) (fun _ => hi)
  have hall : Integrable (fun B : Fin p → Fin q → ℂ => ∏ i, ∏ j, Real.exp (-(b * ‖B i j‖))) := by
    rw [volume_pi]
    exact Integrable.fintype_prod
      (f := fun _ (v : Fin q → ℂ) => ∏ j, Real.exp (-(b * ‖v j‖))) (fun _ => hrow)
  have hrowv : ∫ v : Fin q → ℂ, ∏ j, Real.exp (-(b * ‖v j‖)) = (2 * Real.pi / b ^ 2) ^ q := by
    rw [volume_pi, integral_fintype_prod_eq_prod (f := fun _ (z : ℂ) => Real.exp (-(b * ‖z‖)))]
    simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hallv : ∫ B : Fin p → Fin q → ℂ, ∏ i, ∏ j, Real.exp (-(b * ‖B i j‖)) =
      (2 * Real.pi / b ^ 2) ^ (p * q) := by
    rw [volume_pi, integral_fintype_prod_eq_prod
      (f := fun _ (v : Fin q → ℂ) => ∏ j, Real.exp (-(b * ‖v j‖)))]
    simp only [hrowv, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, mul_comm q p]
  simp only [hprod]
  rw [← hallv, ofReal_integral_eq_lintegral_ofReal hall]
  exact Filter.Eventually.of_forall fun B => by positivity

end GlobalTheory.CartanInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableCoshPow
section
noncomputable section
namespace GlobalTheory.CoshPowMeas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open Filter Topology

variable {p q : ℕ}

theorem continuous_cartanB : Continuous (cartanB : UpqT p q → Matrix (Fin p) (Fin q) ℂ) := by
  have h : Continuous fun g : UpqT p q => GlobalTheory.PolarLogCont.halfLog (UpqT.mat g) :=
    GlobalTheory.PolarLogCont.continuousOn_halfLog.comp_continuous GlobalTheory.UpqTopology.continuous_mat
      fun g => Units.isUnit (show Formalism.UG.Upq p q from g).1
  have hc : Continuous fun M : Mat p q => M.toBlocks₁₂ := by
    refine continuous_matrix fun i j => ?_
    exact continuous_id.matrix_elem (Sum.inl i) (Sum.inr j)
  exact hc.comp h

def sPad (B : Matrix (Fin p) (Fin q) ℂ) (j : Fin q) : ℝ := if (j : ℕ) < p then singVal B j else 0

theorem exists_gram (B : Matrix (Fin p) (Fin q) ℂ) : ∃ V : Matrix (Fin q) (Fin q) ℂ, Vᴴ * V = 1 ∧
    Bᴴ * B = V * Matrix.diagonal (fun j => ((sPad B j : ℝ) : ℂ) ^ 2) * Vᴴ := by
  obtain ⟨U, hU, V, hV, hB⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q B
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have h2 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  refine ⟨V, h2, ?_⟩
  set D : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0 with hD
  have hDD : Dᴴ * D = Matrix.diagonal (fun j => ((sPad B j : ℝ) : ℂ) ^ 2) := by
    ext j j'
    rw [Matrix.mul_apply]
    by_cases hj : (j : ℕ) < p
    · rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin p)]
      · by_cases hjj : j = j'
        · subst hjj
          simp [hD, sPad, hj, singVal, sq]
        · have : (j : ℕ) ≠ j' := fun h => hjj (Fin.ext h)
          simp [hD, hjj, this]
      · intro i _ hi
        have : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
        simp [hD, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · by_cases hjj : j = j'
        · subst hjj
          simp [sPad, hj]
        · simp [hjj]
      · intro i _
        have : (i : ℕ) ≠ j := fun h => hj (h ▸ i.isLt)
        simp [hD, this]
  rw [← hDD]
  conv_lhs => rw [hB]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, h1, Matrix.one_mul]

theorem conj_pow {n : Type} [Fintype n] [DecidableEq n] (V A : Matrix n n ℂ) (h : Vᴴ * V = 1) (k : ℕ) :
    (V * A * Vᴴ) ^ k = V * A ^ k * Vᴴ := by
  induction k with
  | zero => simp [mul_eq_one_comm.1 h]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, h, Matrix.one_mul]

def coshSum (n : ℕ) (B : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  ∑ k ∈ Finset.range n, (((2 * k).factorial : ℕ) : ℂ)⁻¹ • (Bᴴ * B) ^ k

theorem continuous_coshSum (n : ℕ) : Continuous (coshSum n : Matrix (Fin p) (Fin q) ℂ → _) := by
  unfold coshSum
  refine continuous_finset_sum _ fun k _ => ?_
  have h : Continuous fun B : Matrix (Fin p) (Fin q) ℂ => Bᴴ * B :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  exact (h.pow k).const_smul ((((2 * k).factorial : ℕ) : ℂ)⁻¹)

theorem det_coshSum (n : ℕ) (B : Matrix (Fin p) (Fin q) ℂ) : (coshSum n B).det.re =
    ∏ j : Fin q, ∑ k ∈ Finset.range n, sPad B j ^ (2 * k) / ((2 * k).factorial : ℕ) := by
  obtain ⟨V, hV, h⟩ := exists_gram B
  have e : coshSum n B = V * Matrix.diagonal (fun j => ((∑ k ∈ Finset.range n,
      sPad B j ^ (2 * k) / ((2 * k).factorial : ℕ) : ℝ) : ℂ)) * Vᴴ := by
    have e1 : Matrix.diagonal (fun j => ((∑ k ∈ Finset.range n,
      sPad B j ^ (2 * k) / ((2 * k).factorial : ℕ) : ℝ) : ℂ)) = ∑ k ∈ Finset.range n,
        (((2 * k).factorial : ℕ) : ℂ)⁻¹ • (Matrix.diagonal (fun j => ((sPad B j : ℝ) : ℂ) ^ 2)) ^ k := by
      ext i j
      simp only [Matrix.diagonal_pow, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply]
      split_ifs
      · push_cast
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [pow_mul, div_eq_inv_mul]
      · simp
    rw [e1, coshSum, h, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conj_pow _ _ hV, Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.det_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.det_diagonal,
    ← Complex.ofReal_prod, Complex.ofReal_re]

theorem prod_cosh_sPad (B : Matrix (Fin p) (Fin q) ℂ) :
    ∏ j : Fin q, Real.cosh (sPad B j) = ∏ i ∈ Finset.range (min p q), Real.cosh (singVal B i) := by
  unfold sPad
  rw [Fin.prod_univ_eq_prod_range (fun j => Real.cosh (if j < p then singVal B j else 0)) q]
  symm
  refine Finset.prod_subset_one_on_sdiff (Finset.range_subset_range.2 (min_le_right p q)) ?_ ?_
  · intro x hx
    have : ¬ x < p := by
      simp only [Finset.mem_sdiff, Finset.mem_range] at hx; omega
    simp [this]
  · intro x hx
    have : x < p := by
      simp only [Finset.mem_range] at hx; omega
    simp [this]

theorem tendsto_det_coshSum (B : Matrix (Fin p) (Fin q) ℂ) :
    Tendsto (fun n => (coshSum n B).det.re) atTop
      (𝓝 (∏ i ∈ Finset.range (min p q), Real.cosh (singVal B i))) := by
  simp only [det_coshSum, ← prod_cosh_sPad]
  exact tendsto_finset_prod _ fun j _ => (Real.hasSum_cosh (sPad B j)).tendsto_sum_nat

theorem measurable_coshPow : ∀ (p q : ℕ) (c : ℝ), Measurable (coshPow c : UpqT p q → ℝ) := by
  intro p q c
  have : BorelSpace (UpqT p q) := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.2.2.1
  have h : Measurable fun g : UpqT p q =>
      ∏ i ∈ Finset.range (min p q), Real.cosh (singVal (cartanB g) i) := by
    refine measurable_of_tendsto_metrizable
      (f := fun n (g : UpqT p q) => (coshSum n (cartanB g)).det.re) (fun n => ?_)
      (tendsto_pi_nhds.2 fun g => tendsto_det_coshSum _)
    exact (Complex.continuous_re.comp
      (((continuous_coshSum n).comp continuous_cartanB).matrix_det)).measurable
  have e : (coshPow c : UpqT p q → ℝ) = fun g =>
      (∏ i ∈ Finset.range (min p q), Real.cosh (singVal (cartanB g) i)) ^ (-c) := by
    funext g
    exact Real.finset_prod_rpow _ _ (fun i _ => (Real.cosh_pos _).le) _
  rw [e]
  exact h.pow_const _

end GlobalTheory.CoshPowMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MinkowskiBoundComapLattice
section
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.Compare

def conjHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E →+* E)

section Space

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Space

section Sum

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι C : Type} [Fintype ι] {n N : ℕ}

end Sum

section DualSpace

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ}

end DualSpace

section Nabla

variable {K : Type} [Field K] [NumberField K] {ι C : Type} [Fintype ι] {n N : ℕ}

open Classical in

def blk {F I : Type} [Zero F] (e : Fin N ≃ C × I) (M : Matrix I I F) : Matrix (Fin N) (Fin N) F :=
  Matrix.of fun a b => if (e a).1 = (e b).1 then M (e a).2 (e b).2 else 0

omit [NumberField K] in
theorem pairK_basis [StarRing K] (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (i j : VVIdx lam) :
    pairK lam (fun τ => (g τ : Matrix (Fin n) (Fin n) K)) (bVV K lam i) (bVV K lam j) =
      pairBK lam (bVV K lam i) (rhoK lam g (bVV K lam j)) := by
  rw [pairK_apply, pairP_eq_pairB, pairBK_apply, rhoK_coe]
  congr 2
  rw [bVV_coe]
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  rw [hQ, MvPolynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

def gramB (K : Type) [Field K] (lam : ι → DomWeight n) : Matrix (VVIdx lam) (VVIdx lam) K :=
  Matrix.of fun i j => pairBK lam (bVV K lam i) (bVV K lam j)

omit [NumberField K] in
theorem gramB_transpose (lam : ι → DomWeight n) : (gramB K lam)ᵀ = gramB K lam := by
  ext i j
  simp only [gramB, Matrix.transpose_apply, Matrix.of_apply, pairBK_apply]
  exact pairingBSymm_holds K ι n lam _ _

theorem hdualFr_triv {m : ℕ} (P : Matrix (Fin m) (Fin m) K) (M : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) :
    x ∈ @hdualFr K _ m starRingOfComm P M ↔ P *ᵥ x ∈ dualFr M := by
  change (∀ y ∈ M, y ⬝ᵥ (P *ᵥ x) ∈ (1 : Submodule (𝓞 K) K)) ↔ ∀ y ∈ M, (P *ᵥ x) ⬝ᵥ y ∈ (1 : Submodule (𝓞 K) K)
  simp only [dotProduct_comm]

end Nabla

section Clauses

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {ι C : Type} [Fintype ι] {n N : ℕ}
  (emb : ι → E →+* K) (lam : ι → DomWeight n) (R : ℝ) (J : Matrix (Fin n) (Fin n) E)
  (L : C → Submodule (𝓞 E) (Fin n → E)) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ)

def WeylClause : Prop :=
  IsMetric ((sumGram lam e (gramK emb J))⁻¹)ᵀ X →
    TestLatticeCondition N X (dualFr (sumLat lam e fun c => delAt emb lam (L c))) (bound (Fintype.card ι) n R)

def WeylClauseDual : Prop :=
  IsMetric ((sumGram lam e (gramKd emb J))⁻¹)ᵀ X →
    TestLatticeCondition N X (dualFr (sumLat lam e fun c => delAtr emb lam (L c))) (bound (Fintype.card ι) n R)

def NablaClause : Prop :=
  IsMetric (sumGram lam e (gramK emb J)) X →
    TestLatticeCondition N X (sumLat lam e fun c => nabAt emb lam (L c)) (bound (Fintype.card ι) n R)

def NablaClauseDual : Prop :=
  IsMetric (sumGram lam e (gramKd emb J)) X →
    TestLatticeCondition N X (sumLat lam e fun c => nabAtr emb lam (L c)) (bound (Fintype.card ι) n R)

end Clauses

def Under (P : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (_ : E →+* E)
    (ι : Type) [Fintype ι] (_ : ι → E →+* K) (n : ℕ) (lam : ι → DomWeight n) (_ : ℝ) (_ : Matrix (Fin n) (Fin n) E)
    (C : Type) (_ : C → Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (_ : Fin N ≃ C × VVIdx lam)
    (_ : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), Prop) : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (v₀ : InfinitePlace K), Formalism.DivisionValues.IsConjAt v₀ →
  ∀ (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) →
  ∀ (ι : Type) [Fintype ι] (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) →
  ∀ (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R →
  ∀ (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) →
  ∀ (C : Type) [Nonempty C] (L : C → Submodule (𝓞 E) (Fin n → E)), (∀ c, IsSelfDualE cE J (L c)) →
  ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ),
    P E K cE ι emb n lam R J C L N e X

theorem slopeE_eq : SlopeE = Under fun _ _ _ _ _ _ _ _ _ _ emb _ lam R J _ L _ e X =>
    WeylClause emb lam R J L e X ∧ NablaClause emb lam R J L e X ∧
      WeylClauseDual emb lam R J L e X ∧ NablaClauseDual emb lam R J L e X := rfl

def FirstCM : Prop := Under fun E _ _ _ _ _ _ cE _ _ emb n lam R J _ L _ e X =>
  cE ≠ RingHom.id E → 1 ≤ n → WeylClause emb lam R J L e X

def First : Prop := Under fun _ _ _ _ _ _ _ _ _ _ emb _ lam R J _ L _ e X => WeylClause emb lam R J L e X

def FirstDegenerate : Prop := Under fun E _ _ _ _ _ _ cE _ _ emb n lam R J _ L _ e X =>
  cE = RingHom.id E ∨ n = 0 → WeylClause emb lam R J L e X

def SlopeCM : Prop := Under fun E _ _ _ _ _ _ cE _ _ emb n lam R J _ L _ e X =>
  cE ≠ RingHom.id E → 1 ≤ n → WeylClause emb lam R J L e X ∧ NablaClause emb lam R J L e X ∧
      WeylClauseDual emb lam R J L e X ∧ NablaClauseDual emb lam R J L e X

end GlobalTheory.TestLat.Compare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldNonempty
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_nonempty : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ),
    Nonempty (Frac Ω ε) := by
  intro Ω _ _ _ ε
  classical
  haveI : IsDomain (ring ε.range) := GlobalTheory.T.modularFunctionRingOver_isDomain ε.range
  obtain ⟨hmem, hconst⟩ := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  obtain ⟨-, huniq, hC, -, -⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  obtain ⟨e, he_inj, he_exp⟩ := GlobalTheory.T.exists_injective_cuspExpansion_ringHom Ω ε
  obtain ⟨hexp_mem, -, -, -, -, -⟩ := GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε
  obtain ⟨⟨G, hG⟩, hmd, -, -, hHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨-, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units

  let cst : Ω →+* ring ε.range :=
    { toFun := fun x => ⟨fun _ => ε x, (hmem _).2 (hconst _ ⟨x, rfl⟩)⟩
      map_one' := Subtype.ext (funext fun _ => by simp)
      map_mul' := fun x y => Subtype.ext (funext fun _ => by simp)
      map_zero' := Subtype.ext (funext fun _ => by simp)
      map_add' := fun x y => Subtype.ext (funext fun _ => by simp) }
  have hcst : ∀ x, ((cst x : ring ε.range) : ℍ → ℂ) = fun _ => ε x := fun _ => rfl
  have hec : ∀ x, e (cst x) = algebraMap Ω (HahnSeries ℚ Ω) x := by
    intro x
    refine huniq _ _ _ (he_exp (cst x)) ?_
    convert hC x using 1
    · rfl
    · simp [HahnSeries.algebraMap_apply']

  have hsl := fun g : GQ => GlobalTheory.T.exists_ringEquiv_compGLTwoPosRatFun ε.range g hexp_mem
  choose σ hσ using hsl
  have hslc : ∀ g x, σ g (cst x) = cst x := by
    intro g x
    apply Subtype.ext
    rw [hσ]
    rfl

  have hga := fun s : Ω ≃ₐ[ℚ] Ω => GlobalTheory.T.exists_ringEquiv_fn_ring_coeff_eq_apply Ω ε s.toRingEquiv
  choose τ hτ using hga

  let A : ring ε.range →+* Mero := G.comp (ring ε.range).subtype
  have hA : ∀ a : ring ε.range, A a = ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) := fun a => hG a
  have hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs :=
    fun a => (hmd _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ ((hmem _).1 a.2))
  have hAunit : ∀ a, a ≠ 0 → IsUnit (A a) := by
    intro a ha
    rw [hA]
    refine (hunit _ (hdiff a) ?_).2
    intro h0
    apply ha
    have h0' : ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((up ((0 : ring ε.range) : ℍ → ℂ) : ℂ → ℂ) : Mero) := by
      rw [h0, ← hA, map_zero]
    have heq := hid _ _ (hdiff a) (hdiff 0) h0'
    apply Subtype.ext
    funext t
    have := heq t (hHs t)
    simpa [up, UpperHalfPlane.ofComplex_apply] using this
  obtain ⟨K, fK, aK, io, e', sl', ga', A', hinj, hsurj, hioc, he', hsl', hga', hA'⟩ :=
    GlobalTheory.T.exists_fractionField_extension_of_maps Ω (ring ε.range) (HahnSeries ℚ Ω) Mero GQ (Ω ≃ₐ[ℚ] Ω) cst e σ τ A he_inj hec hslc hAunit
  refine ⟨{
    K := K
    fld := fK
    alg := aK
    io := io
    io_inj := hinj
    io_surj := hsurj
    io_c := fun x a ha => ?_
    exp := e'
    exp_io := fun a => ?_
    sl := sl'
    sl_io := fun g a a' ha => ?_
    gal := ga'
    gal_exp := fun s f r => ?_
    an := A'
    an_io := fun a => ?_ }⟩
  · have : a = cst x := Subtype.ext ha
    rw [this, hioc]
  · rw [he']
    exact he_exp a
  · rw [hsl']
    congr 1
    exact Subtype.ext ((hσ g a).trans ha.symm)
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω (s : Ω →+* Ω) 1 (fun _ => 1) one_pos rfl (fun _ _ => (mul_one 1).symm)
    have hΦ' : ∀ h r, (Φ h).coeff r = s (h.coeff r) := by
      intro h r
      have := hΦ h r
      simpa using this
    have key : ∀ a, e' (ga' s (io a)) = Φ (e' (io a)) := by
      intro a
      rw [hga', he', he']
      ext r
      rw [hτ s a (e a) (e (τ s a)) (he_exp a) (he_exp _) r, hΦ']
      rfl
    obtain ⟨a, b, hb, hf⟩ := hsurj f
    have hib : io b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hf' : f = io a * (io b)⁻¹ := by rw [← hf, mul_assoc, mul_inv_cancel₀ hib, mul_one]
    have hfe : e' (ga' s f) = Φ (e' f) := by
      rw [hf']
      simp only [map_mul, map_inv₀, key]
    rw [hfe, hΦ']
  · rw [hA', hA]
    rfl

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityModularFunctionFractionField
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNRecip

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (M : ℕ) (f : T.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f) → ∀ ζ : Ω, IsPrimitiveRoot ζ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s ζ = ζ ^ d → ∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  intro Ω _ _ _ ε T M f hM hf ζ hζ s d hsd γ γ' hc
  obtain ⟨N₀, hN₀, hrec⟩ := GlobalTheory.T.exists_level_gal_sl_commute Ω ε T f
  set N := N₀ * M with hNdef
  have hN : 0 < N := Nat.mul_pos hN₀ hM
  obtain ⟨⟨d', hd'⟩, hu⟩ := GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI Ω ε s N hN
  obtain ⟨u, hu1, -⟩ := hu d' hd'
  have hunit : IsUnit ((d' : ℤ) : ZMod N) := hu1 ▸ u.isUnit
  set ω := eOm ε (1 / (N : ℚ)) with hω
  have hωp : IsPrimitiveRoot ω N := (GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε).2.2.2.2.1 N hN
  have hωM : IsPrimitiveRoot (ω ^ N₀) M := hωp.pow hN rfl
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨i, -, hi⟩ := hωM.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hsζ : s ζ = ζ ^ d' := by
    rw [← hi, map_pow, map_pow, hd', ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
    ring_nf
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have hdd : (d : ZMod M) = d' := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have := (hζ.zpow_eq_one_iff_dvd (d' - d)).1 (by
      rw [zpow_sub₀ hζ0, ← hsd, ← hsζ, div_self]; exact (map_ne_zero s).2 hζ0)
    exact this
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.slTwoDiagConjCongruence_lift_level M N d d' hN (Dvd.intro_left N₀ rfl) hdd hunit
  obtain ⟨γ'', hc'', hκ⟩ := hl1 γ γ' hc
  have hact := GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T
  have hinv : ∀ δ' ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL δ') (T.gal s f) = T.gal s f := by
    intro δ' hδ'
    obtain ⟨δ, hδ, hcδ⟩ := hl2 δ' hδ'
    have := hrec N hN (Dvd.intro M rfl) s d' hd' δ δ' hcδ
    rw [hf δ hδ] at this
    exact this.symm
  rw [hrec N hN (Dvd.intro M rfl) s d' hd' γ γ'' hc'']
  have hγ' : γ' = (γ' * γ''⁻¹) * γ'' := by group
  rw [hγ', map_mul, hact.2, hinv _ hκ]

end GlobalTheory.FNRecip
end

