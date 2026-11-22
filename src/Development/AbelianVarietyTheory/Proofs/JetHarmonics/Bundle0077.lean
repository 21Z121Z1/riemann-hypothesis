import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0008
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0071

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoefHasDerivAt
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

namespace GlobalTheory.TensorStd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable def coefL {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => herm H (g *ᵥ v) w
      map_add' := fun g h => by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c g => by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul] }

theorem coefL_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    coefL H v w g = herm H (g *ᵥ v) w := rfl

theorem coef_hasDerivAt {k r : ℕ} (X : Mx k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    HasDerivAt (fun t : ℝ => herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ v) w)
      (herm (Hpk k r) (X *ᵥ v) w) 0 := by
  have h1 := B5.curve_hasDerivAt (1 : Mx k r) X 0
  simp only [Matrix.one_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at h1
  exact ((coefL (Hpk k r) v w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1

theorem hpart_sum {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H Z + Complex.I • hpart2 H Z = Z := by
  unfold hpart1 hpart2
  rw [smul_smul]
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [this, ← smul_add]
  have : Z - H⁻¹ * Zᴴ * H + (Z + H⁻¹ * Zᴴ * H) = (2 : ℂ) • Z := by rw [two_smul]; abel
  rw [this, smul_smul]; norm_num

theorem dOp_tensor {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (V →L[ℂ] V)} {B : Fin k → (Fin (2 * r + k + 1) → ℂ)}
    {πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))}
    (hπ : IsRepW k r z π) (hπt : IsRepW k r z πt) (hB : IsFrameOf k r [z] B)
    (hf : ∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d))
    {X : Mx k r} (hX : InLieW k r z X) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    dOp πt X y c = dOp π X (y c) + ∑ d, herm (Hpk k r) (X *ᵥ B d) (B c) • y d := by
  have h1 := dOp_hasDeriv hπt.1 hπt.2 hX
  have h2 := dOp_hasDeriv hπ.1 hπ.2 hX
  have h3 : HasDerivAt (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) (dOp πt X y c) 0 :=
    (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin k => V) c).comp
      (ContinuousLinearMap.apply ℂ _ y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h4 : ∀ d, HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (y d)) (dOp π X (y d)) 0 := fun d =>
    ((ContinuousLinearMap.apply ℂ V (y d)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h5 := HasDerivAt.fun_sum (u := Finset.univ) fun d _ => (coef_hasDerivAt X (B d) (B c)).fun_smul (h4 d)
  have h6 : (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) = fun t : ℝ => ∑ d,
      herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ B d) (B c) • π (NormedSpace.exp ((t : ℂ) • X)) (y d) :=
    funext fun t => hf _ (exp_uw hX t) y c
  rw [h6] at h3
  rw [h3.unique h5]
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, hπ.1.1, hB.2.1,
    Finset.sum_add_distrib, one_apply_eq_self]
  simp

theorem EB_tensor_std : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsRepW k r z πt → IsFrameOf k r [z] B → (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) → ∀ a b y c, EB πt B a b y c = EB π B a b (y c) + if c = a then y b else 0 := by
  intro V _ _ _ k r z π B πt _ _ hπ hπt hB hf a b y c
  obtain ⟨l1, l2⟩ := frame_lie hB a b
  have e1 := dOp_tensor hπ hπt hB hf l1 y c
  have e2 := dOp_tensor hπ hπt hB hf l2 y c
  have e3 : ∀ d, herm (Hpk k r) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b) *ᵥ B d) (B c) +
      Complex.I * herm (Hpk k r) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b) *ᵥ B d) (B c) =
      if d = b then (if c = a then 1 else 0) else 0 := by
    intro d
    rw [← coefL_apply, ← coefL_apply, ← smul_eq_mul Complex.I, ← map_smul, ← map_add, hpart_sum, coefL_apply,
      Qx8.unitB_mulVec, hB.2.1]
    have := hB.2.1 a c
    by_cases hd : d = b
    · subst hd
      have e : herm (Hpk k r) ((1 : ℂ) • B a) (B c) = herm (Hpk k r) (B a) (B c) := by rw [one_smul]
      rw [if_pos rfl, if_pos rfl, e, this]
      simp only [eq_comm]
    · simp [hd, herm]
  show dOp πt _ y c + Complex.I • dOp πt _ y c = (dOp π _ (y c) + Complex.I • dOp π _ (y c)) + _
  rw [e1, e2, smul_add, Finset.smul_sum, add_add_add_comm, ← Finset.sum_add_distrib]
  congr 1
  simp only [smul_smul, ← add_smul, e3]
  by_cases hc : c = a <;> simp [hc]

end GlobalTheory.TensorStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyCompatibleStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_tensor_cayley_compatible : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDS ε (muI s)) → TensRaw dualM R RI io pr → IsUnit Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), (∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y)) ∧ (∀ s a b x, pr' s (dualTens E a b x) = F s a b (pr' s x)) ∧ (∀ x, ∑ s, io' s (pr' s x) = x) ∧ (∀ s y, pr' s (io' s y) = y) ∧ (∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0) ∧ (∀ s y d, ((io' s y d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • io s c (y : (RI s).H)) ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  first | exact @GlobalTheory.RawTens.rawTens | exact GlobalTheory.RawTens.rawTens | (intros; apply GlobalTheory.RawTens.rawTens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualMatrixFrameFvecStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_matrix_frame_fvec : ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (e : Fin (r + 1 + (r + k)) ≃ Fin (2 * r + k + 1)), inWb k r z' → 0 < Tz k r z' → ∃ Q : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ, Q.det ≠ 0 ∧ (∀ (i j : Fin (r + 1)), ∑ d, Q (Fin.castAdd (r + k) i) d * fvec k r z' j (e d) = if i = j then 1 else 0) ∧ ∀ (i : Fin (r + k)) (j : Fin (r + 1)), ∑ d, Q (Fin.natAdd (r + 1) i) d * fvec k r z' j (e d) = 0 := by
  first | exact @GlobalTheory.HatNF.DualFrame.exists_dual_matrix | exact GlobalTheory.HatNF.DualFrame.exists_dual_matrix | (intros; apply GlobalTheory.HatNF.DualFrame.exists_dual_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaMul

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem alg {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (C : IsCub θ) (k : ℕ) (a B b x : A)
    (g₁ g g₂ gs gy w w₁ : U) (h₁ : g₂ * θ a b B = g * g₁) (h₂ : gs * θ a (B ^ k) b = g * gy) :
    hv θ k a B (x * b) * (g₁ * w₁) * (hv θ k (a * B ^ k) b x * (gs * w)) =
      hv θ k a (b * B) x * (g₂ * (cubN θ k 1 B b * gy * (w * w₁))) := by
  have e₁ := UUA.hv_comp C k a B b x
  have e₂ := C.N_split k a B b
  have e₃ : hv θ k a B b = cubN θ k a B b * (θ a b B)⁻¹ := rfl
  rw [mul_comm b B]
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e₃
  have b₁ := congrArg Additive.ofMul h₁
  have b₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ b₁ b₂ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃ - b₁ + b₂

theorem exists_gen_mul {k : ℕ} (p p₁ : QkPt D F k) (b₂ : TF (R := R) F ⟶ D.P.A) (hb : b₂ = p.g.b * p₁.g.b)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (w₁ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₁.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw₁ : w₁.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b₂) (DegPre.lineε k)), w₂.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) F) (z : T.left) (J), Good D.P.L z J →
        val w₂ σ.left z J = cubN (th D z J) k 1 (σ ≫ p₁.g.b) (σ ≫ p.g.b) * val (p.g.s p₁.y) σ.left z J *
          (val w σ.left z J * val w₁ σ.left z J) := by
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub (1 : TF (R := R) F ⟶ D.P.A) p₁.g.b p.g.b k
  obtain ⟨w₂, hw₂, v₂⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b₂) (ε' := DegPre.lineε k) (fun U _ h => by
      have l : ∀ b : TF (R := R) F ⟶ D.P.A, ∏ i, h (DegPre.lineφ D F b i) ^ DegPre.lineε k i =
          h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h b.left ^ (-(k : ℤ)) := fun b => by
        rw [Fin.prod_univ_two]; rfl
      have g : ∏ i, h (DegPre.gtφ D F p.g.b p₁.y i) ^ DegPre.gtε i =
          h (p₁.g.b ^ k * p.g.b).left ^ (-1 : ℤ) * h (p₁.g.b ^ k).left ^ (1 : ℤ) * h p.g.b.left ^ (1 : ℤ) *
            h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) := by
        rw [Fin.prod_univ_four, ← cPoint_y p₁]; rfl
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ Fin 4) (K' := Fin 2 ⊕ Fin 2) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := Fin 4) (U := U) _ rfl g)
        (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (l _) (l _))) (Eq.trans ?_ (l b₂).symm)
      rw [hb, mul_comm p.g.b p₁.g.b]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (p.g.s p₁.y)) (LB.mulGen D.P.L _ _ _ _ w w₁))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (p.g.isGen _)) (mulGen_isGen _ _ _ _ _ _ _ hw hw₁))
  refine ⟨w₂, hw₂, fun T σ z J hJ => ?_⟩
  rw [v₂ _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, vN T σ z J hJ, MonObj.comp_one]

theorem phi_mul_core (hG : GlobalFnsSt) {k : ℕ} (p p₁ p₂ : QkPt D F k) (hy : p₂.y = p.y + p₁.y)
    (hg : p.g.IsAdd p₁.g p₂.g)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (w₁ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₁.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw₁ : w₁.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₂.g.b) (DegPre.lineε k)), w₂.IsGen ∧
      ∀ s t t' : Fam D F k, PhiRel D F k p₁ w₁ s t → PhiRel D F k p w t t' → PhiRel D F k p₂ w₂ s t' := by
  have hb : p₂.g.b = p.g.b * p₁.g.b := hg.1
  obtain ⟨w₂, hw₂, v₂⟩ := exists_gen_mul p p₁ p₂.g.b hb w w₁ hw hw₁
  refine ⟨w₂, hw₂, fun s t t' h₁ h => ?_⟩
  rw [phiRel_iff hG _ _ hw₁] at h₁
  rw [phiRel_iff hG _ _ hw] at h
  rw [phiRel_iff hG _ _ hw₂]
  intro α β hαβ T ρ z J hJ
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have e := h (α + p₁.y) β (by rw [← hαβ, hy]; abel) T ρ z J hJ
  have e₁ := h₁ α (α + p₁.y) rfl T (ρ ≫ DegPre.trPt D F p.g.b) z J hJ
  have hf : (ρ ≫ DegPre.trPt D F p.g.b) ≫ fst (TF (R := R) F) D.P.A = ρ ≫ fst _ _ := by
    rw [Category.assoc, tr_fst]
  have hp : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.prB D F = (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ p.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, ← Category.assoc]
  have ht : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.trPt D F p₁.g.b = ρ ≫ DegPre.trPt D F p₂.g.b := by
    rw [Category.assoc, trPt_mul, hb]
  have hy₁ : cP D T p₁.y = ((ρ ≫ fst _ _) ≫ p₁.g.b) ^ k := by
    rw [← comp_cP D (ρ ≫ fst (TF (R := R) F) D.P.A), cPoint_y]; exact map_pow (preHom (ρ ≫ fst (TF (R := R) F) D.P.A)) _ _
  have u₁ : uVal D F k α p₁.g.b (ρ ≫ DegPre.trPt D F p.g.b) z J =
      hv (th D z J) k (cP D T α) ((ρ ≫ fst _ _) ≫ p₁.g.b) ((ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ p.g.b)) := by
    rw [uVal, hp, ← Category.assoc (ρ ≫ DegPre.trPt D F p.g.b), hf]; rfl
  have u₂ : uVal D F k (α + p₁.y) p.g.b ρ z J =
      hv (th D z J) k (cP D T α * ((ρ ≫ fst _ _) ≫ p₁.g.b) ^ k) ((ρ ≫ fst _ _) ≫ p.g.b) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, cPoint_add, hy₁, ← Category.assoc]; rfl
  have u₃ : uVal D F k α p₂.g.b ρ z J =
      hv (th D z J) k (cP D T α) (((ρ ≫ fst _ _) ≫ p.g.b) * ((ρ ≫ fst _ _) ≫ p₁.g.b)) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, ← Category.assoc, hb, MonObj.comp_mul]; rfl
  have g₁ : val (p₂.g.s α) (ρ ≫ fst _ _).left z J *
      th D z J (cP D T α) ((ρ ≫ fst _ _) ≫ p.g.b) ((ρ ≫ fst _ _) ≫ p₁.g.b) =
      val (p.g.s α) (ρ ≫ fst _ _).left z J * val (p₁.g.s α) (ρ ≫ fst _ _).left z J := by
    have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hg.2 α) (ρ ≫ fst (TF (R := R) F) D.P.A).left).trans
      (val_mul hJ _ _ _))
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
    refine Eq.trans ?_ (val_cub D.cub (ρ ≫ fst (TF (R := R) F) D.P.A) hJ (cP D _ α) p.g.b p₁.g.b).symm
    rw [comp_cP]
  have g₂ := gt_mul (ρ ≫ fst (TF (R := R) F) D.P.A) hJ p.g α p₁.y
  rw [hy₁] at g₂
  rw [ht, hf, u₁, val_mul hJ] at e₁
  rw [e₁, u₂, val_mul hJ, _root_.mul_assoc, ← Units.val_mul, alg C k _ _ _ _ _ _ _ _ _ _ _ g₁ g₂] at e
  rw [e, u₃, val_mul hJ, v₂ T _ z J hJ]

end GlobalTheory.ThetaMul

namespace GlobalTheory

theorem phi_mul : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p₁ p₂ : QkPt D.toPre F k, p₂.y = p.y + p₁.y → p.g.IsAdd p₁.g p₂.g → ∀ (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (w₁ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε k))), w.IsGen → w₁.IsGen → ∃ w₂ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₂.g.b) (DegPre.lineε k)), w₂.IsGen ∧ ∀ s t t' : Fam D.toPre F k, PhiRel D.toPre F k p₁ w₁ s t → PhiRel D.toPre F k p w t t' → PhiRel D.toPre F k p₂ w₂ s t' := by
  intro hL V _ _ _ D F _ _ k _ p p₁ p₂ hy hg w w₁ hw hw₁
  exact ThetaMul.phi_mul_core hL.globalFns p p₁ p₂ hy hg w w₁ hw hw₁

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureWeilStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotientMeasure_weil : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM G μG → PI.IsHaarOnM S μS → PI.IsRightInvM S μS → ∃ ν, PI.IsQuotM μG μS ν := by
  first | exact @GlobalTheory.QuotWeil.exists_isQuotM | exact GlobalTheory.QuotWeil.exists_isQuotM | (intros; apply GlobalTheory.QuotWeil.exists_isQuotM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedNormalisation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_shifted_normalisation (k : ℕ) (g : GtPtF D F) (z : D.X) (b' : TF (R := R) F ⟶ D.P.A)
    (hb : b' = g.b * cP D _ z)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b') (DegPre.lineε k)), w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (x : Z) (J), Good D.P.L x J →
        val w' r x J = val (g.s z) r x J ^ k * (val (D.psi z) (r ≫ jFK (R := R) F) x J ^ k *
          val D.rigK (r ≫ jFK (R := R) F) x J ^ k) * val w r x J := by
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b') (ε' := DegPre.lineε k) (fun U _ h => by
      have a₁ : ∀ χ, jFK (R := R) F ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two, hb, mul_comm g.b]
      show h (cP D _ z * g.b).left ^ ((k : ℤ) * (-1 : ℤ)) * h (cP D _ z).left ^ ((k : ℤ) * (1 : ℤ)) *
        h g.b.left ^ ((k : ℤ) * (1 : ℤ)) * h (1 : TF (R := R) F ⟶ D.P.A).left ^ ((k : ℤ) * (-1 : ℤ)) * _ *
        (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) =
        h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h (cP D _ z * g.b).left ^ (-(k : ℤ))
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (g.s z) k)
      (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi z) k)
        (GeneratorPullback.powGen D.P.L _ _ D.rigK k)) (jFK (R := R) F))) w)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (g.isGen z) k)
      (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen z) k)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) _)) hw)
  refine ⟨w', hw', fun Z r x J hJ => ?_⟩
  refine (hv Z r x J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (UUA.val_powGen' _ _ _ _ _) ((val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (UUA.val_powGen' _ _ _ _ _) (UUA.val_powGen' _ _ _ _ _)))))) rfl))

theorem phi_value_shift (hG : GlobalFnsSt) (k : ℕ) (g h g' : GtPtF D F) (z : D.X)
    (hι : GtPtF.IsIota z h) (ha : GtPtF.IsAdd g h g')
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k)))
    (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g'.b) (DegPre.lineε k)))
    (hw' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (x : Z) (J), Good D.P.L x J →
        val w' r x J = val (g.s z) r x J ^ k * (val (D.psi z) (r ≫ jFK (R := R) F) x J ^ k *
          val D.rigK (r ≫ jFK (R := R) F) x J ^ k) * val w r x J)
    (s : Fam D F k) (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (x : T.left) (J)
    (hJ : Good D.P.L x J) :
    sval (s.s (α + k • z)) (ρ ≫ DegPre.trPt D F g.b).left x J *
      (uVal D F k (α + k • z) g.b ρ x J *
        val (LB.mulGen D.P.L _ _ _ _ (g.s (α + k • z)) w) (ρ ≫ fst _ _).left x J).val =
    sval (s.s α) (ρ ≫ DegPre.trPt D F g'.b).left x J *
      (uVal D F k α g'.b ρ x J * val (LB.mulGen D.P.L _ _ _ _ (g'.s α) w') (ρ ≫ fst _ _).left x J).val := by
  have C : IsCub (th D x J) := isCub_cubV D.cub hJ
  have hh : h.b = cP D _ z := hι.1
  have hb : g'.b = g.b * cP D _ z := ha.1.trans (congrArg (g.b * ·) hh)
  obtain ⟨⟨u, hu, hc⟩, hv'⟩ := gen_fe (D := D) (F := F) hG k z α
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe z α u hu hc) _ (ρ ≫ DegPre.trPt D F g.b).left x J hJ
  have htr : (ρ ≫ DegPre.trPt D F g.b) ≫ DegPre.trPt D F (cP D _ z) = ρ ≫ DegPre.trPt D F g'.b := by
    rw [hb, Category.assoc]
    refine congrArg (ρ ≫ ·) ?_
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, tr_fst, tr_fst]
    · have e₁ : (DegPre.trPt D F g.b ≫ DegPre.trPt D F (cP D _ z)) ≫ DegPre.prB D F =
          DegPre.prB D F * (fst _ _ ≫ g.b) * (fst _ _ ≫ cP D _ z) := by
        rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst]
      have e₂ : DegPre.trPt D F (g.b * cP D _ z) ≫ DegPre.prB D F =
          DegPre.prB D F * (fst _ _ ≫ g.b) * (fst _ _ ≫ cP D _ z) := by
        rw [tr_pr, MonObj.comp_mul, _root_.mul_assoc]
      exact e₁.trans e₂.symm
  have hf : (ρ ≫ DegPre.trPt D F g.b) ≫ fst (TF (R := R) F) D.P.A = ρ ≫ fst _ _ := by
    rw [Category.assoc, tr_fst]
  have hp : (ρ ≫ DegPre.trPt D F g.b) ≫ DegPre.prB D F = (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, Category.assoc]
  rw [hv' u hu hc _ (ρ ≫ DegPre.trPt D F g.b) x J hJ, trF_eq, ← Over.comp_left, htr, hf] at e
  rw [e, _root_.mul_assoc, ← Units.val_mul]
  refine congrArg₂ (· * ·) rfl (congrArg Units.val ?_)
  have u1 : uVal D F k α (cP D _ z) (ρ ≫ DegPre.trPt D F g.b) x J =
      hv (th D x J) k (cP D T α) (cP D T z) ((ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ g.b)) := by
    rw [uVal, hp, ← Category.assoc (ρ ≫ DegPre.trPt D F g.b), hf, comp_cP]; rfl
  have u2 : uVal D F k (α + k • z) g.b ρ x J =
      hv (th D x J) k (cP D T α * cP D T z ^ k) ((ρ ≫ fst _ _) ≫ g.b) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, cPoint_add, cPoint_nsmul, ← Category.assoc ρ]; rfl
  have u3 : uVal D F k α g'.b ρ x J =
      hv (th D x J) k (cP D T α) (cP D T z * ((ρ ≫ fst _ _) ≫ g.b)) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, ← Category.assoc ρ, hb, MonObj.comp_mul, comp_cP, mul_comm (cP D T z)]; rfl
  have hvc := UUA.hv_comp C k (cP D T α) (cP D T z) ((ρ ≫ fst _ _) ≫ g.b) (ρ ≫ DegPre.prB D F)
  have h8 : hv (th D x J) k (cP D T α) (cP D T z) ((ρ ≫ fst _ _) ≫ g.b) =
      cubN (th D x J) k (cP D T α) (cP D T z) ((ρ ≫ fst _ _) ≫ g.b) *
        (th D x J (cP D T α) ((ρ ≫ fst _ _) ≫ g.b) (cP D T z))⁻¹ := rfl
  have t1 := gt_nsmul (ρ ≫ fst _ _) hJ g α z k
  have t2 : val (g'.s α) (ρ ≫ fst _ _).left x J * th D x J (cP D T α) ((ρ ≫ fst _ _) ≫ g.b) (cP D T z) =
      val (g.s α) (ρ ≫ fst _ _).left x J * val (D.tau z α) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) x J := by
    have e' := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (ρ ≫ fst _ _) hJ _ _ _))).symm.trans
      ((val_corr hJ (ha.2 α) (ρ ≫ fst _ _).left).trans (val_mul hJ _ _ _))
    have e₂ : (ρ ≫ fst _ _) ≫ DegPre.cF D F α = cP D T α := comp_cP D _ α
    have e₃ : (ρ ≫ fst _ _) ≫ h.b = cP D T z := by rw [hh, comp_cP]
    rw [e₂, e₃] at e'
    exact e'.trans (congrArg₂ (· * ·) rfl ((val_corr hJ (hι.2 α) _).trans (val_pull hJ _ _ _)))
  rw [u1, u2, u3, val_famMult _ hJ, UUA.val_powGen', UUA.val_powGen', val_mul hJ, val_mul hJ, hw' _ _ x J hJ]
  apply Additive.ofMul.injective
  have a1 := congrArg Additive.ofMul hvc
  have a2 := congrArg Additive.ofMul h8
  have a3 := congrArg Additive.ofMul t1
  have a4 := congrArg Additive.ofMul t2
  simp only [ofMul_mul, ofMul_inv] at a1 a2 a3 a4 ⊢
  linear_combination (norm := abel) a1 + a2 + a3 - a4

end

theorem phiRel_of_qkEquiv : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, QkPt.Equiv D.toPre F p p' → ∀ w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)), w.IsGen → ∃ w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p'.g.b) (DegPre.lineε k)), w'.IsGen ∧ ∀ s t : Fam D.toPre F k, PhiRel D.toPre F k p w s t ↔ PhiRel D.toPre F k p' w' s t := by
  intro hL V _ _ _ D F _ _ k _ p p' ⟨z, hy, h, hι, ha⟩ w hw
  have hG := hL.globalFns
  obtain ⟨w', hw', hv⟩ := exists_shifted_normalisation k p.g z p'.g.b
    (ha.1.trans (congrArg (p.g.b * ·) hι.1)) w hw
  refine ⟨w', hw', fun s t => ?_⟩
  rw [phiRel_iff hG p w hw, phiRel_iff hG p' w' hw']
  constructor
  · intro H α β hβ T ρ x J hJ
    rw [← phi_value_shift hG k p.g h p'.g z hι ha w w' hv s α T ρ x J hJ]
    exact H (α + k • z) β (by rw [← hβ, hy]; abel) T ρ x J hJ
  · intro H α β hβ T ρ x J hJ
    obtain ⟨α, rfl⟩ : ∃ α', α' + k • z = α := ⟨α - k • z, sub_add_cancel _ _⟩
    rw [phi_value_shift hG k p.g h p'.g z hι ha w w' hv s α T ρ x J hJ]
    exact H α β (by rw [← hβ, hy]; abel) T ρ x J hJ

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUnitaryWFrameToFrame
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P

namespace GlobalTheory.FrameTrans

variable {k r : ℕ}

noncomputable def swapMat (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (B B' : Fin k → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  1 + Matrix.of fun p q => ∑ c, (B' c p - B c p) * herm H (bvec q) (B c)

end GlobalTheory.FrameTrans

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExpansionUwGroup
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.FrameExpansion

open Matrix in
private lemma herm_mulVec_invariant {k r : ℕ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hH : hᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * h = _root_.Formalism.QuantumDeterminants.Hpk k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v w := by
  simp only [_root_.Formalism.QuantumDeterminants.herm]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hH]

open Matrix in
private lemma inWb_of_coords_eq_zero {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ}
    (h1 : ∀ a, v (_root_.Formalism.QuantumDeterminants.eI k r a) = 0) (h2 : ∀ a, v (_root_.Formalism.QuantumDeterminants.esI k r a) = 0) : _root_.Formalism.QuantumDeterminants.inWb k r v := by
  intro i hi
  rcases hi with hi | hi
  · have e : _root_.Formalism.QuantumDeterminants.eI k r ⟨i, hi⟩ = i := Fin.ext rfl
    rw [← e]; exact h1 _
  · have e : _root_.Formalism.QuantumDeterminants.esI k r ⟨2 * r + k - i, by omega⟩ = i :=
      Fin.ext (show 2 * r + k - (2 * r + k - (i : ℕ)) = i by omega)
    rw [← e]; exact h2 _

open Matrix in
private lemma herm_bvec_esI_jet_harmonics {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.esI k r a)) = v (_root_.Formalism.QuantumDeterminants.eI k r a) := by
  rw [_root_.Formalism.QuantumDeterminants.gn_herm_bvec_right, mulVec, dotProduct]
  simp only [_root_.Formalism.FourierDecayAlt.P.Qx3.hpk_row_es, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open Matrix in
private lemma coord_eI_eq_zero_of_inWb {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : _root_.Formalism.QuantumDeterminants.inWb k r v)
    (a : Fin r) : v (_root_.Formalism.QuantumDeterminants.eI k r a) = 0 :=
  hv _ (Or.inl (show (a : ℕ) < r from a.2))

open Matrix in
private lemma herm_bvec_eI_jet_harmonics {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a)) = v (_root_.Formalism.QuantumDeterminants.esI k r a) := by
  rw [_root_.Formalism.QuantumDeterminants.gn_herm_bvec_right, mulVec, dotProduct]
  simp only [_root_.Formalism.FourierDecayAlt.P.Qx3.hpk_row_e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open Matrix in
private lemma coord_esI_eq_zero_of_inWb {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : _root_.Formalism.QuantumDeterminants.inWb k r v)
    (a : Fin r) : v (_root_.Formalism.QuantumDeterminants.esI k r a) = 0 :=
  hv _ (Or.inr (show r + k < 2 * r + k - (a : ℕ) by have := a.2; omega))

open Matrix in

theorem _root_.GlobalTheory.FrameExpansion.frame_expansion_uw_group :
    ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), _root_.Formalism.QuantumDeterminants.inWb k r z → 0 < _root_.Formalism.QuantumDeterminants.Tz k r z → _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B → (∀ w, _root_.Formalism.QuantumDeterminants.inWb k r w → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w z = 0 → w = ∑ c, _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w (B c) • B c) ∧ ∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, (∀ w, _root_.Formalism.QuantumDeterminants.inWb k r w → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w z = 0 → _root_.Formalism.QuantumDeterminants.inWb k r (h *ᵥ w) ∧ _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ w) z = 0) ∧ (∀ v w, _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v w) ∧ h⁻¹ ∈ _root_.Formalism.QuantumDeterminants.UWset k r z ∧ h * h⁻¹ = 1 ∧ h⁻¹ * h = 1 ∧ ∀ h' ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, h * h' ∈ _root_.Formalism.QuantumDeterminants.UWset k r z := by
  intro k r z B hz hT hB
  have hzz := _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.hzz hT
  refine ⟨fun w hw hwz => _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.complete0 hz hzz hB hw hwz, ?_⟩
  intro h hh
  have hH : hᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * h = _root_.Formalism.QuantumDeterminants.Hpk k r := hh.1
  have hinv := herm_mulVec_invariant hH
  have hfz : h *ᵥ z = z := hh.2.2
  have hdet : IsUnit h.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  refine ⟨fun w hw hwz => ⟨?_, ?_⟩, hinv, _root_.Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh, mul_nonsing_inv h hdet,
    nonsing_inv_mul h hdet, fun h' hh' => _root_.Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hh hh'⟩
  · apply inWb_of_coords_eq_zero
    · intro a
      rw [← herm_bvec_esI_jet_harmonics (h *ᵥ w), ← (hh.2.1 a).2, hinv, herm_bvec_esI_jet_harmonics]
      exact coord_eI_eq_zero_of_inWb hw a
    · intro a
      rw [← herm_bvec_eI_jet_harmonics (h *ᵥ w), ← (hh.2.1 a).1, hinv, herm_bvec_eI_jet_harmonics]
      exact coord_esI_eq_zero_of_inWb hw a
  · rw [← hfz, hinv, hwz]

end GlobalTheory.FrameExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelationRowStepsFunctionalEigenStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glRelation_row_steps_functional_eigen : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → 1 ≤ r → ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * r + k))) (Fin.succAbove 0) u v) = c • l (Formalism.REAL.qminor E (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1, by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
  first | exact @GlobalTheory.RowChain.chain_rows | exact GlobalTheory.RowChain.chain_rows | (intros; apply GlobalTheory.RowChain.chain_rows <;> assumption)
end

