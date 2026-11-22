import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentConjConeDiagonalBound
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem unip_mul_diag_cone : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → r j / r i ≤ C ∧ ∀ z : BlockIx a j → Cinf E, ∃ z' : BlockIx a j → Cinf E, ‖z'‖ ≤ C * (r j / r i) * ‖z‖ ∧ ∀ τ : ℝ, unip (τ • z) * d = d * unip (τ • z') := by
  intro E _ _ _ a t ht i j hij
  obtain ⟨C0, hC0, hb⟩ := GlobalTheory.T.cone_coordinate_ratio_bounded a t ht
  refine ⟨C0 * C0 + C0, by positivity, ?_⟩
  intro r d hr hcone hd
  have hij' : i ≤ j := by rw [Fin.le_def]; omega
  have hji : r j / r i ≤ C0 := hb r hr hcone i j hij'
  have hji0 : 0 ≤ r j / r i := (div_pos (hr j) (hr i)).le
  refine ⟨by nlinarith, fun z => ?_⟩
  refine ⟨fun p => (r p.1.2 / r p.1.1) • z p, ?_, ?_⟩
  · have hX : 0 ≤ (C0 * C0 + C0) * (r j / r i) := by positivity
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p => ?_
    have hk : p.1.1 ≤ i := by rw [Fin.le_def]; have := p.2.1; omega
    have hl : j ≤ p.1.2 := by rw [Fin.le_def]; exact p.2.2
    have h1 : r p.1.2 / r j ≤ C0 := hb r hr hcone j p.1.2 hl
    have h3 : r i / r p.1.1 ≤ C0 := hb r hr hcone p.1.1 i hk
    have hpos : 0 < r p.1.2 / r p.1.1 := div_pos (hr _) (hr _)
    have heq : r p.1.2 / r p.1.1 = (r p.1.2 / r j) * (r j / r i) * (r i / r p.1.1) := by
      have := hr j; have := hr i; have := hr p.1.1
      field_simp
    have hbd : r p.1.2 / r p.1.1 ≤ (C0 * C0 + C0) * (r j / r i) := by
      rw [heq]
      have e1 : 0 ≤ r p.1.2 / r j := (div_pos (hr _) (hr _)).le
      have e3 : 0 ≤ r i / r p.1.1 := (div_pos (hr _) (hr _)).le
      calc r p.1.2 / r j * (r j / r i) * (r i / r p.1.1) ≤ C0 * (r j / r i) * C0 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hji0) h3 e3 (by positivity)
        _ ≤ (C0 * C0 + C0) * (r j / r i) := by nlinarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    exact mul_le_mul hbd (norm_le_pi_norm z p) (norm_nonneg _) hX
  · intro τ
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hd]
    change (1 + nilM (τ • z)) * _ = _ * (1 + nilM (τ • fun p => (r p.1.2 / r p.1.1) • z p))
    ext k l w
    rw [add_mul, mul_add, one_mul, mul_one, Matrix.add_apply, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    congr 1
    simp only [nilM, Matrix.of_apply]
    split_ifs with h
    · simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, add_right_inj]
      have := hr k
      have hk0 : (r k : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      push_cast
      field_simp
    · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.DblDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def topC {n d : ℕ} (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) : Matrix (Fin n) (Fin d) (AE F E) :=
  u.submatrix id (finSumFinEquiv ∘ Sum.inl)

def botC {n d : ℕ} (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) : Matrix (Fin n) (Fin d) (AE F E) :=
  u.submatrix id (finSumFinEquiv ∘ Sum.inr)

def dblE {σ : E →ₐ[F] E} {n d : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E} {κ : Type} [Fintype κ]
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) κ)
    (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) : (κ ⊕ κ → AF F) × (κ ⊕ κ → AF F) :=
  (Sum.elim (co.e (topC u)).1 (co.e (botC u)).1, Sum.elim (co.e (topC u)).2 (-(co.e (botC u)).2))

def boxC {κ : Type} (φ₁ φ₂ : (κ → AF F) → ℂ) : (κ ⊕ κ → AF F) → ℂ :=
  boxFun φ₁ fun x => star (φ₂ x)

end GlobalTheory.DblDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CayleyTransformMemUnitaryLatticeStabilizerStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayleyTransform_mem_unitaryLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl F) (Y : Matrix (Fin d) (Fin d) (AE F E)), At (evFin F v) Y →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ h ∈ GlobalTheory.InertSph.KAt σ W v, mat h * (1 + Y) = 1 - Y := by
  first | exact @GlobalTheory.CayleyStab.cayley_mem_KAt | exact GlobalTheory.CayleyStab.cayley_mem_KAt | (intros; apply GlobalTheory.CayleyStab.cayley_mem_KAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothingStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centreEnvelopingAlgebra_commute_realLieSmoothing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ (ψ : Sm E a) (h : smoothing ν α ψ.1 ∈ Sm E a), ∀ z ∈ Zalg E a, (z ⟨smoothing ν α ψ.1, h⟩).1 = smoothing ν α (z ψ).1 := by
  first | exact @GlobalTheory.CentreSmooth.zalg_smoothing | exact GlobalTheory.CentreSmooth.zalg_smoothing | (intros; apply GlobalTheory.CentreSmooth.zalg_smoothing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerIffIntegralUnitsOfModelStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactPart_centralizer_iff_integralUnits_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∀ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, (∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ t : twCent (MonoidHom.id (UL n w)) γ, ((t : UL n w) ∈ cptPart (twCent (MonoidHom.id (UL n w)) γ) ↔ ((τ t : B.Aˣ)) ∈ intUnits K.O B.A) := by
  first | exact @GlobalTheory.InertUnitOrb.cptPart_iff_intUnits_of_model | exact GlobalTheory.InertUnitOrb.cptPart_iff_intUnits_of_model | (intros; apply GlobalTheory.InertUnitOrb.cptPart_iff_intUnits_of_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparisonCharacter_det_eq_one_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  first | exact @GlobalTheory.InertDetChr.alpha_det_eq_one | exact GlobalTheory.InertDetChr.alpha_det_eq_one | (intros; apply GlobalTheory.InertDetChr.alpha_det_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateLePowOfProdEqOneStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coneCoordinate_le_pow_of_prod_eq_one : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 1 ≤ C ∧ ∀ (r : Fin a → ℝ) (ρ : ℝ), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → 1 ≤ ρ → (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) → ∀ i, r i ≤ C * ρ ^ a ∧ (r i)⁻¹ ≤ C * ρ ^ a := by
  first | exact @GlobalTheory.coneCoord_le_pow_of_prod_eq_one | exact GlobalTheory.coneCoord_le_pow_of_prod_eq_one | (intros; apply GlobalTheory.coneCoord_le_pow_of_prod_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.DblEval

section Blocks

variable {A : Type} {κ κ₁ κ' κ₁' : Type}

def partL (T : ((κ → A) → ℂ) → (κ₁ → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) : (κ₁ ⊕ κ' → A) → ℂ :=
  fun y => T (fun x => Φ (Sum.elim x (y ∘ Sum.inr))) (y ∘ Sum.inl)

def partR (T : ((κ' → A) → ℂ) → (κ₁' → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) : (κ ⊕ κ₁' → A) → ℂ :=
  fun y => T (fun x => Φ (Sum.elim (y ∘ Sum.inl) x)) (y ∘ Sum.inr)

def partLₗ (e : ((κ → A) → ℂ) →ₗ[ℂ] (κ₁ → A) → ℂ) : ((κ ⊕ κ' → A) → ℂ) →ₗ[ℂ] (κ₁ ⊕ κ' → A) → ℂ where
  toFun := partL e
  map_add' Φ Ψ := funext fun y => by
    show e ((fun x => Φ _) + fun x => Ψ _) _ = _
    rw [map_add]; rfl
  map_smul' c Φ := funext fun y => by
    show e (c • fun x => Φ _) _ = _
    rw [map_smul]; rfl

def partRₗ (e : ((κ' → A) → ℂ) →ₗ[ℂ] (κ₁' → A) → ℂ) : ((κ ⊕ κ' → A) → ℂ) →ₗ[ℂ] (κ ⊕ κ₁' → A) → ℂ where
  toFun := partR e
  map_add' Φ Ψ := funext fun y => by
    show e ((fun x => Φ _) + fun x => Ψ _) _ = _
    rw [map_add]; rfl
  map_smul' c Φ := funext fun y => by
    show e (c • fun x => Φ _) _ = _
    rw [map_smul]; rfl

@[simp] theorem partLₗ_apply (e : ((κ → A) → ℂ) →ₗ[ℂ] (κ₁ → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) :
    partLₗ e Φ = partL e Φ := rfl

@[simp] theorem partRₗ_apply (e : ((κ' → A) → ℂ) →ₗ[ℂ] (κ₁' → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) :
    partRₗ e Φ = partR e Φ := rfl

end Blocks

def conjLin {X Y : Type} (e : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) : (X → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun φ y := starRingEnd ℂ (e (fun x => starRingEnd ℂ (φ x)) y)
  map_add' φ ψ := funext fun y => by
    have h : (fun x => starRingEnd ℂ (φ x + ψ x)) = (fun x => starRingEnd ℂ (φ x)) + fun x => starRingEnd ℂ (ψ x) :=
      funext fun x => map_add _ _ _
    simp only [Pi.add_apply]
    rw [h, map_add, Pi.add_apply, map_add]
  map_smul' c φ := funext fun y => by
    have h : (fun x => starRingEnd ℂ (c * φ x)) = starRingEnd ℂ c • fun x => starRingEnd ℂ (φ x) :=
      funext fun x => by simp
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [h, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]

theorem conjLin_apply {X Y : Type} (e : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) (y : Y) :
    conjLin e φ y = starRingEnd ℂ (e (fun x => starRingEnd ℂ (φ x)) y) := rfl

section Loc

variable (F : Type) [Field F] [NumberField F]

def stdInd (κ : Type) (v : Pl F) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

variable {F}

def IsLocOp {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ) : Prop :=
  ∃ (ei : SInf F κ →L[ℂ] SInf F κ₁) (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ₁ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ₁ → Fv F v)) ∧
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ₁ v) ∧
    ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)

end Loc

end GlobalTheory.DblEval

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DoublingEv

def conjMap {X Y : Type} (T : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) : (X → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun φ := star (T (star φ))
  map_add' φ φ' := by rw [star_add, map_add, star_add]
  map_smul' c φ := by rw [star_smul, map_smul, star_smul, star_star]; rfl

theorem conjMap_apply {X Y : Type} (T : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) :
    conjMap T φ = star (T (star φ)) := rfl

variable {R : Type}

def partR {κ κ' κ₁' : Type} (T : ((κ' → R) → ℂ) →ₗ[ℂ] ((κ₁' → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) →ₗ[ℂ] ((κ ⊕ κ₁' → R) → ℂ) where
  toFun Φ s := T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (s ∘ Sum.inr)
  map_add' Φ Ψ := by funext s; exact congrFun (map_add T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (fun x₂ => Ψ (Sum.elim (s ∘ Sum.inl) x₂))) _
  map_smul' c Φ := by funext s; exact congrFun (map_smul T c (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂))) _

def partL {κ κ₁ κ' : Type} (T : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ' → R) → ℂ) where
  toFun Φ s := T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (s ∘ Sum.inl)
  map_add' Φ Ψ := by funext s; exact congrFun (map_add T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (fun x₁ => Ψ (Sum.elim x₁ (s ∘ Sum.inr)))) _
  map_smul' c Φ := by funext s; exact congrFun (map_smul T c (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr)))) _

theorem partR_apply {κ κ' κ₁' : Type} (T : ((κ' → R) → ℂ) →ₗ[ℂ] ((κ₁' → R) → ℂ)) (Φ : (κ ⊕ κ' → R) → ℂ)
    (s : κ ⊕ κ₁' → R) : partR (κ := κ) T Φ s = T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (s ∘ Sum.inr) := rfl

theorem partL_apply {κ κ₁ κ' : Type} (T : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (Φ : (κ ⊕ κ' → R) → ℂ)
    (s : κ₁ ⊕ κ' → R) : partL (κ' := κ') T Φ s = T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (s ∘ Sum.inl) := rfl

def evDbl {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) :
    ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁ → R) → ℂ) :=
  partL e ∘ₗ partR (conjMap e)

theorem evDbl_apply {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (Φ : (κ ⊕ κ → R) → ℂ)
    (s : κ₁ ⊕ κ₁ → R) : evDbl e Φ s =
      e (fun x₁ => conjMap e (fun x₂ => Φ (Sum.elim x₁ x₂)) (s ∘ Sum.inr)) (s ∘ Sum.inl) := by
  simp only [evDbl, LinearMap.comp_apply, partL_apply, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem evDbl_boxFun {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (φ₁ φ₂ : (κ → R) → ℂ) :
    evDbl e (boxFun φ₁ φ₂) = boxFun (e φ₁) (conjMap e φ₂) := by
  funext s
  rw [evDbl_apply]
  have h1 : ∀ x₁ : κ → R, (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₁ x₁ • φ₂ := fun x₁ => by
    funext x₂; simp [boxFun]
  have h2 : (fun x₁ => conjMap e (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) (s ∘ Sum.inr)) =
      conjMap e φ₂ (s ∘ Sum.inr) • φ₁ := by
    funext x₁; rw [h1, map_smul]; simp [mul_comm]
  rw [h2, map_smul]
  simp [boxFun, mul_comm]

section Tame

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def IsTame {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) : Prop :=
  ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ (ι : Type) (_ : Fintype ι)
    (P : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
    (g' : ι → (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), (∀ j, g' j ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, T (pureA F f g) = ∑ j, pureA F (P j f) (g' j)

variable {F}

theorem isTame_id {κ : Type} [Fintype κ] : IsTame F (LinearMap.id : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) :=
  fun g hg => ⟨Unit, inferInstance, fun _ => ContinuousLinearMap.id ℂ _, fun _ => g, fun _ => hg, fun f => by simp⟩

theorem IsTame.comp {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {T' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)}
    (hT : IsTame F T) (hT' : IsTame F T') : IsTame F (T' ∘ₗ T) := by
  intro g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
  choose ι' inst P' g'' hg'' hP' using fun j => hT' (g' j) (hg' j)
  letI : ∀ j, Fintype (ι' j) := inst
  refine ⟨Σ j, ι' j, inferInstance, fun p => (P' p.1 p.2).comp (P p.1), fun p => g'' p.1 p.2,
    fun p => hg'' p.1 p.2, fun f => ?_⟩
  rw [LinearMap.comp_apply, hP, map_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun j _ => hP' j (P j f)

theorem IsTame.mapsTo {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hT : IsTame F T) : ∀ φ ∈ schA F κ, T φ ∈ schA F κ' := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
    rw [hP]
    exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨P j f, g' j, hg' j, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem IsTame.comp_adm {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hT : IsTame F T) {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ T ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
  choose L hL using fun j => hl (g' j) (hg' j)
  refine ⟨∑ j, (L j).comp (P j), fun f => ?_⟩
  rw [LinearMap.comp_apply, hP, map_sum, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => hL j (P j f)

end Tame

end GlobalTheory.DoublingEv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMemStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ := by
  first | exact @GlobalTheory.star_mem_schA_main | exact GlobalTheory.star_mem_schA_main | (intros; apply GlobalTheory.star_mem_schA_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
section
noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisRes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def col0 {n r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin 1) E := X.submatrix id fun _ => 0

def IsIwaHtG (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop :=
  (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
    ∃ k ∈ levelAll σ J L a, g = p * k) ∧
  ∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x →
    ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l

def HidaSetting (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop :=
  IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧ IsHermND σ J ∧ 4 ≤ n ∧ IsWittFrame σ J X Y ∧
    GlobalTheory.EisLine.IsAdapted σ J X Y L a ∧ IsIwaHtG σ J (col0 X) L a h

def IsSerG (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (h : GAd σ J → ℝ)
    (Eis : ℂ → GAd σ J → ℂ) : Prop :=
  ∀ T : Set (ratPts σ J), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
      (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x) →
    ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
      HasSum (fun t : T => (h (t.1.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) (Eis s g)

def EisensteinHyp (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Matrix (Fin n) (Fin 1) E) (h : GAd σ J → ℝ)
    (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ) : Prop :=
  IsSerG σ J x h Eis ∧
  (∀ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F y = adMat F x →
    ∀ (μ : Measure (unipRad σ J x)) (𝓕 : Set (unipRad σ J x)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J x)) 𝓕 μ → μ 𝓕 = 1 →
      ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
        Integrable (fun u : unipRad σ J x => (h (w * u * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) μ ∧
        ∫ u : unipRad σ J x, (h (w * u * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2) ∂μ =
          c s * (h g : ℂ) ^ (-s + ((n : ℂ) - 1) / 2)) ∧
  MeromorphicOn c Set.univ ∧
  (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 s₀ ∧
    (∀ s ∈ U, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) ∧ (∀ s ∈ U, IsSmoothModerate σ J (H s)) ∧
    ∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U) ∧
  ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, c s * c (-s) = 1 ∧ ∀ g, Eis s g = c s * Eis (-s) g

def CoreConcl (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (h : GAd σ J → ℝ)
    (Eis : ℂ → GAd σ J → ℂ) : Prop :=
  IsSerG σ J x h Eis ∧
  (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → GAd σ J → ℂ) (C : ℝ) (N : ℕ), U ∈ 𝓝 s₀ ∧
    (∀ s ∈ U, s ≠ s₀ → ∀ g, Hol s g = (s - s₀) ^ k * Eis s g) ∧ (∀ g, DifferentiableOn ℂ (Hol · g) U) ∧
    ∀ s ∈ U, ∀ g, ‖Hol s g‖ ≤ C * (height σ J g : ℝ) ^ N) ∧
  ∃ U ∈ 𝓝 (-(((n : ℂ) - 1) / 2)), ∃ (C : ℝ) (N : ℕ), ∀ g, DifferentiableOn ℂ (Eis · g) U ∧
    (∀ s ∈ U, ‖Eis s g‖ ≤ C * (height σ J g : ℝ) ^ N) ∧ Eis (-(((n : ℂ) - 1) / 2)) g = 1

def EisCore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h → ∃ Eis, CoreConcl σ J (col0 X) h Eis

end GlobalTheory.EisRes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineBlockLatticesOverPowerSeriesRingStatement
section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_block_lattices_over_power_series_ring : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → BlockPair E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (Wl : Formalism.CohomologicalDescent.FrobeniusPeriodChange.WLat (E →+* PadicAlgCl l) t n O' F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (kap : (E →+* PadicAlgCl l) → Fin t → ℤ) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), Formalism.CohomologicalDescent.FrobeniusPeriodChange.NInputs Wl σ l h u c J (fun i s => bot i + ((s : ℕ) : ℤ)) kap I ζ em jj := by
  first | exact @GlobalTheory.WachBlock.wach_inputs | exact GlobalTheory.WachBlock.wach_inputs | (intros; apply GlobalTheory.WachBlock.wach_inputs <;> assumption)
end

