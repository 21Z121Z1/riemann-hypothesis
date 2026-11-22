import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationNonnegIffSpanMultiplicationTranslates
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0371
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0348
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
section
noncomputable section
namespace GlobalTheory.StabHaar
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  show (g.1 * g.1⁻¹ : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

def stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : Subgroup (UA σ X.J) where
  carrier := {g | (∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)) ∧
    ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X}
  one_mem' := by
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _
    · simp only [inv_one, mat_one, Matrix.one_mulVec]; exact ⟨hz, hz⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_mul, Matrix.map_mul]; exact (hg1 w).mul_left (hh1 w)
    · rw [mul_inv_rev, mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact ⟨(hg2 _ (hh2 z hz).1).1, (hh2 _ (hg2 z hz).2).2⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · set A := (mat g).map (piInf (B.emb w))
      set A' := (mat g⁻¹).map (piInf (B.emb w))
      have e1 : A * A' = 1 := by
        rw [← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
      have e2 : A' * A = 1 := by
        rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have hc := hg1 w
      show A' * X.θ w = X.θ w * A'
      calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [e1, Matrix.mul_one]
        _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
        _ = A' * (A * X.θ w) * A' := by rw [hc.eq]
        _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
        _ = X.θ w * A' := by rw [e2, Matrix.one_mul]
    · rw [inv_inv]; exact ⟨(hg2 z hz).2, (hg2 z hz).1⟩

theorem isStab_stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : IsStab B (stabK (σ := σ) B X) := fun _ => Iff.rfl

theorem exists_haar_of_isCompact {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J))
    (hK : IsCompact (K : Set (UA σ J))) : ∃ μ : Measure K, μ.IsHaarMeasure := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact ⟨Measure.haarMeasure ⊤, Measure.isHaarMeasure_haarMeasure _⟩

theorem exists_haar_idele : ∃ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  exact ⟨Measure.haar, inferInstance⟩

theorem isClosed_stabK (B : Base F E) {n : ℕ} (X : Spc F E n)
    (hL : IsClosed ((latHat X : AddSubgroup (Fin n → AE F E)) : Set (Fin n → AE F E))) :
    IsClosed ((stabK (σ := σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun g : UA σ X.J => mat g⁻¹ := hm.comp continuous_inv
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have h1 : IsClosed {g : UA σ X.J | ∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun w => isClosed_eq ((hm.matrix_map (hp w)).matrix_mul continuous_const)
      (continuous_const.matrix_mul (hm.matrix_map (hp w)))
  have h2 : IsClosed {g : UA σ X.J | ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun z => isClosed_iInter fun _ => ?_
    exact (hL.preimage (hm.matrix_mulVec continuous_const)).inter (hL.preimage (hmi.matrix_mulVec continuous_const))
  exact h1.inter h2

end GlobalTheory.StabHaar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseIntegralMatricesPreservingDoubledLaStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_integral_matrices_preserving_doubled_lattice : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (n : ℕ) (P Q : Matrix (Fin n) (Fin n) A)
    (Λ : Set (Fin n → A)), Function.Injective ι → P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) A) →
    Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) A) → ι 1 • P = P → ι 1 • Q = Q →
    (∀ z, z ∈ Λ ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A, M * M' = 1 →
    (∀ z : Fin n ⊕ Fin n → A, z ∘ Sum.inl ∈ Λ → z ∘ Sum.inr ∈ Λ →
      (M *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M *ᵥ z) ∘ Sum.inr ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inr ∈ Λ) →
    ∃ G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, G * G' = 1 ∧
      M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι := by
  first | exact @GlobalTheory.LatticeStab.matrix_in_diag_basis | exact GlobalTheory.LatticeStab.matrix_in_diag_basis | (intros; apply GlobalTheory.LatticeStab.matrix_in_diag_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dblEmb {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) : Matrix (Fin n ⊕ Fin n) (Fin n₁ ⊕ Fin n₁) (AE F E) :=
  Matrix.fromBlocks (incM F ι) 0 0 (incM F ι)

def isoD (d : ℕ) {n n₁ : ℕ} (H : Plane E n n₁) : Set (Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E)) :=
  {u | ∃ z₁ z₂ : Fin d → AE F E, u = Matrix.vecMulVec z₁ (Sum.elim (incV F H.x) (0 : Fin n → AE F E)) +
    Matrix.vecMulVec z₂ (Sum.elim (0 : Fin n → AE F E) (incV F H.x))}

def IsDLevi {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} (H : Plane E n n₁)
    (gd₁ : UG (cA σ) (dbl (incM F J₁))) (md : UG (cA σ) (dbl (incM F J))) : Prop :=
  md.1.1 *ᵥ Sum.elim (incV F H.x) (0 : Fin n → AE F E) = Sum.elim (incV F H.x) (0 : Fin n → AE F E) ∧
  md.1.1 *ᵥ Sum.elim (0 : Fin n → AE F E) (incV F H.x) = Sum.elim (0 : Fin n → AE F E) (incV F H.x) ∧
  md.1.1 * dblEmb H.ι = dblEmb H.ι * gd₁.1.1

def IsDblOf (ψ : AddChar (AF F) ℂ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (χW : Chr F E)
    (om : Rep σ X W)
    (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
    (omd : UG (cA σ) (dbl (incM F X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)) : Prop :=
  ∃ d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d), (∀ x, d'.e xᵀ = M.co.e x) ∧
    IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd ∧
    IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) (incM F W.J) (dbl (incM F X.J)) dd χW (diagCols (Fin n)) omd ∧
    ∀ (g : UA σ X.J) (gd : UG (cA σ) (dbl (incM F X.J))),
      gd.1.1 = Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂

theorem exists_isDblOf {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') :
    ∃ dd omd, IsDblOf B.ψ M χW om dd omd := by
  obtain ⟨-, ⟨d', hd', -, dd, omd, h1, h2, h3⟩, -⟩ := hP.weil
  exact ⟨dd, omd, d', hd', h1, h2, fun g gd hgd φ₁ h₁ φ₂ h₂ => h3 g gd hgd φ₁ h₁ φ₂ h₂⟩

end GlobalTheory.MixXChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDirac
section
noncomputable section
open NumberField MeasureTheory Matrix Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutGrowth.ApproxId GlobalTheory.GLFin
open scoped ContDiff

namespace GlobalTheory.GLFin.Inhab
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
omit [IsTotallyComplex E] in

theorem contDiffOn_invL : ContDiffOn ℝ ∞ (fun x : Lie E a => toL (Matrix.of x)⁻¹) (invSet E a) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  let S : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  intro x hx
  have hu : IsUnit (S x) := hx
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (S x) := by simpa using contDiffAt_ringInverse ℝ (n := ∞) hu.unit
  have h2 := (T.contDiff.contDiffAt.comp x (h1.comp x S.contDiff.contDiffAt)).contDiffWithinAt (s := invSet E a)
  refine h2.congr (fun y _ => ?_) ?_ <;> exact congrArg toL (Matrix.nonsing_inv_eq_ringInverse _)
end

theorem cP : Continuous (fun g : GA E a => GeneralLinearGroup.map (pInf E) g) := by
  have h : Continuous (pInf E) := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)
  exact Continuous.units_map _ (continuous_id.matrix_map h)

omit [IsTotallyComplex E] in

theorem cQ : Continuous (fun g : GA E a => GeneralLinearGroup.map (pFin E) g) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

omit [IsTotallyComplex E] in

theorem cF : Continuous (finGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) := continuous_const.prodMk continuous_id
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

omit [IsTotallyComplex E] in

theorem cd1 (m : ℝ) (L : Lie E a →L[ℝ] Lie E a) : ContDiff ℝ ∞ fun x => bumpR E a m (L x) :=
  (contDiff_bumpR m).comp L.contDiff

theorem exists_isDirac (μ : Measure (GA E a)) [μ.IsHaarMeasure] (U : Subgroup (GL (Fin a) (Af E)))
    (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    (N : Set (GL (Fin a) (Cinf E))) (hN : N ∈ 𝓝 1) : ∃ f, IsDirac μ U N f := by
  classical
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  have hv : (fun y : GL (Fin a) (Cinf E) => toL y.val) '' N ∈ 𝓝 (oneL E a) := isOpenEmbedding_val.isOpenMap.image_mem_nhds hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hv
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  set m : ℝ := (n : ℝ) + 1 with hmd
  have hm : 0 < m := by positivity
  have hsub : Metric.closedBall (oneL E a) (1 / m) ⊆ (fun y : GL (Fin a) (Cinf E) => toL y.val) '' N :=
    (Metric.closedBall_subset_ball hn).trans hball
  let b : GL (Fin a) (Cinf E) → ℝ := fun y => bumpR E a m (toL y.val)
  have hb : Continuous b := (contDiff_bumpR m).continuous.comp isOpenEmbedding_val.continuous
  have hbc : ∀ (k : Kinf E a) y, b (Unitary.toUnits k * y * (Unitary.toUnits k)⁻¹) = b y := fun k y => bumpR_conj m k _
  let P := GeneralLinearGroup.map (n := Fin a) (pInf E)
  let Q := GeneralLinearGroup.map (n := Fin a) (pFin E)
  let χ : GL (Fin a) (Af E) → ℝ := (U : Set _).indicator 1
  have hχ : Continuous χ := IsClopen.continuous_indicator ⟨U.isClosed_of_isOpen hUo, hUo⟩ continuous_const
  have hχl : ∀ u ∈ U, ∀ k, χ (u * k) = χ k := fun u hu k => by
    simp only [χ, Set.indicator, SetLike.mem_coe, U.mul_mem_cancel_left hu]; rfl
  have hχi : ∀ k, χ k⁻¹ = χ k := fun k => by
    simp only [χ, Set.indicator, SetLike.mem_coe, inv_mem_iff]; rfl
  have hχ0 : ∀ k, 0 ≤ χ k := fun k => Set.indicator_nonneg (fun _ _ => zero_le_one) k
  let f₀ : GA E a → ℝ := fun g => b (P g) * b (P g)⁻¹ * χ (Q g)
  have hc : Continuous f₀ := ((hb.comp cP).mul (hb.comp cP.inv)).mul (hχ.comp cQ)
  have h0 : ∀ g, 0 ≤ f₀ g := fun g => mul_nonneg (mul_nonneg (bumpR_nonneg _ _) (bumpR_nonneg _ _)) (hχ0 _)
  have hsm : ∀ g, f₀ g ≠ 0 → toL (P g).val ∈ Metric.closedBall (oneL E a) (1 / m) ∧ Q g ∈ U := fun g h =>
    ⟨(dist_lt_of_bumpR_ne_zero hm (left_ne_zero_of_mul (left_ne_zero_of_mul h))).le,
      Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩
  have hK : IsCompact ((fun y : GL (Fin a) (Cinf E) => toL y.val) ⁻¹' Metric.closedBall (oneL E a) (1 / m)) :=
    isOpenEmbedding_val.isInducing.isCompact_preimage' (isCompact_closedBall (oneL E a) (1 / m))
      (hsub.trans (Set.image_subset_range _ _))
  have hcs : HasCompactSupport f₀ := by
    refine HasCompactSupport.intro ((hK.prod hUc).image
      ((continuous_infGL.comp continuous_fst).mul (cF.comp continuous_snd))) fun g hg => ?_
    by_contra h
    exact hg ⟨(P g, Q g), hsm g h, infGL_mul_finGL g⟩
  have h1 : f₀ 1 = 1 := by
    have : b 1 = 1 := bumpR_one m
    simp [f₀, this, χ]
  have hpos : 0 < ∫ g, f₀ g ∂μ := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs h0 (x := 1) (by rw [h1]; norm_num)
  set c := (∫ g, f₀ g ∂μ)⁻¹
  have hsym : ∀ g, f₀ g⁻¹ = f₀ g := fun g => by
    simp only [f₀, map_inv, inv_inv, hχi, mul_comm (b (P g))]
  have hleft : ∀ u ∈ U, ∀ g, f₀ (finGL E a u * g) = f₀ g := fun u hu g => by
    simp only [f₀, P, Q, map_mul, pInf_finGL, pFin_finGL, one_mul, hχl u hu]
  refine ⟨fun g => ((c * f₀ g : ℝ) : ℂ), ⟨Complex.continuous_ofReal.comp (continuous_const.mul hc), ?_, ?_, ?_⟩,
    fun g => ⟨?_, Complex.ofReal_im _⟩, ?_, fun g => by rw [hsym], fun k g => ?_, fun u hu g => by rw [hleft u hu],
    fun g hg => ?_⟩
  · exact hcs.comp_left (g := fun x : ℝ => ((c * x : ℝ) : ℂ)) (by simp)
  · intro g
    have e1 : ContDiffOn ℝ ∞ (fun x : Lie E a => bumpR E a m (lmul (toL (P g).val) x)) (invSet E a) :=
      (cd1 m (lmul (toL (P g).val))).contDiffOn
    have e2 : ContDiffOn ℝ ∞ (fun x : Lie E a => bumpR E a m (rmul (toL ((P g)⁻¹).val) (toL (Matrix.of x)⁻¹))) (invSet E a) :=
      (cd1 m (rmul (toL ((P g)⁻¹ : GL (Fin a) (Cinf E)).val))).comp_contDiffOn contDiffOn_invL
    refine (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (((e1.mul e2).mul (contDiffOn_const (c := χ (Q g)))).const_smul c)).congr ?_
    rintro x ⟨u, hu⟩
    obtain rfl : x = toL u.val := hu.symm
    rw [chart_val, hsym]
    simp only [f₀, P, Q, map_mul, pInf_infGL, pFin_infGL, mul_one, _root_.mul_inv_rev]
    have : (Matrix.of (toL u.val))⁻¹ = (u⁻¹).val := (Matrix.coe_units_inv u).symm
    simp only [Function.comp_apply, this]
    rfl
  · let S : Subgroup (GL (Fin a) (Af E)) :=
      { carrier := {k | ∀ g, ((c * f₀ (finGL E a k * g) : ℝ) : ℂ) = ((c * f₀ g : ℝ) : ℂ)}
        one_mem' := fun g => by rw [map_one, one_mul]
        mul_mem' := fun {x y} hx hy g => by rw [map_mul, mul_assoc, hx, hy]
        inv_mem' := fun {x} hx g => (hx (finGL E a x⁻¹ * g)).symm.trans (by rw [← mul_assoc (finGL E a x), ← map_mul, mul_inv_cancel, map_one, one_mul]) }
    exact Subgroup.isOpen_mono (H₁ := U) (H₂ := S) (fun u hu g => by rw [hleft u hu]) hUo
  · exact mul_nonneg (inv_nonneg.2 hpos.le) (h0 g)
  · rw [integral_complex_ofReal, integral_const_mul, inv_mul_cancel₀ hpos.ne']; simp
  · refine congrArg (fun t : ℝ => ((c * t : ℝ) : ℂ)) (?_ : f₀ _ = f₀ _)
    simp only [f₀, P, Q, map_mul, pInf_infGL, pFin_infGL, mul_one, one_mul, _root_.mul_inv_rev]
    rw [← hbc k (GeneralLinearGroup.map (pInf E) g * _), ← hbc k ((Unitary.toUnits k)⁻¹ * _)]
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
  · have h : f₀ g ≠ 0 := fun e => hg (by simp [e])
    obtain ⟨y, hy, e⟩ := hsub (hsm g h).1
    obtain rfl : y = P g := Units.ext e
    exact ⟨_, hy, _, (hsm g h).2, (infGL_mul_finGL g).symm⟩

theorem one_mem_smv (μ : Measure (GA E 1)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : oneFn E 1 ∈ smv μ ⊤ := by
  have h : MemL2Quotient (latticeGL E 1) μ (oneFn E 1).1 := memL2_of_rank_one continuous_const fun _ _ _ => rfl
  refine mem_smv.2 fun l => ?_
  induction l using List.reverseRecOn with
  | nil =>
    have e : word ([] : List (Lie E 1)) (oneFn E 1) = oneFn E 1 := by simp [word]
    rw [e]
    refine ⟨one_mem_cuspCont_iff.2 le_rfl, ?_, ⟨1, fun g => by simp [oneFn]⟩, h.toL2, trivial, h.lift_toL2_ae_eq⟩
    have : {k | finRep E 1 k (oneFn E 1) = oneFn E 1} = Set.univ := Set.eq_univ_of_forall fun k => rfl
    rw [this]; exact isOpen_univ
  | append_singleton l X _ =>
    have e : word (l ++ [X]) (oneFn E 1) = 0 := by simp [word, List.map_append, List.prod_append, lie_oneFn]
    rw [e]; exact zero_mem _

theorem smv_top_ne_bot (μ : Measure (GA E 1)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    smv μ (⊤ : Submodule ℂ (L2 (latticeGL E 1) μ)) ≠ ⊥ := by
  intro h
  have h1 := one_mem_smv μ
  rw [h, Submodule.mem_bot] at h1
  have h2 := congrFun (congrArg Subtype.val h1) 1
  simp [oneFn] at h2

theorem exists_isDirac' (μ : Measure (GA E a)) [μ.IsHaarMeasure] (N : Set (GL (Fin a) (Cinf E))) (hN : N ∈ 𝓝 1) :
    ∃ U f, IsDirac μ U N f ∧ IsTestGL f ∧ f ≠ 0 := by
  have h := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
  obtain ⟨U, hU⟩ := h
  obtain ⟨f, hf⟩ := exists_isDirac μ U hU.1 (by first | exact hU.2 | exact hU.2.1) N hN
  refine ⟨U, f, hf, hf.test, fun e => ?_⟩
  have := hf.mass
  simp [e] at this
end GlobalTheory.GLFin.Inhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerSectionNonzeroAtOrigin
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
noncomputable section

namespace GlobalTheory.Poinc.Origin
open GlobalTheory.UT.CoefBasic

theorem exists_sec_value_ne_zero : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ k : ℕ, 4 ≤ k → ∃ (t : SecA A F k) (c : F), c ≠ 0 ∧ ∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val := by
  intro hL R _ _ A F _ _ ρ hρ k hk
  obtain ⟨M, s, hcov⟩ := (hL.1.ample _ A k hk).1 ⊤ (isAffineOpen_top _)
  obtain ⟨i', hi⟩ : ∃ i' : A.A.left ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.A.left.topIso.inv, A.A.left.topIso.inv_hom_id⟩
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  let χ : (TFK (R := R) F).left ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme :=
    (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ i'
  have hmem : χ z ∈ (⨆ j, nonzeroLocus (s j)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  obtain ⟨t, ht⟩ := exists_sec A.isLB (φ := fun _ : Fin k => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => 1)
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => (k : ℤ))
      (fun U _ f => by
        simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (VVRank.pullTo (L := A.L) (φ := fun _ : Fin k => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd (TFK (R := R) F) A.A).left ≫ i') (fun _ => by rw [Category.assoc, hi, Category.comp_id]))
  obtain ⟨c, hc⟩ := ThetaSpan.exists_value A hρ (F := F) (k := k) t
  refine ⟨t, c, ?_, hc⟩
  rintro rfl
  obtain ⟨J, hJ⟩ := exists_good' A.isLB (Z := (TFK (R := R) F).left) z
  have h1 := hc z J hJ
  have h0 : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z 0) = 0 := by
    show cst (R := R) F z 0 = 0
    rw [cst_eq, map_zero]
  rw [h0, zero_mul] at h1
  have h2 : sA t (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left z J = sval (s j) χ z J :=
    (ht _ _ z J hJ).trans ((VVRank.sval_pullTo _ _ _ _ z hJ).trans (by simp only [χ, Category.assoc]))
  have hu : IsUnit (sval (s j) χ z J) :=
    (AmpleSpan.mem_nonzeroLocus_iff_gs (s j) χ z (hJ.mem (fun _ : Fin k => (A.A.hom ⁻¹ᵁ ⊤).ι) χ)).1 hj
  rw [← h2, h1] at hu
  exact not_isUnit_zero hu

end GlobalTheory.Poinc.Origin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalIsometriesInnerAutAdelicFrameIsometry
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.FinIsoLocal

theorem bij_of_frame {A : Type} [CommRing A] {m n : ℕ} (h : n = m) (j : Matrix (Fin m) (Fin n) A) (β : GL (Fin n) A)
    (M : GL (Fin m) A) (hj : j * β.val = M.val.submatrix id (Fin.cast h)) : Function.Bijective j.mulVec := by
  subst h
  have hj' : j = M.val * (β⁻¹).val := by
    have e : M.val.submatrix id (Fin.cast rfl) = M.val := by ext a b; rfl
    rw [e] at hj
    rw [← hj, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  refine GlobalTheory.FinAdIdent.bij_of_inv (j' := β.val * (M⁻¹).val) ?_ ?_
  · rw [hj', Matrix.mul_assoc, ← Matrix.mul_assoc (β⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rw [hj', Matrix.mul_assoc, ← Matrix.mul_assoc (M⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]

end GlobalTheory.FinIsoLocal

theorem GlobalTheory.FinIsoLocal.exists_local_inner : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (i : Fin D.R.m) (j : Matrix (Fin (Wc D i).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (Φ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)), GlobalTheory.CuspMult.IsFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) R.Pg j Φ → ∃ (jl : ∀ v, GLoc D.sp.cm.sig (Yc D 0).gram v ≃ₜ* GLoc D.sp.cm.sig (Wc D i).gram v) (Φ₀ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)) (b : GfC (Yc D 0)), (∀ v, IsLatticeConj (frameLat (Yc D 0)) (frameLat (Wc D i)) (jl v)) ∧ (∀ v g, Φ₀ (locFin (Yc D 0) v g) = locFin (Wc D i) v (jl v g)) ∧ ∀ g, Φ g = Φ₀ (b * g * b⁻¹) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i j Φ hΦ
  obtain ⟨h, u, hu, -⟩ := hΦ.frame
  have hbij := GlobalTheory.FinIsoLocal.bij_of_frame h j (R.βY 0) (R.βW i * intGL D.host.F D.host.E (Wc D i).rank u) hu
  have hIs : GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsIsom (Yc D 0) (Wc D i) (Formalism.L2.Herm.Af D.host.F) j := ⟨hbij, hΦ.isom⟩
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy (Yc D 0) (Wc D i) j Φ := hΦ.conj
  obtain ⟨β₀, hβ₀, -⟩ := GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice D (Yc D 0)
  obtain ⟨β₀', hβ₀', -⟩ := GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice D (Wc D i)
  have hT : GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.OnePlaceOver (D := D) (∅ : Set (Formalism.L2.DIV.Pl D.host.E)) := by
    intro PP hPP; exact absurd hPP (Set.notMem_empty PP)
  obtain ⟨j₀, hL, hM⟩ := GlobalTheory.FinAdIdent.globalIsometry D (Yc D 0) (Wc D i) h (frameLat (Yc D 0)) (frameLat (Wc D i))
    β₀ β₀' 1 1 hβ₀ hβ₀' ∅ hT
  obtain ⟨Φ₀, hC₀, -⟩ := GlobalTheory.FinAdIdent.inducedIso D (Yc D 0) (Wc D i) h (frameLat (Yc D 0)) (frameLat (Wc D i))
    β₀ β₀' 1 1 hβ₀ hβ₀' ∅ j₀ hL hM
  obtain ⟨jl, h1, h2⟩ := GlobalTheory.T.adelicLatticeIsometry_eq_prod_localComponents D (Yc D 0) (Wc D i) j₀ Φ₀ hL hC₀
  obtain ⟨b, hb⟩ := GlobalTheory.T.adelicIsometryConj_differ_by_innerAutomorphism D (Yc D 0) (Wc D i) j j₀ Φ Φ₀ hIs hL.1 hC hC₀
  exact ⟨jl, Φ₀, b, h1, h2, hb⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIdempotentAdelicLatticeModPrimeStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_idempotent_adelicLattice_mod_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d),
    W.L.IsLattice E → ∀ (v : Pl F) (p : ℕ), 0 < p → (p : 𝓞 F) ∈ v.asIdeal →
    ∀ f : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, f *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∃ y ∈ GlobalTheory.InertSph.latAt W v, (f ^ (2 * N)) *ᵥ z - (f ^ N) *ᵥ z = p • y := by
  first | exact @GlobalTheory.LatIdem.exists_pow_idem | exact GlobalTheory.LatIdem.exists_pow_idem | (intros; apply GlobalTheory.LatIdem.exists_pow_idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalSubBoundedInfiniteSmallFiniteStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_sub_bounded_infinite_small_finite : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (U : Set (Af E)), U ∈ nhds (0 : Af E) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Ad E, ∃ ξ : E, ‖pInf E (x - algebraMap E (Ad E) ξ)‖ ≤ R ∧ pFin E (x - algebraMap E (Ad E) ξ) ∈ U := by
  first | exact @GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small | exact GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small | (intros; apply GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealDiagonalInfGLEqPositiveIdeleDiagonalStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realDiagonal_infGL_eq_positiveIdeleDiagonal : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∃ d : GL (Fin a) (Cinf E), d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) ∧ diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) = infGL E a d := by
  first | exact @GlobalTheory.SiegelTorusInf.exists_diag_infGL | exact GlobalTheory.SiegelTorusInf.exists_diag_infGL | (intros; apply GlobalTheory.SiegelTorusInf.exists_diag_infGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingInertPassageCarriedByFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separating_inertPassage_carried_by_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∃ tr, R.TrISem F tr ∧ ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) → ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2) := by
  first | exact @GlobalTheory.exists_inert_passage_separating | exact GlobalTheory.exists_inert_passage_separating | (intros; apply GlobalTheory.exists_inert_passage_separating <;> assumption)
end

