import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentralCircleOneParameterUnitaryRealPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetColumnsNeZeroOfPointValuesIndependent
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.DetNe

theorem det_ne_zero_of_indep : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (u : Fin (S.D + 1) × Fin S.N → E), LinearIndependent E (fun k => word Φ.mul (fun q j => u ((col k).β q, j)) (Φ.ι (col k).x)) → S.det c col ≠ 0 := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc col u hind hdet
  obtain ⟨c', hspan, hval⟩ := GlobalTheory.T.hermitianMultiplicationFlat_columns_eval F A S hS E A' s δ Φ d b c hc
  set v : Fin d → A' := fun k => word Φ.mul (fun q j => u ((col k).β q, j)) (Φ.ι (col k).x) with hv
  set M : Matrix (Fin d) (Fin d) E := Matrix.of fun i k => c' i (v k) with hM
  have hMdet : M.det = 0 := by
    have h1 : aeval u (S.det c col) = 0 := by rw [hdet, map_zero]
    rw [Sys.det, AlgHom.map_det] at h1
    convert h1 using 2
    ext i k
    simp only [hM, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
    exact ((hval (col k) u).2 i).symm
  obtain ⟨a, ha, hMa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hMdet
  have hmem : ∀ k, v k ∈ Submodule.span E (Φ.ι '' S.V S.T) := fun k => (hval (col k) u).1
  set x : A' := ∑ k, a k • v k with hx
  have hxmem : x ∈ Submodule.span E (Φ.ι '' S.V S.T) :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hmem k)
  have hcx : ∀ i, c' i x = 0 := by
    intro i
    have := congrFun hMa i
    simp only [Matrix.mulVec, dotProduct, hM, Matrix.of_apply, Pi.zero_apply] at this
    rw [hx, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hx0 : x = 0 := by
    rw [← hspan x hxmem]
    simp [hcx]
  have ha0 := (Fintype.linearIndependent_iff.mp hind) a hx0
  exact ha (funext ha0)

end GlobalTheory.HSShort.DetNe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def diagonalBlockOfMatrix {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : Matrix (Fin d) (Fin d) (AE F E) :=
  ⅟(2 : AF F) • ((matD g).toBlocks₁₁ + (matD g).toBlocks₁₂ + (matD g).toBlocks₂₁ + (matD g).toBlocks₂₂)

def BigCell {σ : E →ₐ[F] E} {d : ℕ} (W : Spc F E d) (v : Pl F) (g : UD σ W) : Prop :=
  ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * diagonalBlockOfMatrix g = 1 ∧
    ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v

end GlobalTheory.DblVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralInvariantFormDiagonalLagrangianStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_integral_invariant_form_diagonalLagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type)
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)),
    IsStd ψ → IsDblCoord (cA σ) (-1) JA JB d dd →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (AE F E), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  first | exact @GlobalTheory.RealLift.diagLagr_invForm | exact GlobalTheory.RealLift.diagLagr_invForm | (intros; apply GlobalTheory.RealLift.diagLagr_invForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledHermitianSpaceFrameOfFrameStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_hermitian_space_frame_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (P Q R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ),
    Framed τ JA JB a b A C → Framed τ JA (dbl JB) a b A (fun w => dblM (C w)) := by
  first | exact @GlobalTheory.RealLift.Dbl.framed_dbl | exact GlobalTheory.RealLift.Dbl.framed_dbl | (intros; apply GlobalTheory.RealLift.Dbl.framed_dbl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSiegelParabolicDiagonalActionIntegral
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.InertDbl

theorem diag_mulVec_mem_latAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d : ℕ} (W : Spc F E d) (v : Pl F) (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
    (t : Matrix (Fin d) (Fin d) (AE F E)) (h : M * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * t)
    (hM : ∀ z ∈ latAtD W v, M *ᵥ z ∈ latAtD W v) (z : Fin d → AE F E) (hz : z ∈ GlobalTheory.InertSph.latAt W v) :
    t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  have key : ∀ y : Fin d → AE F E,
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *ᵥ y = Sum.elim y y := by
    intro y
    simp [diagCols, Matrix.fromRows_mulVec]
  have h1 : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *ᵥ z ∈ latAtD W v := by
    rw [key]; exact ⟨hz, hz⟩
  have h2 := hM _ h1
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, key] at h2
  exact h2.1

theorem parD_diag_action :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F),
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ W v, ∀ t : GL (Fin d) (AE F E),
      GlobalTheory.InertDbl.matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (AE F E)) →
      At (evFin F v) ((t : Matrix (Fin d) (Fin d) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
        ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ d W v p hp t h'
  have h : matD p * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * (t : Matrix (Fin d) (Fin d) (AE F E)) := h'
  obtain ⟨⟨hAt, hK⟩, -⟩ := hp
  have hinv : matD p⁻¹ * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) := by
    have h1 : matD p⁻¹ * matD p = 1 := p.1.inv_mul
    have h2 : (t : Matrix (Fin d) (Fin d) (AE F E)) *
        ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = 1 := t.mul_inv
    calc matD p⁻¹ * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))
        = matD p⁻¹ * ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((t : Matrix (Fin d) (Fin d) (AE F E)) *
            ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)))) := by rw [h2, Matrix.mul_one]
      _ = _ := by
        rw [← Matrix.mul_assoc (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)), ← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨?_, fun z hz => ⟨diag_mulVec_mem_latAt W v _ _ h (fun y hy => (hK y hy).1) z hz,
    diag_mulVec_mem_latAt W v _ _ hinv (fun y hy => (hK y hy).2) z hz⟩⟩
  intro u hu
  have h0 := hAt u hu
  have h3 : (matD p - 1) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((t : Matrix (Fin d) (Fin d) (AE F E)) - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]
  have h4 : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
      (u • ((t : Matrix (Fin d) (Fin d) (AE F E)) - 1)) = 0 := by
    rw [Matrix.mul_smul, ← h3, ← Matrix.smul_mul, h0, Matrix.zero_mul]
  ext i j
  have h5 := congrFun (congrFun h4 (Sum.inl i)) j
  rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at h5
  exact h5

end GlobalTheory.InertDbl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceFrameColBlocksEqStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledSpaceFrame_colBlocks_eq : ∀ (α β : Type) [Fintype β] (P Q R S : ℕ) (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (c : Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ),
    (A * c * (dblM C)ᵀ).toCols₁ =
        A * c.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) * Cᵀ ∧
    (A * c * (dblM C)ᵀ).toCols₂ =
        A * c.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) * Cᵀ ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) =
      Jm P Q * c.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) *
        Jm R S ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) =
      -(Jm P Q * c.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) *
        Jm R S) := by
  first | exact @GlobalTheory.RealLift.Dbl.dblM_colBlocks | exact GlobalTheory.RealLift.Dbl.dblM_colBlocks | (intros; apply GlobalTheory.RealLift.Dbl.dblM_colBlocks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerBigCellFactorizati
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacFactor

open Matrix GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

@[reducible] def invTwoE : Invertible (2 : AE F E) :=
  (Invertible.map (algebraMap (AF F) (AE F E)) (2 : AF F)).copy 2 (map_ofNat _ 2).symm

theorem invOf_two_eq [Invertible (2 : AE F E)] :
    (⅟(2 : AE F E)) = algebraMap (AF F) (AE F E) (⅟(2 : AF F)) :=
  invOf_eq_right_inv (by rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, mul_invOf_self, map_one])

theorem valued_two {v : Pl F} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : Valued.v (2 : Fv F v) = 1 := by
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (2 : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h2] at this
  convert this using 2
  exact (map_ofNat _ 2).symm

theorem evFin_half_mem {v : Pl F} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have e : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h := congrArg Valued.v e
  rw [map_mul, valued_two h2, mul_one, map_one] at h
  rw [h]

theorem half_smul_mem {d : ℕ} {W : Spc F E d} {v : Pl F} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : (⅟(2 : AF F)) • y ∈ GlobalTheory.InertSph.latAt W v := by
  have hle : GlobalTheory.InertSph.latAt W v ≤ (GlobalTheory.InertSph.latAt W v).comap
      (DistribMulAction.toAddMonoidHom (Fin d → AE F E) (⅟(2 : AF F))) := by
    show AddSubgroup.closure _ ≤ _
    rw [AddSubgroup.closure_le]
    rintro z ⟨a, ha, hint, y, hy, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply, smul_smul]
    refine AddSubgroup.subset_closure ⟨⅟(2 : AF F) * a, fun u hu => ?_, ?_, y, hy, rfl⟩
    · rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]; exact mul_mem (evFin_half_mem h2) hint
  exact hle hy

section Lat

variable {d : ℕ} {W : Spc F E d} {v : Pl F}

theorem latD_add {z w : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) (hw : w ∈ latD W v) : z + w ∈ latD W v :=
  ⟨add_mem hz.1 hw.1, add_mem hz.2 hw.2⟩

theorem latD_sub {z w : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) (hw : w ∈ latD W v) : z - w ∈ latD W v :=
  ⟨sub_mem hz.1 hw.1, sub_mem hz.2 hw.2⟩

theorem latD_half [Invertible (2 : AE F E)] (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {z : Fin d ⊕ Fin d → AE F E}
    (hz : z ∈ latD W v) : (⅟(2 : AE F E)) • z ∈ latD W v := by
  rw [invOf_two_eq, algebraMap_smul]
  exact ⟨half_smul_mem h2 hz.1, half_smul_mem h2 hz.2⟩

theorem latD_diag {y : Fin d → AE F E} (hy : y ∈ GlobalTheory.InertSph.latAt W v) :
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1) *ᵥ y ∈ latD W v := by
  rw [fromRows_mulVec, one_mulVec]
  exact ⟨hy, hy⟩

theorem latD_anti {y : Fin d → AE F E} (hy : y ∈ GlobalTheory.InertSph.latAt W v) :
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1)) *ᵥ y ∈ latD W v := by
  rw [fromRows_mulVec, one_mulVec, neg_mulVec, one_mulVec]
  exact ⟨hy, neg_mem hy⟩

theorem lat_diagT {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) :
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  rw [fromCols_mulVec, one_mulVec, one_mulVec]
  exact add_mem hz.1 hz.2

theorem lat_antiT {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) :
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  rw [fromCols_mulVec, one_mulVec, neg_mulVec, one_mulVec]
  exact add_mem hz.1 (neg_mem hz.2)

end Lat

section Group

variable {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F}

theorem KD_mul {a b : UD σ W} (ha : a ∈ KD σ W v) (hb : b ∈ KD σ W v) : a * b ∈ KD σ W v := by
  have hm : matD (a * b) = matD a * matD b := rfl
  have hi : matD (a * b)⁻¹ = matD b⁻¹ * matD a⁻¹ := by rw [_root_.mul_inv_rev]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · rw [hm, show matD a * matD b - 1 = (matD a - 1) * matD b + (matD b - 1) by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel, smul_add, ← Matrix.smul_mul, ha.1 u hu, hb.1 u hu,
      Matrix.zero_mul, add_zero]
  · rw [hm, hi, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(ha.2 _ (hb.2 z hz).1).1, (hb.2 _ (ha.2 z hz).2).2⟩

theorem KD_inv {a : UD σ W} (ha : a ∈ KD σ W v) : a⁻¹ ∈ KD σ W v := by
  have h1 : matD a⁻¹ * matD a = 1 := by
    rw [show matD a⁻¹ * matD a = matD (a⁻¹ * a) from rfl, inv_mul_cancel]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · rw [show matD a⁻¹ - 1 = -(matD a⁻¹ * (matD a - 1)) by rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel,
      smul_neg, ← Matrix.mul_smul, ha.1 u hu, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(ha.2 z hz).2, (ha.2 z hz).1⟩

end Group

end GlobalTheory.DblVacFactor

namespace GlobalTheory.DblVacFactor

open Matrix GlobalTheory.DblVac GlobalTheory.BigCell

theorem factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
    IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d).det →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v,
      ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d)⁻¹ *ᵥ z ∈
        GlobalTheory.InertSph.latAt W v) →
    ∃ p q : GlobalTheory.DblVac.UD σ W, p ∈ GlobalTheory.DblVac.KD σ W v ∧ p ∈ GlobalTheory.DblVac.PDiag σ W ∧
      q ∈ GlobalTheory.DblVac.KD σ W v ∧ q ∈ GlobalTheory.DblVac.PAnti σ W ∧ g = p * q := by
  intro F E _ _ _ _ _ σ d W v h2 g hg hdet hC
  letI : Invertible (2 : AE F E) := invTwoE
  have hNt : (antiCols (F := F) (E := E) d)ᵀ = fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) := by
    rw [antiCols, transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  rw [hNt] at hdet hC
  unfold antiCols at hdet hC
  set G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := matD g with hGdef
  set f : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hf
  set J : Matrix (Fin d) (Fin d) (AE F E) := incM F W.J with hJ
  have hG : Gᵀ * dbl J * G.map f = dbl J := g.2
  have h1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map f = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hm1 : (-1 : Matrix (Fin d) (Fin d) (AE F E)).map f = -1 := by rw [Matrix.map_neg _ (map_neg f), h1]
  have hΔT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 1 := by
    rw [transpose_fromRows, transpose_one]
  have hNT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 (-1) := by
    rw [transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  have hΔf : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)).map f =
      fromRows 1 1 := by rw [fromRows_map, h1]
  have hNf : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)).map f =
      fromRows 1 (-1) := by rw [fromRows_map, h1, hm1]
  have hΔtf : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)).map f =
      fromCols 1 1 := by rw [fromCols_map, h1]
  have hNtf : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)).map f =
      fromCols 1 (-1) := by rw [fromCols_map, h1, hm1]
  set D : Matrix (Fin d) (Fin d) (AE F E) := (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) :
    Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) with hDdef
  have hD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hD' : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ hdet
  set M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
    ((fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * D⁻¹) *
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) with hMdef
  have hinv := mul_inv_eq (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) e1
    ((fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * D⁻¹)
  have hmem := mem_unitary f J (dbl J) G _ _ _ _ D⁻¹ hG hΔT hNT hΔf hΔtf hNf hNtf (e3 J) (e4 J) (e5 J) (e6 J) (e7 J) hD
  let P : GL (Fin d ⊕ Fin d) (AE F E) := ⟨1 + ⅟(2 : AE F E) • M, 1 - ⅟(2 : AE F E) • M, hinv.1, hinv.2⟩
  let p : UD σ W := ⟨P, hmem⟩
  have hdetS : IsUnit (⅟(2 : AE F E) • D).det := by
    rw [det_smul]
    exact ((isUnit_of_invertible (⅟(2 : AE F E))).pow _).mul hdet
  let s : GL (Fin d) (AE F E) := ((Matrix.isUnit_iff_isUnit_det _).mpr hdetS).unit

  have hΔtN : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) *
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = 0 := by
    simp [fromCols_mul_fromRows]
  have hMu : ∀ u : AF F, evFin F v u = 0 → u • M = 0 := by
    intro u hu
    have hE : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * (G - 1) *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hΔtN, sub_zero]
    have hu' : u • (G - 1) = 0 := hg.1 u hu
    calc u • M = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * (u • (G - 1)) * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * D⁻¹) * (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
          rw [hMdef, hE]; simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = 0 := by rw [hu']; simp
  have hpK : p ∈ KD σ W v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
    · show u • ((1 + ⅟(2 : AE F E) • M) - 1) = 0
      rw [add_sub_cancel_left, smul_comm, hMu u hu, smul_zero]
    · show (1 + ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_add hz (latD_half h2 (latD_diag (lat_diagT (hg.2 _ (latD_anti (hC _ (lat_antiT hz)))).1)))
    · show (1 - ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_sub hz (latD_half h2 (latD_diag (lat_diagT (hg.2 _ (latD_anti (hC _ (lat_antiT hz)))).1)))
  refine ⟨p, p⁻¹ * g, hpK, ⟨1, ?_⟩, KD_mul (KD_inv hpK) hg, ⟨s, ?_⟩, (mul_inv_cancel_left p g).symm⟩
  · have key : ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hMdef, Matrix.mul_assoc _ _ (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)), e1, Matrix.mul_zero,
        smul_zero, add_zero]
    show ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))
    rw [Units.val_one, Matrix.mul_one]
    exact key
  · show (1 - ⅟(2 : AE F E) • M) * G * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * (s : Matrix (Fin d) (Fin d) (AE F E))
    rw [IsUnit.unit_spec]
    exact q_col G _ _ _ _ D⁻¹ e2 hD'

end GlobalTheory.DblVacFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentralCircleOneParameterUnitaryRealPlaceStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_circle_oneParameter_unitary_realPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type)
    [Fintype β] [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E))
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (w₀ : InfinitePlace F), IsCMExt F E σ →
    ∃ z : ℝ → (AE F E)ˣ, ∃ γ ∈ RLines σ J,
      IsGen τ C γ (fun w => if w = w₀ then Complex.I • (1 : Mat R S) else 0) ∧
      (∀ t : ℝ, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) = (z t : AE F E) • (1 : Matrix β β (AE F E))) ∧
      (∀ t : ℝ, At (evI F) ((z t : AE F E) - 1)) ∧
      ∀ (t : ℝ) (w : InfinitePlace F), piInf (τ w) (z t : AE F E) = if w = w₀ then Complex.exp (t * Complex.I) else 1 := by
  first | exact @GlobalTheory.CentralLine.exists_central_line | exact GlobalTheory.CentralLine.exists_central_line | (intros; apply GlobalTheory.CentralLine.exists_central_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSubgroupSubsetNhdsOne
section
open NumberField MeasureTheory Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.GLFin

namespace GlobalTheory.GLFinSmall

open Set Filter Pointwise Topology

theorem exists_nhds_mul_subset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {W : Set G} (hWc : IsCompact W) (hWo : IsOpen W) : ∃ T ∈ 𝓝 (1 : G), W * T ⊆ W := by
  apply hWc.induction_on (p := fun S ↦ ∃ T ∈ 𝓝 (1 : G), S * T ⊆ W)
    ⟨Set.univ, by simp only [univ_mem, Set.empty_mul, empty_subset, and_self]⟩
    (fun _ _ huv ⟨T, hT, mem⟩ ↦ ⟨T, hT, (mul_subset_mul_right huv).trans mem⟩)
    fun U V ⟨T₁, hT₁, mem1⟩ ⟨T₂, hT₂, mem2⟩ ↦ ⟨T₁ ∩ T₂, inter_mem hT₁ hT₂, by
      rw [union_mul]
      exact union_subset (mul_subset_mul_left inter_subset_left |>.trans mem1)
        (mul_subset_mul_left inter_subset_right |>.trans mem2)⟩
  intro x memW
  have : (x, 1) ∈ (fun p : G × G ↦ p.1 * p.2) ⁻¹' W := by simp [memW]
  rcases isOpen_prod_iff.mp (continuous_mul.isOpen_preimage W hWo) x 1 this with
    ⟨U, V, Uopen, Vopen, xmemU, onememV, prodsub⟩
  have h6 : U * V ⊆ W := mul_subset_iff.mpr (fun _ hx _ hy ↦ prodsub (mk_mem_prod hx hy))
  exact ⟨U ∩ W, ⟨U, Uopen.mem_nhds xmemU, W, fun _ a ↦ a, rfl⟩,
    V, IsOpen.mem_nhds Vopen onememV, fun _ a ↦ h6 ((mul_subset_mul_right inter_subset_left) a)⟩

def rightStab {G : Type} [Group G] (W : Set G) : Subgroup G where
  carrier := {g | ∀ w, w ∈ W ↔ w * g ∈ W}
  one_mem' := by intro w; simp
  mul_mem' := by
    intro g h hg hh w
    rw [hg w, hh (w * g), mul_assoc]
  inv_mem' := by
    intro g hg w
    rw [hg (w * g⁻¹), inv_mul_cancel_right]

theorem exists_compact_open_subgroup_subset {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {W : Set G} (hWc : IsCompact W) (hWo : IsOpen W) (h1 : (1 : G) ∈ W) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧ (U : Set G) ⊆ W := by
  obtain ⟨T, hT, hTW⟩ := exists_nhds_mul_subset hWc hWo
  have hsub : T ∩ T⁻¹ ⊆ (rightStab W : Set G) := by
    intro v hv w
    constructor
    · intro hw; exact hTW (Set.mul_mem_mul hw hv.1)
    · intro hw
      have : w * v * v⁻¹ ∈ W := hTW (Set.mul_mem_mul hw (Set.mem_inv.mp hv.2))
      simpa using this
  have hnhds : (rightStab W : Set G) ∈ 𝓝 (1 : G) :=
    Filter.mem_of_superset (inter_mem hT (inv_mem_nhds_one G hT)) hsub
  have hopen : IsOpen (rightStab W : Set G) := Subgroup.isOpen_of_mem_nhds _ hnhds
  have hW : (rightStab W : Set G) ⊆ W := by
    intro g hg
    have := (hg 1).mp h1
    simpa using this
  refine ⟨rightStab W, hopen, ?_, hW⟩
  exact hWc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) hW

end GlobalTheory.GLFinSmall

theorem GlobalTheory.GLFin.exists_compact_open_subgroup_subset_nhds_one :
    ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E))),
      B ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ U : Subgroup (GL (Fin a) (Af E)),
        IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧
          (U : Set (GL (Fin a) (Af E))) ⊆ B := by
  intro E _ _ a B hB
  obtain ⟨W, hWo, hWc, -, h1, hWB⟩ := GlobalTheory.T.exists_compact_clopen_nhds_one_GL_finiteAdeles E a B hB
  obtain ⟨U, hUo, hUc, hUW⟩ := GlobalTheory.GLFinSmall.exists_compact_open_subgroup_subset hWc hWo h1
  exact ⟨U, hUo, hUc, hUW.trans hWB⟩
end

