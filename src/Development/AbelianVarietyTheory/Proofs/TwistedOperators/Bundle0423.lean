import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0417
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0412
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0413
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0416
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0418
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothWeilOrbitPreservedByHeisenbergDerivativesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_weilOrbit_preserved_by_heisenbergDerivatives : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) → ∀ u, At (evI F) u → ∀ f ∈ G.M.Pol B.ψ B.emb,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f p.2) → (∃ f' ∈ G.M.Pol B.ψ B.emb, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0) → ∀ f₁ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (G.M.heisLine B.ψ u) f f₁ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) ∧ ∃ f₁' ∈ G.M.Pol B.ψ B.emb, ∀ x, HasDerivAt (fun t => T t f₁ x) (f₁' x) 0 := by
  first | exact @GlobalTheory.HeisOrbit.orbit_heis | exact GlobalTheory.HeisOrbit.orbit_heis | (intros; apply GlobalTheory.HeisOrbit.orbit_heis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothWeilOrbitRealPassesToHeisenbergDerivativesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_weilOrbit_real_passes_to_heisenbergDerivatives : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) →
          (∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0) →
          ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ →
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) ∧ ∃ f₁' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₁ x) (f₁' x) 0 := by
  first | exact @GlobalTheory.HeisOrbitReal.orbit_heis_real | exact GlobalTheory.HeisOrbitReal.orbit_heis_real | (intros; apply GlobalTheory.HeisOrbitReal.orbit_heis_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBigCellExistsAdmissibleInverse
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitPlaceBigCell

theorem splitPlace_bigCell_exists_admissible_inverse : (∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl F), (∀ i j, σ (W.J j i) = -W.J i j) →
    IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) →
      (∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) →
      ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro hLoc F E _ _ _ _ _ σ d W v hskew h2 π₁ π₂ b₁ b₂ hd hSx g hg
  obtain ⟨hc₁, hc₂, ha₁, ha₂, hinj, hsurj, hlat⟩ := hd
  obtain ⟨S, hSdet, hS⟩ := hSx
  obtain ⟨k11, k12, k21, k22, k11', k12', k21', k22'⟩ := GlobalTheory.T.doubledVacuumLatticeStabilizer_blocks_keep_lattice σ W v g hg
  have I := fun A hA => GlobalTheory.T.integral_localBasisConjugates_of_keepsLatticeAtPlace W v π₁ π₂ b₁ b₂ hlat hsurj A hA
  have hinv : GlobalTheory.DblVac.matD g⁻¹ * GlobalTheory.DblVac.matD g = 1 := g.1.inv_mul
  obtain ⟨G₁, hG₁, hG₁u⟩ := GlobalTheory.T.integralBlocks_leftInverse_isUnit_det_splitPlace v π₁ b₁ (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv
    (I _ k11).1 (I _ k12).1 (I _ k21).1 (I _ k22).1 (I _ k11').1 (I _ k12').1 (I _ k21').1 (I _ k22').1
  obtain ⟨G₂, hG₂, -⟩ := GlobalTheory.T.integralBlocks_leftInverse_isUnit_det_splitPlace v π₂ b₂ (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv
    (I _ k11).2 (I _ k12).2 (I _ k21).2 (I _ k22).2 (I _ k11').2 (I _ k12').2 (I _ k21').2 (I _ k22').2
  have hU := GlobalTheory.T.unitary_at_splitPlace_localBases σ W v π₁ π₂ b₁ b₂ hc₁ g
  have e : ∀ {m n o : Type} [Fintype n] (A : Matrix m n (v.adicCompletionIntegers F))
      (B : Matrix n o (v.adicCompletionIntegers F)),
      (A * B).map (fun x => (x : Fv F v)) = A.map (fun x => (x : Fv F v)) * B.map (fun x => (x : Fv F v)) :=
    fun A B => Matrix.map_mul (f := (v.adicCompletionIntegers F).subtype)
  have hUO : G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) := by
    apply Matrix.map_injective (f := fun x : v.adicCompletionIntegers F => (x : Fv F v)) Subtype.coe_injective
    beta_reduce
    have en : (-S).map (fun x => (x : Fv F v)) = -(S.map (fun x => (x : Fv F v))) := by ext i j; rfl
    have ez : (0 : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F)).map (fun x => (x : Fv F v)) = 0 := by
      ext i j; rfl
    rw [e, e, Matrix.transpose_map, Matrix.fromBlocks_map, en, ez, hG₁, hG₂, hS]
    exact hU
  obtain ⟨X₁, X₂, hX, hP₁, hP₂⟩ := hLoc h2 S hSdet G₁ G₂ hG₁u hUO
  obtain ⟨Y, hYat, hY₁, hY₂, hYadm⟩ :=
    GlobalTheory.T.exists_admissible_lift_splitPlaceConjugatePair σ W v hskew π₁ π₂ b₁ b₂ hc₁ hc₂ hinj hsurj S hS X₁ X₂ hX
  obtain ⟨N₁, hN₁, hN₁i⟩ := GlobalTheory.T.halfBlockSum_exists_inverse_integral_splitPlace v π₁ b₁ ha₁ (GlobalTheory.DblVac.matD g) G₁ hG₁ X₁ hP₁ Y hY₁
  obtain ⟨N₂, hN₂, hN₂i⟩ := GlobalTheory.T.halfBlockSum_exists_inverse_integral_splitPlace v π₂ b₂ ha₂ (GlobalTheory.DblVac.matD g) G₂ hG₂ X₂ hP₂ Y hY₂
  have hK := GlobalTheory.T.halfBlockSumTwist_sub_one_supportedAtPlace v (GlobalTheory.DblVac.matD g) Y hg.1 hYat
  obtain ⟨M, hMK, hM₁, hM₂⟩ := GlobalTheory.T.exists_leftInverse_lifting_splitPlaceInverses v π₁ π₂ hinj hsurj _ hK N₁ N₂ hN₁ hN₂
  have hYi : ∀ (b : GL (Fin d) (Fv F v)) (X : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F)),
      ∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *
        ((b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) *
          ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))) *
        (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F := by
    intro b X i j
    have : ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *
        ((b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) *
          ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))) *
        (b : Matrix (Fin d) (Fin d) (Fv F v)) = X.map (fun x => (x : Fv F v)) := by
      simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [this]; exact (X i j).2
  refine ⟨Y, hYat, GlobalTheory.T.keepsLatticeAtPlace_of_integral_localBasisConjugates W v π₁ π₂ b₁ b₂ hlat Y ?_ ?_, hYadm, M, hMK,
    GlobalTheory.T.keepsLatticeAtPlace_of_integral_localBasisConjugates W v π₁ π₂ b₁ b₂ hlat M ?_ ?_⟩
  · rw [hY₁]; exact hYi b₁ X₁
  · rw [hY₂]; exact hYi b₂ X₂
  · rw [hM₁]; exact hN₁i
  · rw [hM₂]; exact hN₂i

end GlobalTheory.SplitPlaceBigCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridCommonDataPropertiesHoldStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testGridCommonData_properties_hold : ComOK := by
  first | exact @GlobalTheory.CoreOnto.comOK | exact GlobalTheory.CoreOnto.comOK | (intros; apply GlobalTheory.CoreOnto.comOK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStageCartanFrameConjValuesCuspFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStage_cartanFrame_conj_values_cuspForms : ∀ D : D7, ForStage D fun c _ s => ∃ (cA : GlobalTheory.Mem.Th.CptF s.V) (a : GL (Fin s.V.rank) (AE D)), GlobalTheory.Cusp.IsCartanFrame s.V cA ∧ (∀ τ, IsCartanInv (gramAt D s.V τ) (cart s.M τ)) ∧ (∀ τ, cA τ * cart s.M τ = Formalism.UG.Jpq (s.V.sig (tauE D τ)).1 (s.V.sig (tauE D τ)).2 * cA τ) ∧ GlobalTheory.Doubling.IsMaj s.V a ∧ (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) ∧ ∀ (u : s.CC c), ∀ v ∈ s.KF, (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := by
  first | exact @GlobalTheory.EvenOnto.conj_stage_val_mem_A0_and_cartan_frame | exact GlobalTheory.EvenOnto.conj_stage_val_mem_A0_and_cartan_frame | (intros; apply GlobalTheory.EvenOnto.conj_stage_val_mem_A0_and_cartan_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainUnitVacuumOtherLatticesExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_unitVacuum_otherLattices_exists : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ (r : ReLat (G.V (.core i))) (r' : ReLat (G.V (.core (i + 1)))) (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'), ∃ f₀, IsVacO W.ψ W.θ r.sp r'.sp (cart M) (cart M') (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) f₀ := by
  first | exact @GlobalTheory.CoreVacRe.vacExists_reLat | exact GlobalTheory.CoreVacRe.vacExists_reLat | (intros; apply GlobalTheory.CoreVacRe.vacExists_reLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ThetaMixInj

variable {D : D7}

theorem psi_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (t : AF D.host.F) : ψ t ≠ 0 := by
  intro h
  have e := ψ.map_add_eq_mul t (-t)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at e
  exact one_ne_zero e

theorem heisO_two (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u v : WO S T) (f : WO S T → ℂ) (z : WO S T) :
    heisO ψ S T u (heisO ψ S T v f) z = ψ (symplOH S T z u) * (ψ (symplOH S T (z + u) v) * f (z + u + v)) := rfl

theorem heisO_three (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u v t : WO S T) (f : WO S T → ℂ) (z : WO S T) :
    heisO ψ S T u (heisO ψ S T v (heisO ψ S T t f)) z =
      ψ (symplOH S T z u) * (ψ (symplOH S T (z + u) v) * (ψ (symplOH S T (z + u + v) t) * f (z + u + v + t))) := rfl

theorem incAdj_surj {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (η : Mx D ρ S.rank) :
    ∃ y, d.incAdj S y = d.incY S η := by
  refine ⟨adj (incA D (-D.host.xi0) • (η ⬝ giA S)), ?_⟩
  rw [HypDec.incAdj_apply, adj_adj, Matrix.smul_mul, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, smul_smul,
    ← map_mul, neg_mul_neg, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul]

theorem wittHyperbolic_symplecticPairing_core_dual_eq_zero {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (w : WO S T₀) (η : Mx D ρ S.rank) :
    symplOH S T (d.inc0 S w) (d.incY S η) = 0 := by
  have h := d.hO_inc S 0 0 0 η w 0
  simp only [map_zero, zero_add, add_zero, pairT, hO_eq_trace S T₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul,
    trace_zero] at h
  rw [symplOH_eq, h, map_zero]

set_option maxHeartbeats 1000000 in

theorem mixT_incAdj {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {S : HSp D} (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (g : WO S T → ℂ) (y y' : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (heisO ψ S T (d.incAdj S y') g) y = d.mixT S ψ μ 𝓕 g (y + y') := by
  funext w₀
  unfold HypDec.mixT
  refine congrArg (fun F : Mx D ρ S.rank → ℂ => ∫ ξ in 𝓕, F ξ ∂μ) (funext fun ξ => ?_)
  rw [HypDec.integrandT_eq, HypDec.integrandT_eq, heisO]
  have e1 : symplOH S T (d.incX S ξ + d.incAdj S y + d.inc0 S w₀) (d.incAdj S y') =
      symplOH S T (d.incX S ξ) (d.incAdj S y') := by
    rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_left]
    simp only [HypDec.incAdj_apply, HypDec.symplOH_incY_incY, wittHyperbolic_symplecticPairing_core_dual_eq_zero, add_zero]
  have e2 : d.incX S ξ + d.incAdj S y + d.inc0 S w₀ + d.incAdj S y' = d.incX S ξ + d.incAdj S (y + y') + d.inc0 S w₀ := by
    rw [map_add]; abel
  rw [e1, e2, ← mul_assoc, ← AddChar.map_add_eq_mul, ← GlobalTheory.OrientedHeis.symplOH_add_right, ← map_add]

theorem source {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') {S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (v : VolM D T.rank ρ) (h : ∀ x, d.mixS T ψ v.μ v.𝓕 f x = d.mixS T ψ v.μ v.𝓕 f' x) : f = f' := by
  have L := GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d v
  funext z
  have hz : z = d.extX T (z ⬝ d.jX) + d.ext0 T (z ⬝ d.j0) + d.extY T (z ⬝ d.jY) :=
    ((d.coordS T).symm_apply_apply z).symm
  generalize z ⬝ d.jX = a at hz
  generalize z ⬝ d.j0 = w at hz
  generalize z ⬝ d.jY = b at hz
  subst hz
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (d.extY T b)
  have hg' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf' (d.extY T b)
  have hk := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg (d.extX T a)
  have hk' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg' (d.extX T a)
  have hmix : ∀ x, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.extX T a) (heisO ψ S T (d.extY T b) f)) x =
      d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.extX T a) (heisO ψ S T (d.extY T b) f')) x := fun x => by
    rw [(L _ hg).1 x a, (L _ hg').1 x a, (L f hf).2.1 (x + a) b, (L f' hf').2.1 (x + a) b, h]
  have e1 := (L _ hk).2.2.2.2 w
  have e2 := (L _ hk').2.2.2.2 w
  simp only [hmix] at e1
  have hv := e1.unique e2
  rw [heisO_two, heisO_two] at hv
  have p : d.ext0 T w + d.extX T a + d.extY T b = d.extX T a + d.ext0 T w + d.extY T b := by abel
  rw [p] at hv
  exact mul_left_cancel₀ (psi_ne_zero ψ _) (mul_left_cancel₀ (psi_ne_zero ψ _) hv)

theorem target {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') {T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ)
    (v : VolM D ρ S.rank) (h : ∀ y, d.mixT S ψ v.μ v.𝓕 f y = d.mixT S ψ v.μ v.𝓕 f' y) : f = f' := by
  have L := GlobalTheory.HeisTarget.main D ψ hψ S T T₀ ρ d v.μ v.𝓕 v.covol
  funext z
  obtain ⟨y, hy⟩ := incAdj_surj d S (d.pY ⬝ z)
  have hz : z = d.incX S (d.pX ⬝ z) + d.inc0 S (d.p0 ⬝ z) + d.incAdj S y := by
    rw [hy]; exact ((d.coordT S).symm_apply_apply z).symm
  generalize d.pX ⬝ z = ξ at hz
  generalize d.p0 ⬝ z = w at hz
  subst hz
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (d.incAdj S y)
  have hg' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf' (d.incAdj S y)
  have hk := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg (d.inc0 S w)
  have hk' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg' (d.inc0 S w)
  have hm := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hk (d.incX S ξ)
  have hm' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hk' (d.incX S ξ)
  have hmix : ∀ y₀, d.mixT S ψ v.μ v.𝓕
        (heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.inc0 S w) (heisO ψ S T (d.incAdj S y) f))) y₀ =
      d.mixT S ψ v.μ v.𝓕
        (heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.inc0 S w) (heisO ψ S T (d.incAdj S y) f'))) y₀ := fun y₀ => by
    rw [(L _ hk).1 ξ y₀, (L _ hk').1 ξ y₀, (L _ hg).2.1 w y₀, (L _ hg').2.1 w y₀, mixT_incAdj, mixT_incAdj, h]
  have e1 := (L _ hm).2.2
  have e2 := (L _ hm').2.2
  simp only [hmix] at e1
  have hv := e1.unique e2
  rw [heisO_three, heisO_three, zero_add] at hv
  exact mul_left_cancel₀ (psi_ne_zero ψ _) (mul_left_cancel₀ (psi_ne_zero ψ _) (mul_left_cancel₀ (psi_ne_zero ψ _) hv))

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f f' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ), (∀ x, d.mixS T ψ v.μ v.𝓕 f x = d.mixS T ψ v.μ v.𝓕 f' x) → f = f') ∧ ∀ (T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (v : VolM D ρ S.rank), (∀ y, d.mixT S ψ v.μ v.𝓕 f y = d.mixT S ψ v.μ v.𝓕 f' y) → f = f' :=
  fun _ _ hψ _ _ _ _ hf hf' =>
    ⟨fun _ _ d v h => source hψ hf hf' d v h, fun _ _ d v h => target hψ hf hf' d v h⟩

end GlobalTheory.ThetaMixInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleChainBounded
section
noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.ThetaGLSub GlobalTheory.ThetaGLRank

namespace GlobalTheory.ThetaGLRank

theorem boundedChains_thetaGL : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} →
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, GlobalTheory.ThetaGLSub.IsSub χ (N i)) → r ≤ L := by
  intro P k _ _ _ _ n m χ hχ
  have key : ∀ d : ℕ, ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, IsSub χ (N i) ∧ N i ≤ aug m χ ⊔ rkSub k n m (n + 1 - d)) → r ≤ L := by
    intro d
    induction d with
    | zero =>
      refine ⟨1, fun r N hN hQ => ?_⟩
      by_contra h
      push_neg at h
      have e : ∀ i, N i = aug m χ := fun i =>
        le_antisymm (by simpa [rkSub_succ_n] using (hQ i).2) (hQ i).1.1
      have hlt : (⟨0, by omega⟩ : Fin r) < ⟨1, h⟩ := by simp [Fin.lt_def]
      exact (hN hlt).ne (by rw [e, e])
    | succ d ih =>
      obtain ⟨L1, h1⟩ := ih
      by_cases hd : d ≤ n
      · obtain ⟨L2, h2⟩ := GlobalTheory.T.theta_rank_submodule_chain_bounded P k n m χ hχ (n - d)
        have e1 : n + 1 - d = n - d + 1 := by omega
        have e2 : n + 1 - (d + 1) = n - d := by omega
        refine ⟨L1 + L2, GlobalTheory.T.chain_length_bound_of_sup_inf (aug m χ ⊔ rkSub k n m (n + 1 - d))
          (fun x => IsSub χ x ∧ x ≤ aug m χ ⊔ rkSub k n m (n + 1 - (d + 1)))
          (fun x => IsSub χ x ∧ x ≤ aug m χ ⊔ rkSub k n m (n + 1 - d))
          (fun x => IsSub χ x ∧ aug m χ ⊔ rkSub k n m (n - d + 1) ≤ x ∧ x ≤ aug m χ ⊔ rkSub k n m (n - d))
          L1 L2 ?_ ?_ h1 (fun r N hN hQ => h2 r N hN hQ)⟩
        · intro x hx
          exact ⟨GlobalTheory.ThetaGLRank.IsSub.inf hx.1 (isSub_aug_sup χ _), inf_le_right⟩
        · intro x hx
          refine ⟨GlobalTheory.ThetaGLSub.IsSub.sup hx.1 (isSub_aug_sup χ _), ?_, ?_⟩
          · rw [← e1]; exact le_sup_right
          · refine sup_le (e2 ▸ hx.2) ?_
            rw [e1]
            exact sup_le_sup_left (rkSub_succ_le _) _
      · refine ⟨L1, fun r N hN hQ => h1 r N hN fun i => ⟨(hQ i).1, ?_⟩⟩
        have : n + 1 - (d + 1) = n + 1 - d := by omega
        rw [← this]; exact (hQ i).2
  obtain ⟨L, hL⟩ := key (n + 1)
  refine ⟨L, fun r N hN hQ => hL r N hN fun i => ⟨hQ i, ?_⟩⟩
  rw [Nat.sub_self, rkSub_zero]
  exact le_sup_of_le_right (hQ i).2.1

end GlobalTheory.ThetaGLRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracePairingArchimedeanVarsNondegenerateRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.GaussLine

theorem pairInf_nondeg : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (q : κ → mixedEmbedding.mixedSpace F),
    (∀ x, GlobalTheory.GaussLine.pairInf F κ x q = 0) → q = 0 := by
  intro F _ _ κ _ q hq
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have h := hq (Pi.single i b)
  rw [GlobalTheory.GaussLine.pairInf_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp),
    Pi.single_eq_same, mul_comm] at h
  simpa using h

end GlobalTheory.GaussLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationThetaFunctionSupLeQuotientHeig
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.SupThetaGrowth

theorem om_sup_quotHeight : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h w, ‖om (g, h) f w‖ ≤ C * (quotHeight S g * quotHeight T h) ^ A := by
  intro D ψ S T χS χT om hom f hf
  obtain ⟨C, A, hC⟩ := om_sup_growth D ψ S T χS χT om hom f hf
  refine ⟨max C 0 * 4 ^ A, A, fun g h w => ?_⟩
  obtain ⟨γ, hγ, h1⟩ := exists_height_le_two_mul_quotHeight S g
  obtain ⟨γ', hγ', h2⟩ := exists_height_le_two_mul_quotHeight T h
  have e := om_rat_mul D ψ S T χS χT om hom f hf γ⁻¹ (inv_mem hγ) γ'⁻¹ (inv_mem hγ') (γ * g) (γ' * h) w
  rw [inv_mul_cancel_left, inv_mul_cancel_left] at e
  rw [e]
  have p1 := (height_pos S (γ * g)).le
  have p2 := (height_pos T (γ' * h)).le
  have q1 := (quotHeight_pos S g).le
  calc _ ≤ C * (height S (γ * g) * height T (γ' * h)) ^ A := hC _ _ _
    _ ≤ max C 0 * (height S (γ * g) * height T (γ' * h)) ^ A :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (mul_nonneg p1 p2) A)
    _ ≤ max C 0 * (2 * quotHeight S g * (2 * quotHeight T h)) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg p1 p2)
          (mul_le_mul h1 h2 p2 (mul_nonneg zero_le_two q1)) A) (le_max_right _ _)
    _ = max C 0 * 4 ^ A * (quotHeight S g * quotHeight T h) ^ A := by
        generalize quotHeight S g = a
        generalize quotHeight T h = b
        rw [show 2 * a * (2 * b) = 4 * (a * b) by ring, mul_pow, mul_assoc]

end GlobalTheory.SupThetaGrowth
end

