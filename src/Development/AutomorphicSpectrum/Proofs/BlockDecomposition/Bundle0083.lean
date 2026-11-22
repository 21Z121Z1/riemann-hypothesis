import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0063
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0064
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0065
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0041
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0030
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0062
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0061

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSumInvariantStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_sum_invariant : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ), (Function.support fun q : G ⧸ K => f q.out).Finite → (∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → ∀ v : V, (∀ k ∈ K, ρ k v = v) → ∀ k ∈ K, ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := by
  first | exact @GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed | exact GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed | (intros; apply GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdPropertyStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_third_property : PositivityTheory.Rg.Tf.Loc.H3 := by
  first | exact @GlobalTheory.CompanionTheory.TwistedCent.h3 | exact GlobalTheory.CompanionTheory.TwistedCent.h3 | (intros; apply GlobalTheory.CompanionTheory.TwistedCent.h3 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatementStatement
section
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bound_statement : GlobalTheory.CompanionTheory.Jp.JpHgt := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt | exact GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt | (intros; apply GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HenselPolynomialRefinementStatement
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hensel_polynomial_refinement : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → ∀ P : Polynomial T, P.Monic → 0 < P.natDegree → ∀ (M : ℕ) (a : B), P.eval (g a) ∈ Ideal.span {g π ^ (P.natDegree * M)} → ∃ a₁ : B, a₁ - a ∈ Ideal.span {π ^ M} ∧ P.eval (g a₁) ∈ Ideal.span {g π ^ (P.natDegree * (M + 1))} := by
  first | exact @GlobalTheory.CompanionTheory.AicStep.aic_step | exact GlobalTheory.CompanionTheory.AicStep.aic_step | (intros; apply GlobalTheory.CompanionTheory.AicStep.aic_step <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCountFromHyperplanesStatement
section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_count_from_hyperplanes : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  (w : (Fin (n + 1) → k) → V) (c A : ℝ),
  (∀ x, 0 ≤ (B x x).re) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 →
    Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a b : Fin (n + 1) → k, a ≠ 0 → (∀ s : k, b ≠ s • a) →
    Fintype.card k ^ 2 * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → ∀ s : k, s ≠ 0 → w (s • a) = w a) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → (B (w a) (w a)).re = c) →
  (∀ x : Fin (n + 1) → k, x ≠ 0 →
    (B (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)
       (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)).re = A) →
  (Fintype.card k : ℝ) ^ n * c ≤ (Fintype.card k : ℝ) * A := by
  first | exact @GlobalTheory.CompanionTheory.GapOpLower.lower_from_counts | exact GlobalTheory.CompanionTheory.GapOpLower.lower_from_counts | (intros; apply GlobalTheory.CompanionTheory.GapOpLower.lower_from_counts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarBlockDecompositionStatement
section
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_haar_block_decomposition : ∀ (n : ℕ) (ν : Measure (hermC (n + 1))) (ν' : Measure (hermC n)),
    ν.IsAddHaarMeasure → ν'.IsAddHaarMeasure →
    ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : hermC (n + 1) → ENNReal, Measurable F →
      ∫⁻ b, F b ∂ν = c * ∫⁻ b', ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ, F (blk b' u d) ∂volume ∂volume ∂ν' := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatricesCardStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_matrices_card : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ n : ℕ, Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H} = q ^ (n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg | exact GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianRepCountFourierExpansion
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.LevelId

variable {R : Type} [CommRing R]

theorem cT_mul (σ : R →+* R) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    cT σ (x * y) = cT σ y * cT σ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_cT (σ : R →+* R) (h : ∀ a, σ (σ a) = a) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    cT σ (cT σ x) = x := by
  ext i j
  exact h (x i j)

theorem cT_sub (σ : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x - y) = cT σ x - cT σ y := by
  ext i j
  exact map_sub σ (x j i) (y j i)

theorem red_mul (ϖ : R) (k : ℕ) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    red ϖ k (x * y) = red ϖ k x * red ϖ k y := by
  unfold red
  exact Matrix.map_mul

theorem red_sub (ϖ : R) (k : ℕ) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k (x - y) = red ϖ k x - red ϖ k y := by
  ext i j
  exact map_sub (Ideal.Quotient.mk (lev ϖ k)) (x i j) (y i j)

theorem red_neg (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (-x) = - red ϖ k x := by
  ext i j
  exact map_neg (Ideal.Quotient.mk (lev ϖ k)) (x i j)

theorem red_cT (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (cT σ x) = cT (barσ σ ϖ h k) (red ϖ k x) := by
  ext i j
  exact (barσ_mk σ ϖ h k (x j i)).symm

theorem red_surj (ϖ : R) (k : ℕ) {a b : ℕ} :
    Function.Surjective (red ϖ k : Matrix (Fin a) (Fin b) R → _) := by
  intro y
  refine ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (y i j)).choose, ?_⟩
  ext i j
  exact (Ideal.Quotient.mk_surjective (y i j)).choose_spec

theorem red_gram (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (x : Matrix (Fin m) (Fin n) R) :
    red ϖ k (cT σ x * S * x) = cT (barσ σ ϖ h k) (red ϖ k x) * red ϖ k S * red ϖ k x := by
  rw [red_mul, red_mul, red_cT σ ϖ h]

theorem image_sol (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) :
    red ϖ k '' {x : Matrix (Fin m) (Fin n) R | red ϖ k (cT σ x * S * x) = red ϖ k T} =
      {y | cT (barσ σ ϖ h k) y * red ϖ k S * y = red ϖ k T} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show cT (barσ σ ϖ h k) (red ϖ k x) * red ϖ k S * red ϖ k x = red ϖ k T
    rw [← red_gram σ ϖ h]
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := red_surj ϖ k y
    refine ⟨x, ?_, rfl⟩
    show red ϖ k (cT σ x * S * x) = red ϖ k T
    rw [red_gram σ ϖ h]
    exact hy

theorem gram_sub_mem (σ : R →+* R) (ϖ : R) (hinv : ∀ a, σ (σ a) = a) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : cT σ S = S) (hT : cT σ T = T)
    (y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) :
    cT (barσ σ ϖ h k) y * red ϖ k S * y - red ϖ k T ∈ hermMod σ ϖ n k := by
  obtain ⟨x, rfl⟩ := red_surj ϖ k y
  unfold hermMod
  refine ⟨cT σ x * S * x - T, ?_, ?_⟩
  · show cT σ (cT σ x * S * x - T) = cT σ x * S * x - T
    rw [cT_sub, cT_mul, cT_mul, cT_cT σ hinv, hS, hT, Matrix.mul_assoc]
  · show red ϖ k (cT σ x * S * x - T) = _
    rw [red_sub, red_gram σ ϖ h]

theorem neg_mem_herm (σ : R →+* R) (ϖ : R) (n k : ℕ) {B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)}
    (hB : B ∈ hermMod σ ϖ n k) : -B ∈ hermMod σ ϖ n k := by
  unfold hermMod at hB ⊢
  obtain ⟨h0, hh, rfl⟩ := hB
  refine ⟨-h0, ?_, red_neg ϖ k h0⟩
  show cT σ (-h0) = -h0
  have hh' : cT σ h0 = h0 := hh
  ext i j
  have e : σ (h0 j i) = h0 i j := congrFun (congrFun hh' i) j
  show σ (-(h0 j i)) = -(h0 i j)
  rw [map_neg, e]

theorem nuAt_neg (ϖ : R) {n k : ℕ} (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :
    nuAt ϖ (-B) = nuAt ϖ B := by
  unfold nuAt
  have hset : (Set.range fun x : Fin n → R ⧸ lev ϖ k => Matrix.vecMul x (-B)) =
      Set.range fun x : Fin n → R ⧸ lev ϖ k => Matrix.vecMul x B := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      show Matrix.vecMul (-x) B = Matrix.vecMul x (-B)
      rw [Matrix.neg_vecMul, Matrix.vecMul_neg]
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      show Matrix.vecMul (-x) (-B) = Matrix.vecMul x B
      rw [Matrix.neg_vecMul, Matrix.vecMul_neg, neg_neg]
  rw [hset]

end GlobalTheory.CompanionTheory.SiegLoc.LevelId

open GlobalTheory.CompanionTheory.SiegLoc.LevelId in

theorem GlobalTheory.CompanionTheory.SiegLoc.level_identity : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (m n k : ℕ) (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), cT σ S = S → cT σ T = T → (∀ Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k), Y ∈ hermMod σ ϖ n k → (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧ (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0)) → (∀ B ∈ hermMod σ ϖ n k, (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ψ k (Matrix.trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) = (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B))) → siegAt ϖ σ ψ q ε m T k = ((densAt σ ϖ S T k : ℝ) : ℂ) := by
  intro R _ σ ϖ q ε hR _ ψ hψ m n k S T hS hT horth hgauss
  classical
  have : Fintype ↥(hermMod σ ϖ n k) := Fintype.ofFinite _
  have hx : ∀ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
      (∑' B : hermMod σ ϖ n k,
        ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x - red ϖ k T)))) =
        if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then
          (Nat.card (hermMod σ ϖ n k) : ℂ) else 0 := by
    intro x
    have hmem := gram_sub_mem σ ϖ hR.inv hR.fix_ϖ k S T hS hT x
    by_cases hxe : cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T
    · rw [if_pos hxe]
      exact (horth _ hmem).1 (sub_eq_zero.mpr hxe)
    · rw [if_neg hxe]
      exact (horth _ hmem).2 (sub_ne_zero.mpr hxe)
  have hsplit : ∀ (B : hermMod σ ϖ n k) (x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)),
      ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x - red ϖ k T))) =
        ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
          ψ k (-Matrix.trace (B.1 * red ϖ k T)) := by
    intro B x
    rw [Matrix.mul_sub, Matrix.trace_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hsol : (solCount σ ϖ S T k : ℂ) = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
      if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0 := by
    unfold solCount
    rw [image_sol σ ϖ hR.fix_ϖ k S T, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.natCast_card_filter]
    exact Finset.sum_congr rfl fun x _ => if_congr Iff.rfl rfl rfl
  have h1 : ∀ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), (Nat.card (hermMod σ ϖ n k) : ℂ) *
      (if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0) =
      ∑ B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
        ψ k (-Matrix.trace (B.1 * red ϖ k T)) := by
    intro x
    rw [mul_ite, mul_one, mul_zero, ← hx x, tsum_fintype]
    exact Finset.sum_congr rfl fun B _ => hsplit B x
  have hcount : (Nat.card (hermMod σ ϖ n k) : ℂ) * (solCount σ ϖ S T k : ℂ) =
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) *
        ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
          ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    calc (Nat.card (hermMod σ ϖ n k) : ℂ) * (solCount σ ϖ S T k : ℂ)
        = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), (Nat.card (hermMod σ ϖ n k) : ℂ) *
            (if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0) := by
          rw [hsol, Finset.mul_sum]
      _ = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ∑ B : hermMod σ ϖ n k,
            ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
              ψ k (-Matrix.trace (B.1 * red ϖ k T)) := Finset.sum_congr rfl fun x _ => h1 x
      _ = ∑ B : hermMod σ ϖ n k, ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
            ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
              ψ k (-Matrix.trace (B.1 * red ϖ k T)) := Finset.sum_comm
      _ = ∑ B : hermMod σ ϖ n k, (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) *
            (ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
              ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1)) := by
          refine Finset.sum_congr rfl fun B _ => ?_
          rw [← Finset.sum_mul, hgauss B.1 B.2]
          ring
      _ = _ := by rw [Finset.mul_sum]
  have hneg : ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) =
      ∑ B : hermMod σ ϖ n k, ψ k (Matrix.trace (red ϖ k T * B.1)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    let e : hermMod σ ϖ n k ≃ hermMod σ ϖ n k :=
      { toFun := fun B => ⟨-B.1, neg_mem_herm σ ϖ n k B.2⟩
        invFun := fun B => ⟨-B.1, neg_mem_herm σ ϖ n k B.2⟩
        left_inv := fun B => Subtype.ext (neg_neg _)
        right_inv := fun B => Subtype.ext (neg_neg _) }
    refine Fintype.sum_equiv e _ _ fun B => ?_
    show _ = ψ k (Matrix.trace (red ϖ k T * -B.1)) *
      ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ (-B.1))
    rw [nuAt_neg, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_mul_comm]
  have hfin : siegAt ϖ σ ψ q ε m T k = ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    unfold siegAt
    rw [tsum_fintype, hneg]
  have hM : (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcast : ((densAt σ ϖ S T k : ℝ) : ℂ) = (solCount σ ϖ S T k : ℂ) * (Nat.card (hermMod σ ϖ n k) : ℂ) /
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) := by
    unfold densAt
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_natCast,
      Complex.ofReal_natCast]
  rw [hfin, hcast, eq_div_iff hM]
  linear_combination (-1 : ℂ) * hcount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSpaceAnisotropicUnitStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_space_anisotropic_unit : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nontrivial V → ∃ w : V, IsUnit (B.h w w) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.exists_unit_norm | exact GlobalTheory.CompanionTheory.UnrDens.exists_unit_norm | (intros; apply GlobalTheory.CompanionTheory.UnrDens.exists_unit_norm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationDichotomyStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_localization_dichotomy : ∀ {S : Type} [CommRing S] (ϖ : S) (P : Ideal S), P.IsPrime → (Val ϖ → Dich (Ideal.Quotient.mk (compI P) ϖ)) ∧ (ϖ ∈ nonZeroDivisors S → Ideal.Quotient.mk (compI P) ϖ ∈ nonZeroDivisors (S ⧸ compI P)) := by
  first | exact @GlobalTheory.CompanionTheory.CompDich.dich_comp | exact GlobalTheory.CompanionTheory.CompDich.dich_comp | (intros; apply GlobalTheory.CompanionTheory.CompDich.dich_comp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseTransformContinuousStatement
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_transform_continuous : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T] [FirstCountableTopology T] (φ : ℝ × ℝ → T → X), ExpDecay φ → Continuous (fun p : (ℝ × ℝ) × T => φ p.1 p.2) → Continuous (fun y : (ℂ × ℂ) × T => inv (fun t => φ t y.2) y.1) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint | exact GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseTransformHolomorphicLines
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier.InvLine

theorem integrable_exp_neg_abs_plane {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ × ℝ => Real.exp (-c * |t.1|) * Real.exp (-c * |t.2|)) :=
  (integrable_exp_neg_mul_abs hc).mul_prod (integrable_exp_neg_mul_abs hc)

theorem dot_add_smul (p v : ℂ × ℂ) (τ : ℂ) (t : ℝ × ℝ) :
    dot (p + τ • v) t = dot p t + τ * dot v t := by
  simp [dot]
  ring

theorem norm_cexp_dot (l : ℂ × ℂ) (t : ℝ × ℝ) :
    ‖Complex.exp (dot l t)‖ = Real.exp (rdot (l.1.re, l.2.re) t) := by
  rw [Complex.norm_exp]
  simp [dot, rdot]

theorem norm_dot_le (v : ℂ × ℂ) (t : ℝ × ℝ) :
    ‖dot v t‖ ≤ (‖v.1‖ + ‖v.2‖) * (|t.1| + |t.2|) := by
  have h1 : ‖dot v t‖ ≤ ‖v.1‖ * |t.1| + ‖v.2‖ * |t.2| := by
    refine (norm_add_le _ _).trans ?_
    simp [norm_mul]
  have := norm_nonneg v.1
  have := norm_nonneg v.2
  have := abs_nonneg t.1
  have := abs_nonneg t.2
  nlinarith [mul_nonneg (norm_nonneg v.1) (abs_nonneg t.2), mul_nonneg (norm_nonneg v.2) (abs_nonneg t.1)]

theorem le_two_div_mul_exp {ε s : ℝ} (hε : 0 < ε) : s ≤ 2 / ε * Real.exp (ε / 2 * s) := by
  have h := Real.add_one_le_exp (ε / 2 * s)
  have h2 : s = 2 / ε * (ε / 2 * s) := by field_simp
  have h3 : ε / 2 * s ≤ Real.exp (ε / 2 * s) := by linarith
  calc s = 2 / ε * (ε / 2 * s) := h2
    _ ≤ _ := by gcongr

theorem inv_differentiable_line : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ (g : T) (p v : ℂ × ℂ), Differentiable ℂ (fun τ : ℂ => inv (fun t => φ t g) (p + τ • v)) := by
  intro X _ _ _ T _ φ hφ hc g p v τ₀
  obtain ⟨ε, hε, U, hU, M, hM⟩ := hφ ((p + τ₀ • v).1.re, (p + τ₀ • v).2.re) g
  have hgU : g ∈ U := mem_of_mem_nhds hU
  have hA : 0 < ‖v.1‖ + ‖v.2‖ + 1 := by positivity
  have hr : 0 < ε / (‖v.1‖ + ‖v.2‖ + 1) := div_pos hε hA
  have hre : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ w : ℂ, ‖w‖ ≤ ‖v.1‖ + ‖v.2‖ + 1 →
      ∀ q : ℂ, |(q + τ * w).re - (q + τ₀ * w).re| ≤ ε := by
    intro τ hτ w hw q
    have h1 : (q + τ * w).re - (q + τ₀ * w).re = ((τ - τ₀) * w).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im]
      ring
    rw [h1]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have h2 : ‖τ - τ₀‖ ≤ ε / (‖v.1‖ + ‖v.2‖ + 1) := by
      have := Metric.mem_ball.1 hτ
      rw [dist_eq_norm] at this
      exact this.le
    calc ‖τ - τ₀‖ * ‖w‖ ≤ ε / (‖v.1‖ + ‖v.2‖ + 1) * (‖v.1‖ + ‖v.2‖ + 1) := by gcongr
      _ = ε := by field_simp
  have key : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ t : ℝ × ℝ,
      ‖φ t g‖ ≤ M * Real.exp (-rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
        * Real.exp (-ε * (|t.1| + |t.2|)) := by
    intro τ hτ t
    refine hM _ ?_ ?_ g hgU t
    · exact hre τ hτ v.1 (by linarith [norm_nonneg v.2]) p.1
    · exact hre τ hτ v.2 (by linarith [norm_nonneg v.1]) p.2
  have hFn : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ t : ℝ × ℝ,
      ‖Complex.exp (dot (p + τ • v) t) • φ t g‖ ≤ |M| * Real.exp (-ε * (|t.1| + |t.2|)) := by
    intro τ hτ t
    rw [norm_smul, norm_cexp_dot]
    have h1 := key τ hτ t
    have h2 := Real.exp_pos (rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
    calc _ ≤ Real.exp (rdot ((p + τ • v).1.re, (p + τ • v).2.re) t) *
          (M * Real.exp (-rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
            * Real.exp (-ε * (|t.1| + |t.2|))) := by gcongr
      _ = M * Real.exp (-ε * (|t.1| + |t.2|)) := by
        rw [Real.exp_neg]
        field_simp
      _ ≤ _ := by gcongr; exact le_abs_self M
  have hcont : ∀ τ : ℂ, Continuous fun t : ℝ × ℝ => Complex.exp (dot (p + τ • v) t) • φ t g := by
    intro τ
    refine Continuous.smul ?_ (hc g)
    simp only [dot]
    fun_prop
  have hdotc : Continuous fun t : ℝ × ℝ => dot v t := by
    unfold dot
    fun_prop
  have hint : Integrable (fun t : ℝ × ℝ => Complex.exp (dot (p + τ₀ • v) t) • φ t g) :=
    (integrable_and_norm_integral_le X (fun t => φ t g) (p + τ₀ • v) ε M hε (hc g)
      (fun t => hM _ (by simp [hε.le]) (by simp [hε.le]) g hgU t)).1
  have hbound : Integrable (fun t : ℝ × ℝ => ((‖v.1‖ + ‖v.2‖) * (2 / ε) * |M|) *
      (Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|))) :=
    (integrable_exp_neg_abs_plane (half_pos hε)).const_mul _
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (ℝ × ℝ)))
    (F := fun (τ : ℂ) (t : ℝ × ℝ) => Complex.exp (dot (p + τ • v) t) • φ t g)
    (F' := fun (τ : ℂ) (t : ℝ × ℝ) => dot v t • (Complex.exp (dot (p + τ • v) t) • φ t g))
    (x₀ := τ₀) (s := Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)))
    (bound := fun t : ℝ × ℝ => ((‖v.1‖ + ‖v.2‖) * (2 / ε) * |M|) *
      (Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|)))
    (Metric.ball_mem_nhds _ hr)
    (Eventually.of_forall fun τ => (hcont τ).aestronglyMeasurable)
    hint
    (Continuous.aestronglyMeasurable (Continuous.smul hdotc (hcont τ₀)))
    (ae_of_all _ fun t τ hτ => by
      rw [norm_smul]
      have h1 := norm_dot_le v t
      have h2 := hFn τ hτ t
      have h3 := le_two_div_mul_exp (s := |t.1| + |t.2|) hε
      have h4 : Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|)
          = Real.exp (-(ε / 2) * (|t.1| + |t.2|)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h5 : Real.exp (ε / 2 * (|t.1| + |t.2|)) * Real.exp (-ε * (|t.1| + |t.2|))
          = Real.exp (-(ε / 2) * (|t.1| + |t.2|)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h4, ← h5]
      calc _ ≤ ((‖v.1‖ + ‖v.2‖) * (2 / ε * Real.exp (ε / 2 * (|t.1| + |t.2|)))) *
            (|M| * Real.exp (-ε * (|t.1| + |t.2|))) := by
            refine mul_le_mul (h1.trans ?_) h2 (norm_nonneg _) (by positivity)
            gcongr
        _ = _ := by ring)
    hbound
    (ae_of_all _ fun t τ _ => by
      have h1 : HasDerivAt (fun τ : ℂ => Complex.exp (dot (p + τ • v) t))
          (Complex.exp (dot (p + τ • v) t) * dot v t) τ := by
        have h2 : HasDerivAt (fun τ : ℂ => dot p t + τ * dot v t) (dot v t) τ := by
          simpa using ((hasDerivAt_id τ).mul_const (dot v t)).const_add (dot p t)
        have h3 := h2.cexp
        simp only [← dot_add_smul] at h3
        exact h3
      have h4 := h1.smul_const (φ t g)
      rw [smul_smul, mul_comm]
      exact h4)
  exact (hd.2.differentiableAt).const_smul (((2 * Real.pi) ^ 2 : ℂ)⁻¹)

end GlobalTheory.CompanionTheory.TubeFourier.InvLine
end

