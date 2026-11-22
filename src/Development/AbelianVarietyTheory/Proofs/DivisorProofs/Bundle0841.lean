import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobAtRestrictFiniteAbelianSubextension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0693
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0834

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HtMapLeOfPoints
section
open Module NumberField GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.DescentFamily

open Formalism.HN

theorem numeric {a N mu muA ht mm P Λ ε t : ℝ} (ha : 0 < a) (haN : a ≤ N) (hN : N ≤ (1 + ε) * a)
    (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε) (hht : ht ≤ 2 * P) (hmm : -(2 * Λ) ≤ mm) (ht' : t ≤ muA - 2 * P)
    (h : a * (muA - ht) + (N - a) * mm ≤ N * mu) : t - ε * (|t| + 2 * Λ) ≤ mu := by
  have hN0 : 0 < N := ha.trans_le haN
  have h1 : a * t ≤ a * (muA - ht) := mul_le_mul_of_nonneg_left (by linarith) ha.le
  have h2 : (N - a) * (-(2 * Λ)) ≤ (N - a) * mm := mul_le_mul_of_nonneg_left hmm (by linarith)
  have h3 : (N - a) * t ≤ (N - a) * |t| := mul_le_mul_of_nonneg_left (le_abs_self t) (by linarith)
  have h4 : N - a ≤ ε * N := by nlinarith
  have h5 : (N - a) * (|t| + 2 * Λ) ≤ ε * N * (|t| + 2 * Λ) :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  refine le_of_mul_le_mul_left ?_ hN0
  nlinarith

section

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]

theorem htMap_le_of_points (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det)
    (φ : V →ₗ[K] W) (hφ : φ ≠ 0) (P : ℝ)
    (h : ∀ v f, Formalism.HermitianLatticesTheory.normAt b' X' v (φ f) ≤ Real.exp P * Formalism.HermitianLatticesTheory.normAt b X v f) :
    htMap b X b' X' φ ≤ 2 * P := by
  have hf : (0 : ℝ) < (nPl K : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have h1 : ∀ v, Real.log (opNormAt b X b' X' v φ ^ 2) ≤ 2 * P := by
    intro v
    rw [Real.log_pow]
    push_cast
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Real.log_le_iff_le_exp (PlaceOperatorNorms.opNormAt_pos b X b' X' hX hX' v φ hφ)]
    exact Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points b X b' X' hX φ v _ (Real.exp_pos _).le (h v)
  unfold htMap
  have h2 : ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2) ≤ (nPl K : ℝ) * (2 * P) := by
    calc _ ≤ ∑ _v : InfinitePlace K, 2 * P := Finset.sum_le_sum fun v _ => h1 v
      _ = (nPl K : ℝ) * (2 * P) := by simp [nPl]
  calc 1 / (nPl K : ℝ) * ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2)
      ≤ 1 / (nPl K : ℝ) * ((nPl K : ℝ) * (2 * P)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * P := by field_simp

theorem normAt_pi_sq [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (n : ℕ) (v : InfinitePlace K)
    (x : Fin n → V) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basis fun _ : Fin n => b)
      (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v x ^ 2 =
        ∑ j, Formalism.HermitianLatticesTheory.normAt b X v (x j) ^ 2 := by
  simp only [← Formalism.ExtensionFiltration.majAt_self_re]
  rw [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.majAt_pi b X hX, Complex.re_sum]

end

theorem descent : ∀ (K V W : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (NA : (K →+* ℂ) → V → ℝ) (NB : (K →+* ℂ) → W → ℝ) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W) (n : ℕ) (φ : Fin n → V →ₗ[K] W) (P Λ ε t : ℝ), HasGram NA → HasGram NB → A.FG → B.FG → A ≠ ⊥ → (∀ h, ∀ f ∈ A, φ h f ∈ B) → (∀ f, (∀ h, φ h f = 0) → f = 0) → (∀ σ f, ∑ h, NB σ (φ h f) ^ 2 ≤ Real.exp (2 * P) * NA σ f ^ 2) → (∃ s : Set W, s ⊆ (B : Set W) ∧ (∀ y ∈ s, ∀ σ, NB σ y ≤ Real.exp Λ) ∧ (B : Set W) ⊆ (Submodule.span K s : Set W)) → 0 ≤ Λ → 0 ≤ ε → (n : ℝ) * Formalism.HN.rkK B ≤ (1 + ε) * Formalism.HN.rkK A → t ≤ slope_sq NA A - 2 * P → t - ε * (|t| + 2 * Λ) ≤ slope_sq NB B := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ NA NB A B n φ P Λ ε t hA hB hAfg hBfg hA0 hint hinj hnorm hs hΛ hε hrk ht
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨p, ⟨b, X⟩, hGA⟩⟩ := hA
  obtain ⟨⟨q, ⟨b', X'⟩, hGB⟩⟩ := hB
  change IsGram b X NA at hGA
  change IsGram b' X' NB at hGB
  have hX : ∀ v, IsUnit (X v).det := fun v => (hGA v).1
  have hX' : ∀ v, IsUnit (X' v).det := fun v => (hGB v).1
  rw [slope_sq_eq hGA hAfg] at ht
  rw [slope_sq_eq hGB hBfg]
  obtain ⟨f0, hf0A, hf0⟩ := (Submodule.ne_bot_iff A).1 hA0
  obtain ⟨h0, hh0⟩ : ∃ h, φ h f0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf0 (hinj f0 hc)
  have hn : 0 < n := h0.pos
  have hB0 : B ≠ ⊥ := (Submodule.ne_bot_iff B).2 ⟨_, hint h0 f0 hf0A, hh0⟩
  obtain ⟨p1, p2, -⟩ := Formalism.BranchingDeterminantCap.power_slope_mu K W _ b' X' hX' B n hBfg hB0 hn
  set bn : Basis (Σ _ : Fin n, Fin q) K (Fin n → W) := Pi.basis fun _ : Fin n => b' with hbn
  set Xn : InfinitePlace K → Matrix (Σ _ : Fin n, Fin q) (Σ _ : Fin n, Fin q) ℂ :=
    fun v => Matrix.blockDiagonal' fun _ : Fin n => X' v with hXndef
  set Bn : Submodule (𝓞 K) (Fin n → W) := Submodule.pi Set.univ fun _ : Fin n => B with hBn
  have hXn : ∀ v, IsUnit (Xn v).det := fun v => Formalism.BranchingDeterminantCap.PrismTransfer.blockDiag_det (X' v) (hX' v)
  have hBnfg : Bn.FG := Submodule.fg_pi fun _ => hBfg
  let Φ : V →ₗ[K] (Fin n → W) := LinearMap.pi φ
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    exact fun f hf => hinj f fun h => congrFun hf h
  have hΦle : A.map (Φ.restrictScalars (𝓞 K)) ≤ Bn := by
    rintro _ ⟨f, hf, rfl⟩ h -
    exact hint h f hf
  have hΦ0 : Φ ≠ 0 := fun h => hh0 (congrFun (LinearMap.congr_fun h f0) h0)
  have hBn0 : Bn ≠ ⊥ := (Submodule.ne_bot_iff Bn).2
    ⟨Φ f0, hΦle ⟨f0, hf0A, rfl⟩, fun h => hh0 (congrFun h h0)⟩
  have hht : htMap b X bn Xn Φ ≤ 2 * P := by
    refine htMap_le_of_points b X bn Xn hX hXn Φ hΦ0 P fun v f => ?_
    have n0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt b X v f := Real.sqrt_nonneg _
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [hbn, hXndef, normAt_pi_sq b' X' hX', mul_pow, ← Real.exp_nat_mul, (hGA v).2]
    simp only [(hGB v).2]
    exact_mod_cast hnorm v.embedding f
  have hmm : -(2 * Λ) ≤ muMinDef bn Xn Bn := by
    obtain ⟨s, hsB, hsn, hsp⟩ := hs
    refine Formalism.ExtensionFiltration.spanMuMin K _ _ bn Xn hXn Bn Λ hBnfg hBn0
      ⟨⋃ i : Fin n, (fun y => (Pi.single i y : Fin n → W)) '' s, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
      intro j _
      by_cases hj : j = i
      · subst hj; simpa using hsB hy
      · simp [Pi.single_eq_of_ne hj]
    · intro x hx v
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
      rw [hbn, hXndef, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.normAt_single b' X' hX', (hGB v).2]
      exact hsn y hy _
    · intro x hx
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have h1 : x i ∈ Submodule.span K s := hsp (hx i trivial)
      have h2 := Submodule.mem_map_of_mem (f := LinearMap.single K (fun _ : Fin n => W) i) h1
      rw [Submodule.map_span] at h2
      exact Submodule.span_mono (Set.subset_iUnion
        (fun i : Fin n => (fun y => (Pi.single i y : Fin n → W)) '' s) i) h2
  have hd := Formalism.ExtensionFiltration.descentSlope K V _ (Fin n → W) _ b X bn Xn hX hXn Φ A Bn hAfg hBnfg hA0 hΦinj hΦle
  rw [p2] at hd
  have hle : rkK A ≤ rkK Bn := by
    haveI : Module.Finite K (Fin n → W) := Module.Finite.of_basis bn
    rw [← Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_map Φ hΦinj A]
    exact Submodule.finrank_mono (Submodule.span_mono hΦle)
  have hpos : 0 < rkK A := Nat.pos_of_ne_zero (Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b A hA0)
  refine numeric (a := rkK A) (N := rkK Bn) (by exact_mod_cast hpos) (by exact_mod_cast hle) ?_ hΛ hε hht hmm ht hd
  rw [p1]
  push_cast
  exact hrk

end GlobalTheory.DescentFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaRestrictFiniteAbelianUnramifiedEqOneStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_restrict_finiteAbelian_unramified_eq_one : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L) (v : HeightOneSpectrum (𝓞 K)), IsUnramifiedIn K v L → ∀ (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω, σ ∈ ReciprocityTheory.Gal.Ine (F := K) A → haveI := h.isGalois; AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) = 1 := by
  first | exact @GlobalTheory.InertiaRestrict.restrict_eq_one | exact GlobalTheory.InertiaRestrict.restrict_eq_one | (intros; apply GlobalTheory.InertiaRestrict.restrict_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCMTypeOfEmbeddingsCardEqFinrankStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCMTypeOfEmbeddings_card_eq_finrank : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2), Fintype.card I = Module.finrank K E := by
  first | exact @GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType | exact GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType | (intros; apply GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobAtRestrictFiniteAbelianSubextensionStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrobAt_restrict_finiteAbelian_subextension : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L) (v : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω, Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) σ → ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal → haveI := h.finiteDimensional; haveI := h.isGalois; IsFrobAt K L (AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e)) Q := by
  first | exact @GlobalTheory.FrobRestrict.isFrobAt_restrict | exact GlobalTheory.FrobRestrict.isFrobAt_restrict | (intros; apply GlobalTheory.FrobRestrict.isFrobAt_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGeneratorIsoBundleOfMatrixRelationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGenerator_isoBundle_of_matrix_relation : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (R : Type) [CommRing R] (A' B' : Over (Sp R)) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ), GlobalTheory.HomFixUniv.Generates bA ψA A'.hom c → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → (⟨u⟩ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)).IsGen := by
  first | (exact @GlobalTheory.HomFixUniv.isGen_of_matRel) | (exact GlobalTheory.HomFixUniv.isGen_of_matRel) | (intros; apply GlobalTheory.HomFixUniv.isGen_of_matRel  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilDualFrobenius
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem GlobalTheory.DualFrobNil.isNil_dual_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → IsConn G.dual → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit U → (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e hB hA hconn U hU hfr
  obtain ⟨m, hmax, hpm⟩ := Ideal.exists_le_maximal (Ideal.span {(p : O)}) (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact Fact.out)
  have hp : (p : O) ∈ m := hpm (Ideal.mem_span_singleton_self _)
  obtain ⟨c', hc'⟩ := GlobalTheory.T.coeff_p_logarithms_congr_inv_frobenius_matrix_mod_p p F.B F.Q F.s F.σ F.s_alg F.frame.inj d k e U hU hfr (fun a => (hA a).2)
    (fun r j => by obtain ⟨b, -, hb⟩ := (hB.1 r).2.1 j; exact ⟨b, hb⟩)
  refine GlobalTheory.T.isNilpotent_dualFrobenius_of_block F.B O F.θ F.σ p m (by rw [map_natCast]; exact hp) hmax.ne_top
    (fun b => by obtain ⟨c, hc⟩ := F.σ_pow b; exact ⟨c, hc⟩) d k U c' (fun a j => (hc' a j).2) ?_
  set Sh : (Fin d → O ⧸ m) → (Fin d → O ⧸ m) :=
    fun w a => ∑ j, Ideal.Quotient.mk m (F.θ (c' a j)) * w j ^ p with hSh
  obtain ⟨n, hlift⟩ := GlobalTheory.T.exists_cartierDual_lift_linearCoefficients_mod p O G d c m hp
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_uniform_convolution_pow_apply_mem_localDual p O G n m hmax (hconn n)
  have hθ : ∀ x ∈ RingHom.ker F.θ ⊔ Ideal.span {(p : F.B)}, F.θ x ∈ m := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [map_add, RingHom.mem_ker.1 hy, zero_add, map_mul, map_natCast]
    exact m.mul_mem_left _ hp
  have step : ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ Fs, φ (c.ev n Fs) - ∑ i, u i * lin Fs i ∈ m) →
      ∃ u' : Fin d → O, (∀ Fs, (φ ^ p) (c.ev n Fs) - ∑ i, u' i * lin Fs i ∈ m) ∧
        (fun a => Ideal.Quotient.mk m (u' a)) = Sh (fun a => Ideal.Quotient.mk m (u a)) := by
    intro u φ hφ
    refine ⟨fun a => constantCoeff ((invDer c.μ u)^[p] (X a)), fun Fs => ?_, ?_⟩
    · obtain ⟨t, ht⟩ := GlobalTheory.T.constantCoeff_iterate_invariant_derivation_linear p O d c.μ c.isLaw.const c.isLaw.unit c.isLaw.comm u Fs
      have h1 := GlobalTheory.T.convPow_ofConv_sub_constantCoeff_invariantDerivation p O G d c n m hp u φ hφ p Fs
      have h2 : (p : O) * t ∈ m := m.mul_mem_right t hp
      have e1 : (φ ^ p) (c.ev n Fs) - ∑ i, constantCoeff ((invDer c.μ u)^[p] (X i)) * lin Fs i =
          ((φ ^ p) (c.ev n Fs) - constantCoeff ((invDer c.μ u)^[p] Fs)) + p * t := by
        rw [← ht]; simp only [lin]; ring
      rw [e1]; exact m.add_mem h1 h2
    · funext a
      choose ũ hũ using fun i => F.frame.surj (u i)
      have hnat := GlobalTheory.T.map_invariantDerivationFormalGroupLaw_iterate F.B O F.θ d μ' hL.const ũ p (X a)
      have hmu : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
      have hu : (fun i => F.θ (ũ i)) = u := funext hũ
      rw [hmu, hu, map_X] at hnat
      have key := hθ _ (GlobalTheory.T.constantCoeff_pIterate_invariantDerivation_coord p F.B O F.Q F.θ F.frame d μ' hL (e (Sum.inl a)) a (hB.1 _) (hA a).1
        (hA a).2 (c' a) (fun i => (hc' a i).1) ũ)
      have hcc : constantCoeff ((invDer c.μ u)^[p] (X a)) =
          F.θ (constantCoeff ((invDer μ' ũ)^[p] (X a))) := by
        rw [← hnat, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
      simp only [hSh]
      rw [hcc, ← hu]
      simp only [← map_pow, ← map_mul, ← map_sum]
      rw [Ideal.Quotient.eq]
      simpa [map_sub, map_sum, map_mul, map_pow] using key
  have iter : ∀ t (u : Fin d → O) (φ : G.dual.A n), (∀ Fs, φ (c.ev n Fs) - ∑ i, u i * lin Fs i ∈ m) →
      ∃ u' : Fin d → O, (∀ Fs, (φ ^ (p ^ t)) (c.ev n Fs) - ∑ i, u' i * lin Fs i ∈ m) ∧
        (fun a => Ideal.Quotient.mk m (u' a)) = Sh^[t] (fun a => Ideal.Quotient.mk m (u a)) := by
    intro t
    induction t with
    | zero => intro u φ hφ; exact ⟨u, by simpa using hφ, rfl⟩
    | succ t ih =>
      intro u φ hφ
      obtain ⟨u1, h1, e1⟩ := ih u φ hφ
      obtain ⟨u2, h2, e2⟩ := step u1 _ h1
      refine ⟨u2, fun Fs => ?_, ?_⟩
      · rw [pow_succ, pow_mul]; exact h2 Fs
      · rw [e2, e1, Function.iterate_succ_apply']
  refine ⟨r, fun w => ?_⟩
  obtain ⟨u, rfl⟩ : ∃ u : Fin d → O, (fun a => Ideal.Quotient.mk m (u a)) = w :=
    ⟨fun a => (Ideal.Quotient.mk_surjective (w a)).choose,
      funext fun a => (Ideal.Quotient.mk_surjective (w a)).choose_spec⟩
  obtain ⟨φ, hφ⟩ := hlift u
  obtain ⟨u', h', e'⟩ := iter r u φ hφ
  rw [← e']
  funext a
  have h1 : φ 1 ∈ m := by
    have := hφ 1
    simpa [lin, coeff_one] using this
  have hle : r ≤ p ^ r := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h3 := hr φ h1 (p ^ r) hle (c.x n a)
  have h4 := h' (X a)
  rw [(c.isEval n).1 a] at h4
  have hs : ∑ i, u' i * lin (X a : MvPowerSeries (Fin d) O) i = u' a := by
    simp [lin, coeff_X, Finsupp.single_eq_single_iff]
  rw [hs] at h4
  have h5 : u' a ∈ m := by
    have := m.sub_mem h3 h4
    simpa using this
  simpa [Ideal.Quotient.eq_zero_iff_mem] using h5
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGeneratingCombinationMatrixLocusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_generatingCombinationMatrixLocus : ∀ (Rg : Type) [CommRing Rg] (A₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) [UniversallyClosed f] (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N), N.IsLB → ∃ U : (Sp (MvPolynomial (Fin (mA * mB)) Rg)).Opens, ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.Generates a φ p (matOf g) ↔ ∀ τ, g τ ∈ U) := by
  first | (exact @GlobalTheory.HomFixOpen.main) | (exact GlobalTheory.HomFixOpen.main) | (intros; apply GlobalTheory.HomFixOpen.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUniformiserAtIffAdicCompletionIsUnifAtStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUniformiserAt_iff_adicCompletion_isUnifAt : ∀ {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ), IsUniformiserAt K v (x : v.adicCompletion K) ↔ Formalism.L2.Host.IsUnifAt v x := by
  first | exact @GlobalTheory.UnifVal.isUniformiserAt_iff_isUnifAt | exact GlobalTheory.UnifVal.isUniformiserAt_iff_isUnifAt | (intros; apply GlobalTheory.UnifVal.isUniformiserAt_iff_isUnifAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.MovedVacuum

theorem isVacuum_thetaIntertwiner_selfDual (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl t0 : ℂ) (hc : StandardLatticesGL3.Crv D cc dl)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0) {a b : ℕ}
    {L L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' L₁' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (hL : StandardLatticesGL3.SD D L) (hL' : StandardLatticesGL3.SD D L') (hL₁ : StandardLatticesGL3.SD D L₁) (hL₁' : StandardLatticesGL3.SD D L₁')
    {G : TaylorLogMetric.VC D a b → ℂ} (hG : StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' G) :
    StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L₁ L₁'
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc dl) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc dl) L L')
        (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc dl) L₁ L₁') G) := by
  obtain ⟨e, κ, he, hκ, rfl⟩ := hG
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.TripleIntertwiner.triple_constant D cc dl hc a b _ _ _
    (Or.inl ⟨_, e, he, rfl⟩) (Or.inr ⟨L, L', hL, hL', rfl⟩) (Or.inr ⟨L₁, L₁', hL₁, hL₁', rfl⟩) _
    (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D (GlobalTheory.InducedType.induced_type D).1 cc dl t0 hc ht e he.1)
  refine ⟨e, κ * μ, he, GlobalTheory.VacuumMove.mod1All_mul hκ hμ, funext fun z => ?_⟩
  rw [GlobalTheory.VacuumMove.Iop_mul, mul_assoc κ μ]
  exact congrArg (κ * ·) (congrFun h z)

theorem sd_stdL (D : D7) (n : ℕ) : StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D n) := by
  letI := D.host.cmStar
  exact GlobalTheory.SeamSelfDual.isSDLat_pi D.host.E n

theorem isVacuum_movedThetaVacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) (B.thZero a b) → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' (B.thMoved a b L L') := by
  intro D cc dl B t0 hc ht a b L L' hL hL' h0
  exact isVacuum_thetaIntertwiner_selfDual D cc dl t0 hc ht hL (sd_stdL D b) hL hL'
    (isVacuum_thetaIntertwiner_selfDual D cc dl t0 hc ht (sd_stdL D a) (sd_stdL D b) hL (sd_stdL D b) h0)

end GlobalTheory.MovedVacuum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoNormalisationAtZeroSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isoNormalisation_at_zeroSection : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)ˣ), (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Normal t c αA βB → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ (φB' ≫ GlobalTheory.HomFixUniv.θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p) (by simp)).hom (c i j) *
          ((φA' ≫ GlobalTheory.HomFixUniv.θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (u p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  first | (exact @GlobalTheory.HomFixNorm.norm_at_zero) | (exact GlobalTheory.HomFixNorm.norm_at_zero) | (intros; apply GlobalTheory.HomFixNorm.norm_at_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KoszulResolutionThreeTermsExact
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Koszul

noncomputable def pairEquiv (g : ℕ) : {z : Sym2 (Fin g) // ¬ z.IsDiag} ≃ Fin (g.choose 2) :=
  Fintype.equivFinOfCardEq (by rw [Sym2.card_subtype_not_diag, Fintype.card_fin])

variable {O : Type} [CommRing O] {g : ℕ}

noncomputable def upper (x : Fin (g.choose 2) → O) : Matrix (Fin g) (Fin g) O :=
  fun i j => if h : i < j then
    x (pairEquiv g ⟨s(i, j), by rw [Sym2.mk_isDiag_iff]; exact h.ne⟩) else 0

noncomputable def skew (x : Fin (g.choose 2) → O) : Matrix (Fin g) (Fin g) O :=
  fun i j => upper x i j - upper x j i

lemma upper_add (x x' : Fin (g.choose 2) → O) : upper (x + x') = upper x + upper x' := by
  ext i j; simp only [upper, Matrix.add_apply]; split_ifs <;> simp

lemma upper_smul (a : O) (x : Fin (g.choose 2) → O) : upper (a • x) = a • upper x := by
  ext i j; simp only [upper, Matrix.smul_apply]; split_ifs <;> simp

lemma skew_add (x x' : Fin (g.choose 2) → O) : skew (x + x') = skew x + skew x' := by
  ext i j; simp only [skew, upper_add, Matrix.add_apply]; ring

lemma skew_smul (a : O) (x : Fin (g.choose 2) → O) : skew (a • x) = a • skew x := by
  ext i j; simp only [skew, upper_smul, Matrix.smul_apply, smul_eq_mul]; ring

noncomputable def d₂ (f : Fin g → O) : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O) where
  toFun x := (skew x).mulVec f
  map_add' x x' := by rw [skew_add, Matrix.add_mulVec]
  map_smul' a x := by
    rw [skew_smul]; ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

lemma d₂_apply (f : Fin g → O) (x : Fin (g.choose 2) → O) : d₂ f x = (skew x).mulVec f := rfl

lemma sum_skew_mulVec (f : Fin g → O) (x : Fin (g.choose 2) → O) :
    ∑ i, (skew x).mulVec f i * f i = 0 := by
  simp only [Matrix.mulVec, dotProduct, skew, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [sub_eq_zero, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma exists_skew_eq (c : Matrix (Fin g) (Fin g) O) (hd : ∀ i, c i i = 0)
    (hs : ∀ i j, c i j = - c j i) : ∃ x : Fin (g.choose 2) → O, skew x = c := by
  let F : Sym2 (Fin g) → O :=
    Sym2.lift ⟨fun i j => c (min i j) (max i j), fun i j => show c (min i j) (max i j) = c (min j i) (max j i) by rw [min_comm, max_comm]⟩
  refine ⟨fun k => F ((pairEquiv g).symm k).1, ?_⟩
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [skew, upper, h, lt_asymm h, F, min_eq_left h.le, max_eq_right h.le]
  · simp [skew, upper, hd]
  · simp [skew, upper, h, lt_asymm h, F, min_eq_left h.le, max_eq_right h.le, ← hs i j]

end GlobalTheory.Koszul

open GlobalTheory.Koszul in

theorem GlobalTheory.koszul_resolution_three_terms : ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∃ (e₁ : (Fin g → O) →ₗ[O] O) (e₂ : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O)), Function.Exact e₁ (Ideal.span (Set.range f)).mkQ ∧ Function.Exact e₂ e₁ ∧ (∀ x, e₁ x ∈ Ideal.span (Set.range f)) ∧ ∀ x i, e₂ x i ∈ Ideal.span (Set.range f) := by
  intro O _ g f hreg
  refine ⟨Fintype.linearCombination O f, d₂ f, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Fintype.range_linearCombination]
  · intro y
    constructor
    · intro hy
      rw [Fintype.linearCombination_apply] at hy
      obtain ⟨c, hd, hs, rfl⟩ := GlobalTheory.T.weaklyRegular_relations_eq_koszulRelations O g f hreg y (by simpa [smul_eq_mul] using hy)
      obtain ⟨x, hx⟩ := exists_skew_eq c hd hs
      exact ⟨x, by rw [d₂_apply, hx]⟩
    · rintro ⟨x, rfl⟩
      rw [Fintype.linearCombination_apply, d₂_apply]
      simpa [smul_eq_mul] using sum_skew_mulVec f x
  · intro x
    show _ ∈ Submodule.span O (Set.range f)
    rw [← Fintype.range_linearCombination]
    exact LinearMap.mem_range_self _ x
  · intro x i
    rw [d₂_apply]
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))
end

