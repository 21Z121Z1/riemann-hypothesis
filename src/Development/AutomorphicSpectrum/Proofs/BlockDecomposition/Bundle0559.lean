import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0533
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantClosedSubgroupCompactQuotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0541
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterIntegralOrthogonality
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Orth

variable {D : D7}

theorem trA_incA_eq (e : D.host.E) :
    trA (incA D e) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
  have h : LinearMap.mulLeft (AF D.host.F) (incA D e) =
      LinearMap.baseChange (AF D.host.F) (LinearMap.mulLeft D.host.F e) := by
    ext b
    simp [TensorProduct.AlgebraTensorModule.curry_apply, incA, inclR, LinearMap.baseChange_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
  simp only [trA, Algebra.trace_apply]
  change LinearMap.trace _ _ (LinearMap.mulLeft (AF D.host.F) (incA D e)) =
    algebraMap _ _ (LinearMap.trace _ _ (LinearMap.mulLeft D.host.F e))
  rw [h, LinearMap.trace_baseChange]

theorem trA_smul_half (x : AF D.host.F) :
    trA (x • half D) = x := by
  have hE := D.host.toHostAx.der.finrank_E
  have hF := D.host.toHostAx.der.finrank_F
  have hpos : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
  have htow := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    rw [hF] at hpos htow
    rw [hE] at htow
    have h4 : 2 * D.R.ord * Module.finrank D.host.F D.host.E = 2 * D.R.ord * 2 := by
      rw [htow]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  have hhalf : trA (half D) = 1 := by
    rw [half, trA_incA_eq]
    have : (1 / 2 : D.host.E) = algebraMap D.host.F D.host.E (1 / 2) := by
      rw [map_div₀, map_one, map_ofNat]
    rw [this, Algebra.trace_algebraMap, h2]
    norm_num
  have hlin : trA (x • half D) = x * trA (half D) := by
    simp only [trA, map_smul, smul_eq_mul]
  rw [hlin, hhalf, mul_one]

theorem inner_rat_eq (V : HSp D) {s : ℕ} (q : Matrix (Fin V.rank) (Fin s) D.host.E) (y : Mx D V.rank s) :
    GlobalTheory.StdUnn.inner V (rat q) y = rat (qᴴ * V.gram) ⬝ y := by
  simp only [GlobalTheory.StdUnn.inner]
  rw [← rat_conjTranspose, gA, ← Matrix.mul_assoc, ← rat_mul]

theorem chi_add (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {s : ℕ} (x y u : Mx D V.rank s) :
    ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x (y + u)))) =
      ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x y))) * ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x u))) := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_add, Matrix.trace_add, trA, map_add, AddChar.map_add_eq_mul]

theorem chi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) {γ : Mx D V.rank s} (hγ : γ ∈ ratMx D V.rank s) :
    ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) γ))) = 1 := by
  obtain ⟨g, rfl⟩ := mem_ratMx.mp hγ
  have htr : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E), Matrix.trace (rat M) = incA D (Matrix.trace M) := by
    intro n M
    simp [rat, Matrix.trace, map_sum]
  rw [inner_rat_eq]
  change ψ (trA (Matrix.trace (rat (qᴴ * V.gram) * rat g))) = 1
  rw [← rat_mul, htr, trA_incA_eq]
  exact hψ.2.2.1 _

theorem exists_chi_ne_one {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    {q : Matrix (Fin V.rank) (Fin s) D.host.E} (hq : q ≠ 0) :
    ∃ u : Mx D V.rank s, ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) u))) ≠ 1 := by
  obtain ⟨x, hx⟩ := hψ.2.2.2
  have hM : qᴴ * V.gram ≠ 0 := by
    intro h
    apply hq
    have h1 : qᴴ = 0 := by
      rw [← Matrix.mul_nonsing_inv_cancel_right V.gram qᴴ (gram_isUnit_det V), h, Matrix.zero_mul]
    simpa using congrArg Matrix.conjTranspose h1
  obtain ⟨i, j, hij⟩ : ∃ i j, (qᴴ * V.gram) i j ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hM (Matrix.ext hne)
  have key : ∀ (A : Mx D s V.rank) (c : AE D), Matrix.trace (A * Matrix.single j i c) = A i j * c := by
    intro A c
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_zero]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  refine ⟨Matrix.single j i (incA D ((qᴴ * V.gram) i j)⁻¹ * (x • half D)), ?_⟩
  rw [inner_rat_eq]
  change ψ (trA (Matrix.trace (rat (qᴴ * V.gram) *
      Matrix.single j i (incA D ((qᴴ * V.gram) i j)⁻¹ * (x • half D))))) ≠ 1
  rw [key, show rat (qᴴ * V.gram) i j = incA D ((qᴴ * V.gram) i j) from rfl, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ hij, map_one, one_mul, trA_smul_half]
  exact hx

theorem orthogonality : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (s : ℕ)
    (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)), IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ q : Matrix (Fin V.rank) (Fin s) D.host.E,
      (q = 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 1) ∧
      (q ≠ 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 0) := by
  intro D ψ hψ V s μs 𝓕s hcov q
  constructor
  · rintro rfl
    have h0 : ∀ y : Mx D V.rank s, ψ (trA (Matrix.trace (inner V (rat (0 : Matrix (Fin V.rank) (Fin s) D.host.E)) y))) = 1 := by
      intro y
      simp [GlobalTheory.StdUnn.inner, rat_zero, adj_zero, trA]
    simp_rw [h0]
    rw [MeasureTheory.setIntegral_const]
    simp [Measure.real, hcov.2.2]
  · intro hq
    obtain ⟨u, hu⟩ := exists_chi_ne_one hψ V hq
    set φ : Mx D V.rank s → ℂ := fun y => ψ (trA (Matrix.trace (inner V (rat q) y))) with hφ
    have hper : ∀ γ ∈ ratMx D V.rank s, ∀ a, φ (γ + a) = φ a := by
      intro γ hγ a
      simp only [hφ]
      rw [chi_add, chi_rat hψ V q hγ, one_mul]
    have h1 := covolOne_integral_add hcov φ hper u
    have h2 : ∀ a, φ (a + u) = φ u * φ a := by
      intro a
      simp only [hφ]
      rw [chi_add, mul_comm]
    simp only [h2] at h1
    rw [MeasureTheory.integral_const_mul] at h1
    have h3 : (φ u - 1) * ∫ y in 𝓕s, φ y ∂μs = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) hu
    · exact h

end GlobalTheory.CompanionTheory.EisUnfold.Orth

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterTracePairingEqInnerPsiStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trace_pairing_eq_inner_psi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
  (b : HermR (AF F) σ n) (X : Fin n → Fin M → AF F ⊗[F] E),
  ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) =
    psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
        gramR (Ainf F) σ J (projInf X)))) *
    psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
      (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
        gramR (Af F) σ J (projFin X)))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.adelic_phase_split | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.adelic_phase_split | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.adelic_phase_split <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedUnipotentCompactExhaustion
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnipExhaust

theorem exists_compact_subgroup_between {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {U : Subgroup (GL (Fin N) k)}
    (hU : U ≤ unipB k (Fin N)) (hcl : IsClosed (U : Set (GL (Fin N) k)))
    (Q : Set (GL (Fin N) k)) (hQ : IsCompact Q) (hQU : Q ⊆ (U : Set (GL (Fin N) k))) :
    ∃ L : {L : Subgroup (GL (Fin N) k) // IsCompact (L : Set (GL (Fin N) k)) ∧ L ≤ U},
      Q ⊆ (L.1 : Set (GL (Fin N) k)) := by
  obtain ⟨U₀, hc, hs⟩ := GlobalTheory.UnipCptSub.exists_compact_subgroup_of_isCompact Q hQ
    (fun g hg => hU (hQU hg))
  refine ⟨⟨U₀ ⊓ U, ?_, inf_le_right⟩, fun g hg => ⟨hs hg, hQU hg⟩⟩
  rw [Subgroup.coe_inf]
  exact hc.inter_right hcl

theorem exists_monotone_compact_exhaustion :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
      (U : Subgroup (GL (Fin N) k)), U ≤ unipB k (Fin N) → IsClosed (U : Set (GL (Fin N) k)) →
      ∃ L : ℕ → Subgroup (GL (Fin N) k), Monotone L ∧ (∀ j, IsCompact (L j : Set (GL (Fin N) k))) ∧
        (∀ j, L j ≤ U) ∧ ∀ n ∈ U, ∃ j, n ∈ L j := by
  intro k _ _ _ _ N U hU hcl
  haveI : SecondCountableTopology (GL (Fin N) k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : LocallyCompactSpace (GL (Fin N) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  haveI : SigmaCompactSpace (GL (Fin N) k) := inferInstance
  let S := {L : Subgroup (GL (Fin N) k) // IsCompact (L : Set (GL (Fin N) k)) ∧ L ≤ U}
  let K : ℕ → Set (GL (Fin N) k) := compactCovering (GL (Fin N) k)
  have hstep : ∀ (j : ℕ) (A : S), ∃ B : S,
      (K j ∩ (U : Set (GL (Fin N) k))) ∪ (A.1 : Set (GL (Fin N) k)) ⊆ (B.1 : Set (GL (Fin N) k)) :=
    fun j A => exists_compact_subgroup_between hU hcl _
      (((isCompact_compactCovering _ j).inter_right hcl).union A.2.1)
      (Set.union_subset Set.inter_subset_right A.2.2)
  choose next hnext using hstep
  let b : S := ⟨⊥, by rw [Subgroup.coe_bot]; exact isCompact_singleton, bot_le⟩
  let f : ℕ → S := fun j => Nat.rec b (fun i A => next i A) j
  have hsucc : ∀ j, f (j + 1) = next j (f j) := fun _ => rfl
  refine ⟨fun j => (f j).1, monotone_nat_of_le_succ fun j g hg => ?_, fun j => (f j).2.1,
    fun j => (f j).2.2, fun n hn => ?_⟩
  · rw [hsucc]
    exact hnext j (f j) (Or.inr hg)
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1
      ((iUnion_compactCovering (GL (Fin N) k)).symm ▸ Set.mem_univ n : n ∈ ⋃ i, K i)
    refine ⟨j + 1, ?_⟩
    show n ∈ (f (j + 1)).1
    rw [hsucc]
    exact hnext j (f j) (Or.inl ⟨hj, hn⟩)

end GlobalTheory.CompanionTheory.UnipExhaust
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantClosedSubgroupCompactQuotientStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutant_closed_subgroup_compact_quotient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (M : Type) [Finite M] (S : M → Matrix (Fin n) (Fin n) E) (L : Subgroup (GAd σ J)), IsClosed (L : Set (GAd σ J)) → (∀ g ∈ L, ∀ k, (matHom _ σ J g).1 * (S k).map (inclR (F := F) (AF F)) = (S k).map (inclR (F := F) (AF F)) * (matHom _ σ J g).1) → (∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ L, ∀ ξ : Fin n → E, ξ ≠ 0 → ε ≤ hgt σ J g ξ) → (∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (S k).map (inclR (F := F) (AF F)) = (S k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ L) → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ L ∧ ∀ g ∈ L, ∃ δ ∈ ratPts σ J, δ ∈ L ∧ δ⁻¹ * g ∈ Ω := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.exists_isCompact_of_centralizer_height | exact GlobalTheory.CompanionTheory.ParCocompact.exists_isCompact_of_centralizer_height | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.exists_isCompact_of_centralizer_height <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicColumnNormLower
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.AdelicColumn

def trGL {n : ℕ} {R : Type*} [CommRing R] (m : GL (Fin n) R) : GL (Fin n) R :=
  ⟨(m : Matrix (Fin n) (Fin n) R)ᵀ, ((m⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

theorem continuous_trGL {n : ℕ} {R : Type*} [CommRing R] [TopologicalSpace R] :
    Continuous (trGL : GL (Fin n) R → GL (Fin n) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val (M := Matrix (Fin n) (Fin n) R)).matrix_transpose
  · exact (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) R)).matrix_transpose

theorem single_vecMul_trGL {n : ℕ} {R : Type*} [CommRing R] (m : GL (Fin n) R) (j : Fin n) :
    (Pi.single j (1 : R) : Fin n → R) ᵥ* ((trGL m : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      fun i => (m : Matrix (Fin n) (Fin n) R) i j := by
  ext i
  simp [trGL]

theorem column_bound :
    ∀ (C : Set (AdelicGLn.AdelicGL ℚ 3)), IsCompact C → ∃ ε : ℝ, 0 < ε ∧ ∀ m ∈ C, ∀ j : Fin 3,
      Reduction.HasFiniteContent (fun i => (m : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) i j) ∧
        ε ≤ Reduction.adelicNorm (fun i => (m : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) i j) := by
  intro C hC
  obtain ⟨ε, hε, h⟩ := Reduction.exists_pos_le_height (hC.image continuous_trGL)
  refine ⟨ε, hε, fun m hm j => ?_⟩
  have hcol := single_vecMul_trGL m j
  constructor
  · rw [← hcol]
    exact (Reduction.hasFiniteContent_single_one j).vecMul (trGL m)
  · have hx : (Pi.single j (1 : ℚ) : Fin 3 → ℚ) ≠ 0 := by
      intro h0
      simpa using congrFun h0 j
    have := h (trGL m) ⟨m, hm, rfl⟩ _ hx
    rw [Reduction.height, Reduction.ratVec_single_one] at this
    rwa [← hcol]

end GlobalTheory.CompanionTheory.AdelicColumn
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicNormBoundedStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_adelic_norm_bounded : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (D : Set (Fin N → AF F)), IsCompact D → ∃ P : ℝ, 0 < P ∧ ∀ y ∈ D, GroundTheory.Automorphic.Reduction.adelicNorm y ≤ P := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact | exact GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactElementEigenvaluesUnitsStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_element_eigenvalues_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (g : H) (p : GLw n w) (s : Fin n → (w.adicCompletion E)ˣ), g.1 = p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹ → IsCompact (closure (Subgroup.zpowers g : Set H)) → ∀ i, Valued.v (s i : w.adicCompletion E) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers | exact GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactHeightLowerBoundStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_height_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (D : Set (GAd σ J)), IsCompact D → ∃ P : ℝ, 0 < P ∧ ∀ g ∈ D, ∀ v : Fin n → E, v ≠ 0 → 1 ≤ P * hgt σ J g v := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.exists_one_le_mul_hgt | exact GlobalTheory.CompanionTheory.RedCov.Simple.exists_one_le_mul_hgt | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.exists_one_le_mul_hgt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticone
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.UnderIdeal

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {A Ω : Type*} [CommRing A] [Field Ω]

theorem eval_eq_zero_of_mem_mCoordIdeal (e : A →+* Ω) (he : Function.Injective e) (ρ : (Σ k, ι k) → A)
    {f : Geo.MRing ι} (hf : f ∈ Geo.mCoordIdeal fun p => e (ρ p)) (ε : A →+* ℂ) (t : K → ℂ) :
    eval (fun p => t p.1 * ε (ρ p)) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  let q : Geo.MRing ι →+* MvPolynomial K A := eval₂Hom (Int.castRingHom _) fun p => C (ρ p) * X p.1
  have h1 : (MvPolynomial.map e).comp q =
      (Geo.mConeMap (fun p => e (ρ p)) : Geo.MRing ι →ₐ[ℤ] MvPolynomial K Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp [q]
    · simp [q, Geo.mConeMap]
  have h0 : q f = 0 := by
    refine map_injective e he ?_
    rw [map_zero]
    have := congrArg (fun g => g f) h1
    refine this.trans ?_
    exact hf
  have h2 : (eval₂Hom ε t).comp q =
      (eval (fun p => t p.1 * ε (ρ p))).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp [q]
    · simp [q, mul_comm]
  have := congrArg (fun g => g f) h2
  simp only [RingHom.comp_apply, h0, map_zero] at this
  exact this.symm

end Alg

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_eq_mul (x : MP ℤ m n) (c : ∀ k, Bk n k) (hx : x ∈ mchart c) :
    ∃ b : Fin (m + 1) → (MP ℤ m n).residueField x, (∀ k, b k ≠ 0) ∧ ∀ p : Σ k, Bk n k,
      ptCoord x p = b p.1 * (MP ℤ m n).evaluation (mchart c) x hx
        (resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2)) := by
  have key : ∀ k, ∃ b : (MP ℤ m n).residueField x, b ≠ 0 ∧ ∀ j : Bk n k,
      ptCoord x ⟨k, j⟩ = b * (MP ℤ m n).evaluation (blockChart n k (c k)) x (mchart_le c k hx)
        (pullRatio (prB n k) _ (c k) le_rfl j) := by
    intro k
    let W₀ := blockChart n k (ptChart x k)
    let W₁ := blockChart n k (c k)
    let V := W₀ ⊓ W₁
    have hxV : x ∈ V := ⟨mem_ptChart x k, mchart_le c k hx⟩
    have hV₀ : V ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := inf_le_left
    have hV₁ : V ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (c k) := inf_le_right
    have e₀ : ∀ j : Bk n k, ptCoord x ⟨k, j⟩ =
        (MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (ptChart x k) hV₀ j) := by
      intro j
      show (MP ℤ m n).evaluation W₀ x (mem_ptChart x k) (pullRatio (prB n k) W₀ (ptChart x k) le_rfl j) = _
      rw [← ProjImage.evaluation_resG (inf_le_left : V ≤ W₀) x hxV]
      exact congrArg _ (resG_pullRatio (φ := prB n k) (hi := le_rfl) inf_le_left)
    have e₁ : ∀ j : Bk n k, (MP ℤ m n).evaluation W₁ x (mchart_le c k hx)
        (pullRatio (prB n k) W₁ (c k) le_rfl j) =
        (MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (c k) hV₁ j) := by
      intro j
      rw [← ProjImage.evaluation_resG (inf_le_right : V ≤ W₁) x hxV]
      exact congrArg _ (resG_pullRatio (φ := prB n k) (hi := le_rfl) inf_le_right)
    refine ⟨(MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (ptChart x k) hV₀ (c k)), ?_, fun j => ?_⟩
    · intro h0
      have e := congrArg ((MP ℤ m n).evaluation V x hxV)
        ((pullRatio_mul_pullRatio (φ := prB n k) (hi := hV₀) (hj := hV₁) (k := ptChart x k)).trans pullRatio_self)
      rw [map_mul, h0, zero_mul, map_one] at e
      exact zero_ne_one e
    · refine (e₀ j).trans ?_
      rw [e₁ j, ← map_mul]
      exact congrArg _ (pullRatio_mul_pullRatio (φ := prB n k) (hi := hV₀) (hj := hV₁) (k := j)).symm
  choose b hb hbe using key
  refine ⟨b, hb, fun p => ?_⟩
  rw [ProjImage.evaluation_resG]
  exact hbe p.1 p.2

theorem evaluation_genericPoint_injective {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U) :
    Function.Injective (X.evaluation U (genericPoint X) h) := by
  have h1 : Function.Injective (X.residue (genericPoint X)).hom :=
    RingHom.injective (R := X.functionField) (X.residue (genericPoint X)).hom
  exact h1.comp (fnOf_injective U h)

end GlobalTheory.CompanionTheory.MPDict.UnderIdeal

namespace GlobalTheory.CompanionTheory.MPDict

open UnderIdeal in

theorem exists_mem_mcPts_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀), ∃ z ∈ mcPts (ptIdeal (i (genericPoint X))), IsUnder (PtsOver.map i rfl _ y) z := by
  intro m n X _ i _ y
  obtain ⟨z, hz, hu⟩ := exists_isUnder_of_cxPt m n (PtsOver.map i rfl _ y)
  refine ⟨z, ⟨hz, fun f hf => ?_⟩, hu⟩
  choose c hc using hz
  have hwk : ∀ k, PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) :=
    fun k => (hu k (c k)).1.2 (hc k)
  have hwV : PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => CxPts.mem_ptsIn.1 (hwk k))
  have hyV : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) := hwV
  have hη : genericPoint X ∈ i ⁻¹ᵁ mchart c :=
    ((genericPoint_spec X).mem_open_set_iff (i ⁻¹ᵁ mchart c).isOpen).2 ⟨_, trivial, CxPts.mem_ptsIn.1 hyV⟩
  obtain ⟨b, hb, hbe⟩ := ptCoord_eq_mul (i (genericPoint X)) c hη
  let r : (Σ k, Bk n k) → Γ(MP ℤ m n, mchart c) := fun p =>
    resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2)
  let ρ : (Σ k, Bk n k) → Γ(X, i ⁻¹ᵁ mchart c) := fun p => (i.app (mchart c)).hom (r p)
  let φ := (i.residueFieldMap (genericPoint X)).hom
  have hf' : f ∈ Geo.mCoordIdeal fun p => (X.evaluation _ _ hη).hom (ρ p) := by
    have e := ProjImage.imageZ_mCoordIdeal_of_eq (ι := Bk n) (ι' := Bk n) id Function.injective_id id (fun _ => rfl) φ
      (fun k => φ (b k)) (fun k => (map_ne_zero φ).2 (hb k))
      (ptCoord (i (genericPoint X))) (fun p => (X.evaluation _ _ hη).hom (ρ p)) (fun p => by
        rw [hbe p, map_mul]
        congr 1
        exact Scheme.evaluation_naturality_apply _ _ _ _)
    rw [ptIdeal, ← e] at hf
    simpa [ReciprocityTheory.ChartRestriction.G.AI.I4.imageZ] using hf
  have h := eval_eq_zero_of_mem_mCoordIdeal (X.evaluation _ _ hη).hom
    (evaluation_genericPoint_injective _ hη) ρ hf' (evHom hyV) (fun k => z ⟨k, c k⟩)
  have hz' : (fun p : Σ k, Bk n k => z ⟨p.1, c p.1⟩ * evHom hyV (ρ p)) = z := by
    funext ⟨k, j⟩
    have e1 : evHom hyV (ρ ⟨k, j⟩) = z ⟨k, j⟩ / z ⟨k, c k⟩ := by
      rw [← CxPts.ev_eq hyV]
      refine Eq.trans ?_ ((hu k (c k)).2 j (hwk k))
      refine Eq.trans ?_ (CxPts.ev_res (mchart_le c k) hwV _)
      exact (valR_comp y.1 i (mchart c) (r ⟨k, j⟩)).symm
    show z ⟨k, c k⟩ * evHom hyV (ρ ⟨k, j⟩) = z ⟨k, j⟩
    rw [e1, mul_div_cancel₀ _ (hc k)]
  rw [hz'] at h
  exact h

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeIntegralFiniteLargeExponentStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_integral_finite_large_exponent : ∀ (F : Type) [Field F] [NumberField F] (n r : ℕ) (c : ℝ), 0 < c → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    ∫⁻ t in cone r c, ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.ConeInt.lintegral_cone_lt_top | exact GlobalTheory.CompanionTheory.ConeInt.lintegral_cone_lt_top | (intros; apply GlobalTheory.CompanionTheory.ConeInt.lintegral_cone_lt_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFourierCharacterOfMatrixStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_fourier_character_of_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ T : Matrix (Fin n) (Fin n) E, Continuous (chiT σ ψ T) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.continuous_chiT | exact GlobalTheory.CompanionTheory.SiegelND.Coef.continuous_chiT | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.continuous_chiT <;> assumption)
end

