import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0173
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0157
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0175
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.CapelliMain

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonDoubleCosetAdjointStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_doubleCoset_adjoint : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (Δ : Set M2) (ι κ : Type) [Fintype ι] [Fintype κ] (β : ι → M2) (α : κ → M2) (h f : ℍ → ℂ), 1 ≤ k → 0 < N → N ∣ L → 0 < q → q.Coprime N → Wt L ρ → (∀ δ ∈ Δ, δ.det = q ∧ (N : ℤ) ∣ δ 1 0) → LRep L Δ β → RRep L Δ α → Inv k L (ch ε) h → Inv k L (ch ε) f → Continuous h → Continuous f → (∀ i, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (h τ) * slz k (β i) f τ * (τ.im : ℂ) ^ k))) → pet k ρ h (hsum k (ch ε) β f) = pet k ρ (fun τ => ∑ j, ch ε⁻¹ (α j 0 0) * slz k (α j).adjugate h τ) f := by
  first | exact @GlobalTheory.EisM.pet_hsum_adjoint | exact GlobalTheory.EisM.pet_hsum_adjoint | (intros; apply GlobalTheory.EisM.pet_hsum_adjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PotentialCocycleDehomogenisedLawsStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialCocycleDehomogenised_laws : ∀ (w N l : ℕ), 0 < N → 0 < l → (∀ F ∈ Pot ℂ w (Gam N l), cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w ∧ (∀ γ : GlobalTheory.HeckeFamilyMatrices.Lev N l, ∀ τ ∈ Hs, deh (slP ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F γ) ∧ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w → F ∈ Triv ℂ w (Gam N l))) ∧ (∀ F G, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (F + G) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F + cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) G) ∧ (∀ (c : ℂ) F, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (c • F) = c • cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  first | exact @GlobalTheory.KZ.cocP_laws | exact GlobalTheory.KZ.cocP_laws | (intros; apply GlobalTheory.KZ.cocP_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionHeckeUEqSumSlashStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_heckeU_eq_sum_slash : ∀ (k l : ℕ) (a : ℕ → ℂ), 1 ≤ k → 0 < l → PolyB a → PolyB (Uo l a) ∧ ∀ τ : ℍ, qs (Uo l a) τ = ∑ j : Fin l, slz k (repU l j) (qs a) τ := by
  first | exact @GlobalTheory.EisM.Uo_qs_sum_slz | exact GlobalTheory.EisM.Uo_qs_sum_slz | (intros; apply GlobalTheory.EisM.Uo_qs_sum_slz <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QNotPthPowInClosureAlgebraicPadicIntStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.q_not_pth_pow_in_closure_algebraic_padicInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
      b ^ p ≠ algebraMap (O0 p) Ω (qO p) := by
  first | exact @GlobalTheory.K5.NotPow.q_not_pow | exact GlobalTheory.K5.NotPow.q_not_pow | (intros; apply GlobalTheory.K5.NotPow.q_not_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinDirichletSeriesIdentityHecke
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem rankin_dirichlet_identity : ∀ (e : ℕ) (χ ψ θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ m n, ψ (m * n) = ψ m * ψ n) → (∀ m n, θ (m * n) = θ m * θ n) → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → ∀ b : ℕ → ℂ, (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) ∧ LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) * LSeries (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) * LSeries (fun n => θ n * g n) ((2 * (e : ℝ) + s : ℝ) : ℂ) := by
  intro e χ ψ θ g s he hs hψ hθ hn hg hsum b hb
  have hGB := GlobalTheory.T.lSeriesSummable_mul_divisorSum' e ψ θ g b s he hs (fun n => ⟨(hn n).2.1, (hn n).2.2⟩) hsum hb
  have hU := GlobalTheory.T.lSeriesSummable_twist_pow_of_summable_sq_div e ψ g s he hs (fun n => (hn n).2.1) hsum
  have hV := GlobalTheory.T.lSeriesSummable_bounded_mul_of_summable_sq_div e θ g s he hs (fun n => (hn n).2.2) hsum
  have hz := GlobalTheory.T.lSeries_squares_eq_shift e χ ψ θ s he hs hn
  refine ⟨hGB, ?_⟩
  rw [← hz.2, ← LSeries_convolution' hz.1 hGB, ← GlobalTheory.T.lSeries_twist_natPow_eq_shift e ψ g s he, ← LSeries_convolution' hU hV]
  exact LSeries_congr (fun {n} hn0 => (GlobalTheory.T.convolution_twist_eq_convolution_squares e χ ψ θ g b hψ hθ hg hb n hn0).symm) _

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumDilateStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_dilate : ∀ (j L N : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ τ' : ℍ), 0 < N → (τ' : ℂ) = N * τ →
    lat j 0 L v Φ τ' = lat j 0 L ((N : ℤ) * v.1, v.2) (fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0) τ := by
  first | exact @GlobalTheory.EisM.lat_dilate | exact GlobalTheory.EisM.lat_dilate | (intros; apply GlobalTheory.EisM.lat_dilate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumEqTsumOfKillsStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_eq_tsum_of_kills : ∀ (j L : ℕ) (s : ℝ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 2 ≤ j → 0 < s → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → (Summable fun x : ℤ × ℤ => ‖trm j s ((x.1 : ℂ) * τ + x.2)‖) ∧ lat j s L v Φ τ = ∑' x : ℤ × ℤ, Φ x * trm j s ((x.1 : ℂ) * τ + x.2) := by
  first | exact @GlobalTheory.EisM.lat_eq_tsum_of_kills | exact GlobalTheory.EisM.lat_eq_tsum_of_kills | (intros; apply GlobalTheory.EisM.lat_eq_tsum_of_kills <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RightGamma0CosetDecompositionAdjugateHeckeTStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightGamma0CosetDecomposition_adjugate_heckeT : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → RRep L (DT L q) (fun i => (repT q i).adjugate) := by
  first | exact @GlobalTheory.EisM.rrep_DT_adj_repT | exact GlobalTheory.EisM.rrep_DT_adj_repT | (intros; apply GlobalTheory.EisM.rrep_DT_adj_repT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SaturationLevelFunctionsIntegralRelationStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturation_levelFunctions_integralRelation : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (a b : ℍ → ℂ) (p : ℕ → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b → b ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a (γ • τ) * b τ = a τ * b (γ • τ)) → (∀ i, InR ε.range (p i)) → p n ≠ 0 → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * a τ ^ i * b τ ^ (n - i) = 0) → ∃ h : ℍ → ℂ, InR ε.range h ∧ ∀ τ, p n τ * a τ = h τ * b τ := by
  first | exact @GlobalTheory.FN.Sat.sat | exact GlobalTheory.FN.Sat.sat | (intros; apply GlobalTheory.FN.Sat.sat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularSSmulStatement
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_modularS_smul : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → sg c x (ModularGroup.S • τ) = sg c (act x ModularGroup.S) τ := by
  first | exact @GlobalTheory.Sieg.sg_S | exact GlobalTheory.Sieg.sg_S | (intros; apply GlobalTheory.Sieg.sg_S <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPermOfNotInjective
section
open Polynomial MeasureTheory

namespace GlobalTheory.CapelliWeyl

theorem sum_perm_of_not_injective {M : Type} [AddCommMonoid M] {n : ℕ}
    (F : (Fin n → Fin n) → M) (hF : ∀ s, ¬ Function.Injective s → F s = 0) :
    ∑ s, F s = ∑ p : Equiv.Perm (Fin n), F p := by
  symm
  have e : ∑ p : Equiv.Perm (Fin n), F p = ∑ s ∈ Finset.univ.map
      (⟨fun p : Equiv.Perm (Fin n) => (p : Fin n → Fin n), DFunLike.coe_injective⟩ :
        Equiv.Perm (Fin n) ↪ (Fin n → Fin n)), F s := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => hF s fun hinj => hs ?_
  rw [Finset.mem_map]
  exact ⟨Equiv.ofBijective s (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩

theorem map_det_eq {C W : Type} [CommRing C] [Ring W] {n : ℕ} (f : C →+* W)
    (M : Matrix (Fin n) (Fin n) C) :
    f M.det = ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      (List.ofFn fun j : Fin n => f (M (p j) j)).prod := by
  rw [Matrix.det_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, map_zsmul, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
  rfl

theorem normal_sum_of_map {C W : Type} [CommRing C] [Ring W] {n : ℕ} (f : C →+* W)
    (M : Matrix (Fin n) (Fin n) C) (d : Fin n → Fin n → W) :
    ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      ∑ s : Fin n → Fin n, (List.ofFn fun j : Fin n => f (M (s j) (p j))).prod *
        (List.ofFn fun j : Fin n => d (s j) j).prod =
    (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      (List.ofFn fun j : Fin n => f (M (p j) j)).prod) *
    (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      (List.ofFn fun j : Fin n => d (p j) j).prod) := by
  have hdet : ∀ s : Fin n → Fin n, ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      (List.ofFn fun j : Fin n => f (M (s j) (p j))).prod = f (M.submatrix s id).det := by
    intro s
    rw [← Matrix.det_transpose, map_det_eq]
    rfl
  rw [← map_det_eq]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← smul_mul_assoc, ← Finset.sum_mul, hdet]
  rw [sum_perm_of_not_injective
    (fun s => f (M.submatrix s id).det * (List.ofFn fun j : Fin n => d (s j) j).prod)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.det_permute, map_mul, map_intCast, mul_assoc, ← zsmul_eq_mul, mul_smul_comm]
  · intro s hs
    simp only [Function.Injective, not_forall] at hs
    obtain ⟨i, j, hij, hne⟩ := hs
    rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hij]), map_zero, zero_mul]

theorem exists_comm_lift {W : Type} [Ring W] {n : ℕ} (x : Fin n → Fin n → W)
    (hx : ∀ a b c e, Commute (x a b) (x c e)) :
    ∃ f : MvPolynomial (Fin n × Fin n) ℤ →+* W, ∀ a b, f (MvPolynomial.X (a, b)) = x a b := by
  let S : Set W := Set.range fun p : Fin n × Fin n => x p.1 p.2
  have hS : ∀ u ∈ S, ∀ v ∈ S, u * v = v * u := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact (hx _ _ _ _).eq
  letI : CommRing (Subring.closure S) := Subring.closureCommRingOfComm hS
  refine ⟨(Subring.closure S).subtype.comp
    (MvPolynomial.eval₂Hom (Int.castRingHom _)
      (fun p => (⟨x p.1 p.2, Subring.subset_closure ⟨p, rfl⟩⟩ : Subring.closure S))), ?_⟩
  intro a b
  rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
  rfl

theorem capelli_identity : ∀ {W : Type} [Ring W] {n : ℕ} (x d : Fin n → Fin n → W), (∀ a b c e, Commute (x a b) (x c e)) → (∀ a b c e, Commute (d a b) (d c e)) → (∀ a b c e, d a b * x c e - x c e * d a b = if a = c ∧ b = e then 1 else 0) → ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) • (List.ofFn fun j : Fin n => (∑ k, x k (p j) * d k j) + if p j = j then ((n - 1 - j.val : ℕ) : W) else 0).prod = (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) • (List.ofFn fun j : Fin n => x (p j) j).prod) * (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) • (List.ofFn fun j : Fin n => d (p j) j).prod) := by
  intro W _ n x d hx _ hdx
  have hA := PI.HookSteps.Cap.capelli_absolute_value W (Fin n) (Fin n) (fun a t => x t a)
    (fun b t => d t b) (fun a s b t => (hx _ _ _ _).eq)
    (fun a s b t => by
      have h := hdx t b s a
      rw [sub_eq_iff_eq_add'] at h
      rw [h]
      congr 1
      refine if_congr ⟨?_, ?_⟩ rfl rfl <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2.symm, h1.symm⟩)
    n id id
  simp only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero] at hA
  obtain ⟨f, hf⟩ := exists_comm_lift x hx
  have hB := normal_sum_of_map f (Matrix.of fun a b => MvPolynomial.X (a, b)) d
  simp only [Matrix.of_apply, hf] at hB
  rw [← hB]
  refine Eq.trans ?_ (hA.trans rfl)
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold PI.HookSteps.Cap.Lw PI.HookSteps.Cap.Eop
  congr 3
  funext j
  have hj : 1 + j.val ≤ n := by have := j.isLt; omega
  rw [Nat.sub_sub, Nat.cast_sub hj, Nat.cast_add, Nat.cast_one, ← sub_sub]
  rfl

end GlobalTheory.CapelliWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableRegularizedEisensteinLatticeTermStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_regularizedEisensteinLatticeTerm : ∀ (j L : ℕ) (v : ℤ × ℤ) (τ : ℍ), 1 ≤ j → 0 < L → Summable fun x => ‖dif L v (dif L v (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2))) x‖ := by
  first | exact @GlobalTheory.LatSumZ.latsum_summable | exact GlobalTheory.LatSumZ.latsum_summable | (intros; apply GlobalTheory.LatSumZ.latsum_summable <;> assumption)
end

