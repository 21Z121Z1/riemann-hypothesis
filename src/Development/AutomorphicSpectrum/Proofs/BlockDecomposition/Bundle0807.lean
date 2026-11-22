import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0800
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0776
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarActionFifthReal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0802
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0803
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockSplittingMaximalCompact
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PfSWUS.FockSplit

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

section Box

open NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem isPureFin_box (b : Module.Basis (Fin d) F E) {n M : ℕ}
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v))
    (hS : ∀ v, v ∉ S → A v = HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b ((GlobalTheory.CompanionTheory.WhitFree.boxF A).indicator (fun _ => (1 : ℂ)))
      (fun v => (A v).indicator 1) := by
  classical
  refine ⟨fun v => ?_, ?_, fun X => ?_⟩
  · haveI : T2Space (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
      (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).isEmbedding.t2Space
    have hcl : IsClopen (A v) := ⟨(hA v).1.isClosed, (hA v).2⟩
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
      HasCompactSupport.intro (hA v).1 fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ A v
    · exact ⟨A v, (hA v).2, hx, fun y hy => by
        beta_reduce
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
        rfl⟩
    · exact ⟨(A v)ᶜ, hcl.compl.isOpen, hx, fun y hy => by
        beta_reduce
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩
  · refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    refine hv ?_
    show (A v).indicator 1 = _
    rw [hS v h]
  · by_cases hX : X ∈ GlobalTheory.CompanionTheory.WhitFree.boxF A
    · rw [Set.indicator_of_mem hX]
      exact (finprod_eq_one_of_forall_eq_one fun v => Set.indicator_of_mem (hX v) _).symm
    · rw [Set.indicator_of_notMem hX]
      obtain ⟨v₀, hv₀⟩ : ∃ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v X ∉ A v := by
        by_contra h
        push_neg at h
        exact hX h
      refine (finprod_eq_zero _ v₀ (Set.indicator_of_notMem hv₀ _) ?_).symm
      have hfin := Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b X)
      refine (hfin.union S.finite_toSet).subset fun v hv => ?_
      by_contra h
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not, Finset.mem_coe] at h
      apply hv
      show (A v).indicator 1 (HeckeCharacterZeroLocus.SiegelWeilU.projV v X) = 1
      rw [hS v h.2]
      exact Set.indicator_of_mem h.1 _

end Box

theorem exists_fin_sum {M : Type*} [AddCommGroup M] [Module ℂ M] {P : M → Prop}
    (hs : ∀ (a : ℂ) (x : M), P x → P (a • x)) {x : M} (hx : x ∈ Submodule.span ℂ {y | P y}) :
    ∃ (N : ℕ) (f : Fin N → M), x = ∑ j, f j ∧ ∀ j, P (f j) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, fun _ => x, by simp, fun _ => h⟩
  | zero => exact ⟨0, Fin.elim0, by simp, fun j => j.elim0⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, f, rfl, hf⟩ := hx
    obtain ⟨N', f', rfl, hf'⟩ := hy
    refine ⟨N + N', Fin.append f f', by simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right], fun j => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa [Fin.append_left] using hf i
    · simpa [Fin.append_right] using hf' i
  | smul a x _ hx =>
    obtain ⟨N, f, rfl, hf⟩ := hx
    exact ⟨N, fun j => a • f j, by rw [Finset.smul_sum], fun j => hs a _ (hf j)⟩

variable {D : D7} {n : ℕ}

theorem evalPoly_monomial_mul {m : ℕ} (e : D.what₂.Tau × Fin m × Fin n × Bool →₀ ℕ) (a c : ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.monomial e (a * c)) z = a * evalPoly (MvPolynomial.monomial e c) z := by
  simp only [evalPoly, MvPolynomial.eval_monomial, mul_assoc]

theorem isMonoFock_smul {θ : InfFam D} {V : HSp D} {l : D.what₂.Tau → ℝ}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {φ : Mx D V.rank n → ℂ} (a : ℂ)
    (h : IsMonoFock θ V l s φ) : IsMonoFock θ V l s (a • φ) := by
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  refine ⟨e, a * c, g, d, bs, gv, hp, funext fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, evalPoly_monomial_mul, mul_assoc]

theorem gen_mem_span (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    (fun x : Mx D V.rank n => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) ∈ Submodule.span ℂ {φ | IsMonoFock θ V l s φ} := by
  classical
  haveI : FiniteDimensional D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let b := Module.finBasis D.host.F D.host.E
  let tr : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := fun X i j => X j i
      invFun := fun Z j i => Z i j
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => continuous_pi fun i =>
        (continuous_apply j).comp (continuous_apply i) }
  let g' : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun X => g (tr X)
  have hg' : IsSB g' := ⟨hg.1.comp_continuous tr.continuous, hg.2.comp_homeomorph tr⟩
  obtain ⟨t, A, S, hA, hS, hdec⟩ := Box.exists_box_combN b g' hg'
  let ind : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ :=
    fun a Z => (GlobalTheory.CompanionTheory.WhitFree.boxF (A a)).indicator (fun _ => (1 : ℂ)) (fun j i => Z i j)
  have hpure : ∀ a ∈ t, HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b (fun X => ind a fun i j => X j i)
      (fun v => (A a v).indicator 1) := fun a ha => isPureFin_box b (A a) S (hA a) (hS a ha)
  have hφ : (fun x : Mx D V.rank n => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) =
      ∑ e ∈ p.support, ∑ a ∈ t, g' a • (fun x : Mx D V.rank n =>
        evalPoly (MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) *
          gauss V l s (fun τ => compAt θ τ x) * ind a (fun i j => finPart D (x i j))) := by
    funext x
    have hp : evalPoly p (fun τ => compAt θ τ x) =
        ∑ e ∈ p.support, evalPoly (MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) := by
      calc evalPoly p (fun τ => compAt θ τ x)
          = evalPoly (∑ e ∈ p.support, MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) := by
            rw [← p.as_sum]
        _ = _ := by simp only [evalPoly, map_sum]
    have hgx : g (fun i j => finPart D (x i j)) =
        ∑ a ∈ t, g' a * ind a (fun i j => finPart D (x i j)) :=
      hdec (fun j i => finPart D (x i j))
    rw [hp, hgx, Finset.sum_mul, Finset.sum_mul, Finset.sum_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hφ]
  refine Submodule.sum_mem _ fun e _ => Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨e, p.coeff e, ind a, _, b, _, hpure a ha, rfl⟩

theorem fockA_le_span (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    fockA θ V n l s ≤ Submodule.span ℂ {φ | IsMonoFock θ V l s φ} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  exact gen_mem_span θ V l s p g hg

end GlobalTheory.CompanionTheory.PfSWUS.FockSplit

namespace GlobalTheory.CompanionTheory.PfSWUS

theorem fockSplitK : PositivityTheory.PfSWUS.FockSplitK := by
  intro D n V ψ χ θ μ ω H l s ν Φ hStd _ k hk
  exact FockSplit.exists_fin_sum (fun a _ h => FockSplit.isMonoFock_smul a h)
    (FockSplit.fockA_le_span θ V l s (fockKStable D n V ψ χ θ μ ω H l s ν Φ hStd k hk))

end GlobalTheory.CompanionTheory.PfSWUS

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerSummableRationalHermitian
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HermSum

open GlobalTheory.StdUnn.Model (submatrix_fromBlocks_mul block_matrix_one)

theorem mat_mul_block_decomposition {D : D7} {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem weyl_mul_inv {R : Type} [CommRing R] {k : ℕ} :
    blk4 (0 : Matrix (Fin k) (Fin k) R) 1 (-1) 0 * blk4 0 (-1) 1 0 = 1 := by
  rw [submatrix_fromBlocks_mul]
  simp [block_matrix_one]

theorem weyl_conj {R : Type} [CommRing R] {k : ℕ} (d : Matrix (Fin k) (Fin k) R) :
    blk4 (0 : Matrix (Fin k) (Fin k) R) 1 (-1) 0 * blk4 1 d 0 1 * blk4 0 (-1) 1 0 = blk4 1 0 (-d) 1 := by
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

private theorem mat_one_eq_one {D : D7} {n : ℕ} : mat (1 : G D n) = 1 := by
  simp only [GlobalTheory.StdUnn.mat, map_one, Units.val_one]

private theorem mat_inv_eq_of_mat_mul_eq_one {D : D7} {n : ℕ} (g : G D n) (M : Mx D (n + n) (n + n))
    (h : mat g * M = 1) : mat g⁻¹ = M := by
  have h1 : mat g⁻¹ * mat g = 1 := by rw [← mat_mul_block_decomposition, inv_mul_cancel, mat_one_eq_one]
  calc mat g⁻¹ = mat g⁻¹ * (mat g * M) := by rw [h, mul_one]
    _ = M := by rw [← mul_assoc, h1, one_mul]

private theorem blk4_apply_inr_inl {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c i j := by
  show (Matrix.fromBlocks a b c d).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c i j
  rw [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]

private theorem mulVec_single_one_apply' {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (i j : Fin m) : (M *ᵥ Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec]

private theorem eq_zero_of_mem_P_of_mat_eq_blk4 {D : D7} {n : ℕ} (x : G D n) (hx : x ∈ P D n)
    (d : Mx D n n) (hd : mat x = blk4 1 0 (-d) 1) : d = 0 := by
  have key : ∀ v : Fin (n + n) → AE D,
      v ∈ GlobalTheory.StdUnn.upperHalf D n ↔ (mat x).mulVec v ∈ GlobalTheory.StdUnn.upperHalf D n := hx
  refine Matrix.ext fun i j => ?_
  have hv : (Pi.single (finSumFinEquiv (Sum.inl j)) 1 : Fin (n + n) → AE D) ∈
      GlobalTheory.StdUnn.upperHalf D n := by
    rw [GlobalTheory.StdUnn.upperHalf, LinearMap.mem_ker]
    ext l
    rw [LinearMap.funLeft_apply, Pi.zero_apply, Pi.single_eq_of_ne]
    exact fun h => Sum.inr_ne_inl (finSumFinEquiv.injective h)
  have h2 := (key _).1 hv
  rw [hd, GlobalTheory.StdUnn.upperHalf, LinearMap.mem_ker] at h2
  have h3 := congrFun h2 i
  rw [LinearMap.funLeft_apply, Pi.zero_apply, mulVec_single_one_apply', blk4_apply_inr_inl, Matrix.neg_apply,
    neg_eq_zero] at h3
  rw [h3, Matrix.zero_apply]

theorem summable_height_rpow : ∀ (D : D7) (ρ : ℕ) (H : G D ρ → ℝ≥0), IsHt H → ∀ (w : G D ρ) (nb : hermA D ρ → G D ρ),
  mat w = blk4 0 1 (-1) 0 → (∀ z : hermA D ρ, mat (nb z) = blk4 1 z.1 0 1) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Summable (fun ζ : ratHerm D ρ => (H (w * nb ζ.1) : ℝ) ^ τ) := by
  intro D ρ H hH w nb hw hnb τ hτ
  have hτ0 : 0 ≤ τ := le_trans (Nat.cast_nonneg ρ) hτ.le
  set Φ : G D ρ → ℂ := fun g => (((H g : ℝ) ^ τ : ℝ) : ℂ) with hΦ
  set s₁ : ℂ := ((τ - (ρ : ℝ) / 2 : ℝ) : ℂ) with hs₁
  have hlaw : PositivityTheory.Rg.Rsw.IsLaw 1 s₁ Φ := by
    intro q hq a ha g
    have e1 := hH.2.2 q hq a ha g
    have e2 : s₁ + (ρ : ℂ) / 2 = (τ : ℂ) := by
      rw [hs₁]
      push_cast
      ring
    rw [e2]
    simp only [hΦ, e1, MonoidHom.one_apply, OneMemClass.coe_one, NNReal.coe_mul, GlobalTheory.Doubling.npow]
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), Complex.ofReal_mul,
      ← Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    simp
  have hcont : Continuous Φ := by
    have hH' : Continuous fun g => (H g : ℝ) := NNReal.continuous_coe.comp hH.1
    exact Complex.continuous_ofReal.comp (hH'.rpow_const fun _ => Or.inr hτ0)
  have hre : (ρ : ℝ) / 2 < s₁.re := by
    rw [hs₁, Complex.ofReal_re]
    linarith
  have hconv := GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law D ρ 1 s₁ Φ hcont hlaw hre 1
  have hHecke : Formalism.L2.Theta.IsHeckeChar D 1 :=
    ⟨by
      have h1 : (⇑(1 : (AE D)ˣ →* Circle)) = fun _ => 1 := funext fun _ => MonoidHom.one_apply _
      rw [h1]
      exact continuous_const, fun _ => MonoidHom.one_apply _⟩
  have hinv := GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw (1 : (AE D)ˣ →* Circle) s₁ Φ hHecke hlaw
  have hWr : mat w = GlobalTheory.MixModel.rat (blk4 (0 : Matrix (Fin ρ) (Fin ρ) D.host.E) 1 (-1) 0) := by
    rw [hw, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_neg',
      GlobalTheory.CompanionTheory.PcB.rat_one']
  have hwinv : mat w⁻¹ = blk4 0 (-1) 1 0 := by
    apply mat_inv_eq_of_mat_mul_eq_one
    rw [hw]
    exact weyl_mul_inv
  have hWr' : mat w⁻¹ = GlobalTheory.MixModel.rat (blk4 (0 : Matrix (Fin ρ) (Fin ρ) D.host.E) (-1) 1 0) := by
    rw [hwinv, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_neg', GlobalTheory.CompanionTheory.PcB.rat_one']
  have hwmem : w ∈ GF D ρ := GlobalTheory.CompanionTheory.PcB.mem_GF w _ _ hWr hWr'
  have hrat : ∀ ζ : ratHerm D ρ, ∃ Z : Matrix (Fin ρ) (Fin ρ) D.host.E,
      GlobalTheory.MixModel.rat Z = ((ζ.1 : hermA D ρ) : Mx D ρ ρ) := by
    intro ζ
    obtain ⟨Z, hZ⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_comap.mp ζ.2)
    exact ⟨Z, hZ⟩
  have hnbinv : ∀ ζ : ratHerm D ρ, mat (nb ζ.1)⁻¹ = blk4 1 (-((ζ.1 : hermA D ρ) : Mx D ρ ρ)) 0 1 := by
    intro ζ
    apply mat_inv_eq_of_mat_mul_eq_one
    rw [hnb, GlobalTheory.CompanionTheory.PcB.block_unipotent_mul, add_neg_cancel, block_matrix_one]
  have hnbmem : ∀ ζ : ratHerm D ρ, nb ζ.1 ∈ GF D ρ := by
    intro ζ
    obtain ⟨Z, hZ⟩ := hrat ζ
    refine GlobalTheory.CompanionTheory.PcB.mem_GF _ (blk4 1 Z 0 1) (blk4 1 (-Z) 0 1) ?_ ?_
    · rw [hnb, ← hZ, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_zero']
    · rw [hnbinv, ← hZ, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_zero',
        GlobalTheory.CompanionTheory.PcB.rat_neg']
  set x : ratHerm D ρ → GF D ρ := fun ζ => ⟨w * nb ζ.1, mul_mem hwmem (hnbmem ζ)⟩ with hx
  set ι : ratHerm D ρ → GlobalTheory.Eis.Cosets (P D ρ) (GF D ρ) :=
    fun ζ => Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ) with hι
  have hinj : Function.Injective ι := by
    intro ζ ζ' h
    have h0 : Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ) =
        Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ') := h
    have h1 : x ζ' * (x ζ)⁻¹ ∈ (P D ρ).subgroupOf (GF D ρ) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact h0)
    have h2 : (w * nb ζ'.1) * (w * nb ζ.1)⁻¹ ∈ P D ρ := Subgroup.mem_subgroupOf.mp h1
    have hm : mat ((w * nb ζ'.1) * (w * nb ζ.1)⁻¹) =
        blk4 1 0 (-(((ζ'.1 : hermA D ρ) : Mx D ρ ρ) + -((ζ.1 : hermA D ρ) : Mx D ρ ρ))) 1 := by
      rw [mul_inv_rev, mat_mul_block_decomposition, mat_mul_block_decomposition, mat_mul_block_decomposition, hw, hnb, hwinv, hnbinv ζ, ← mul_assoc,
        mul_assoc (blk4 0 1 (-1) 0), GlobalTheory.CompanionTheory.PcB.block_unipotent_mul]
      exact weyl_conj _
    have h3 := eq_zero_of_mem_P_of_mat_eq_blk4 _ h2 _ hm
    exact Subtype.ext (Subtype.ext (add_neg_eq_zero.mp h3).symm)
  have hterm : ∀ ζ : ratHerm D ρ,
      ‖GlobalTheory.Eis.term (P D ρ) (GF D ρ) Φ 1 (ι ζ)‖ = (H (w * nb ζ.1) : ℝ) ^ τ := by
    intro ζ
    have ho : Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (Quotient.out (ι ζ)) =
        Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ) := Quotient.out_eq (ι ζ)
    have hrel : x ζ * (Quotient.out (ι ζ))⁻¹ ∈ (P D ρ).subgroupOf (GF D ρ) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact ho)
    have hγ : Quotient.out (ι ζ) * (x ζ)⁻¹ ∈ (P D ρ).subgroupOf (GF D ρ) := by
      have h4 := inv_mem hrel
      rwa [mul_inv_rev, inv_inv] at h4
    have hγP : ((Quotient.out (ι ζ) * (x ζ)⁻¹ : GF D ρ) : G D ρ) ∈ P D ρ ⊓ GF D ρ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hγ, (Quotient.out (ι ζ) * (x ζ)⁻¹).2⟩
    have hsplit : ((Quotient.out (ι ζ) : GF D ρ) : G D ρ) * 1 =
        ((Quotient.out (ι ζ) * (x ζ)⁻¹ : GF D ρ) : G D ρ) * ((x ζ : GF D ρ) : G D ρ) := by
      rw [mul_one, ← Subgroup.coe_mul, inv_mul_cancel_right]
    show ‖Φ (((Quotient.out (ι ζ) : GF D ρ) : G D ρ) * 1)‖ = _
    rw [hsplit, hinv _ hγP]
    show ‖(((H (w * nb ζ.1) : ℝ) ^ τ : ℝ) : ℂ)‖ = (H (w * nb ζ.1) : ℝ) ^ τ
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
  have hsum : Summable (fun q => ‖GlobalTheory.Eis.term (P D ρ) (GF D ρ) Φ 1 q‖) := hconv
  exact (hsum.comp_injective hinj).congr hterm

end GlobalTheory.CompanionTheory.HermSum

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecomposition
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV.NodeApply

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem levi_eq_mul_cf (u u' : BlockIx (r + s) r → Ad E) (m m' : GA E r × GA E s) (k k' : Kinf E (r + s))
    (c c' : GL (Fin (r + s)) (Af E)) (hc : c ∈ KO E (r + s)) (hc' : c' ∈ KO E (r + s))
    (h : unip u * lev (Ad E) r s m * cf (r + s) k c = unip u' * lev (Ad E) r s m' * cf (r + s) k' c') :
    ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)),
      c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m' = (m.1 * cf r k₁ c₁, m.2 * cf s k₂ c₂) := by
  obtain ⟨v, hv⟩ := lev_mul_unip (m⁻¹) (-u + u')
  have hu : (unip u : GA E (r + s))⁻¹ = unip (-u) := by
    rw [inv_eq_iff_mul_eq_one, ← D.unip_add', add_neg_cancel, unip_zero]
  have key : unip v * lev (Ad E) r s (m⁻¹ * m') = cf (r + s) (k * k'⁻¹) (c * c'⁻¹) := by
    rw [← cf_mul, ← cf_inv, map_mul, ← mul_assoc, ← hv, D.unip_add', map_inv, ← hu]
    have h2 : unip u' * lev (Ad E) r s m' =
        unip u * lev (Ad E) r s m * cf (r + s) k c * (cf (r + s) k' c')⁻¹ := by
      rw [h]; group
    rw [mul_assoc (lev (Ad E) r s m)⁻¹, mul_assoc (unip u)⁻¹, h2]
    group
  obtain ⟨k₁, c₁, k₂, c₂, h₁, h₂, hm⟩ := GlobalTheory.T.levi_factor_of_unipotent_decomp v (m⁻¹ * m') _ _
    (mul_mem hc (inv_mem hc')) key
  refine ⟨k₁, c₁, k₂, c₂, h₁, h₂, ?_⟩
  calc m' = m * (m⁻¹ * m') := (mul_inv_cancel_left m m').symm
    _ = _ := by rw [hm]; rfl

theorem nodeFn_apply : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 := by
  intro E _ _ _ r s e₁ e₂ f₁ f₂ u m k c hc
  obtain ⟨k', c', hc', hx'⟩ :=
    (exists_iw (unip u * lev (Ad E) r s m * cf (r + s) k c)).choose_spec.choose_spec
  obtain ⟨k₁, c₁, k₂, c₂, h₁, h₂, hm⟩ := levi_eq_mul_cf u _ m _ k k' c c' hc hc' hx'
  have hl : leviOf (unip u * lev (Ad E) r s m * cf (r + s) k c) =
      (m.1 * cf r k₁ c₁, m.2 * cf s k₂ c₂) := hm
  rw [nodeFn, hl, f₁.rinv _ _ _ h₁, f₂.rinv _ _ _ h₂]

end GlobalTheory.CompanionTheory.LimV.NodeApply

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarActionFifthRealStatement
section
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_action_fifth_real : PositivityTheory.RgBcC.RealD.CapelliProductsScalar := by
  first | exact @GlobalTheory.CompanionTheory.CapScal.capScal | exact GlobalTheory.CompanionTheory.CapScal.capScal | (intros; apply GlobalTheory.CompanionTheory.CapScal.capScal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergentStatement
section
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_eisenstein_convergent : ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ →
    (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      φ (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) * φ g) →
    (n : ℝ) / 2 < s₁.re → ∀ g : G D n, CosetConv (P D n) (GF D n) φ g := by
  first | exact @GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law | exact GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law | (intros; apply GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSectionContinuousStatement
section
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_section_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω →
    ∀ (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f →
    ∀ (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)), IsCovolOne (ratL B A) ν 𝓖 →
    Continuous (swSection A B ν 𝓖 ω f) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous | exact GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous | (intros; apply GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_adelic_iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ ∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame | exact GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame <;> assumption)
end

