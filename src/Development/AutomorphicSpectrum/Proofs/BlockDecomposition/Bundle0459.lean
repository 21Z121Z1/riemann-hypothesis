import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0033
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0440
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeNoSecondWeights
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantUnipotentActionTrivial
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem qC_sigX_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : HPG k (i + 1) (t + 1)) (h1 : (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1)) (h2 : (pgProj k (i + 1) (t + 1) u).2 = 1) (w : τ.V ⊗[ℂ] σ.V), qC τ σ (sigX τ σ u w) = qC τ σ w := by
  intro k _ _ _ _ i t τ σ u h1 h2 w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    have hd : ((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (pgProj k (i + 1) (t + 1) u).1 : ℂˣ) : ℂ) = 1 := by
      have := GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_unip (k := k) (i + 1) (((t + 1 : ℕ) : ℝ) / 2) ⟨_, h1⟩
      simpa using congrArg Units.val this
    have ha : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) u).1 a = τ.ρ (pgProj k (i + 1) (t + 1) u).1 a := by
      refine (twist_apply τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) _ a).trans ?_
      rw [hd, one_smul]
    have hρ : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) u).2 = 1 := by
      rw [h2, map_one]
    have hb : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) u).2 b = b :=
      LinearMap.congr_fun hρ b
    have e : sigX τ σ u (a ⊗ₜ[ℂ] b) = (τ.ρ (pgProj k (i + 1) (t + 1) u).1 a) ⊗ₜ[ℂ] b :=
      (extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
        (pgProj k (i + 1) (t + 1) u) a b).trans (congrArg₂ (fun x y => TensorProduct.tmul ℂ x y) ha hb)
    have hq : (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ (τ.ρ (pgProj k (i + 1) (t + 1) u).1 a) =
        (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ a := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      unfold twKer
      apply Submodule.subset_span
      exact ⟨⟨_, h1⟩, a, by simp⟩
    rw [e]
    exact congrArg (fun x => TensorProduct.tmul ℂ x b) hq

end GlobalTheory.CompanionTheory.BZPhiPG
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantUnipotentCharacterTrivial
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem qO_extTensor_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : MirUin k (i + 1)) (hu : mirChar k ψ i u = 1) (v : τ.V ⊗[ℂ] σ.V),
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ ((u : Mir k (i + 1)), 1) v) = qO τ σ ψ v := by
  intro k _ _ _ _ i t ψ τ σ u hu v
  let L : (τ.V ⊗[ℂ] σ.V) →ₗ[ℂ] (τ.V ⊗[ℂ] σ.V) :=
    extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ ((u : Mir k (i + 1)), 1)
  have hd : ((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (u : Mir k (i + 1)) : ℂˣ) : ℂ) = 1 := by
    have := GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_unip (k := k) (i + 1) (((t + 1 : ℕ) : ℝ) / 2) u
    simpa using congrArg Units.val this
  have ha : ∀ a : τ.V, (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (u : Mir k (i + 1)) a = τ.ρ (u : Mir k (i + 1)) a := by
    intro a
    refine (twist_apply τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) _ a).trans ?_
    rw [hd, one_smul]
  have hρ : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ 1 = 1 := map_one _
  have hb : ∀ b : σ.V, (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ 1 b = b := fun b => LinearMap.congr_fun hρ b
  have e : ∀ (a : τ.V) (b : σ.V), L (a ⊗ₜ[ℂ] b) = (τ.ρ (u : Mir k (i + 1)) a) ⊗ₜ[ℂ] b := fun a b =>
    (extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
      ((u : Mir k (i + 1)), 1) a b).trans (congrArg₂ (fun x y => TensorProduct.tmul ℂ x y) (ha a) (hb b))
  have hq : ∀ a : τ.V, (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ (τ.ρ (u : Mir k (i + 1)) a) =
      (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ a := by
    intro a
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    unfold twKer
    apply Submodule.subset_span
    exact ⟨u, a, by simp [hu]⟩
  have key : ∀ w : τ.V ⊗[ℂ] σ.V, qO τ σ ψ (L w) = qO τ σ ψ w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      rw [e]
      exact congrArg (fun x => TensorProduct.tmul ℂ x b) (hq a)
  exact key v

end GlobalTheory.CompanionTheory.BZPhiPG
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComapUNAndMapSM
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.LeviInt

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_entries_int {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (h1 : ∀ i j, (m.1.val i j) ∈ Ov E w) (h2 : ∀ i j, (m.2.val i j) ∈ Ov E w)
    (hX : ∀ i j, X i j ∈ Ov E w) (i j : Fin n) :
    ((blk h w m X : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j ∈ Ov E w := by
  rw [CtLevel.blk_val]
  obtain ⟨i', rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j', rfl⟩ := (CtLevel.blkEq h).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simpa using h1 i' j'
  · simp only [fromBlocks_apply₁₂, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (h1 _ _) (hX _ _)
  · simp
  · simpa using h2 i' j'

theorem blk_corner {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (i : Fin a) (j : Fin b) :
    ((blk h w 1 X : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
      (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j)) = X i j := by
  rw [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simp

theorem comap_uN_and_map_sM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E), ((GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) = intMat a b w ∧ ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)).map (GlobalTheory.LeviFubini.sM h w) ≤ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviFubini.parB h w) := by
  intro E _ _ _ a b n h w
  have hinv : ∀ X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      ((GlobalTheory.LeviFubini.uN h w X : GlobalTheory.LeviFubini.parB h w) : GLw n w)⁻¹ =
        blk h w 1 (Multiplicative.toAdd X⁻¹) := fun X => by
    rw [← GlobalTheory.LeviFubini.uN_val, map_inv, Subgroup.coe_inv]
  have hint : ∀ k : ℕ, ∀ i j : Fin k, ((1 : GLw k w).val i j) ∈ Ov E w := fun k i j => by
    rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  refine ⟨le_antisymm (fun X hX => ?_) ?_, ?_⟩
  · rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, GlobalTheory.LeviFubini.uN_val] at hX
    refine Subgroup.subset_closure fun i j => ?_
    have h1 := (GlobalTheory.AdelicU.mem_GLint_iff.1 hX).1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j))
    rw [blk_corner] at h1
    exact h1
  · refine (Subgroup.closure_le _).2 fun X hX => ?_
    have hX' : ∀ i j, Multiplicative.toAdd X i j ∈ Ov E w := hX
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [GlobalTheory.LeviFubini.uN_val]
      exact blk_entries_int h w 1 _ (hint a) (hint b) hX' i j
    · rw [hinv]
      refine blk_entries_int h w 1 _ (hint a) (hint b) (fun i j => ?_) i j
      simpa using Subring.neg_mem _ (hX' i j)
  · rintro _ ⟨m, ⟨h1, h2⟩, rfl⟩
    obtain ⟨h11, h12⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 h1
    obtain ⟨h21, h22⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 h2
    rw [Subgroup.mem_subgroupOf]
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [GlobalTheory.LeviFubini.sM_val]
      exact blk_entries_int h w m 0 h11 h21 (fun _ _ => Subring.zero_mem _) i j
    · rw [← Subgroup.coe_inv, ← map_inv, GlobalTheory.LeviFubini.sM_val]
      exact blk_entries_int h w m⁻¹ 0 h12 h22 (fun _ _ => Subring.zero_mem _) i j

end GlobalTheory.CompanionTheory.LeviInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicIntegralDenominator
section
open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.AdeleDen

private theorem natCast_mul_mem_intAd {F : Type} [Field F] [NumberField F] (m : ℕ)
    {a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F} (ha : a ∈ PI.AdCpctDenWork.intAd F) :
    (m : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) * a ∈ PI.AdCpctDenWork.intAd F := by
  rw [PI.AdCpctDenWork.mem_intAd] at ha ⊢
  intro v
  rw [PI.AdCpctDenWork.natCast_mul_apply]
  exact mul_mem (PI.AdCpctDenWork.natCast_mem_int v m) (ha v)

theorem exists_common_denominator :
    ∀ (E : Type) [Field E] [NumberField E] (Q : Set (Af E)), IsCompact Q →
    ∃ D : ℕ, D ≠ 0 ∧ ∀ x : E, algebraMap E (Af E) x ∈ Q → ∃ r : 𝓞 E, (r : E) = D * x := by
  intro E _ _ Q hQ
  let U : ℕ → Set (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) := fun N =>
    {a | ((N.factorial : ℕ) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) * a ∈ PI.AdCpctDenWork.intAd E}
  have hUo : ∀ N, IsOpen (U N) := fun N =>
    (continuous_const.mul continuous_id).isOpen_preimage _ PI.AdCpctDenWork.isOpen_intAd
  have hUc : Q ⊆ ⋃ N, U N := by
    intro a _
    obtain ⟨m, hm, hma⟩ := PI.AdCpctDenWork.exists_nat_adele a
    refine Set.mem_iUnion.2 ⟨m, ?_⟩
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hm le_rfl
    show ((m.factorial : ℕ) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) * a ∈ PI.AdCpctDenWork.intAd E
    rw [hk, Nat.cast_mul, mul_comm (m : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E), mul_assoc]
    exact natCast_mul_mem_intAd k hma
  have hUd : Directed (· ⊆ ·) U := by
    refine Monotone.directed_le ?_
    intro N M hNM a ha
    obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hNM
    show ((M.factorial : ℕ) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) * a ∈ PI.AdCpctDenWork.intAd E
    rw [hk, Nat.cast_mul, mul_comm ((N.factorial : ℕ) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E), mul_assoc]
    exact natCast_mul_mem_intAd k ha
  obtain ⟨N, hN⟩ := hQ.elim_directed_cover U hUo hUc hUd
  refine ⟨N.factorial, Nat.factorial_ne_zero N, fun x hx => ?_⟩
  have hmem := hN hx
  have hint : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      IsDedekindDomain.HeightOneSpectrum.valuation E v ((N.factorial : E) * x) ≤ 1 := by
    intro v
    have h1 : algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) ((N.factorial : E) * x) ∈
        PI.AdCpctDenWork.intAd E := by
      rw [map_mul, map_natCast]
      exact hmem
    have h2 := (PI.AdCpctDenWork.mem_intAd _).1 h1 v
    rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2
    exact h2
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one E _ hint
  exact ⟨r, by rw [NumberField.RingOfIntegers.coe_eq_algebraMap, hr]⟩

end GlobalTheory.CompanionTheory.AdeleDen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactArchimedeanEntriesBounded
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem archMat_entries_bounded_of_isCompact (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (GAd σ J))
    (hC : IsCompact C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ C, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
      ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ B := by
  classical
  have hb : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
      ∃ b : ℝ, ∀ g ∈ C, ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ b := by
    intro w τ i j
    have hc : Continuous fun g : GAd σ J => ‖archMat σ J τ (projArch σ J w g) i j‖ :=
      (((GlobalTheory.Orb.continuous_archMat σ J τ).comp (continuous_projArch σ J w)).matrix_elem i j).norm
    obtain ⟨b, hb⟩ := hC.bddAbove_image hc.continuousOn
    exact ⟨b, fun g hg => hb ⟨g, hg, rfl⟩⟩
  choose b hb using hb
  haveI : Fintype (InfinitePlace F) := inferInstance
  refine ⟨∑ w : InfinitePlace F, ∑ τ : EmbOver E w, ∑ i : Fin n, ∑ j : Fin n, |b w τ i j|,
    Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg _, fun g hg w τ i j => ?_⟩
  calc ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ b w τ i j := hb w τ i j g hg
    _ ≤ |b w τ i j| := le_abs_self _
    _ ≤ ∑ j : Fin n, |b w τ i j| :=
        Finset.single_le_sum (f := fun j => |b w τ i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, |b w τ i j| :=
        Finset.single_le_sum (f := fun i => ∑ j : Fin n, |b w τ i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ τ : EmbOver E w, ∑ i : Fin n, ∑ j : Fin n, |b w τ i j| :=
        Finset.single_le_sum (f := fun τ => ∑ i : Fin n, ∑ j : Fin n, |b w τ i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ τ)
    _ ≤ ∑ w : InfinitePlace F, ∑ τ : EmbOver E w, ∑ i : Fin n, ∑ j : Fin n, |b w τ i j| :=
        Finset.single_le_sum (f := fun w => ∑ τ : EmbOver E w, ∑ i : Fin n, ∑ j : Fin n, |b w τ i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ w)

end GlobalTheory.CompanionTheory.CFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFiniteRationalDenominator
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * x) :=
  _root_.UpperTheory.Reformulated.B.DYha3.main x

theorem exists_nat_mul_isIntegral_of_isCompact (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {𝒦 : Set (Af F ⊗[F] E)} (h𝒦 : IsCompact 𝒦) :
    ∃ d : ℕ, 0 < d ∧ ∀ e : E, inclR (F := F) (Af F) e ∈ 𝒦 → IsIntegral ℤ ((d : E) * e) := by
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let bb := Algebra.TensorProduct.basis (Af F) b
  have hc : ∀ i, Continuous (fun x : Af F ⊗[F] E => bb.coord i x) := fun i =>
    IsModuleTopology.continuous_of_linearMap (bb.coord i)
  have hcoord : ∀ (e : E) i, bb.coord i (inclR (F := F) (Af F) e) = algebraMap F (Af F) (b.repr e i) := by
    intro e i
    change bb.repr ((1 : Af F) ⊗ₜ[F] e) i = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp [Algebra.algebraMap_eq_smul_one]
  choose m hm hmi using fun i =>
    GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_integral_of_isCompact F (h𝒦.image (hc i))
  choose D hD hDi using fun i => exists_nat_mul_isIntegral (b i)
  refine ⟨(∏ i, m i) * ∏ i, D i, Nat.mul_pos (Finset.prod_pos fun i _ => hm i)
    (Finset.prod_pos fun i _ => hD i), fun e he => ?_⟩
  have hsum : ((((∏ i, m i) * ∏ i, D i : ℕ)) : E) * e =
      ∑ i, algebraMap F E (((∏ i, m i : ℕ) : F) * b.repr e i) * (((∏ i, D i : ℕ)) : E) * b i := by
    conv_lhs => rw [← b.sum_repr e]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [hsum]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  obtain ⟨z, hz⟩ := hmi i (b.repr e i) ⟨_, he, hcoord e i⟩
  have h1 : IsIntegral ℤ (algebraMap F E (((∏ i, m i : ℕ) : F) * b.repr e i)) := by
    have : ((∏ i, m i : ℕ) : F) * b.repr e i = (q : F) * (z : F) := by
      rw [hq, hz, Nat.cast_mul]
      ring
    rw [this]
    exact IsIntegral.algebraMap ((isIntegral_natCast q).mul z.2)
  have h2 : (((∏ i, D i : ℕ)) : E) * b i = (r : E) * ((D i : E) * b i) := by
    rw [hr, Nat.cast_mul]
    ring
  rw [mul_assoc, h2]
  exact h1.mul ((isIntegral_natCast r).mul (hDi i))

end GlobalTheory.CompanionTheory.CFin

namespace GlobalTheory.CompanionTheory.CFin

theorem bounded_denominators : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (𝒞 : Set (GFin σ J)), IsCompact 𝒞 → ∀ {ι : Type} [Fintype ι] (A : Matrix ι (Fin n) E) (B : Matrix (Fin n) ι E), ∃ d : ℕ, 0 < d ∧ ∀ δ : GRat σ J, projFin σ J (ratEmb σ J δ) ∈ 𝒞 → ∀ u v, IsIntegral ℤ ((d : E) * (A * δ.1.1 * B) u v) := by
  intro F E _ _ _ _ _ σ n J 𝒞 h𝒞 ι _ A B
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  let f : ι → ι → GFin σ J → Af F ⊗[F] E := fun u v y =>
    (A.map (inclR (F := F) (Af F)) * (matHom (Af F) σ J y).1 * B.map (inclR (F := F) (Af F))) u v
  have hmat : Continuous fun y : GFin σ J => ((matHom (Af F) σ J y).1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    Units.continuous_val.comp (GlobalTheory.AdelicU.isEmbedding_matHom (Af F) σ J).continuous
  have hf : ∀ u v, Continuous (f u v) := fun u v => by
    have : Continuous fun y : GFin σ J =>
        A.map (inclR (F := F) (Af F)) * (matHom (Af F) σ J y).1 * B.map (inclR (F := F) (Af F)) :=
      (continuous_const.matrix_mul hmat).matrix_mul continuous_const
    exact this.matrix_elem u v
  obtain ⟨d, hd, h⟩ := exists_nat_mul_isIntegral_of_isCompact F E
    (𝒦 := ⋃ u, ⋃ v, f u v '' 𝒞)
    (isCompact_iUnion fun u => isCompact_iUnion fun v => h𝒞.image (hf u v))
  refine ⟨d, hd, fun δ hδ u v => h _ ?_⟩
  refine Set.mem_iUnion.2 ⟨u, Set.mem_iUnion.2 ⟨v, _, hδ, ?_⟩⟩
  have hval : ((matHom (Af F) σ J (GlobalTheory.AdelicU.projFin σ J (ratEmb σ J δ))).1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) =
      δ.1.1.map (inclR (F := F) (Af F)) := by
    refine Matrix.ext fun r s => ?_
    change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] (δ.1.1 r s)) =
      (1 : Af F) ⊗ₜ[F] (δ.1.1 r s)
    simp
  change (A.map (inclR (F := F) (Af F)) * (matHom (Af F) σ J (GlobalTheory.AdelicU.projFin σ J (ratEmb σ J δ))).1 *
    B.map (inclR (F := F) (Af F))) u v = _
  rw [hval, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]

end GlobalTheory.CompanionTheory.CFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionCongrEquivStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactInduction_congr_equiv : ∀ {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (H : Subgroup G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'),
    σ.Equiv σ' → Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  first | exact @GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd | exact GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd | (intros; apply GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistEquivStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactInduction_twist_equiv : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (χ : G →* ℂˣ), IsOpen (χ.ker : Set G) →
    Nonempty ((twist (cInd H σ) χ).Equiv (cInd H (twist σ (χ.comp H.subtype)))) := by
  first | exact @GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv | exact GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv | (intros; apply GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeIntegralZeroVarsLtTop
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelCone

theorem cone_integral_zero_vars_lt_top :
    ∀ (F : Type) [Field F] [NumberField F] (n d : ℕ) (c : ℝ),
      ∫⁻ t in GlobalTheory.SiegelSet.cone 0 c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n d c
  have h : ∀ t : Fin 0 → ℝ, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) = 1 := by
    intro t
    simp [GlobalTheory.SiegelSet.modulus]
  simp_rw [h]
  rw [setLIntegral_const, one_mul]
  exact measure_lt_top _ _

end GlobalTheory.CompanionTheory.SiegelCone
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeNoSecondWeightsStatement
section
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_no_second_weights : PositivityTheory.RgBcC.RealD.ConeWeightsNotSecondType := by
  first | exact @GlobalTheory.CompanionTheory.ConeSecondWeights.cone_weight_not_in_second | exact GlobalTheory.CompanionTheory.ConeSecondWeights.cone_weight_not_in_second | (intros; apply GlobalTheory.CompanionTheory.ConeSecondWeights.cone_weight_not_in_second <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupsBasisNhds
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem exists_entry_nhds {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] (m : ℕ)
    {t : Set (Matrix (Fin m) (Fin m) k)} (ht : t ∈ 𝓝 (1 : Matrix (Fin m) (Fin m) k)) :
    ∃ U ∈ 𝓝 (0 : k), ∀ A : Matrix (Fin m) (Fin m) k,
      (∀ a b, A a b - (1 : Matrix (Fin m) (Fin m) k) a b ∈ U) → A ∈ t := by
  have hc : Continuous fun B : Matrix (Fin m) (Fin m) k => 1 + B := continuous_const.add continuous_id
  have hs : (fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t ∈ 𝓝 (0 : Matrix (Fin m) (Fin m) k) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using ht
  have e : 𝓝 (0 : Fin m → Fin m → k) = Filter.pi fun a => 𝓝 ((0 : Fin m → Fin m → k) a) := nhds_pi
  have hs' : ((fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t : Set (Fin m → Fin m → k)) ∈
      Filter.pi fun a => 𝓝 ((0 : Fin m → Fin m → k) a) := by
    rw [← e]
    exact hs
  obtain ⟨I, -, t₁, ht₁, hsub⟩ := Filter.mem_pi.1 hs'
  have h2 : ∀ a, ∃ t₂ : Fin m → Set k, (∀ b, t₂ b ∈ 𝓝 (0 : k)) ∧ Set.univ.pi t₂ ⊆ t₁ a := by
    intro a
    have e' : 𝓝 (0 : Fin m → k) = Filter.pi fun b => 𝓝 ((0 : Fin m → k) b) := nhds_pi
    have h : t₁ a ∈ Filter.pi fun b => 𝓝 ((0 : Fin m → k) b) := by
      rw [← e']
      exact ht₁ a
    obtain ⟨J, -, t₂, ht₂, hJ⟩ := Filter.mem_pi.1 h
    exact ⟨t₂, ht₂, fun x hx => hJ fun b _ => hx b (Set.mem_univ b)⟩
  choose t₂ ht₂ hsub₂ using h2
  refine ⟨⋂ a, ⋂ b, t₂ a b, Filter.iInter_mem.2 fun a => Filter.iInter_mem.2 fun b => ht₂ a b,
    fun A hA => ?_⟩
  have hmem : A - 1 ∈ (fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t :=
    hsub fun a _ => hsub₂ a fun b _ => Set.mem_iInter.1 (Set.mem_iInter.1 (hA a b) a) b
  simpa using hmem

theorem congM_subset_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (O : Set (Mir k n)) (hO : O ∈ 𝓝 (1 : Mir k n)) :
    ∃ s₀ : kˣ, ∀ (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1),
      ValuativeRel.valuation k (s : k) ≤ ValuativeRel.valuation k (s₀ : k) →
        (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) ⊆ O := by
  obtain ⟨u, hu, huO⟩ :=
    (mem_nhds_subtype ((GlobalTheory.BZMir.Mir k n : Set (GL (Fin (n + 1)) k))) 1 O).1 hO
  have hu1 : u ∈ 𝓝 (1 : GL (Fin (n + 1)) k) := by simpa using hu
  rw [Units.isEmbedding_embedProduct.toIsInducing.nhds_eq_comap, Filter.mem_comap] at hu1
  obtain ⟨w, hw, hwu⟩ := hu1
  rw [Units.embedProduct_apply, nhds_prod_eq, Filter.mem_prod_iff] at hw
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := hw
  have ht₁' : t₁ ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by simpa using ht₁
  have ht₂' : MulOpposite.op ⁻¹' t₂ ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    have h := MulOpposite.continuous_op.continuousAt.preimage_mem_nhds ht₂
    simpa using h
  obtain ⟨U₁, hU₁, h₁⟩ := GlobalTheory.CompanionTheory.BZPhiPG.Onto.exists_entry_nhds (n + 1) ht₁'
  obtain ⟨U₂, hU₂, h₂⟩ := GlobalTheory.CompanionTheory.BZPhiPG.Onto.exists_entry_nhds (n + 1) ht₂'
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.SplitWeil.exists_cball_subset (Filter.inter_mem hU₁ hU₂)
  refine ⟨s₀, fun s hs hss₀ g hg => ?_⟩
  have hball : ∀ x : k, x ∈ GlobalTheory.SplitWeil.cball s → x ∈ GlobalTheory.SplitWeil.cball s₀ := by
    intro x hx
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx ⊢
    exact le_trans hx hss₀
  refine huO (hwu (hsub (Set.mem_prod.2 ⟨?_, ?_⟩)))
  · have hg' : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      hg.1
    show ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ t₁
    exact h₁ _ fun a b => (hs₀ (hball _ (hg' a b))).1
  · have hg' : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s
        (((g : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      hg.2
    show MulOpposite.op (((g : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ t₂
    exact h₂ _ fun a b => (hs₀ (hball _ (hg' a b))).2

end GlobalTheory.CompanionTheory.BZPhiPG.Onto
end

