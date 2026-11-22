import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0814
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0821
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0831
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0835
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0776
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0773
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0784
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0830
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0832
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0823
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0810
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0811
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0827
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0833
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0101
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFormulaOfTotalMassOne

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralVanishingOpenSubgroup
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibInvK

theorem fibV_mul_right_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ b' ∈ K₁, ∀ g : GL (Fin (i + t)) k, fibV b (g * b') = fibV b g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ c K₁ hK z b hval hzero b' hb' g
  have hβ : GlobalTheory.BZMir.levi k (i + t) b' ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK := by
    show ∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt (i + t) c, ∃ a ∈ K₁,
      GlobalTheory.BZMir.levi k (i + t) b' = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y * GlobalTheory.BZMir.levi k (i + t) a
    exact ⟨0, zero_mem _, b', hb', by rw [GlobalTheory.CompanionTheory.BZPsiPG.uM_zero, one_mul]⟩
  have key : ∀ p : GlobalTheory.BZMir.Mir k (i + t), ∀ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
      b.1.1.1 (p * β) = b.1.1.1 p := by
    intro p β hβ
    by_cases hp : ∃ h : GlobalTheory.BZMir.Leib.HPG k i t,
        ∃ β₀ ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : GlobalTheory.BZMir.Mir k (i + t)) * β₀
    · obtain ⟨h, β₀, hβ₀, rfl⟩ := hp
      rw [mul_assoc, hval h (β₀ * β) (Subgroup.mul_mem _ hβ₀ hβ), hval h β₀ hβ₀]
    · have hp' : ¬ ∃ h : GlobalTheory.BZMir.Leib.HPG k i t,
          ∃ β₀ ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
            p * β = (h : GlobalTheory.BZMir.Mir k (i + t)) * β₀ := by
        rintro ⟨h, β₀, hβ₀, he⟩
        refine hp ⟨h, β₀ * β⁻¹, Subgroup.mul_mem _ hβ₀ (Subgroup.inv_mem _ hβ), ?_⟩
        rw [← mul_assoc, ← he, mul_inv_cancel_right]
      rw [hzero _ hp', hzero _ hp]
  funext v
  unfold GlobalTheory.CompanionTheory.BZPsiPG.fibV
  rw [map_mul, ← mul_assoc]
  exact key _ _ hβ

end GlobalTheory.CompanionTheory.BZPsiPG.FibInvK

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralVanishingSubgroup
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

theorem fibV_one_bump : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → fibV b 1 = (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)).indicator (fun _ => z) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ c K₁ hK z b h1 h2
  funext v
  by_cases hv : v ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c
  · rw [Set.indicator_of_mem (show v ∈ (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)) from hv)]
    have hm : midV k i t v ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt (i + t) c := by
      intro j
      induction j using Fin.addCases with
      | left j =>
        show Fin.append (0 : Fin i → k) v (Fin.castAdd t j) ∈ _
        rw [Fin.append_left]
        exact (zero_mem (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt i c)) j
      | right j =>
        show Fin.append (0 : Fin i → k) v (Fin.natAdd i j) ∈ _
        rw [Fin.append_right]
        exact hv j
    have hp : uM k (i + t) (midV k i t v) * levi k (i + t) 1 ∈
        GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK := ⟨_, hm, 1, one_mem _, rfl⟩
    have e := h1 1 _ hp
    rw [map_one] at e
    simpa [fibV] using e
  · rw [Set.indicator_of_notMem (show v ∉ (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)) from hv)]
    apply h2
    rintro ⟨h, β, hβ, e⟩
    obtain ⟨x, q, hq⟩ := GlobalTheory.T.parabolic_unipotent_levi_decomp k i t h
    obtain ⟨y, hy, b', hb', rfl⟩ := hβ
    rw [hq, uM_levi_mul_uM_levi] at e
    obtain ⟨e1, e2⟩ := uM_levi_inj _ (show uM k (i + t) (midV k i t v) * levi k (i + t) 1 = _ from e)
    have hq' : (q : GL (Fin (i + t)) k) = b'⁻¹ := eq_inv_of_mul_eq_one_left e2.symm
    apply hv
    intro j
    have e3 := congrFun e1 (Fin.natAdd i j)
    have e4 : midV k i t v (Fin.natAdd i j) = v j := Fin.append_right _ _ _
    have e5 : topV k i t x (Fin.natAdd i j) = 0 := Fin.append_right _ _ _
    rw [Pi.add_apply, e4, e5, zero_add, hq'] at e3
    rw [e3]
    exact mulVec_mem_latt (hK (inv_mem hb')) hy _

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreSubgroupOpenCompact
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

open GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

variable {k : Type} [Field k]

theorem colv_uM_mul_levi (n : ℕ) (y : Fin n → k) (b : GL (Fin n) k) :
    GlobalTheory.CompanionTheory.MirLevi.colv (uM k n y * levi k n b) = y := by
  have hu : ((GlobalTheory.CompanionTheory.BZPsiPG.uM k n y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k n y := by
    first
    | rfl
    | (ext a c; simp [GlobalTheory.CompanionTheory.BZPsiPG.uM, GlobalTheory.BZMir.unip])
  have hL : ((GlobalTheory.BZMir.levi k n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      GlobalTheory.BZMir.glEmbMat k n (b : Matrix (Fin n) (Fin n) k) := rfl
  funext i
  simp only [GlobalTheory.CompanionTheory.MirLevi.colv, Subgroup.coe_mul, Units.val_mul, hu, hL]
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem eq_uM_colv_mul_levi (n : ℕ) (p : Mir k n) :
    p = uM k n (GlobalTheory.CompanionTheory.MirLevi.colv p) * levi k n (mirabolicProjection k n p) := by
  have h1 : GlobalTheory.BZMir.mirabolicProjection k n
      (p * (GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n p))⁻¹) = 1 := by
    rw [map_mul, map_inv, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_levi_eq, mul_inv_cancel]
  obtain ⟨y, hy⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_uM_of_mem k n
    (GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k n _ h1)
  have hp : p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y *
      GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n p) := by
    rw [← hy, inv_mul_cancel_right]
  have hy' : GlobalTheory.CompanionTheory.MirLevi.colv p = y := by
    rw [hp]
    exact GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.colv_uM_mul_levi n y _
  rw [hy']
  exact hp

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colv (n : ℕ) : Continuous (GlobalTheory.CompanionTheory.MirLevi.colv : Mir k n → Fin n → k) := by
  show Continuous fun p : GlobalTheory.BZMir.Mir k n => fun i : Fin n =>
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)
  first
  | exact continuous_pi fun i =>
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem (Fin.castSucc i) (Fin.last n)
  | exact continuous_pi fun i => (continuous_apply (Fin.last n)).comp
      ((continuous_apply (Fin.castSucc i)).comp (Units.continuous_val.comp continuous_subtype_val))
  | fun_prop

theorem coe_Bgrp_eq (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) :
    (Bgrp n c K₁ h : Set (Mir k n)) =
      GlobalTheory.CompanionTheory.MirLevi.colv ⁻¹' (latt n c : Set (Fin n → k)) ∩ mirabolicProjection k n ⁻¹' (K₁ : Set (GL (Fin n) k)) := by
  ext p
  change (∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c, ∃ b ∈ K₁,
      p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * GlobalTheory.BZMir.levi k n b) ↔
    (GlobalTheory.CompanionTheory.MirLevi.colv p ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c ∧ GlobalTheory.BZMir.mirabolicProjection k n p ∈ K₁)
  constructor
  · rintro ⟨y, hy, b, hb, rfl⟩
    refine ⟨?_, ?_⟩
    · rwa [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.colv_uM_mul_levi]
    · rwa [map_mul, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_uM, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_levi_eq, one_mul]
  · rintro ⟨hy, hb⟩
    exact ⟨_, hy, _, hb, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.eq_uM_colv_mul_levi n p⟩

theorem coe_Bgrp_eq_image (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) :
    (Bgrp n c K₁ h : Set (Mir k n)) =
      (fun q : (Fin n → k) × GL (Fin n) k => uM k n q.1 * levi k n q.2) ''
        ((latt n c : Set (Fin n → k)) ×ˢ (K₁ : Set (GL (Fin n) k))) := by
  ext p
  change (∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c, ∃ b ∈ K₁,
      p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * GlobalTheory.BZMir.levi k n b) ↔ _
  constructor
  · rintro ⟨y, hy, b, hb, rfl⟩
    exact ⟨(y, b), ⟨hy, hb⟩, rfl⟩
  · rintro ⟨⟨y, b⟩, ⟨hy, hb⟩, rfl⟩
    exact ⟨y, hy, b, hb, rfl⟩

theorem isOpen_isCompact_Bgrp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k))
    (h : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) →
    IsOpen (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) ∧
      IsCompact (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) := by
  intro k _ _ _ _ n c K₁ h hK
  have hc := GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj k n
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.coe_Bgrp_eq]
    exact ((GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_latt n c).preimage (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.continuous_colv n)).inter
      (hK.preimage hc.2.2)
  · rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.coe_Bgrp_eq_image]
    have hK₁ : IsCompact (K₁ : Set (GL (Fin n) k)) :=
      (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).of_isClosed_subset
        (K₁.isClosed_of_isOpen hK) (SetLike.coe_subset_coe.mpr h)
    exact ((GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isCompact_latt n c).prod hK₁).image
      ((hc.2.1.comp continuous_fst).mul (hc.1.comp continuous_snd))

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceCutoffContinuousCompactSupport
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi.Test

theorem psiA_isTest : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) →
    ∀ v : HeightOneSpectrum (𝓞 F), Continuous (psiA S g a v) ∧ HasCompactSupport (psiA S g a v) := by
  intro F _ _ S g a hg v
  have hu : (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v = 1 := by
    have h : ((a : AF F) * ((a⁻¹ : (AF F)ˣ) : AF F)).2 v = (1 : AF F).2 v := by rw [a.mul_inv]
    exact h
  have ha : (a : AF F).2 v ≠ 0 := left_ne_zero_of_mul_eq_one hu
  let e : (Unit → Fv F v) ≃ₜ Fv F v :=
    (Homeomorph.funUnique Unit (Fv F v)).trans (Homeomorph.mulLeft₀ ((a : AF F).2 v) ha)
  have he : ∀ y, e y = (a : AF F).2 v * y () := fun y => rfl
  have hO : IsClopen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isClopen_integer _
  have hOc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have key : ∀ h : Fv F v → ℝ, Continuous h → HasCompactSupport h →
      Continuous (h ∘ e) ∧ HasCompactSupport (h ∘ e) := fun h h1 h2 =>
    ⟨h1.comp e.continuous, h2.comp_isClosedEmbedding e.isClosedEmbedding⟩
  by_cases hv : v ∈ S
  · have hfun : psiA S g a v = g v ∘ e := by
      funext y
      simp [psiA, hv, he]
    rw [hfun]
    exact key _ (hg v hv).1 (hg v hv).2
  · have hfun : psiA S g a v =
        (Set.indicator (v.adicCompletionIntegers F : Set (Fv F v)) (fun _ => (1 : ℝ))) ∘ e := by
      funext y
      simp [psiA, hv, he, Set.indicator_apply]
    rw [hfun]
    refine key _ (hO.continuous_indicator continuous_const) ?_
    exact HasCompactSupport.intro hOc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.CompanionTheory.BasePsi.Test

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiTermsSummable
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.Domination

theorem summable_tsum_le_of_shift {ι : Type*} [AddCommGroup ι] {F c : ι → ℝ} (ζ : ι) (hF : ∀ i, 0 ≤ F i)
    (h : ∀ i, F (i + ζ) ≤ c i) (hc : Summable c) : Summable F ∧ ∑' i, F i ≤ ∑' i, c i := by
  have hs : Summable (F ∘ Equiv.addRight ζ) := Summable.of_nonneg_of_le (fun _ => hF _) h hc
  refine ⟨(Equiv.addRight ζ).summable_iff.1 hs, ?_⟩
  rw [← (Equiv.addRight ζ).tsum_eq F]
  exact hs.tsum_le_tsum h hc

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem rt_add_add (η ζ : Matrix (Fin ρ) (Fin p) D.host.E) (y : Mx D ρ p) :
    GlobalTheory.CompanionTheory.FJE.rt (η + ζ) + y = GlobalTheory.CompanionTheory.FJE.rt η + (GlobalTheory.CompanionTheory.FJE.rt ζ + y) := by
  have : GlobalTheory.CompanionTheory.FJE.rt (η + ζ) = GlobalTheory.CompanionTheory.FJE.rt η + GlobalTheory.CompanionTheory.FJE.rt ζ := by
    ext i j
    exact map_add (incA D) _ _
  rw [this, add_assoc]

theorem norm_Wz_shift (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ) (hf : IsLaw χ s f) (g : G D n) (e : G D p)
    (η ζ₂ : Matrix (Fin ρ) (Fin p) D.host.E) (y' x₀ y₀ : Mx D ρ p) (z' : hermA D ρ)
    (hz : M.emb e * (M.nzx 0 x₀ * M.sh y₀) = M.nzx z' (GlobalTheory.CompanionTheory.FJE.rt ζ₂) * M.sh y' * M.emb e) :
    ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y') * M.emb e * g)‖ =
      ‖Wz M m ψ b₀ f (M.sh (η.map (incA D)) * M.emb e * (M.nzx 0 x₀ * (M.sh y₀ * g)))‖ := by
  have e1 : M.sh (η.map (incA D)) * M.emb e * (M.nzx 0 x₀ * (M.sh y₀ * g)) =
      M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * (M.nzx z' (GlobalTheory.CompanionTheory.FJE.rt ζ₂) * (M.sh y' * M.emb e * g)) := by
    calc _ = M.sh (η.map (incA D)) * (M.emb e * (M.nzx 0 x₀ * M.sh y₀)) * g := by
          simp only [mul_assoc]
      _ = _ := by
          rw [hz]
          simp only [mul_assoc]
  have e2 : M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y') * M.emb e * g =
      M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * (M.sh y' * M.emb e * g) := by
    rw [← GlobalTheory.CompanionTheory.FJE.sh_add]
    simp only [mul_assoc]
  have hv : ‖GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (GlobalTheory.CompanionTheory.FJE.rt ζ₂) (GlobalTheory.CompanionTheory.FJE.rt η)‖ = 1 := hψ.2.1 _
  rw [e1, e2, GlobalTheory.T.coefficient_heisenberg_equivariance M m ψ hψ b₀ χ s f hf, norm_mul, norm_mul,
    (GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts ψ hψ b₀).2.1, hv, one_mul, one_mul]

theorem apply_add_symm {A : Type*} [TopologicalSpace A] [AddCommGroup A] (T : (A × A) ≃ₜ+ (A × A)) {a₁ a₂ b₁ b₂ y : A}
    (h : T (a₁, a₂) = (b₁, b₂)) : T (a₁ + (T.symm (y, 0)).1, a₂ + (T.symm (y, 0)).2) = (b₁ + y, b₂) := by
  have e : (a₁ + (T.symm (y, 0)).1, a₂ + (T.symm (y, 0)).2) = (a₁, a₂) + T.symm (y, 0) := rfl
  rw [e, map_add, h, T.apply_symm_apply]
  simp

set_option maxHeartbeats 1000000 in

theorem domination : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ)
    (f : G D n → ℂ), IsLaw χ s f → ∀ g : G D n,
    (∀ C : Set (G D n), IsCompact C →
      ∃ c : GlobalTheory.Eis.Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → ℝ, Summable c ∧
        ∀ g ∈ C, ∀ u, ‖Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)‖ ≤ c u) →
    ∃ t : GlobalTheory.Eis.Cosets (P D p) (GF D p) → ℝ, Summable t ∧
      ∀ (q : GlobalTheory.Eis.Cosets (P D p) (GF D p)) (y : Mx D ρ p),
        Summable (fun η : Matrix (Fin ρ) (Fin p) D.host.E =>
          ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y) * M.emb (q.out : GF D p) * g)‖) ∧
        ∑' η : Matrix (Fin ρ) (Fin p) D.host.E,
          ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y) * M.emb (q.out : GF D p) * g)‖ ≤ t q := by
  intro D n ρ p hn M m ψ hψ b₀ χ s f hf g hdom
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D ρ p
  have hΦ : Continuous fun v : Mx D ρ p × Mx D ρ p => M.nzx 0 v.2 * (M.sh v.1 * g) := by
    have h1 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.nzx 0 v.2 :=
      M.nzx_cont.comp (continuous_const.prodMk continuous_snd)
    have h2 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.sh v.1 := M.sh_cont.comp continuous_fst
    exact h1.mul (h2.mul continuous_const)
  obtain ⟨c, hc, hb⟩ := hdom _ ((hK.prod hK).image hΦ)
  refine ⟨fun q => ∑' η, c (q, η), hc.prod, fun q y => ?_⟩
  obtain ⟨T, hT1, -, hT3⟩ := GlobalTheory.T.lattice_translation_preserved M ((q.out : GF D p) : G D p) (q.out : GF D p).2
  obtain ⟨a₁, ha₁, hy⟩ := hKc (T.symm (y, 0)).1
  obtain ⟨a₂, ha₂, hx⟩ := hKc (T.symm (y, 0)).2
  obtain ⟨ξ₁, rfl⟩ : ∃ ξ, GlobalTheory.CompanionTheory.FJE.rt ξ = a₁ := ha₁
  obtain ⟨ξ₂, rfl⟩ : ∃ ξ, GlobalTheory.CompanionTheory.FJE.rt ξ = a₂ := ha₂
  obtain ⟨ζ₁, ζ₂, hζ⟩ := hT1 ξ₁ ξ₂
  have hTv := apply_add_symm (y := y) T hζ
  obtain ⟨z', hz'⟩ := hT3 (GlobalTheory.CompanionTheory.FJE.rt ξ₁ + (T.symm (y, 0)).1) (GlobalTheory.CompanionTheory.FJE.rt ξ₂ + (T.symm (y, 0)).2)
  rw [hTv] at hz'
  refine summable_tsum_le_of_shift ζ₁ (fun _ => norm_nonneg _) (fun η => ?_) (hc.prod_factor q)
  rw [rt_add_add, norm_Wz_shift M m ψ hψ b₀ χ s f hf g _ η ζ₂ _ _ _ z' hz']
  exact hb _ ⟨(_, _), ⟨hy, hx⟩, rfl⟩ (q, η)

end GlobalTheory.CompanionTheory.FJE.Domination
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainUnfoldingTwoSumsStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_unfolding_two_sums : ∀ {A X Y U : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A)
    (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] [Countable U] (c : X → Y) (y0 : Y)
    (F : X → A → ℂ) (F0 : U → A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam)
    (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1)
    (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1)
    (Um : X → ℝ) (_ : Summable Um) (τ : Λ → X ≃ X)
    (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q)
    (_ : ∀ b, ∃ l : Λ, ∀ q, ‖F q b‖ ≤ Um (τ l q))
    (e : Λ × U → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e)
    (_ : ∀ (l l' : Λ) u, τ l' (e (l, u)) = e (l' + l, u))
    (_ : ∀ (l : Λ) u b, F (e (l, u)) b = F0 u ((l : A) + b))
    (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b),
    (∀ u, Integrable (F0 u) lam ∧ ∫ b, ‖F0 u b‖ ∂lam ≤ ∑' l : Λ, Um (e (l, u))) ∧
    HasSum (fun u => ∫ b, F0 u b * ch b ∂lam) (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldFam.unfold_fam | exact GlobalTheory.CompanionTheory.UnfoldFam.unfold_fam | (intros; apply GlobalTheory.CompanionTheory.UnfoldFam.unfold_fam <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCentreRationalFormStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_centre_rational_form : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn),
    (∀ a b, M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0) ∧ (∀ z y, M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0) ∧
    (∀ z h, M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0) ∧
    ∀ l : ratHerm D ρ, M.nzx l.1 0 ∈ GF D n ∧ ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.centre_nzx | exact GlobalTheory.CompanionTheory.ZUnf.centre_nzx | (intros; apply GlobalTheory.CompanionTheory.ZUnf.centre_nzx <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianExistencePrincipleStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_existence_principle : HEx := by
  first | exact @GlobalTheory.CompanionTheory.RgBase.hEx | exact GlobalTheory.CompanionTheory.RgBase.hEx | (intros; apply GlobalTheory.CompanionTheory.RgBase.hEx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticePreservedCofinitelyByUnit
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat

theorem eventually_cV_mul_mem_latV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (y : (AF F ⊗[F] E)ˣ), ∀ᶠ v in cofinite, ∀ Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E, (fun a i => cV v (y : AF F ⊗[F] E) * Y a i) ∈ latV b v ↔ Y ∈ latV b v := by
  intro F E _ _ _ _ _ σ _ d b y
  have e1 := GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b
    (projFin (fun _ _ : Fin 1 => (y : AF F ⊗[F] E)))
  have e2 := GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b
    (projFin (fun _ _ : Fin 1 => ((y⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)))
  filter_upwards [e1, e2, GlobalTheory.CompanionTheory.SW.LatFix.eventually_mul_closed b] with v h1 h2 h3 Y
  have c1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      (cV v (y : AF F ⊗[F] E)) k ∈ v.adicCompletionIntegers F := fun k => h1 0 0 k
  have c2 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      (cV v ((y⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) k ∈ v.adicCompletionIntegers F :=
    fun k => h2 0 0 k
  have hone : cV v ((y⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * cV v (y : AF F ⊗[F] E) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  constructor
  · intro hY a i k
    have h := h3 _ _ c2 (hY a i) k
    rwa [← mul_assoc, hone, one_mul] at h
  · intro hY a i k
    exact h3 _ _ c1 (hY a i) k

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFormulaOfTotalMassOneStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_formula_of_total_mass_one : PositivityTheory.SiegelWeilFormula.Densx.MassOne → Prop1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.Rank.mass_formula_of_total_mass_one | exact GlobalTheory.CompanionTheory.Mass.Rank.mass_formula_of_total_mass_one | (intros; apply GlobalTheory.CompanionTheory.Mass.Rank.mass_formula_of_total_mass_one <;> assumption)
end

