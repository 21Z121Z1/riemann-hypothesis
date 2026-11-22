import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0568
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0002
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AutomorphicArithmetic.DivisorFrames.Bundle0008
import Development.AutomorphicArithmetic.DivisorFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AutomorphicArithmetic.DivisorFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsScaledStandardPairSectionsOfMaxCompactTran
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private noncomputable def subst {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) :
    Matrix (Fin m) (Fin n) k ≃ₜ Matrix (Fin m) (Fin n) k where
  toFun X := g.val * X * h.val
  invFun X := (g⁻¹).val * X * (h⁻¹).val
  left_inv X := by
    show (g⁻¹).val * (g.val * X * h.val) * (h⁻¹).val = X
    rw [Matrix.mul_assoc g.val, ← Matrix.mul_assoc (g⁻¹).val, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  right_inv X := by
    show g.val * ((g⁻¹).val * X * (h⁻¹).val) * h.val = X
    rw [Matrix.mul_assoc (g⁻¹).val, ← Matrix.mul_assoc g.val, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

private theorem subst_SB {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) {f : Matrix (Fin m) (Fin n) k → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin n) k)) :
    (fun X => f (g.val * X * h.val)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin n) k) :=
  ⟨hf.1.comp_continuous (subst g h).continuous, hf.2.comp_homeomorph (subst g h)⟩

private theorem subst_ne {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) {f : Matrix (Fin m) (Fin n) k → ℂ}
    {Y : Matrix (Fin m) (Fin n) k} (hf : f Y ≠ 0) : ∃ X : Matrix (Fin m) (Fin n) k, f (g.val * X * h.val) ≠ 0 := by
  obtain ⟨X, rfl⟩ := (subst g h).surjective Y
  exact ⟨X, hf⟩

open GlobalTheory.StdPairCone in
private theorem stdA_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : ∃ X, stdA ν ϖ c a a' X ≠ 0 := by
  let X : Matrix (Fin a) (Fin (a + a')) k :=
    Matrix.of fun i => Fin.append ((1 : Matrix (Fin a) (Fin a) k) i) (fun _ => 0)
  have h1 : blk₁ X = 1 := by ext i j; simp [blk₁, X]
  have h2 : blk₂ X = 0 := by ext i j; simp [blk₂, X]
  refine ⟨X, ?_⟩
  have h : (blk₁ X).det ≠ 0 ∧ IsGLO (blk₁ X) ∧ ∀ i j, blk₂ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    rw [h1, h2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [GlobalTheory.SplitWeil.cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  rw [stdA, dif_pos h]
  exact Units.ne_zero _

open GlobalTheory.StdPairCone in
private theorem stdB_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : ∃ Y, stdB ν ϖ c a a' Y ≠ 0 := by
  let X : Matrix (Fin a') (Fin (a + a')) k :=
    Matrix.of fun i => Fin.append (fun _ => 0) ((1 : Matrix (Fin a') (Fin a') k) i)
  have h1 : blk₂ X = 1 := by ext i j; simp [blk₂, X]
  have h2 : blk₁ X = 0 := by ext i j; simp [blk₁, X]
  refine ⟨X, ?_⟩
  have h : (blk₂ X).det ≠ 0 ∧ IsGLO (blk₂ X) ∧ ∀ i j, blk₁ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    rw [h1, h2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [GlobalTheory.SplitWeil.cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  rw [stdB, dif_pos h]
  exact Units.ne_zero _

end SlopeTestRemainingChoices

theorem UpperTheory.exists_scaled_standardPairSections_of_maxCompact_translate :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
        (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c m a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → ν = α / β → 1 ≤ c → GlobalTheory.SplitFlip.CondLE ϖ c ν →
        GlobalTheory.SplitFlip.CondLE ϖ m α → GlobalTheory.SplitFlip.CondLE ϖ m β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
        ∀ (gA : GL (Fin a) k) (gB : GL (Fin a') k) (cc : GL (Fin (a + a')) k), gA ∈ GlobalTheory.SplitWeil.KO k (Fin a) →
        ∃ (lam : ℂ) (Ξ : Matrix (Fin a) (Fin (a + a')) k → ℂ) (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ), lam ≠ 0 ∧
          (∀ X, Ξ X = GlobalTheory.StdPairCone.stdA ν ϖ c a a' (gA.val * X * (cc⁻¹).valᵀ)) ∧
          (∀ Y, Ψ Y = lam * GlobalTheory.StdPairCone.stdB ν ϖ c a a' (gB.val * Y * cc.val)) ∧
          Ξ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) ∧ Ξ ≠ 0 ∧ Ψ ≠ 0 ∧
          GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β Ξ =
            GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) finSumFinEquiv ν α Ψ := by
  intro k _ _ _ _ _ _ α β ν ϖ c m a a' hϖ hν hc hcν hα hβ nα nβ gA gB cc hgA
  obtain ⟨hz, -⟩ := GlobalTheory.T.standardPair_localZetaMatch_ne_zero α β ν ϖ c m a a' hϖ hν hc hcν hα hβ nα nβ
  obtain ⟨hA, hB⟩ := GlobalTheory.T.standardPair_members_mem_schwartzBruhat ν ϖ c a a' hϖ hcν
  have hab : ν * β = α := by
    rw [hν]
    ext x
    simp
  obtain ⟨lam, hl, H⟩ := GlobalTheory.T.zetaIdentity_persists_row_column_changes k a a rfl (Fin a') (Fin a') (Fin (a + a')) (Fin (a + a')) (Equiv.refl _)
    (Equiv.refl _) finSumFinEquiv finSumFinEquiv (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a')))
    (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) ϖ ν β gA gB cc hgA
  rw [hab] at H
  have H' := H _ _ hz
  refine ⟨lam, fun X => GlobalTheory.StdPairCone.stdA ν ϖ c a a' (gA.val * X * (GlobalTheory.SplitFlip.invT cc).val),
    fun Y => lam * GlobalTheory.StdPairCone.stdB ν ϖ c a a' (gB.val * Y * cc.val), hl, fun _ => rfl, fun _ => rfl,
    subst_SB gA _ hA, (GlobalTheory.WeilM.SB _).smul_mem lam (subst_SB gB cc hB), ?_, ?_, H'⟩
  · obtain ⟨Y, hY⟩ := stdA_ne ν ϖ c a a'
    obtain ⟨X, hX⟩ := subst_ne gA (GlobalTheory.SplitFlip.invT cc) hY
    exact fun h => hX (congrFun h X)
  · obtain ⟨Y, hY⟩ := stdB_ne ν ϖ c a a'
    obtain ⟨X, hX⟩ := subst_ne gB cc hY
    exact fun h => mul_ne_zero hl hX (congrFun h X)
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsSplitBasisConjLatticeOfSelfDualFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_splitBasis_conj_lattice_of_selfDual_frame :
    ∀ (D : D7) (S : HSp D) (Λ L : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (β : GL (Fin S.rank) (EAf D)),
        IsSelfDualC S Λ → Formalism.L2.DIV.IsFrame β Λ → (∀ y, y ∈ L ↔ star y ∈ Λ) →
        ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.E →ₐ[D.host.F] Fv D.host.F v), ∃ b : GL (Fin S.rank) (Fv D.host.F v),
          IsSplitBasis t L b ∧ IsSplitBasis t L (-b) ∧ (b⁻¹).1 = (S.gram.map t * β.1.map (evW t))ᵀ := by
  intro D S Λ L β hΛ hβ hL v t
  obtain rfl : L = GlobalTheory.TripleSpaceW.conjSub Λ := by
    ext y
    rw [hL, GlobalTheory.TripleSpaceW.mem_conjSub]
  haveI := GlobalTheory.TripleSpaceW.conjSub_isLattice hΛ.1
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.AdelicU.exists_isSplitBasis t (GlobalTheory.TripleSpaceW.conjSub Λ) (GlobalTheory.AdelicU.isCMExt_host D)
  obtain ⟨g, hg, hgv⟩ := UpperTheory.exists_maxCompact_eq_frame_gram_splitBasis D S Λ β hΛ hβ v t b₀ hb₀
  rw [← (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne v S.rank).1] at hg
  have h1 : IsSplitBasis t (GlobalTheory.TripleSpaceW.conjSub Λ) (b₀ * g⁻¹) := by
    rw [hb₀.iff_mem_GLint, inv_mul_cancel_left]
    exact inv_mem hg
  refine ⟨b₀ * g⁻¹, h1, fun u => ?_, ?_⟩
  · have := h1 (-u)
    simp only [Pi.neg_apply, neg_mem_iff, Matrix.mulVec_neg] at this
    rw [Units.val_neg, Matrix.neg_mulVec, neg_mem_iff]
    exact this
  · rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hgv, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      Matrix.transpose_mul]
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsThOEqOfIsLatVacThetaFun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ptO_crd {D : D7} {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (hG : IsUnit G.det) (e : Fin k ≃ Fin d)
    (u : Matrix (Fin m) (Fin k) (AE D)) :
    ptO G e (HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G)) = u := by
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹ = (1 : Matrix (Fin m) (Fin m) (AE D)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hG, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold GlobalTheory.TripleRead.ptO
  rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  ext i j
  simp

private theorem ptO_two {D : D7} {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d)
    (x : Matrix (Fin d) (Fin m) (AE D)) : ptO G e (2 • x) = 2 • ptO G e x := by
  unfold GlobalTheory.TripleRead.ptO
  rw [two_nsmul, two_nsmul, Matrix.add_mul]
  rfl

private theorem isHalf_crd {D : D7} {m k d : ℕ} (H : Matrix (Fin m) (Fin m) (AE D)) (e : Fin k ≃ Fin d)
    (u : Matrix (Fin m) (Fin k) (AE D)) (a : AE D) (h : ∀ i j, a * u i j = u i j) :
    IsHalf a (HMul.hMul (uᵀ.submatrix e.symm id) H : Matrix (Fin d) (Fin m) (AE D)) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc]
  exact congrArg (· * H l j) (h l (e.symm i))

theorem UpperTheory.exists_thO_eq_of_isLatVac_thetaFun :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)),
        IsLat e Vs Ws ΛS ΛX →
        ∀ f₀ : WO (sgn ε S) X → ℂ, IsThetaFunO ψ (sgn ε S) X f₀ → IsLatVac (heisO ψ (sgn ε S) X) (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True) f₀ →
        ∃ g : SInf D.host.F (Fin S.rank × Fin d), f₀ = thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) := by
  intro D ψ ε S X d e Bs Vs Ws M hP ΛS ΛX hL f₀ hth hvac
  obtain ⟨-, hrho, -, -, hinj, hon⟩ := UpperTheory.thetaOperator_intertwines_heisenberg D ψ ε S X d e Bs Vs Ws M hP
  obtain ⟨hlat, -⟩ := UpperTheory.ptO_sgn_mem_latAtV_iff_mem_latO D ψ ε S X d e Bs Vs Ws M hP ΛS ΛX hL
  obtain ⟨Ψ, hΨ, rfl⟩ := (hon f₀).1 hth
  obtain ⟨r, s, hV⟩ := hP.herm
  obtain ⟨r', s', hW⟩ := hP.skew
  have hψ := hP.psi
  subst hψ
  have hG : IsUnit (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram).det :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn ε S)
  have hfix : ∀ y : WO (sgn ε S) X, heisO Bs.ψ (sgn ε S) X y (thO M Bs.ψ (sgn ε S).gram e Ψ) = thO M Bs.ψ (sgn ε S).gram e Ψ →
      M.co.rho Bs.ψ (ptO (sgn ε S).gram e y) Ψ = Ψ := fun y hy =>
    hinj _ (GlobalTheory.HeisSchA.rho_mem_schA M Bs.ψ hP.base.std _ Ψ hΨ) _ hΨ ((hrho Ψ y).trans hy)
  obtain ⟨g, hg⟩ := UpperTheory.exists_eq_pure_vacuum_of_lattice_invariant D.host.F D.host.E D.sp.cm.sig Bs S.rank d Vs Ws M r s r' s' hP.base hV hW hP.good Ψ hΨ
    (fun v γ hγ => by
      have h0 := ptO_crd (D := D) _ hG e γ
      have h1 := hlat v _ (h0.symm ▸ hγ)
      have h2 := hfix _ (hvac.1 _ h1)
      have h3 := (ptO_two (D := D) _ e _).trans (congrArg (2 • ·) h0)
      exact h3 ▸ h2)
    (fun v t γ hγ ht => by
      obtain ⟨a, ha, haz⟩ := UpperTheory.exists_splitIdempotent_mul_eq_of_piW_eq_zero D v t
      have h0 := ptO_crd (D := D) _ hG e γ
      have h1 := hlat v _ (h0.symm ▸ hγ)
      have hat := (GlobalTheory.LatVac.latAtV_at_stable Vs Ws v).1 γ hγ
      have h2 := hfix _ (hvac.2 a ha _ h1 (isHalf_crd _ e γ a fun i j =>
        haz _ (fun u hu => congrFun (congrFun (hat u hu) i) j) (congrFun (congrFun ht i) j)))
      exact h0 ▸ h2)
  exact ⟨g, by rw [← hg]⟩
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.MemIntAfAndInIdIffSplitComponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem toEAf_surj' (D : D7) (z : EAf D) : ∃ a : AE D, toEAf D a = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x a => exact ⟨(show AF D.host.F from ((0, a) : _ × _)) ⊗ₜ x, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

private theorem evW_eq_piF {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (z : EAf D) : GlobalTheory.BotMatch.evW τ z = piF τ z := by
  obtain ⟨a, rfl⟩ := toEAf_surj' D z
  rw [GlobalTheory.BotMatch.evW_toEAf, piF_toEAf]

private theorem cpt_eq_one {D : D7} {e : AE D} {S : Finset (HeightOneSpectrum (𝓞 D.host.E))} (h : IsIdemSum e S)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ S) : GlobalTheory.StdFrames.cpt w (toEAf D e) = 1 := by
  obtain ⟨⟨es, h1, rfl⟩, -⟩ := h
  rw [map_sum, map_sum, Finset.sum_eq_single w (fun Q hQ hne => (GlobalTheory.StdFrames.cpt_of_isIdemAt (h1 Q hQ)).2 w hne.symm)
    (fun hn => absurd hw hn)]
  exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (h1 w hw)).1

private theorem conjPrime_notMem {D : D7} {e : AE D} {S : Finset (HeightOneSpectrum (𝓞 D.host.E))} (h : IsIdemSum e S)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ S) : GlobalTheory.IdemSupport.cP w ∉ S := by
  intro hc
  have h1 := cpt_eq_one h hw
  have h2 := cpt_eq_one h hc
  have h3 := congrArg (fun x => GlobalTheory.StdFrames.cpt w (toEAf D x)) h.2
  simp only [map_mul, map_zero, h1, one_mul, GlobalTheory.StdFrames.toEAf_cA] at h3
  have h4 := GlobalTheory.StdFrames.cpt_sg_eq_zero (Q := w) (z := toEAf D e - 1) (by rw [map_sub, h2, map_one, sub_self])
  rw [map_sub, map_sub, map_one, map_one, h3, zero_sub, neg_eq_zero] at h4
  exact one_ne_zero h4

theorem UpperTheory.mem_intAf_and_inId_iff_splitComponents :
    ∀ (D : D7) (e₀ : AE D) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e₀ S →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) → (∀ v : P, splitPrime (t v) ∈ S) →
        ∀ (c : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (z : EAf D), toEAf D e₀ * z = z →
        (z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ v : P, piF (t v) z ∈ (ValuativeRel.valuation (Fv D.host.F v)).integer) ∧
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ S, w.asIdeal ^ c w) z ↔
          ∀ v : P, piF (t v) z ∈ GlobalTheory.SplitWeil.cball (unifAt v.1 ^ c (splitPrime (t v)))) := by
  intro D e₀ S hS P t hP ht c z hz
  have h1 : ∀ w, w ∈ S ↔ ∃ i : P, splitPrime (t i) = w := by
    intro w
    refine ⟨fun hw => ?_, fun ⟨i, hi⟩ => hi ▸ ht i⟩
    let i : P := ⟨w.under (𝓞 D.host.F), (hP _).2 ⟨w, hw, rfl⟩⟩
    refine ⟨i, ?_⟩
    have hu : (splitPrime (t i)).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := GlobalTheory.AdelicU.splitPrime_under (t i)
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP hu with h | h
    · exact h
    · exact absurd (h ▸ ht i) (conjPrime_notMem hS hw)
  have h2 : Function.Injective (fun i : P => splitPrime (t i)) := fun i j hij =>
    Subtype.ext ((GlobalTheory.AdelicU.splitPrime_under (t i)).symm.trans
      ((congrArg (fun w : HeightOneSpectrum (𝓞 D.host.E) => w.under (𝓞 D.host.F)) hij).trans
        (GlobalTheory.AdelicU.splitPrime_under (t j))))
  have h := UpperTheory.mem_intAdeles_and_ideal_iff_splitEmbeddings D e₀ S hS P (fun v => v.1) t h1 h2 c z hz
  simp only [evW_eq_piF] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.StdSectionFirstEqProdLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem det_mem' {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem S _) (prod_mem fun i _ => h _ _)

open Classical in
private theorem botFst_loc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (c a a' d : ℕ) (hr : a + a' = d) (M : Matrix (Fin d) (Fin a) k) :
    GlobalTheory.StdPairCone.stdA ν ϖ c a a' ((Mᵀ).submatrix id (finCongr hr)) =
      if (∀ i j, M i j ∈ (ValuativeRel.valuation k).integer) ∧ ∀ i j, a ≤ i.1 → M i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
        GlobalTheory.StdPairCone.unitInd ν (topL a M).det else 0 := by
  subst hr
  have hb : GlobalTheory.StdPairCone.blk₁ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a'))) = (topL a M)ᵀ := by
    ext i j
    have : j.1 < a + a' ∧ i.1 < a := ⟨by omega, i.2⟩
    simp only [GlobalTheory.StdPairCone.blk₁, topL, Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, dif_pos this]
    rfl
  have hb2 : ∀ i j, GlobalTheory.StdPairCone.blk₂ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a'))) i j = M (Fin.natAdd a j) i :=
    fun i j => rfl
  have hb1 : ∀ i j, GlobalTheory.StdPairCone.blk₁ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a'))) i j = M (Fin.castAdd a' j) i :=
    fun i j => rfl
  have hd : (GlobalTheory.StdPairCone.blk₁ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a')))).det = (topL a M).det := by
    rw [hb, Matrix.det_transpose]
  have hsub : ∀ x, x ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) → x ∈ (ValuativeRel.valuation k).integer := by
    intro x hx
    have h1 : ValuativeRel.valuation k x ≤ ValuativeRel.valuation k ((ϖ ^ c : kˣ) : k) := hx
    have h2 : ((ϖ ^ c : kˣ) : k) ∈ (ValuativeRel.valuation k).integer := by
      rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem c
    exact (Valuation.mem_integer_iff _ _).2 (le_trans h1 ((Valuation.mem_integer_iff _ _).1 h2))
  unfold GlobalTheory.StdPairCone.stdA GlobalTheory.StdPairCone.unitInd GlobalTheory.StdPairCone.IsGLO
  simp only [hb1, hb2]
  by_cases h : (∀ i j, M i j ∈ (ValuativeRel.valuation k).integer) ∧ ∀ i j, a ≤ i.1 → M i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · rw [if_pos h]
    by_cases h' : (topL a M).det ≠ 0 ∧ ValuativeRel.valuation k (topL a M).det = 1
    · rw [dif_pos h', dif_pos ⟨hd ▸ h'.1, ⟨fun i j => h.1 _ _, hd ▸ h'.2⟩, fun i j => h.2 _ _ (by simp)⟩]
      simp only [hd]
    · rw [dif_neg h', dif_neg]
      rintro ⟨h1, ⟨-, h2⟩, -⟩
      exact h' ⟨hd ▸ h1, hd ▸ h2⟩
  · rw [if_neg h, dif_neg]
    rintro ⟨-, ⟨h1, -⟩, h2⟩
    refine h ⟨fun i j => ?_, fun i j => ?_⟩
    · induction i using Fin.addCases with
      | left i => exact h1 j i
      | right i => exact hsub _ (h2 j i)
    · induction i using Fin.addCases with
      | left i => intro hi; exact absurd i.2 (not_lt.2 hi)
      | right i => exact fun _ => h2 j i

theorem UpperTheory.stdSectionFirst_eq_prod_local :
    ∀ (D : D7) (ε : AE D) (Pw : Finset (Pl D.host.E)), IsIdemSum ε Pw → ∀ (ι : Type) [Fintype ι] (pl : ι → Pl D.host.F)
        (τ : ∀ i, D.host.E →ₐ[D.host.F] Fv D.host.F (pl i)), (∀ w, w ∈ Pw ↔ ∃ i, splitPrime (τ i) = w) →
        Function.Injective (fun i => splitPrime (τ i)) → ∀ (c : Pl D.host.E → ℕ) (ν : (AE D)ˣ →* Circle) (A WW : HSp D) (βA : GL (Fin A.rank) (Lev.EAf D))
          (βW : GL (Fin WW.rank) (Lev.EAf D)) (a' : ℕ) (hk : A.rank + a' = WW.rank) (x : WO A WW), IsHalf ε x →
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν ε (∏ w ∈ Pw, w.asIdeal ^ c w) A WW βA βW x =
            ∏ i, GlobalTheory.StdPairCone.stdA (chrW ν (τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i)) (c (splitPrime (τ i))) A.rank a'
              ((((frMapO A WW βA βW x).map (GlobalTheory.BotMatch.evW (τ i)))ᵀ).submatrix id (finCongr hk)) := by
  intro D ε Pw hε ι _ pl τ hP hinj c ν A WW βA βW a' hk x hx
  classical
  have hϖ : ∀ i, GlobalTheory.SplitFlip.IsUnif (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i)) := fun i =>
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F (pl i))).choose_spec
  simp only [botFst_loc _ _ (hϖ _)]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  have hN : ∀ i j, toEAf D ε * frMapO A WW βA βW x i j = frMapO A WW βA βW x i j := by
    have h1 : toEAf D ε • Matrix.map x (toEAf D) = Matrix.map x (toEAf D) := by
      ext i j
      show toEAf D ε * toEAf D (x i j) = toEAf D (x i j)
      rw [← map_mul, hx i j]
    have h2 : toEAf D ε • frMapO A WW βA βW x = frMapO A WW βA βW x := by
      unfold frMapO
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, h1]
    exact fun i j => congrFun (congrFun h2 i) j
  generalize frMapO A WW βA βW x = N at hN
  have hI := fun i j => UpperTheory.mem_intAdeles_and_ideal_iff_splitEmbeddings D ε Pw hε ι pl τ hP hinj c (N i j) (hN i j)
  have htop : ∀ v, GlobalTheory.BotMatch.evW (τ v) (topL A.rank N).det = (topL A.rank (N.map (GlobalTheory.BotMatch.evW (τ v)))).det := fun v => by
    rw [RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp only [topL, RingHom.mapMatrix_apply, Matrix.map_apply]
    split_ifs
    · rfl
    · exact map_zero _
  by_cases h : IsIntM N ∧ ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) (N i j)
  · rw [if_pos ⟨hx, h⟩, UpperTheory.unitChar_idempotentSum_eq_prod_unitInd D ε Pw hε ι pl τ hP hinj ν _ (topL A.rank N)]
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [if_pos ⟨fun i j => (hI i j).1.1 (h.1 i j) v, fun i j hi => (hI i j).2.1 (h.2 i j hi) v⟩, htop]
    · intro v
      rw [htop]
      refine det_mem' _ _ fun i j => ?_
      simp only [topL]
      split_ifs
      · exact (hI _ _).1.1 (h.1 _ _) v
      · exact zero_mem _
  · rw [if_neg fun h' => h h'.2]
    by_contra hne
    have hv := fun v : ι => Finset.prod_ne_zero_iff.1 (Ne.symm hne) v (Finset.mem_univ v)
    have hv' := fun v : ι => (ite_ne_right_iff.1 (hv v)).1
    exact h ⟨fun i j => (hI i j).1.2 fun v => (hv' v).1 i j, fun i j hi => (hI i j).2.2 fun v => (hv' v).2 i j hi⟩
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.UnitCharIdempotentSumEqProdOverSplitPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cpt_sum {D : D7} {e : AE D} {S : Finset (HeightOneSpectrum (𝓞 D.host.E))} (he : IsIdemSum e S)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ S) : GlobalTheory.StdFrames.cpt (D := D) w (toEAf D e) = 1 := by
  obtain ⟨⟨es, h, rfl⟩, -⟩ := he
  rw [map_sum (toEAf D), map_sum (GlobalTheory.StdFrames.cpt (D := D) w),
    Finset.sum_eq_single_of_mem w hw fun Q hQ hne => (GlobalTheory.StdFrames.cpt_of_isIdemAt (h Q hQ)).2 w hne.symm]
  exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (h w hw)).1

private theorem no_conj {D : D7} {e : AE D} {S : Finset (HeightOneSpectrum (𝓞 D.host.E))} (he : IsIdemSum e S)
    {w w' : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ S) (hw' : w' ∈ S)
    (h : w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F)) : w = w' := by
  rcases GlobalTheory.IdemSupport.eq_or_eq_cP h with h1 | h1
  · exact h1
  · exfalso
    have h0 : toEAf D e * GlobalTheory.StdFrames.sg D (toEAf D e) = 0 := by
      rw [← GlobalTheory.StdFrames.toEAf_cA, ← RingHom.map_mul, he.2, RingHom.map_zero]
    have h2 : GlobalTheory.StdFrames.cpt (D := D) (GlobalTheory.IdemSupport.cP w') (1 - toEAf D e) = 0 := by
      rw [← h1, RingHom.map_sub, RingHom.map_one, cpt_sum he hw, sub_self]
    have h3 := GlobalTheory.StdFrames.cpt_sg_eq_zero h2
    have h4 := congrArg (GlobalTheory.StdFrames.cpt (D := D) w') h0
    rw [RingHom.map_mul, RingHom.map_zero, cpt_sum he hw', one_mul] at h4
    rw [RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, h4, sub_zero] at h3
    exact one_ne_zero h3

private theorem evW_eq {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (z : EAf D) : GlobalTheory.BotMatch.evW τ z = piF τ z := by
  obtain ⟨y, rfl⟩ := (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).surjective z
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨a, ha⟩ := e.surjective (0, y)
  have h2 : finPart D a = y := by
    have : (e a).2 = finPart D a := (he a).2
    rw [← this, ha]
  rw [← h2]
  exact (GlobalTheory.BotMatch.evW_toEAf τ a).trans (piF_toEAf τ a).symm

theorem UpperTheory.unitChar_idempotentSum_eq_prod_over_splitPlaces :
    ∀ (D : D7) (e₀ : AE D) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e₀ S →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) → (∀ v : P, splitPrime (t v) ∈ S) →
        ∀ (ν : (AE D)ˣ →* Circle) (k : ℕ) (N : Matrix (Fin k) (Fin k) (EAf D)), IsIntM N →
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e₀ N = ∏ v : P, GlobalTheory.StdPairCone.unitInd (chrW ν (t v)) (N.map (piF (t v))).det := by
  intro D e₀ S he P t hP hS ν k N hN
  have hdet : N.det ∈ GlobalTheory.StdFrames.OA D := by
    rw [Matrix.det_apply']
    exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hN _ _)
  have key := UpperTheory.unitChar_idempotentSum_eq_prod_unitInd D e₀ S he P (fun v => v.1) t (fun w => ⟨fun hw => ?_, ?_⟩) ?_ ν k N ?_
  · rw [key]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [evW_eq, RingHom.map_det]
    rfl
  · refine ⟨⟨_, (hP _).2 ⟨w, hw, rfl⟩⟩, no_conj he (hS _) hw ?_⟩
    exact GlobalTheory.AdelicU.splitPrime_under _
  · rintro ⟨v, rfl⟩
    exact hS v
  · intro v v' h
    have h1 := congrArg (fun w : HeightOneSpectrum (𝓞 D.host.E) => w.under (𝓞 D.host.F)) h
    simp only [GlobalTheory.AdelicU.splitPrime_under] at h1
    exact Subtype.ext h1
  · intro v
    have h1 := (GlobalTheory.StdFrames.mem_OA_iff _).1 hdet (splitPrime (t v))
    rw [← GlobalTheory.BotMatch.complEquiv_evW, HeightOneSpectrum.mem_adicCompletionIntegers,
      GlobalTheory.LFun.SplitTie.complEquiv_apply, GlobalTheory.LFun.SplitTie.valued_complMap] at h1
    haveI : (Valued.v : Valuation (v.1.adicCompletion D.host.F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one.2 h1
end

