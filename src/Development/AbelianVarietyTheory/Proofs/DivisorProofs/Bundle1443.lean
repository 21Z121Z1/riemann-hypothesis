import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixSchwartzMajorantInvMulLe
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MajMul

theorem maj_mul_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) ≤ C * GlobalTheory.Unf.maj θ K' N x := by
  intro D θ hθ V n Q hQ K hK
  obtain ⟨K', hK', hbox⟩ := GlobalTheory.T.exists_compactBox_of_unitaryTranslate_compact D V n Q hQ K hK
  obtain ⟨C₀, hC₀, hreal⟩ := GlobalTheory.T.adelicMatrixRealSize_le_const_mul_of_compact_translate D θ hθ V n Q hQ
  refine ⟨K', hK', fun N => ⟨C₀ ^ N, by positivity, fun y hy x => ?_⟩⟩
  set z : Mx D V.rank n := HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x with hz
  unfold GlobalTheory.Unf.maj
  by_cases hin : GlobalTheory.Unf.InBox K z
  · rw [if_pos hin, if_pos (hbox y hy x hin)]
    have h0 := GlobalTheory.Unf.realSize_nonneg θ z
    have h1 := GlobalTheory.Unf.realSize_nonneg θ x
    have h2 := hreal y hy x
    have h3 : 1 + GlobalTheory.Unf.realSize θ x ≤ C₀ * (1 + GlobalTheory.Unf.realSize θ z) := by nlinarith
    have hp : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ x) ^ N := by positivity
    have hq : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ z) ^ N := by positivity
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq hp, one_mul]
    calc (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ (C₀ * (1 + GlobalTheory.Unf.realSize θ z)) ^ N := by gcongr
      _ = C₀ ^ N * (1 + GlobalTheory.Unf.realSize θ z) ^ N := by rw [mul_pow]
  · rw [if_neg hin]
    have := GlobalTheory.Unf.maj_nonneg θ K' N x
    unfold GlobalTheory.Unf.maj at this
    have hC : (0:ℝ) ≤ C₀ ^ N := by positivity
    exact mul_nonneg hC this

end GlobalTheory.MajMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScale
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace GlobalTheory.LatScaleSum

open mixedEmbedding

theorem evI_algebraMap (F : Type) [Field F] [NumberField F] (x : F) :
    evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  unfold evI
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

noncomputable abbrev latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Submodule ℤ (κ → mixedSpace F) :=
  Submodule.span ℤ (Set.range (Pi.basis (fun _ : κ => latticeBasis F)))

theorem mem_latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (y : κ → F)
    (hy : ∀ i, IsIntegral ℤ (y i)) : (fun i => mixedEmbedding F (y i)) ∈ latPi F κ := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro ji
  rw [Pi.basis_repr]
  have h1 : mixedEmbedding F (y ji.1) ∈ mixedEmbedding.integerLattice F := by
    exact ⟨⟨y ji.1, hy ji.1⟩, rfl⟩
  have h2 := (mem_span_latticeBasis F).mpr h1
  exact (Module.Basis.mem_span_iff_repr_mem ℤ _ _).mp h2 ji.2

theorem summable_inv_one_add_pow (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Summable fun z : latPi F κ =>
      ((1 + ‖(z : κ → mixedSpace F)‖) ^ (Module.finrank ℤ (latPi F κ) + 1))⁻¹ := by
  set N : ℕ := Module.finrank ℤ (latPi F κ) + 1 with hN
  have h0 := ZLattice.summable_norm_rpow (latPi F κ) (-(N : ℝ)) (by rw [hN]; push_cast; linarith)
  have h1 : Summable fun z : latPi F κ => (if z = 0 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro z hz
    have : z ≠ 0 := by simpa using hz
    simp [this]
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_) (h0.add h1)
  have hr : 0 ≤ ‖z‖ ^ (-(N : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hz : z = 0
  · subst hz
    simp
  · simp only [hz, if_false, add_zero]
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    have : ‖z‖ = ‖(z : κ → mixedSpace F)‖ := rfl
    rw [← this]
    gcongr
    linarith

end GlobalTheory.LatScaleSum

namespace GlobalTheory.LatScaleSum

open mixedEmbedding

theorem thetaSum_norm_le_pow :
    ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k := by
  intro F _ _ κ _
  set L := latPi F κ with hL
  set N₀ : ℕ := Module.finrank ℤ L + 1 with hN
  set H : (κ → mixedSpace F) → ℝ := fun v => ((1 + ‖v‖) ^ N₀)⁻¹ with hH
  have hHs : Summable fun z : L => H z := summable_inv_one_add_pow F κ
  refine ⟨N₀, N₀, ∑' z : L, H z, ?_⟩
  intro A m Ψ hm hb hint
  set f : (κ → F) → ℂ := fun ξ => Ψ (fun i => algebraMap F (AF F) (ξ i)) with hf
  set ψ : (κ → F) → (κ → mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i) with hψdef
  have hψ : ∀ ξ : κ → F, (fun i => evI F (algebraMap F (AF F) (ξ i))) = ψ ξ :=
    fun ξ => funext fun i => evI_algebraMap F (ξ i)
  set g : (κ → F) → (κ → mixedSpace F) := fun ξ => ψ (fun i => (m : F) * ξ i) with hgdef
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  have hginj : Function.Injective g := by
    intro ξ η h
    funext i
    have := congrFun h i
    simp only [hgdef, hψdef] at this
    exact mul_left_cancel₀ hm0 (mixedEmbedding_injective F this)
  have hgsmul : ∀ ξ, g ξ = m • ψ ξ := by
    intro ξ
    funext i
    simp only [hgdef, hψdef, Pi.smul_apply]
    rw [← nsmul_eq_mul, map_nsmul]
  set Lind : (κ → mixedSpace F) → ℝ := (L : Set (κ → mixedSpace F)).indicator H with hLind
  have hLs : Summable Lind := summable_subtype_iff_indicator.mp hHs
  have hLnn : ∀ v, 0 ≤ Lind v := fun v => Set.indicator_nonneg (fun v _ => by positivity) v
  have hA : 0 ≤ A := le_trans (by positivity) (hb 0)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have key : ∀ ξ, ‖f ξ‖ ≤ A * (m : ℝ) ^ N₀ * Lind (g ξ) := by
    intro ξ
    by_cases h : f ξ = 0
    · rw [h, norm_zero]
      have := hLnn (g ξ)
      positivity
    · have hi := hint ξ h
      have hmem : g ξ ∈ L := mem_latPi F κ _ hi
      rw [hLind, Set.indicator_of_mem hmem]
      have hb' := hb ξ
      rw [hψ ξ] at hb'
      have hpos : 0 < (1 + ‖ψ ξ‖) ^ N₀ := by positivity
      have e1 : ‖f ξ‖ ≤ A * ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hb'
      have hgn : ‖g ξ‖ ≤ m * ‖ψ ξ‖ := by rw [hgsmul]; exact norm_nsmul_le
      have hmpos : (0 : ℝ) < m := by linarith
      have e2 : ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ ≤ (m : ℝ) ^ N₀ * H (g ξ) := by
        simp only [hH]
        calc ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ = (m : ℝ) ^ N₀ * (((m : ℝ) * (1 + ‖ψ ξ‖)) ^ N₀)⁻¹ := by
              rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hmpos.ne'), one_mul]
          _ ≤ (m : ℝ) ^ N₀ * ((1 + ‖g ξ‖) ^ N₀)⁻¹ := by
              gcongr
              nlinarith [norm_nonneg (ψ ξ)]
      calc ‖f ξ‖ ≤ A * ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ := e1
        _ ≤ A * ((m : ℝ) ^ N₀ * H (g ξ)) := mul_le_mul_of_nonneg_left e2 hA
        _ = _ := by ring
  have hu : Summable fun ξ => A * (m : ℝ) ^ N₀ * Lind (g ξ) :=
    (hLs.comp_injective hginj).mul_left _
  have hfs : Summable fun ξ => ‖f ξ‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) key hu
  have hcomp : ∑' ξ, Lind (g ξ) ≤ ∑' v, Lind v := tsum_comp_le_tsum_of_inj hLs hLnn hginj
  have hsub : ∑' v, Lind v = ∑' z : L, H z := (tsum_subtype (L : Set (κ → mixedSpace F)) H).symm
  have hmk : 0 ≤ A * (m : ℝ) ^ N₀ := by positivity
  calc ‖thetaSum F Ψ‖ = ‖∑' ξ, f ξ‖ := rfl
    _ ≤ ∑' ξ, ‖f ξ‖ := norm_tsum_le_tsum_norm hfs
    _ ≤ ∑' ξ, A * (m : ℝ) ^ N₀ * Lind (g ξ) := hfs.tsum_le_tsum key hu
    _ = A * (m : ℝ) ^ N₀ * ∑' ξ, Lind (g ξ) := tsum_mul_left
    _ ≤ A * (m : ℝ) ^ N₀ * ∑' z : L, H z := by
        rw [← hsub]; exact mul_le_mul_of_nonneg_left hcomp hmk
    _ = (∑' z : L, H z) * A * (m : ℝ) ^ N₀ := by ring

end GlobalTheory.LatScaleSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleRepHasTraceFiniteAdelicPureTensorFunctStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction : ∀ (D : D7) (V : HSp D) (ν : Measure (GfC V)) [ν.IsHaarMeasure] (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c) ∧ ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → IsCompact (K : Set (GfC V)) → (∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g) → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) 0 → ∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x := by
  first | exact @GlobalTheory.FinTrace.hasTrace_finFn | exact GlobalTheory.FinTrace.hasTrace_finFn | (intros; apply GlobalTheory.FinTrace.hasTrace_finFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIwasawaMajorantFrameStatement
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_iwasawa_majorant_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (a : GL (Fin n) (AF F ⊗[F] E)), IsMajorantFrame σ J a → ∀ (w : InfinitePlace F) (g : GArch σ J w), ∃ q k : GArch σ J w, k ∈ stabArch σ J w (bc (compInf F E w) a) ∧ g = q * k ∧ ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1 := by
  first | exact @GlobalTheory.IwArchLine.exists_q_k | exact GlobalTheory.IwArchLine.exists_q_k | (intros; apply GlobalTheory.IwArchLine.exists_q_k <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanWeilOperatorTransportsHeisenbergLineD
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.HeisTransport

theorem actsD_heisLine_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ →
      ActsD (evI F) (M.heisLine B.ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil g hg h hh T hT hTi u hu f f₁ hf
  have hS := IsUWeilPair.isUSplitting hWeil
  set ψ := B.ψ with hψ
  set p : UA σ X.J × UA σ W.J := (g, h) with hp

  have hrest : ∀ (φ : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Af F) →
      Rest (evI F) (⇑φ) (fun x => g' (fun i => (x i).2)) := by
    intro φ g' hg'
    refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨φ, g', hg', rfl⟩⟩
    change g' (fun i => (x i + z i).2) = g' (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
  have hpure : ∀ (φ : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Af F) →
      om p (pureA F φ g') = pureA F (T φ) g' := fun φ g' hg' => hT φ _ (hrest φ g' hg')

  have h0 : ∀ v : Matrix (Fin n) (Fin d) (AE F E), ∀ t : ℝ, M.heisLine ψ v t 0 = 0 := by
    intro v t
    funext x
    simp [Model.heisLine, Darboux.rho, schr]

  obtain ⟨D, hD⟩ := GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hB.std
  have hSDD := (hD u hu f).1
  have hL := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₁ (D u f)
  have hAD : ActsD (evI F) (M.heisLine ψ u) f (D u f) := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (D u f) f₁).1 _ (h0 u) hSDD
  have hf₁ : f₁ = D u f := hL.2.2.1 _ hf hAD
  rw [← hf₁] at hSDD

  have himpl : ∀ t : ℝ, ∀ Φ ∈ schA F (Fin n × Fin d),
      M.heisLine ψ (mat g * u * (mat h).transpose) t (om p Φ) = om p (M.heisLine ψ u t Φ) := by
    intro t Φ hΦ
    have e := hS.impl p (realAd F t • u) Φ hΦ
    simp only [Model.heisLine]
    rw [e]
    congr 2
    simp only [actAB, hp, mat, Matrix.mul_smul, Matrix.smul_mul]

  have hSD : GlobalTheory.RealLift.SD (M.heisLine ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
    intro g' hg' l hl
    have hΦ : pureA F (⇑f) g' ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g', hg', rfl⟩
    have e : (fun t => l (M.heisLine ψ (mat g * u * (mat h).transpose) t (pureA F (⇑(T f)) g'))) =
        fun t => (l ∘ₗ om p) (M.heisLine ψ u t (pureA F (⇑f) g')) := by
      funext t
      rw [← hpure f g' hg', himpl t _ hΦ]
      rfl
    rw [e, ← hpure f₁ g' hg']
    exact hSDD g' hg' (l ∘ₗ om p) (hS.adm p l hl)
  exact (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (T f) (T f₁) (T f₁)).1 _ (h0 _) hSD

end GlobalTheory.HeisTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicMapPhiInjectiveStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_map_phi_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Function.Injective (Phi S lam K') := by
  first | exact @GlobalTheory.BCT.TrKer.Phi_injective | exact GlobalTheory.BCT.TrKer.Phi_injective | (intros; apply GlobalTheory.BCT.TrKer.Phi_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.DblSiegelX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def zs {n n₁ d : ℕ} (H : Plane E n n₁) (u : Fin d → AE F E) : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
  Matrix.vecMulVec (incV F H.y) ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *ᵥ u)

variable {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} {d : ℕ}

theorem rho_add (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (w : V) (Φ Ψ : (κ → AF F) → ℂ) :
    dd.rho ψ w (Φ + Ψ) = dd.rho ψ w Φ + dd.rho ψ w Ψ := by
  funext x; simp [Darboux.rho, schr, mul_add]

theorem rho_smul (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (w : V) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    dd.rho ψ w (c • Φ) = c • dd.rho ψ w Φ := by
  funext x; simp [Darboux.rho, schr]; ring

def avgFun (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (Φ : (κ → AF F) → ℂ) : (Fin d → AE F E) → ℂ :=
  fun u => lam (dd.rho ψ (z u) Φ)

theorem avgFun_add (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V)
    (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (Φ Ψ : (κ → AF F) → ℂ) :
    avgFun dd ψ z lam (Φ + Ψ) = avgFun dd ψ z lam Φ + avgFun dd ψ z lam Ψ := by
  funext u; simp [avgFun, rho_add]

theorem avgFun_smul (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V)
    (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    avgFun dd ψ z lam (c • Φ) = c • avgFun dd ψ z lam Φ := by
  funext u; simp [avgFun, rho_smul]

def avgSub (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (μ : @Measure (Fin d → AE F E) (borel _)) : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Φ | Integrable (avgFun dd ψ z lam Φ) μ}
  zero_mem' := by
    show Integrable (avgFun dd ψ z lam 0) μ
    have : avgFun dd ψ z lam 0 = 0 := by
      have h := avgFun_smul dd ψ z lam 0 0
      simpa using h
    rw [this]; exact integrable_zero _ _ _
  add_mem' := fun {Φ Ψ} hΦ hΨ => by
    show Integrable (avgFun dd ψ z lam (Φ + Ψ)) μ
    rw [avgFun_add]; exact hΦ.add hΨ
  smul_mem' := fun c Φ hΦ => by
    show Integrable (avgFun dd ψ z lam (c • Φ)) μ
    rw [avgFun_smul]; exact hΦ.smul c

def averagedIntegralIntegrable (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (μ : @Measure (Fin d → AE F E) (borel _)) : avgSub dd ψ z lam μ →ₗ[ℂ] ℂ where
  toFun Φ := ∫ u, avgFun dd ψ z lam Φ.1 u ∂μ
  map_add' Φ Ψ := by
    simp only [Submodule.coe_add, avgFun_add, Pi.add_apply]
    exact integral_add Φ.2 Ψ.2
  map_smul' c Φ := by
    simp only [Submodule.coe_smul, avgFun_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

def avgL (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (μ : @Measure (Fin d → AE F E) (borel _)) : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ :=
  (LinearMap.exists_extend (averagedIntegralIntegrable dd ψ z lam μ)).choose

theorem avgL_apply (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V)
    (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (μ : @Measure (Fin d → AE F E) (borel _)) (Φ : (κ → AF F) → ℂ)
    (h : Integrable (avgFun dd ψ z lam Φ) μ) : avgL dd ψ z lam μ Φ = ∫ u, avgFun dd ψ z lam Φ u ∂μ := by
  have := congrArg (fun f => f ⟨Φ, h⟩) (LinearMap.exists_extend (averagedIntegralIntegrable dd ψ z lam μ)).choose_spec
  exact this

end GlobalTheory.DblSiegelX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.SiegelAvg

def IsHaarB {Y : Type} [AddGroup Y] [TopologicalSpace Y] (μ : @Measure Y (borel Y)) : Prop :=
  @Measure.IsAddHaarMeasure Y _ _ (borel Y) μ

variable {Y V : Type} [TopologicalSpace Y] [AddCommGroup V] [Module ℂ V]

def Conv (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) (v : V) : Prop :=
  letI : MeasurableSpace Y := borel Y
  Integrable (fun y => L₁ (T y v)) μ

def convSub (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) : Submodule ℂ V where
  carrier := {v | Conv μ L₁ T v}
  zero_mem' := by
    letI : MeasurableSpace Y := borel Y
    show Integrable (fun y => L₁ (T y 0)) μ
    simp only [map_zero]
    exact integrable_zero _ _ _
  add_mem' := by
    letI : MeasurableSpace Y := borel Y
    intro v w hv hw
    show Integrable (fun y => L₁ (T y (v + w))) μ
    simp only [map_add]
    exact Integrable.add hv hw
  smul_mem' := by
    letI : MeasurableSpace Y := borel Y
    intro c v hv
    show Integrable (fun y => L₁ (T y (c • v))) μ
    simp only [map_smul, smul_eq_mul]
    exact Integrable.const_mul hv c

def avg0 (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) : convSub μ L₁ T →ₗ[ℂ] ℂ where
  toFun v := letI : MeasurableSpace Y := borel Y; ∫ y, L₁ (T y (v : V)) ∂μ
  map_add' v w := by
    letI : MeasurableSpace Y := borel Y
    show ∫ y, L₁ (T y ((v : V) + w)) ∂μ = ∫ y, L₁ (T y v) ∂μ + ∫ y, L₁ (T y w) ∂μ
    simp only [map_add]
    exact integral_add v.2 w.2
  map_smul' c v := by
    letI : MeasurableSpace Y := borel Y
    show ∫ y, L₁ (T y (c • (v : V))) ∂μ = c • ∫ y, L₁ (T y v) ∂μ
    simp only [map_smul, smul_eq_mul]
    exact integral_const_mul c _

def avgForm (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) : V →ₗ[ℂ] ℂ :=
  (LinearMap.exists_extend (avg0 μ L₁ T)).choose

theorem avgForm_apply (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) {v : V}
    (hv : Conv μ L₁ T v) :
    avgForm μ L₁ T v = (letI : MeasurableSpace Y := borel Y; ∫ y, L₁ (T y v) ∂μ) :=
  LinearMap.congr_fun (LinearMap.exists_extend (avg0 μ L₁ T)).choose_spec ⟨v, hv⟩

def schrL {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) : Module.End ℂ ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' φ φ' := funext fun x => by simp only [schr, Pi.add_apply]; ring
  map_smul' c φ := funext fun x => by simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def starFam {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ}
    {Bf : Matrix (Fin a) (Fin b ⊕ Fin b) (AE F E) → Matrix (Fin a) (Fin b ⊕ Fin b) (AE F E) → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (u : Fin a → AE F E) (y : Fin b → AE F E) :
    Module.End ℂ ((κ → AF F) → ℂ) :=
  schrL ψ (dd.e (Matrix.vecMulVec u (Sum.elim y y)))

theorem starFam_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ}
    {Bf : Matrix (Fin a) (Fin b ⊕ Fin b) (AE F E) → Matrix (Fin a) (Fin b ⊕ Fin b) (AE F E) → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (u : Fin a → AE F E) (y : Fin b → AE F E) (φ : (κ → AF F) → ℂ) :
    starFam dd ψ u y φ = dd.rho ψ (Matrix.vecMulVec u (Sum.elim y y)) φ := rfl

end GlobalTheory.SiegelAvg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelGoodFormsDimsAgreePartwise
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.DimPartsFull

theorem dimParts : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → R.toRealDat.LUnif → (R.toCx3 F).DimParts false :=
  fun hP _ _ _ _ _ _ _ _ _ _ _ _ R F _ hOk hW hEx hX hD hM hU =>
    dimParts_of_schur R F hOk hW hEx hX hD hM hU (GlobalTheory.T.schurConstantsExistOnChain_of_cuspRapidDecay hP R.toRealDat)

end GlobalTheory.DimPartsFull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiInvariantConjugacyClassesFinite
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.bi_invariant_conjugacy_classes_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {q : GlobalTheory.LKDef.DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | exact @GlobalTheory.LKDef.FinPairs.finite_classes_irr_term_ne_zero | exact GlobalTheory.LKDef.FinPairs.finite_classes_irr_term_ne_zero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompMemKinfEquivariantAutomorphicMapsStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_comp_mem_kinfEquivariantAutomorphicMaps : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) (T : W →ₗ[ℂ] Sm E a), T ∈ maps L W hW → ∀ z ∈ Zalg E a, z ∘ₗ T ∈ maps L W hW := by
  first | exact @GlobalTheory.AutGrowth.comp_mem_maps | exact GlobalTheory.AutGrowth.comp_mem_maps | (intros; apply GlobalTheory.AutGrowth.comp_mem_maps <;> assumption)
end

