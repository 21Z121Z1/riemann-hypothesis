import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0069
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicHaarFiniteInfiniteProduct
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanIwasawaMinimalParabolic
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianPartLeLevi
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCD

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedBasisBlockEntriesStatement
section
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_embedding_adapted_basis : ∀ (D : D7) [IsTotallyComplex D.host.E] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (l d : ℕ) (h : l + d ≤ m)
    (ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V), GlobalTheory.BlockForms.IsBlockEmb D.sp.cm.sig V.gram X Y h ι →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C → ∀ (τ : D.what₂.Tau)
    (F : GlobalTheory.Mem.AutSpace.SmFun θ V) (f : GlobalTheory.CuspRep.Sm D.host.E d), (∀ x, f.1 x = F.1 (ι x)) →
    ∀ (i j : Fin d) (p q p' q' : Fin V.rank), p.val = l + i.val → q.val = l + j.val →
    p'.val + l + j.val + 1 = V.rank → q'.val + l + i.val + 1 = V.rank → ∀ (z : ℂ) (x : GlobalTheory.CuspRep.GA D.host.E d),
      (GlobalTheory.CuspRep.lieS D.host.E d i j (GlobalTheory.CuspRep.atEmb (tauE D τ) z) f).1 x =
        (GlobalTheory.Mem.RealTranslate.derEnd hθ τ (z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
          (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹)) F).1 (ι x) := by
  first | exact @GlobalTheory.CompanionTheory.BlockEntry.lieS_eq_derEnd | exact GlobalTheory.CompanionTheory.BlockEntry.lieS_eq_derEnd | (intros; apply GlobalTheory.CompanionTheory.BlockEntry.lieS_eq_derEnd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicHaarFiniteInfiniteProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_eq_iSup_parts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ T : Finset (Fin r), levi σ J X Y T = ⨆ i, part σ J X Y T i := by
  first | exact @GlobalTheory.CompanionTheory.LeviGen.levi_eq_iSup_part | exact GlobalTheory.CompanionTheory.LeviGen.levi_eq_iSup_part | (intros; apply GlobalTheory.CompanionTheory.LeviGen.levi_eq_iSup_part <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanIwasawaMinimalParabolicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_normalizes_unipotent_variant : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)), ∀ g ∈ levi D.sp.cm.sig V.gram X Y T, ∀ n ∈ unip D.sp.cm.sig V.gram X T, g * n * g⁻¹ ∈ unip D.sp.cm.sig V.gram X T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.conj_mem_unip_of_mem_levi | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.conj_mem_unip_of_mem_levi | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.conj_mem_unip_of_mem_levi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanUnitaryElementLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit

section Lin

variable {A : Type} [CommRing A] {n m : ℕ}

theorem mulVec_eq_of_mem (C : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A) (U : Matrix (Fin m) (Fin n) A)
    (W : Matrix (Fin n) (Fin m) A) (I : Set (Fin m)) (hDC : D * C = 0) (hUC : ∀ i j, j ∈ I → (U * C) i j = 0)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Cᵀ i) '' I)) : (1 + C * U + W * D) *ᵥ y = y := by
  obtain ⟨a, ha, rfl⟩ := (GlobalTheory.StdPar.UnipArch.mem_span_cols_iff C I y).1 hy
  have h1 : (U * C) *ᵥ a = 0 := funext fun i => by
    show ∑ l, (U * C) i l * a l = 0
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l ∈ I
    · rw [hUC i l hl, zero_mul]
    · rw [ha l hl, mul_zero]
  have h2 : (1 + C * U + W * D) *ᵥ (C *ᵥ a) = C *ᵥ a + C *ᵥ ((U * C) *ᵥ a) + W *ᵥ ((D * C) *ᵥ a) := by
    simp only [add_mulVec, one_mulVec, ← mulVec_mulVec]
  rw [h2, h1, hDC]
  simp

theorem mulVec_sub_mem (C : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A) (U : Matrix (Fin m) (Fin n) A)
    (W : Matrix (Fin n) (Fin m) A) (I : Set (Fin m)) (hU : ∀ i v, i ∉ I → U i v = 0) {y : Fin n → A}
    (hy : W *ᵥ (D *ᵥ y) = 0) : (1 + C * U + W * D) *ᵥ y - y ∈ Submodule.span A ((fun i => Cᵀ i) '' I) := by
  have h : (1 + C * U + W * D) *ᵥ y - y = C *ᵥ (U *ᵥ y) := by
    simp only [add_mulVec, one_mulVec, ← mulVec_mulVec, hy]
    abel
  rw [h]
  refine (GlobalTheory.StdPar.UnipArch.mem_span_cols_iff C I _).2 ⟨U *ᵥ y, fun l hl => ?_, rfl⟩
  show ∑ v, U l v * y v = 0
  exact Finset.sum_eq_zero fun v _ => by rw [hU l v hl, zero_mul]

theorem mem_iff_of_fix {M : Matrix (Fin n) (Fin n) A} (hM : Function.Injective M.mulVec) (S : Submodule A (Fin n → A))
    (hS : ∀ y ∈ S, M *ᵥ y = y) (y : Fin n → A) : y ∈ S ↔ M *ᵥ y ∈ S :=
  ⟨fun h => by rwa [hS y h], fun h => by rwa [← hM (hS _ h)]⟩

end Lin

theorem mem_unip {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin m) E) (T : Finset (Fin m)) (g : GAd σ J)
    (U : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) (W : Matrix (Fin n) (Fin m) (AF F ⊗[F] E))
    (hX : Formalism.UG.cT (σ : E →+* E) X * J * X = 0) (hU : ∀ i v, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → U i v = 0)
    (hW : ∀ v i, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → W v i = 0)
    (hUX : ∀ i j, j ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → (U * GlobalTheory.SiegelSet.adMat F X) i j = 0)
    (hg : (GlobalTheory.AdelicU.matHom _ σ J g).1 =
      1 + GlobalTheory.SiegelSet.adMat F X * U + W * GlobalTheory.SiegelSet.adMat F (Formalism.UG.cT (σ : E →+* E) X * J)) :
    g ∈ GlobalTheory.StdPar.unip σ J X T := by
  have hDC : adMat F (Formalism.UG.cT (σ : E →+* E) X * J) * adMat F X = 0 := by
    rw [adMat, adMat, ← Matrix.map_mul, hX]
    exact Matrix.map_zero _ (map_zero _)
  have hinj : Function.Injective (GlobalTheory.AdelicU.matHom _ σ J g).1.mulVec :=
    Matrix.mulVec_injective_of_isUnit (Units.isUnit _)
  have hfix : ∀ y ∈ colSpan F X (upTo T), (GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y = y := fun y hy => by
    rw [hg]
    exact mulVec_eq_of_mem _ _ U W _ hDC hUX hy
  have hsub : ∀ y, W *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) = 0 →
      (GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y - y ∈ colSpan F X (upTo T) := fun y hy => by
    rw [hg]
    exact mulVec_sub_mem _ _ U W _ hU hy
  have hiff : ∀ S ≤ colSpan F X (upTo T), ∀ y, y ∈ S ↔ (GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y ∈ S := fun S hS =>
    mem_iff_of_fix hinj S fun y hy => hfix y (hS hy)
  refine ⟨Subgroup.mem_iInf.2 fun j => ?_, hiff _ le_rfl, fun y hy => hsub y ?_⟩
  · by_cases hj : j ∈ upTo T
    · have hA : colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} ≤ colSpan F X (upTo T) :=
        Submodule.span_mono (Set.image_mono fun i ⟨k, hk, hik, _⟩ => ⟨k, hk, hik⟩)
      have hB : colSpan F X {j} ≤ colSpan F X (upTo T) :=
        Submodule.span_mono (Set.image_mono (Set.singleton_subset_iff.2 hj))
      refine ⟨hiff _ hA, fun y hy => ?_⟩
      rw [hfix y (hB hy), sub_self]
      exact zero_mem _
    · have hA : {i | ∃ k ∈ T, i ≤ k ∧ k < j} = upTo T := Set.ext fun i =>
        ⟨fun ⟨k, hk, hik, _⟩ => ⟨k, hk, hik⟩, fun ⟨k, hk, hik⟩ =>
          ⟨k, hk, hik, not_le.1 fun h => hj ⟨k, hk, h⟩⟩⟩
      rw [hA]
      refine ⟨hiff _ le_rfl, fun y hy => hsub y ?_⟩
      obtain ⟨a, -, rfl⟩ := (GlobalTheory.StdPar.UnipArch.mem_span_cols_iff _ _ y).1 hy
      rw [mulVec_mulVec a, hDC, zero_mulVec, mulVec_zero]
  · funext v
    show ∑ i, W v i * (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) i = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ upTo T
    · have h : (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) i = 0 := by
        simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy
        exact hy i hi
      rw [h, mul_zero]
    · rw [hW v i hi, zero_mul]

end GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

def IsSliceFrame {D : D7} (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) {m m' : ℕ}
    (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (e : Fin m' → Fin m)
    (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E) : Prop :=
  StrictMono e ∧ (∀ i, i ∉ upTo T ↔ i ∈ Set.range e) ∧
    frameMat V V' ι * X' = X.submatrix id e ∧ frameMat V V' ι * Y' = Y.submatrix id e

variable {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V}

abbrev prM (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) : Matrix (Fin V'.rank) (Fin V.rank) D.host.E :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat D.sp.cm V' V ι

theorem repr_symm (V : HSp D) (a : Fin V.rank → D.host.E) (i : Fin V.rank) :
    V.frame.repr (V.frame.equivFun.symm a) i = a i := by
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem hT_frame (V : HSp D) (a b : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) = ∑ i, ∑ j, star (a i) * V.gram i j * b j := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp only [repr_symm]

theorem prM_mul_frameMat (hι : HSpace.IsIsomEmb V' V ι) : prM V V' ι * frameMat V V' ι = 1 :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat_embMat D.sp.cm V' V ι hι

theorem cT_frameMat_mul_gram :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram = V'.gram * prM V V' ι :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_projMat D.sp.cm V' V ι

theorem mat_eq (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h) (b : GA D V') :
    (matHom V (s b)).1 = 1 + HMul.hMul (HMul.hMul (adMat D.host.F (frameMat V V' ι)) ((matHom V' b).1 - 1)) (adMat D.host.F (prM V V' ι)) := by
  rw [(GlobalTheory.AutFunCompare.embRel_iff V V' ι hι (s b) b).1 (hs b)]
  rfl

theorem prM_mulVec_eq_zero {x : Fin V.rank → D.host.E}
    (h : ∀ v' : V'.V, V.hT (V.frame.equivFun.symm x) (ι v') = 0) : prM V V' ι *ᵥ x = 0 := by
  have hJ : IsUnit V'.gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V'
  have h1 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram) *ᵥ x = 0 := by
    funext j
    have h2 : V.hT (ι (V'.frame j)) (V.frame.equivFun.symm x) = 0 :=
      (V.herm.eq (V.frame.equivFun.symm x) (ι (V'.frame j))).symm.trans (by rw [h]; simp)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord] at h2
    simp only [repr_symm] at h2
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_) h2
    simp only [Formalism.UG.cT, frameMat, LinearMap.toMatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  rw [cT_frameMat_mul_gram, ← Matrix.mulVec_mulVec] at h1
  exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hJ) (h1.trans (Matrix.mulVec_zero _).symm)

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb

open Formalism.L2.Fam.ThC (colM colM_vec frameMat_eq frame_rel perp_rel prM coM embU)
open GlobalTheory.CompanionTheory.LeviGen (prj prX prY ind)
open Formalism.UG (cT)

section Abstract

variable {R : Type} [CommRing R] {a b : ℕ}

theorem lift_of_fix (s : R →+* R) {M : Matrix (Fin a) (Fin b) R} {P : Matrix (Fin b) (Fin a) R}
    {Q G H J : Matrix (Fin a) (Fin a) R} {K : Matrix (Fin b) (Fin b) R}
    (hMP : M * P + Q = 1) (hPM : P * M = 1) (hGQ : G * Q = Q) (hQG : Q * G = Q) (hGH : G * H = 1) (hHG : H * G = 1)
    (hU : cT s G * J * G = J) (hK : cT s M * J * M = K) :
    (P * G * M) * (P * H * M) = 1 ∧ (P * H * M) * (P * G * M) = 1 ∧ M * (P * G * M) = G * M ∧
      cT s (P * G * M) * K * (P * G * M) = K := by
  have eMP : M * P = 1 - Q := eq_sub_of_add_eq hMP
  have hQM : Q * M = 0 := by
    have : (M * P + Q) * M = M := by rw [hMP, Matrix.one_mul]
    rw [Matrix.add_mul, Matrix.mul_assoc, hPM, Matrix.mul_one] at this
    exact left_eq_add.1 this.symm
  have hQH : Q * H = Q := by rw [← hQG, Matrix.mul_assoc, hGH, Matrix.mul_one, hQG]
  have hHQ : H * Q = Q := by rw [← hGQ, ← Matrix.mul_assoc, hHG, Matrix.one_mul, hGQ]
  have hmid : ∀ {A B : Matrix (Fin a) (Fin a) R}, A * B = 1 → Q * B = Q → A * Q = Q →
      (P * A * M) * (P * B * M) = 1 := by
    intro A B hAB hQB hAQ
    calc (P * A * M) * (P * B * M) = P * A * (M * P) * B * M := by simp only [Matrix.mul_assoc]
      _ = P * (A * B) * M - P * (A * Q) * B * M := by
        rw [eMP]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by
        rw [hAB, hAQ, Matrix.mul_one, hPM, Matrix.mul_assoc P Q B, hQB, Matrix.mul_assoc P Q M, hQM, Matrix.mul_zero,
          sub_zero]
  have hMG : M * (P * G * M) = G * M := by
    calc M * (P * G * M) = (M * P) * G * M := by simp only [Matrix.mul_assoc]
      _ = G * M := by
        rw [eMP, Matrix.sub_mul, Matrix.sub_mul, hQG, hQM, Matrix.one_mul, sub_zero]
  refine ⟨hmid hGH hQH hGQ, hmid hHG hQG hHQ, hMG, ?_⟩
  calc cT s (P * G * M) * K * (P * G * M)
      = cT s (M * (P * G * M)) * J * (M * (P * G * M)) := by
        rw [show cT s (M * (P * G * M)) = cT s (P * G * M) * cT s M by rw [Formalism.UG.cT_mul], ← hK]
        simp only [Matrix.mul_assoc]
    _ = cT s M * (cT s G * J * G) * M := by
        rw [hMG, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = K := by rw [hU, hK]

end Abstract

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem mul_P {b : Type} [Fintype b] (N : Matrix b (Fin n) E) (I : Set (Fin r)) :
    N * USplit.P σ J X Y I = (N * X * diagonal (ind I : Fin r → E)) * cT (σ : E →+* E) Y * J +
      (N * Y * diagonal (ind I : Fin r → E)) * cT (σ : E →+* E) X * J := by
  simp only [USplit.P, prj, prX, prY, Matrix.mul_add, Matrix.mul_assoc]

theorem cTX_mul_P (hW : IsWittFrame σ J X Y) (I : Set (Fin r)) :
    cT (σ : E →+* E) X * J * USplit.P σ J X Y I = diagonal (ind I : Fin r → E) * (cT (σ : E →+* E) X * J) := by
  rw [mul_P, hW.xx, hW.xy]
  simp [Matrix.mul_assoc]

theorem cTY_mul_P (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (I : Set (Fin r)) :
    cT (σ : E →+* E) Y * J * USplit.P σ J X Y I = diagonal (ind I : Fin r → E) * (cT (σ : E →+* E) Y * J) := by
  rw [mul_P, hW.yy, Comm.yJx hCM hJ hW]
  simp [Matrix.mul_assoc]

end Frame

section Space

variable {D : D7}

theorem repr_symm (V : HSp D) (c : Fin V.rank → D.host.E) : ⇑(V.frame.repr (V.frame.equivFun.symm c)) = c :=
  funext fun a => congrFun (V.frame.equivFun.apply_symm_apply c) a

theorem hT_col (V : HSp D) {m : ℕ} (C : Matrix (Fin V.rank) (Fin m) D.host.E) (c : Fin V.rank → D.host.E) (i : Fin m) :
    V.hT (V.frame.equivFun.symm fun j => C j i) (V.frame.equivFun.symm c) =
      ((cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) *ᵥ c) i := by
  have h := colM_vec V (fun i => V.frame.equivFun.symm fun j => C j i) (V.frame.equivFun.symm c) i
  have e : colM V (fun i => V.frame.equivFun.symm fun j => C j i) = C :=
    Matrix.ext fun a b => congrFun (repr_symm V fun j => C j b) a
  rw [e, repr_symm] at h
  exact h.symm

theorem mulVec_perp {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} {c : Fin V.rank → D.host.E}
    (h : ∀ v ∈ LinearMap.range ι, V.hT (V.frame.equivFun.symm c) v = 0) :
    (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram) *ᵥ c = 0 := by
  funext a
  have e := colM_vec V (fun k => ι (V'.frame k)) (V.frame.equivFun.symm c) a
  rw [repr_symm] at e
  rw [frameMat_eq, e, ← V.herm.eq, h _ ⟨_, rfl⟩]
  simp

end Space

section Main

variable {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}
  {T : Finset (Fin m)}

theorem mul_diag_zero {b : Type} [Fintype b] {N : Matrix b (Fin m) D.host.E} {I : Set (Fin m)}
    (h : ∀ a, ∀ i ∈ I, N a i = 0) : N * diagonal (ind I : Fin m → D.host.E) = 0 := by
  classical
  refine Matrix.ext fun a i => ?_
  rw [Matrix.mul_diagonal, GlobalTheory.CompanionTheory.LeviGen.ind_apply]
  by_cases hi : i ∈ I
  · rw [h a i hi, zero_mul]; rfl
  · rw [if_neg hi, mul_zero]; rfl

theorem frame_proj (hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig) (hJ : IsHermND D.sp.cm.sig V.gram)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (hι : HSpace.IsIsomEmb V' V ι)
    (hr : ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧
      V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) :
    frameMat V V' ι * prM V V' ι = 1 - USplit.P D.sp.cm.sig V.gram X Y (upTo T) := by
  classical
  set M := frameMat V V' ι with hM
  set Pr := prM V V' ι with hPr
  set Q := USplit.P D.sp.cm.sig V.gram X Y (upTo T) with hQ
  have hPM : Pr * M = 1 := by
    rw [hPr, prM, Matrix.mul_assoc, frame_rel hι, Matrix.nonsing_inv_mul _ (gram_det_ne V').isUnit]
  have hX : ∀ a, ∀ i ∈ upTo T, (cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * X) a i = 0 := fun a i hi =>
    congrFun (mulVec_perp (ι := ι) (c := fun j => X j i) fun v hv => ((hr v).1 hv i hi).1) a
  have hY : ∀ a, ∀ i ∈ upTo T, (cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * Y) a i = 0 := fun a i hi =>
    congrFun (mulVec_perp (ι := ι) (c := fun j => Y j i) fun v hv => ((hr v).1 hv i hi).2) a
  have hMQ : cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * Q = 0 := by
    rw [hQ, mul_P, mul_diag_zero hX, mul_diag_zero hY]
    simp
  have hcol : ∀ j, ∃ u, ι u = V.frame.equivFun.symm fun a => (1 - Q) a j := fun j => by
    refine (hr _).2 fun i hi => ?_
    rw [hT_col, hT_col]
    have hi' : (ind (upTo T) : Fin m → D.host.E) i = 1 := by rw [GlobalTheory.CompanionTheory.LeviGen.ind_apply, if_pos hi]
    constructor
    · have e : cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram * (1 - Q) =
          (1 - diagonal (ind (upTo T) : Fin m → D.host.E)) * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) := by
        rw [Matrix.mul_sub, Matrix.mul_one, hQ, cTX_mul_P hW, Matrix.sub_mul, Matrix.one_mul]
      have e' := congrFun (congrFun e i) j
      refine e'.trans ?_
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.diagonal_mul, hi', one_mul, sub_self]
    · have e : cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram * (1 - Q) =
          (1 - diagonal (ind (upTo T) : Fin m → D.host.E)) * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) := by
        rw [Matrix.mul_sub, Matrix.mul_one, hQ, cTY_mul_P hCM hJ hW, Matrix.sub_mul, Matrix.one_mul]
      have e' := congrFun (congrFun e i) j
      refine e'.trans ?_
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.diagonal_mul, hi', one_mul, sub_self]
  choose u hu using hcol
  have hA : M * Matrix.of (fun b j => V'.frame.repr (u j) b) = 1 - Q := by
    refine Matrix.ext fun a j => ?_
    have e := congrFun (LinearMap.toMatrix_mulVec_repr V'.frame V.frame ι (u j)) a
    rw [hu j, repr_symm] at e
    exact e
  have e1 : M * Pr * (1 - Q) = 1 - Q := by
    rw [← hA, Matrix.mul_assoc M Pr, ← Matrix.mul_assoc Pr, hPM, Matrix.one_mul]
  have e2 : M * Pr * Q = 0 := by
    rw [hPr, prM, Matrix.mul_assoc, Matrix.mul_assoc, hMQ]
    simp
  calc M * Pr = M * Pr * (1 - Q) + M * Pr * Q := by rw [← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]
    _ = 1 - Q := by rw [e1, e2, add_zero]

end Main

section Final

theorem range_embHom : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D)
    (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι →
    (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T,
      V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) →
    ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) →
    (∀ h, s h ∈ uPart D.sp.cm.sig V.gram X Y T) ∧ (∀ g ∈ uPart D.sp.cm.sig V.gram X Y T, ∃ h, s h = g) ∧
      ∀ h ∈ GfC V', s h ∈ GfC V := by
  intro D V m X Y hW T V' ι hι hr s hs
  obtain ⟨hCM, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  refine ⟨fun h => ?_, fun g hg => ?_, fun h hh => Formalism.L2.Fam.ThC.emb_fin hι hs hh⟩
  · intro y hy
    let S : Submodule (AF D.host.F ⊗[D.host.F] D.host.E) (Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) :=
      LinearMap.eqLocus (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram (s h)).1.mulVecLin LinearMap.id
    have hle : colSpan D.host.F X (upTo T) ⊔ colSpan D.host.F Y (upTo T) ≤ S := by
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨i, hi, rfl⟩
        exact (hs h).2 (fun j => X j i) (mulVec_perp fun v hv => ((hr v).1 hv i hi).1)
      · rintro _ ⟨i, hi, rfl⟩
        exact (hs h).2 (fun j => Y j i) (mulVec_perp fun v hv => ((hr v).1 hv i hi).2)
    exact hle hy
  · have hF := frame_proj hCM (hJ V) hW hι hr
    set Q := USplit.P D.sp.cm.sig V.gram X Y (upTo T) with hQ
    have hF' : frameMat V V' ι * prM V V' ι + Q = 1 := by rw [hF, sub_add_cancel]
    have hPM' : prM V V' ι * frameMat V V' ι = 1 := by
      rw [prM, Matrix.mul_assoc, frame_rel hι, Matrix.nonsing_inv_mul _ (gram_det_ne V').isUnit]
    have hMP : (frameMat V V' ι).map (incA D) * (prM V V' ι).map (incA D) + adMat D.host.F Q = 1 := by
      rw [← Matrix.map_mul]
      show (frameMat V V' ι * prM V V' ι).map (incA D) + Q.map (incA D) = 1
      rw [← Matrix.map_add _ (map_add (incA D)), hF', Matrix.map_one _ (map_zero _) (map_one _)]
    have hPM : (prM V V' ι).map (incA D) * (frameMat V V' ι).map (incA D) = 1 := by
      rw [← Matrix.map_mul, hPM', Matrix.map_one _ (map_zero _) (map_one _)]
    have hGQ := USplit.Q_fix_of_uPart hCM (hJ V) hW hg
    have hJu : IsUnit (JR (F := D.host.F) (AF D.host.F) V.gram).det := by
      rw [show JR (F := D.host.F) (AF D.host.F) V.gram = V.gram.map (incA D) from rfl,
        show (V.gram.map (incA D)).det = incA D V.gram.det from (RingHom.map_det (incA D) V.gram).symm]
      exact (isUnit_iff_ne_zero.2 (hJ V).2).map (incA D)
    have hQG := Comm.mul_eq_of_unitary hJu (USplit.matHom_unitary g) (USplit.adMat_P_selfAdjoint hCM (hJ V) _) hGQ
    have hK : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((frameMat V V' ι).map (incA D)) *
        JR (F := D.host.F) (AF D.host.F) V.gram * (frameMat V V' ι).map (incA D) =
        JR (F := D.host.F) (AF D.host.F) V'.gram := by
      rw [Comm.cT_map]
      have e := congrArg (fun A => Matrix.map A (incA D)) (frame_rel hι)
      simp only [Matrix.map_mul] at e
      exact e
    obtain ⟨h1, h2, h3, h4⟩ := lift_of_fix (sigR (AF D.host.F) D.sp.cm.sig) hMP hPM hGQ hQG
      (USplit.matHom_mul_inv g) (USplit.matHom_inv_mul g) (USplit.matHom_unitary g) hK
    let h : GA D V' := show HR (AF D.host.F) D.sp.cm.sig V'.gram from ⟨⟨_, _, h1, h2⟩, h4⟩
    refine ⟨h, embU D V V' ι hι _ _ h (hs h) ⟨h3.symm, fun x hx => ?_⟩⟩
    have hPx : prM V V' ι *ᵥ x = 0 := by rw [prM, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    have hQx : Q *ᵥ x = x := by
      have e : (frameMat V V' ι * prM V V' ι + Q) *ᵥ x = x := by rw [hF', Matrix.one_mulVec]
      rwa [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hPx, Matrix.mulVec_zero, zero_add] at e
    have hb : adMat D.host.F Q *ᵥ (fun i => incA D (x i)) = fun i => incA D (x i) := by
      funext i
      exact ((incA D).map_mulVec Q x i).symm.trans (congrArg _ (congrFun hQx i))
    show (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram g).1 *ᵥ (fun i => incA D (x i)) = _
    rw [← hb, Matrix.mulVec_mulVec, hGQ]

end Final

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FrameFamilyRightTranslateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_frame_K_type_coefficients : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (φ : GA D V → ℂ), φ ∈ cuspOn θ V X Y T U ε fr ρ c → ∀ b : GA D V, (fun x => φ (x * b)) ∈ cuspOn θ V X Y T (U.map (MulAut.conj b).toMonoidHom) ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) ρ c := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl.cuspOn_mul_right | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl.cuspOn_mul_right | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl.cuspOn_mul_right <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianPartLeLeviStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_decomposition_hermitian_centralizer : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)), ∀ mm ∈ levi D.sp.cm.sig V.gram X Y T, ∃ mH ∈ uPart D.sp.cm.sig V.gram X Y T, ∃ mo ∈ levi D.sp.cm.sig V.gram X Y T, (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * mo = mo * t) ∧ mm = mH * mo := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLeviStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_family_right_translate : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ b : GA D V, IsFrameFam V ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.isFrameFam_mul_infMat_inv | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.isFrameFam_mul_infMat_inv | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.isFrameFam_mul_infMat_inv <;> assumption)
end

