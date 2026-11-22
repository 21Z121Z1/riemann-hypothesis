import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0338

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCompactKinfAndConj
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cusp.KinfCompact

section Mat

variable {p q n : ℕ} {A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ} {B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ}
  {G m : Matrix (Fin n) (Fin n) ℂ}

theorem Jpq_mul_self : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem inv_frame (hA : Aᴴ * Formalism.UG.Jpq p q * A = G) (h : A * B = 1) : Bᴴ * G * B = Formalism.UG.Jpq p q := by
  calc Bᴴ * G * B = (A * B)ᴴ * Formalism.UG.Jpq p q * (A * B) := by
        rw [← hA, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_block_iff (h1 : B * A = 1) (h2 : A * B = 1) :
    (∃ b : Mat p q, IsKC b ∧ b * A = A * m) ↔ Formalism.UG.Jpq p q * (A * m * B) = A * m * B * Formalism.UG.Jpq p q := by
  constructor
  · rintro ⟨b, hb, e⟩
    have : A * m * B = b := by rw [← e, Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [this]
    exact (LocWeil.CompactPart.isKC_iff b).1 hb
  · intro h
    exact ⟨A * m * B, (LocWeil.CompactPart.isKC_iff _).2 h, by rw [Matrix.mul_assoc, h1, Matrix.mul_one]⟩

theorem norm_entry_le (hA : Aᴴ * Formalism.UG.Jpq p q * A = G) (h1 : B * A = 1) (h2 : A * B = 1) (hm : mᴴ * G * m = G)
    (h : Formalism.UG.Jpq p q * (A * m * B) = A * m * B * Formalism.UG.Jpq p q) (i j : Fin n) :
    ‖m i j‖ ≤ ∑ c, ∑ a, ‖B i a‖ * ‖A c j‖ := by
  set b := A * m * B with hb
  have e1 : bᴴ * Formalism.UG.Jpq p q * b = Formalism.UG.Jpq p q := by
    calc _ = Bᴴ * (mᴴ * (Aᴴ * Formalism.UG.Jpq p q * A) * m) * B := by
          rw [hb, conjTranspose_mul, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hA, hm, inv_frame hA h2]
  have e2 : bᴴ * b = 1 := by
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc] at e1
    rw [← Matrix.mul_one (bᴴ * b), ← Jpq_mul_self, ← Matrix.mul_assoc, e1]
  have hU : b ∈ Matrix.unitaryGroup (Fin p ⊕ Fin q) ℂ := Matrix.mem_unitaryGroup_iff'.2 e2
  have e3 : m = B * b * A := by
    rw [hb]; simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [e3, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul, ← Finset.sum_mul, Matrix.mul_apply]
  refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)) (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (entry_norm_bound_of_unitary hU a c)

end Mat

variable {D : D7}

theorem isClosed_realPts (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  have : T2Space (Af D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GinfC V : Set (GA D V)) = {g | (finHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  exact isClosed_eq (GlobalTheory.Member.continuous_finHom_val D V) continuous_const

theorem continuous_realMat {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    Continuous fun h => infMat D.sp.cm.sig V.gram (θ τ) h := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have e : θ τ = θ₀ (tauE D τ) := SmoothForms.RealPts.infEmb_unique _ _ _ (hθ τ) (hθ₀ _)
  rw [e]
  exact ((GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1 (tauE D τ)).2.2.2.1

theorem isCompact_Kinf_and_conj : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), V.SigOK → ∀ A : CptF V, IsCartanFrame V A → IsCompact (Kinf θ V A : Set (GA D V)) ∧ ∀ A' : CptF V, IsCartanFrame V A' → ∃ g ∈ GinfC V, ∀ k, k ∈ Kinf θ V A' ↔ g * k * g⁻¹ ∈ Kinf θ V A := by
  intro D θ hθ V hV A hA
  choose B h1 h2 using fun τ => LocWeil.CompactPart.exists_inv hV (hA τ)
  refine ⟨?_, fun A' hA' => ?_⟩
  · obtain ⟨R, hR⟩ := Finite.bddAbove_range fun x : D.what₂.Tau × Fin V.rank × Fin V.rank =>
      ∑ c, ∑ a, ‖B x.1 x.2.1 a‖ * ‖A x.1 c x.2.2‖
    obtain ⟨K, hK, hKm⟩ := StabCompact.exists_compact_stab D V θ hθ R
    refine hK.of_isClosed_subset ?_ fun k hk => hKm k (fun y => ?_) fun τ i j => ?_
    · have e : (Kinf θ V A : Set (GA D V)) = (GinfC V : Set (GA D V)) ∩ ⋂ τ,
          {k | Formalism.UG.Jpq _ _ * (A τ * infMat D.sp.cm.sig V.gram (θ τ) k * B τ) =
            A τ * infMat D.sp.cm.sig V.gram (θ τ) k * B τ * Formalism.UG.Jpq _ _} := by
        ext k
        rw [Set.mem_inter_iff, Set.mem_iInter]
        exact and_congr_right fun _ => forall_congr' fun τ => exists_block_iff (h1 τ) (h2 τ)
      rw [e]
      refine (isClosed_realPts V).inter (isClosed_iInter fun τ => ?_)
      have hc := (continuous_const (y := A τ)).matrix_mul (continuous_realMat hθ V τ) |>.matrix_mul
        (continuous_const (y := B τ))
      exact isClosed_eq (continuous_const.matrix_mul hc) (hc.matrix_mul continuous_const)
    · have ha' : finHom V k = 1 := hk.1
      rw [SmoothForms.RealPts.finMat_eq V, ha', Units.val_one, Matrix.one_mulVec]
    · exact (norm_entry_le (hA τ) (h1 τ) (h2 τ) (FockCompare.RealAction.infMat_mem_UH hθ V k τ)
        ((exists_block_iff (h1 τ) (h2 τ)).1 (hk.2 τ)) i j).trans (hR ⟨(τ, i, j), rfl⟩)
  · obtain ⟨g, hg, hu⟩ := (SmoothForms.RealPts.glue θ hθ V).2 (fun τ => B τ * A' τ) fun τ => by
      change (B τ * A' τ)ᴴ * gramAt D V τ * (B τ * A' τ) = gramAt D V τ
      calc _ = (A' τ)ᴴ * ((B τ)ᴴ * gramAt D V τ * B τ) * A' τ := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [inv_frame (hA τ) (h2 τ), hA' τ]
    refine ⟨g, hg, fun k => and_congr ?_ (forall_congr' fun τ => exists_congr fun b => and_congr_right fun _ => ?_)⟩
    · rw [mul_mem_cancel_right (inv_mem hg), mul_mem_cancel_left hg]
    · have e0 : A τ * infMat D.sp.cm.sig V.gram (θ τ) g = A' τ := by
        rw [hu, ← Matrix.mul_assoc, h2, Matrix.one_mul]
      have e1 : infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) g = 1 := by
        rw [← SmoothForms.HeightCoset.infMat_mul', inv_mul_cancel, SmoothForms.HeightCoset.infMat_one']
      have e2 := mul_eq_one_comm.1 e1
      rw [SmoothForms.HeightCoset.infMat_mul', SmoothForms.HeightCoset.infMat_mul', ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, e0]
      constructor
      · intro h
        rw [← h, ← e0, Matrix.mul_assoc, Matrix.mul_assoc, e2, Matrix.mul_one]
      · intro h
        rw [← e0, ← Matrix.mul_assoc, h, Matrix.mul_assoc _ _ (infMat _ _ _ g), e1, Matrix.mul_one, e0]

end GlobalTheory.Cusp.KinfCompact

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
section
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}

theorem isParamVec_iff_isSysParam (hJ : SphOff J χ Sb) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ Sb)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = v) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g)
    {c : List ℤ → ℂ} (hc : ∀ d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c d • f) (B : Multiset ℂˣ) :
    IsParamVec D.sp.cm.sig V.gram (frameLat V) h ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) f B ↔
      IsSysParam D.sp.cm.sig V.rank h c B := by
  have hx : f ∈ fixed ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v))
      (stabLoc D.sp.cm.sig V.gram (frameLat V) v) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext (hf k hk)
  have hs := isEigenSys_of_heckeLin hJ hv h hx hc
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hH := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  exact ⟨hs.isSysParam, hs.isParamVec h0 hx
    (fun hv => (SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hL.span_eq_top h hv hd).imp fun _ he => he.1)
    fun hw τ hτ => ((((exists_isInertChart _ (isCMExt_host D) v).2 w h hw).2.2.2.2 τ hτ).2 _ _ _ hH hL.fg
      hL.span_eq_top hd).imp fun _ he => he.1⟩

theorem isParamFunV_iff_isSysParamD (hJ : SphOff J χ Sb) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ v ∉ Sb, ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g)
    {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    (hc : ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) (B : Fam D.host.E) :
    IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B :=
  forall₂_congr fun v hv => forall₂_congr fun w h => isParamVec_iff_isSysParam hJ hv h h0 (hf v hv) (hc w) (B w)

theorem isParamFunV_iff_isSysParamD_of_level (hJ : SphOff J χ Sb) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    (hc : ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) (B : Fam D.host.E) :
    IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B :=
  isParamFunV_iff_isSysParamD hJ h0 (fun _ hv _ hk => fixed_of_level hJ hv hf hk) hc B

variable {S : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {M : DSModel V S}

theorem isParamFunV_iff_of_mem_partFull (hJ : SphOff J χ Sb) {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    {T : MMap M} (hT : T ∈ partFull θ M J χ Sb c) {x : M.Vec} (h0 : T x ≠ 0) (B : Fam D.host.E) :
    IsParamFunV V Sb (T x) B ↔ IsSysParamD D Sb V.rank c B :=
  have h := (mem_partFull θ M J χ Sb c T).1 hT
  isParamFunV_iff_isSysParamD_of_level hJ h0 (((GlobalTheory.MultMem.mem_mult_iff ..).1 h.1).lev x)
    (fun P d R hR => h.2 P d R hR x) B

theorem isParamFunV_iff_of_mem_partDual (hJ : SphOff J χ Sb) {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    {T : MMap M} (hT : T ∈ partDual θ M J χ Sb c) {x : M.Vec} (h0 : T x ≠ 0) (B : Fam D.host.E) :
    IsParamFunV V Sb (T x) B ↔ IsSysParamD D Sb V.rank (fun P d => c P (dualLab d)) B :=
  isParamFunV_iff_of_mem_partFull hJ hT h0 B

theorem param_iff_sysParam (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (B : Fam D.host.E) (hJ : SphOff J χ Sb) :
    (∀ f : GA D V → ℂ, f ≠ 0 →
      (∀ v ∉ Sb, ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g) →
      (∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) →
      (IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B)) ∧
    ∀ (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S),
      ∀ T ∈ partFull θ M J χ Sb c, ∀ x : M.Vec, T x ≠ 0 →
        (IsParamFunV V Sb (T x) B ↔ IsSysParamD D Sb V.rank c B) :=
  ⟨fun _ h0 hf hc => isParamFunV_iff_isSysParamD hJ h0 hf hc B,
    fun _ _ _ _ hT _ h0 => isParamFunV_iff_of_mem_partFull hJ hT h0 B⟩

theorem sphOff_KsphC (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    SphOff (KsphC V ∅) (fun _ => 1) Sb := fun P _ => by
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (comp_finAdEquiv D) P
  exact ⟨e, f, h, fun _ _ => Iff.rfl, fun _ _ _ => rfl⟩

end GlobalTheory.LFun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemExtSubSpanDepth
section
noncomputable section

namespace GlobalTheory.Cusp.FlagCocompact

open scoped TensorProduct
open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

theorem exists_adapted_set {K M : Type} [Field K] [AddCommGroup M] [Module K M] (X : ℕ → Submodule K M)
    (hX : Monotone X) (h0 : X 0 = ⊥) (k : ℕ) :
    ∃ s : Set M, LinearIndepOn K id s ∧ s ⊆ X k ∧ ∀ i ≤ k, X i ≤ Submodule.span K (s ∩ X i) := by
  induction k with
  | zero => exact ⟨∅, linearIndepOn_empty _ _, Set.empty_subset _, fun i hi => by
      rw [Nat.le_zero.1 hi, h0]; exact bot_le⟩
  | succ k ih =>
    obtain ⟨s, hs, h1, h2⟩ := ih
    have h3 : s ⊆ X (k + 1) := h1.trans (hX k.le_succ)
    refine ⟨hs.extend h3, hs.linearIndepOn_extend h3, hs.extend_subset h3, fun i hi => ?_⟩
    rcases Nat.le_succ_iff.1 hi with h | rfl
    · exact (h2 i h).trans (Submodule.span_mono (Set.inter_subset_inter_left _ (hs.subset_extend h3)))
    · rw [Set.inter_eq_left.2 (hs.extend_subset h3)]
      exact hs.subset_span_extend h3

theorem exists_adapted_basis {K M : Type} [Field K] [AddCommGroup M] [Module K M] [Module.Finite K M]
    (X : ℕ → Submodule K M) (hX : Monotone X) (h0 : X 0 = ⊥) (k : ℕ) :
    ∃ (r : ℕ) (e : Fin r → M) (d : Fin r → ℕ), LinearIndependent K e ∧ (∀ j, d j < k) ∧
      ∀ i ≤ k, X i = Submodule.span K (e '' {j | d j < i}) := by
  classical
  obtain ⟨s, hs, h1, h2⟩ := exists_adapted_set X hX h0 k
  have hf : Finite s := LinearIndependent.finite (R := K) hs
  obtain ⟨r, ⟨q⟩⟩ := Finite.exists_equiv_fin s
  let e : Fin r → M := fun j => (q.symm j).1
  have he : LinearIndependent K e := LinearIndependent.comp hs q.symm q.symm.injective
  have hex : ∀ j, ∃ i, e j ∈ X (i + 1) := fun j => ⟨k, hX k.le_succ (h1 (q.symm j).2)⟩
  have hd : ∀ j i, Nat.find (hex j) < i ↔ e j ∈ X i := fun j i => by
    refine ⟨fun h => hX (Nat.succ_le_of_lt h) (Nat.find_spec (hex j)), fun h => ?_⟩
    cases i with
    | zero => rw [h0] at h; exact absurd h (he.ne_zero j)
    | succ i => exact Nat.lt_succ_of_le (Nat.find_min' _ h)
  refine ⟨r, e, fun j => Nat.find (hex j), he, fun j => (hd j k).2 (h1 (q.symm j).2), fun i hi => le_antisymm
    ((h2 i hi).trans (Submodule.span_mono ?_)) (Submodule.span_le.2 ?_)⟩
  · rintro x ⟨hx, hx'⟩
    have : e (q ⟨x, hx⟩) = x := by simp [e]
    exact ⟨q ⟨x, hx⟩, (hd _ _).2 (this.symm ▸ hx'), this⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact (hd _ _).1 hj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {V : HSpace E}

omit [NumberField F] in

theorem mem_extSub_span_depth {R : Type} [CommRing R] [Algebra F R] {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) E}
    (d : Fin r → ℕ) (i : ℕ) (y : Fin V.rank → R ⊗[F] E) :
    y ∈ extSub (F := F) V R (Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | d j < i})) ↔
      ∃ a : Fin r → R ⊗[F] E, (∀ j, i ≤ d j → a j = 0) ∧ y = (C.map (inclR (F := F) R)).mulVec a := by
  let C' : Matrix (Fin V.rank) (Fin r) E := fun a j => if d j < i then C a j else 0
  have e : Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | d j < i}) = colSpan V C' := by
    refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨j, hj, rfl⟩
      exact ⟨j, congrArg (vecOf V) (funext fun a => if_pos hj)⟩
    · rintro _ ⟨j, rfl⟩
      by_cases hj : d j < i
      · exact Submodule.subset_span ⟨j, hj, congrArg (vecOf V) (funext fun a => (if_pos hj).symm)⟩
      · have : C'ᵀ j = 0 := funext fun a => if_neg hj
        simp [this, vecOf]
  rw [e, AutFunCompare.mem_extSub_colSpan]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun j => if d j < i then a j else 0, fun j hj => if_neg (not_lt.2 hj), funext fun b => ?_⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : d j < i <;> simp [C', hj]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, funext fun b => ?_⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : d j < i
    · simp [C', hj]
    · rw [ha j (not_lt.1 hj), mul_zero, mul_zero]

theorem exists_adapted_frame (𝔉 : IsoFlag V) : ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) E) (d : Fin r → ℕ),
    LinearIndependent E Cᵀ ∧ (∀ j, d j < 𝔉.k) ∧
      ∀ i, 𝔉.X i = Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | d j < i.val}) := by
  have : Module.Finite E V.V := Module.Finite.of_basis V.frame
  obtain ⟨r, e, d, he, hd, hX⟩ := exists_adapted_basis (K := E)
    (fun i => 𝔉.X ⟨min i 𝔉.k, Nat.lt_succ_of_le (min_le_right _ _)⟩)
    (fun a b h => 𝔉.strictMono.monotone (Fin.mk_le_mk.2 (min_le_min_right _ h)))
    (by rw [← 𝔉.zero]; congr 1) 𝔉.k
  refine ⟨r, Matrix.of fun a j => V.frame.repr (e j) a, d, he.map' V.frame.equivFun.toLinearMap (LinearEquiv.ker _),
    hd, fun i => ?_⟩
  have e1 : (fun k => vecOf V ((Matrix.of fun a j => V.frame.repr (e j) a)ᵀ k)) = e :=
    funext fun k => V.frame.equivFun.symm_apply_apply (e k)
  rw [e1, ← hX i (Nat.lt_succ_iff.1 i.2)]
  congr 1
  ext
  simp [Nat.lt_succ_iff.1 i.2]

theorem unip_cocompact (hc : CMData F E) (𝔉 : IsoFlag V) : Cocompact (ratPts hc V) (𝔉.unip hc (AF F)) := by
  obtain ⟨r, C, d, hC, hd, hX⟩ := exists_adapted_frame 𝔉
  have ht : 𝔉.top = colSpan V C := (hX _).trans (congrArg (Submodule.span _) (by
    rw [← Set.image_univ]; congr 1; exact Set.eq_univ_of_forall fun j => hd j))
  have h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0 := by
    have h := 𝔉.iso
    change 𝔉.top ≤ perp V 𝔉.top at h
    rw [ht] at h
    ext a k
    have := (mem_perp_colSpan hc V C _).1 (h (Submodule.subset_span ⟨k, rfl⟩))
    simp only [repr_vecOf] at this
    exact congrFun this a
  have hm : ∀ (g : GA hc V) (x : Fin V.rank → E),
      ((HA.mat _ hc.sig V.gram g).1 - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
      act hc V g (coordR V _ (vecOf V x)) - coordR V _ (vecOf V x) := fun g x => by
    have : coordR (F := F) V (AF F) (vecOf V x) = fun i => inclR (F := F) (AF F) (x i) :=
      funext fun i => by rw [coordR, repr_vecOf]
    rw [this, Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  have e : 𝔉.unip hc (AF F) = Subgroup.closure (Mem.UnipCocompact.radSet hc V C d) := by
    rw [← Subgroup.closure_eq (𝔉.unip hc (AF F))]
    congr 1
    ext g
    refine IsoFlag.mem_unip_iff.trans
      (and_congr ⟨fun h i => ?_, fun h i x hx => ?_⟩ ⟨fun h x hx => ?_, fun h x hx => ?_⟩)
    · have := h ⟨d i, hd i⟩ (vecOf V (Cᵀ i)) (by
        rw [hX]; exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩)
      rw [hX, ← hm] at this
      exact (mem_extSub_span_depth d _ _).1 this
    · rw [hX] at hx ⊢
      refine act_sub_mem_of_mem_span ?_ hx
      rintro _ ⟨j, hj, rfl⟩
      obtain ⟨a, ha, h'⟩ := h j
      exact (mem_extSub_span_depth d _ _).2
        ⟨a, fun l hl => ha l (Nat.le_trans (Nat.lt_succ_iff.1 hj) hl), (hm g _).symm.trans h'⟩
    · rw [ht] at h
      rw [hm]
      exact (mem_extSub_colSpan V _ C _).1 (h _ ((mem_perp_colSpan hc V C _).2 (by simpa only [repr_vecOf] using hx)))
    · rw [ht] at hx ⊢
      have := h _ ((mem_perp_colSpan hc V C _).1 hx)
      rw [hm, show vecOf V (fun i => V.frame.repr x i) = x from V.frame.equivFun.symm_apply_apply x] at this
      exact (mem_extSub_colSpan V _ C _).2 this
  rw [e]
  obtain ⟨K, hK, h⟩ := Mem.UnipCocompact.closure_radSet_cocompact hc V C hC h0 d
  refine ⟨K, hK, fun n => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h n
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩

end GlobalTheory.Cusp.FlagCocompact

namespace GlobalTheory.Cusp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cocompact_flag : ∀ (D : D7) (V : HSp D) (𝔉 : IsoFlag V), Cocompact (GQ V) (NA 𝔉) := fun D V 𝔉 => by
  rw [AutFunCompare.GQ_eq]
  exact FlagCocompact.unip_cocompact D.sp.cm 𝔉

end GlobalTheory.Cusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TestVectorAdelicPairTranslatesMovedLatticeVacuum
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.Expand
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ArchFree.expand

theorem om_expand : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), ∀ (g : GA D P.a) (g' : GA D P.d) L₁ L₁', Moves D (g : GL (Fin P.a) (AE D)) L₁ → Moves D (g' : GL (Fin P.d) (AE D)) L₁' → ∃ (c : ℂ) (k : ℕ) (r : Fin k → Qbar) (y : Fin k → VC D P.a P.d), 0 < Q → (Mod1All c ∧ (∀ i, Q • y i ∈ La D (tor0 D cc δ) L₁ L₁') ∧ (∀ i, IsIntegral ℤ ((Q : Qbar) ^ (P.a * P.d) * r i)) ∧ (∀ ρ : Qbar →+* ℂ, (∑ i, ‖ρ (r i)‖) ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d)) ∧ (P.W.Om g g' P.F = fun z => c * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (y i) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d) (La D (tor0 D cc δ) L₁ L₁') P.e0) z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ‖lamC lam c‖ = 1) := by
  intro D cc δ t0 Q hC _ P g g' L₁ L₁' hL hL'
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · exact ⟨0, 0, Fin.elim0, Fin.elim0, fun h => absurd h (by omega)⟩
  have hSD : ∀ (N : ℕ) (g : GA D N) L, Moves D (g : GL (Fin N) (AE D)) L → SD D L := by
    intro N g L hL
    obtain ⟨Lt, h1, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
    have : L = Lt g := by
      ext x; rw [hL x, (h1 g).1 x]
    rw [this]; exact (h1 g).2
  have hSD0 : ∀ N : ℕ, SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hW, hint, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hC P.a P.d (La0 D (tor0 D cc δ) P.a P.d)
    (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  obtain ⟨-, -, -, -, -, -, hq⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hC P.a P.d (La D (tor0 D cc δ) L₁ L₁')
    (Or.inr ⟨_, _, hSD _ g _ hL, hSD _ g' _ hL', rfl⟩)
  have he0 : P.e0 ∈ Th D (tor0 D cc δ) (stdL D P.a) (stdL D P.d) := P.vac.1
  have hfix : ∀ x ∈ La0 D (tor0 D cc δ) P.a P.d, Wd D (tor0 D cc δ) x P.e0 = P.e0 := by
    intro x hx
    rw [hW x hx]; funext z; exact he0.2 x hx z
  have heT : P.e0 ∈ TT D (tor0 D cc δ) P.a P.d :=
    ⟨he0.1, 1, one_pos, fun x hx => by rw [one_nsmul]; exact hfix x hx⟩
  obtain ⟨c, hc1, hc2, hc3⟩ := GlobalTheory.T.vacuum_under_adelic_pair_unit_modulus_factor D cc δ hC P.a P.d (P.d_even.mul_left _) P.e0 he0 P.W g g'
    L₁ L₁' hL hL'
  obtain ⟨k, r, z, hz, hr1, hr2, hF⟩ := P.pres
  have hT : ∀ i, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 ∈ TT D (tor0 D cc δ) P.a P.d := by
    intro i
    refine ⟨Wd_diff _ he0.1, Q, hQ, fun x hx => ?_⟩
    obtain ⟨m, hm⟩ := hint x hx _ (hz i)
    rw [Hf_nsmul_right, ← Hf_nsmul_left] at hm
    rw [Wd_comm _ _ m hm, hfix _ (nsmul_mem hx _)]
  have hQc : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hQ.ne'
  have key : ∀ i, ∃ y : VC D P.a P.d, Q • y ∈ La D (tor0 D cc δ) L₁ L₁' ∧
      P.W.Om g g' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0) =
        Wd D (tor0 D cc δ) y (P.W.Om g g' P.e0) := by
    intro i
    obtain ⟨B, hB, h⟩ := approx_La (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1.1 _ _ hL hL' (hz i)
    obtain ⟨m, hm, hl⟩ := P.W.lift g g' ((Q : D.host.E)⁻¹ • B) P.e0 heT
    obtain ⟨B', h1, h2⟩ := h (m * Q) (by positivity)
    refine ⟨pt D (tor0 D cc δ) δ ((Q : D.host.E)⁻¹ • B'), ?_, ?_⟩
    · rw [pt_div, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hQc, one_smul]; exact h1
    · rw [← hl _ (closeTo_div hQ h2), pt_div, ← hB, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hQc, one_smul]
  choose y hy1 hy2 using key
  have hu : ∀ i, ∃ u : Qbar, (u : ℂ) = wdPh D (tor0 D cc δ) (y i) ∧ IsIntegral ℤ u ∧
      ∀ ρ : Qbar →+* ℂ, ‖ρ u‖ = 1 := by
    intro i
    obtain ⟨m, hm⟩ := hq _ (hy1 i)
    exact root_unity (by positivity) (wdPh_pow _ m hm)
  choose u hu1 hu2 hu3 using hu
  refine ⟨c, k, fun i => r i * u i, y, fun _ => ⟨hc1, hy1, fun i => ?_, fun ρ => ?_, ?_, hc3⟩⟩
  · rw [← mul_assoc]; exact (hr1 i).mul (hu2 i)
  · simpa only [map_mul, norm_mul, hu3, mul_one] using hr2 ρ
  · have hF' : P.F = ∑ i, (r i : ℂ) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 := by
      rw [hF]; funext w; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hF', (Om_sum P.W g g' Finset.univ _ _ hT).2]
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hy2, hc2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.coe_mul, hu1]
    simp only [Wd, U]
    ring

end GlobalTheory.ArchFree.expand
end
end

