import Mathlib
import Formalism.LocalToGlobal.Columns.Bundle0015
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0464
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisRingHomBounded
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0465
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMem
section
open NumberField

noncomputable section

namespace GlobalTheory.NabScale

open MvPolynomial IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def IntAt (w : HeightOneSpectrum (𝓞 K)) (m : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ t ∈ w.asIdeal.primeCompl, ∃ A : Matrix (Fin n) (Fin n) (𝓞 K),
    A.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • m

theorem IntAt.det {w : HeightOneSpectrum (𝓞 K)} {m : Matrix (Fin n) (Fin n) K} (h : IntAt w m) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * m.det := by
  obtain ⟨t, ht, A, hA⟩ := h
  refine ⟨t ^ n, Submonoid.pow_mem _ ht n, A.det, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, Matrix.det_smul, map_pow]
  simp

theorem detPow_scaled (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (c : K)
    (hc : IntAt w (c • (g : Matrix (Fin n) (Fin n) K)))
    (hc' : IntAt w (c • ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) (e : ℤ) :
    ∃ u ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K u * (c ^ (n * e.natAbs) * detPow K n g e) := by
  obtain ⟨k, rfl | rfl⟩ := e.eq_nat_or_neg
  · obtain ⟨t, ht, y, hy⟩ := hc.det
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, Matrix.det_smul, map_pow, Int.natAbs_natCast, detPow, zpow_natCast, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.val_det_apply]
    simp only [Fintype.card_fin]
    ring
  · obtain ⟨t, ht, y, hy⟩ := hc'.det
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, Matrix.det_smul, map_pow, Int.natAbs_neg, Int.natAbs_natCast, detPow, zpow_neg, zpow_natCast,
      ← inv_pow, Units.val_pow_eq_pow_val, ← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    simp only [Fintype.card_fin]
    ring

theorem sqAct_scaled (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (c : K)
    (hc : IntAt w (c • (g : Matrix (Fin n) (Fin n) K)))
    (hc' : IntAt w (c • ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (lam : DomWeight n) (f : MvPolynomial (Fin n × Fin n) K) (hf : f ∈ (nablaSq (𝓞 K) n lam).map (toK K _)) :
    ∃ s ∈ w.asIdeal.primeCompl,
      algebraMap (𝓞 K) K s • (c ^ (∑ j, lam.natW j + n * lam.detShift.natAbs) • sqAct K n lam g f) ∈
        (nablaSq (𝓞 K) n lam).map (toK K _) := by
  obtain ⟨f, hf, rfl⟩ := hf
  obtain ⟨t, ht, A, hA⟩ := hc
  obtain ⟨u, hu, y, hy⟩ := detPow_scaled w g c ⟨t, ht, A, hA⟩ hc' lam.detShift
  refine ⟨u * t ^ (∑ j, lam.natW j), Submonoid.mul_mem _ hu (Submonoid.pow_mem _ ht _),
    y • Formalism.GradedWeylDivisibility.rowAct (𝓞 K) Aᵀ f,
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable (𝓞 K) n n _ _ f hf), ?_⟩
  have hK : map (algebraMap (𝓞 K) K) f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n lam.natW :=
    Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ f hf
  have hT : Aᵀ.map (algebraMap (𝓞 K) K) = (algebraMap (𝓞 K) K t * c) • (g : Matrix (Fin n) (Fin n) K)ᵀ := by
    rw [Matrix.transpose_map, hA, Matrix.transpose_smul, Matrix.transpose_smul, smul_smul]
  rw [map_smul, GlobalTheory.NabStab.toK_apply, GlobalTheory.NabStab.toK_apply, GlobalTheory.NabStab.map_rowAct, hT,
    GlobalTheory.NabStab.rowAct_smul _ _ _ hK.1, sqAct, ← IsScalarTower.algebraMap_smul K y, hy, smul_smul, smul_smul, smul_smul,
    map_mul, map_pow]
  congr 1
  ring

def scaleExp {ι : Type} [Fintype ι] (lam : ι → DomWeight n) : ℕ :=
  ∑ τ, (∑ j, (lam τ).natW j + n * (lam τ).detShift.natAbs)

theorem polyAction_scaled_mem_locP_nabStd {ι : Type} [Fintype ι] (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K) (c : K)
    (hc : ∀ τ, IntAt w (c • ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hc' : ∀ τ, IntAt w (c • (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam),
      c ^ scaleExp lam • actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  have key : ∀ F ∈ nabStd K lam, c ^ scaleExp lam • actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
    intro F hF
    unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      choose s hs hs' using fun τ => sqAct_scaled w (g τ) c (hc τ) (hc' τ) (lam τ) (f τ) (hf τ)
      refine ⟨∏ τ, s τ, Submonoid.prod_mem _ fun τ _ => hs τ, Submodule.subset_span ⟨_, hs', ?_⟩⟩
      have h1 := actTen K ι n lam g f
      unfold ten at h1
      rw [h1, ← IsScalarTower.algebraMap_smul K, map_prod, scaleExp, ← Finset.prod_pow_eq_pow_sum, smul_smul,
        ← Finset.prod_mul_distrib]
      simp only [map_smul, smul_smul]
      rw [Finset.prod_smul]
    | zero => rw [map_zero, smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add, smul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [LinearMap.map_smul_of_tower, smul_comm]
      exact Submodule.smul_mem _ _ hx
  rintro F ⟨s, hs, hF⟩
  obtain ⟨t, ht, h2⟩ := key _ hF
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  rw [LinearMap.map_smul_of_tower] at h2
  rw [mul_smul, smul_comm s (c ^ scaleExp lam)]
  exact h2

theorem intAt_of_cols (w : HeightOneSpectrum (𝓞 K)) (m : Matrix (Fin n) (Fin n) K)
    (h : ∀ j, ∃ t ∈ w.asIdeal.primeCompl, ∀ a, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * m a j) :
    IntAt w m := by
  classical
  choose s hs hs' using h
  have h2 : ∀ a j : Fin n, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K (∏ i, s i) * m a j := by
    intro a j
    obtain ⟨y, hy⟩ := hs' j a
    refine ⟨(∏ i ∈ Finset.univ.erase j, s i) * y, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, map_mul, hy, mul_assoc]
  choose A hA using h2
  refine ⟨∏ i, s i, Submonoid.prod_mem _ fun i _ => hs i, Matrix.of A, ?_⟩
  ext a j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hA]

theorem intAt_transition (w : HeightOneSpectrum (𝓞 K)) {L L' : Submodule (𝓞 K) (Fin n → K)} {B B' : GL (Fin n) K}
    (hB : IsBasisAt w L B) (hB' : IsBasisAt w L' B') (c : K) (h : ∀ x ∈ L, c • x ∈ L') :
    IntAt w (c • ((B'⁻¹ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  apply intAt_of_cols
  intro j
  have h1 : (fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := by
    unfold IsBasisAt at hB
    rw [hB]
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨j, rfl⟩⟩
  obtain ⟨s, hs, hx⟩ := h1
  have h2 : c • (s • fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B') := by
    unfold IsBasisAt at hB'
    rw [← hB']
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact h _ hx⟩
  obtain ⟨s', hs', hx'⟩ := h2
  have h3 : colLat B' = gLat B' (colLat 1) := by rw [← colLat_mul, mul_one]
  rw [h3] at hx'
  obtain ⟨z, hz, hzx⟩ := hx'
  refine ⟨s' * s, Submonoid.mul_mem _ hs' hs, fun a => ?_⟩
  obtain ⟨y, hy⟩ := GlobalTheory.NabStab.int_of_mem_colLat_one hz a
  refine ⟨y, ?_⟩
  have hz' : z = ((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (s' • c • s • fun a => (B : Matrix (Fin n) (Fin n) K) a j) := by
    have hzx' : (B' : Matrix (Fin n) (Fin n) K) *ᵥ z = s' • c • s • fun a => (B : Matrix (Fin n) (Fin n) K) a j := hzx
    rw [← hzx', Matrix.mulVec_mulVec]
    simp
  rw [hy, hz']
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Units.val_mul, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

section ESide

variable {E : Type} [Field E] [NumberField E] {ι : Type}

theorem tauLat_smul_mem (emb : ι → E →+* K) (τ : ι) {M M' : Submodule (𝓞 E) (Fin n → E)} (N : ℕ)
    (h : ∀ x ∈ M, (N : 𝓞 E) • x ∈ M') : ∀ x ∈ tauLat emb τ M, (N : 𝓞 K) • x ∈ tauLat emb τ M' := by
  intro x hx
  unfold tauLat at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    refine Submodule.subset_span ⟨(N : 𝓞 E) • m, h m hm, ?_⟩
    funext a
    simp [Algebra.smul_def]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem dualFr_tauLat_smul_mem (emb : ι → E →+* K) (τ : ι) {M M' : Submodule (𝓞 E) (Fin n → E)} (N : ℕ)
    (h : ∀ x ∈ M', (N : 𝓞 E) • x ∈ M) :
    ∀ φ ∈ dualFr (tauLat emb τ M), (N : K) • φ ∈ dualFr (tauLat emb τ M') := by
  intro φ hφ x hx
  have h1 := hφ _ (tauLat_smul_mem emb τ N h x hx)
  show ((N : K) • φ) ⬝ᵥ x ∈ _
  rw [smul_dotProduct]
  rw [dotProduct_smul] at h1
  convert h1 using 1
  simp [Algebra.smul_def]

end ESide

theorem nabAtr_smul_pow_mem : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι]
    (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (M M' : Submodule (𝓞 E) (Fin n → E)) (N : ℕ),
    N ≠ 0 → Submodule.IsLattice E M → Submodule.IsLattice E M' → (∀ x ∈ M, (N : 𝓞 E) • x ∈ M') →
    (∀ x ∈ M', (N : 𝓞 E) • x ∈ M) →
    ∃ a : ℕ, ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, ((N : K) ^ a) • F ∈ Formalism.L2.DIV.nabAtr emb lam M' := by
  intro E K _ _ _ _ ι _ n emb lam M M' N _ hM _ h1 h2
  refine ⟨scaleExp lam, fun F hF => ?_⟩
  have hL : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ M)) := fun τ => dualFr_tauLat_isLattice emb τ M hM
  have hLL' : ∀ τ, ∀ φ ∈ dualFr (tauLat emb τ M), (N : K) • φ ∈ dualFr (tauLat emb τ M') :=
    fun τ => dualFr_tauLat_smul_mem emb τ N h2
  have hL'L : ∀ τ, ∀ φ ∈ dualFr (tauLat emb τ M'), (N : K) • φ ∈ dualFr (tauLat emb τ M) :=
    fun τ => dualFr_tauLat_smul_mem emb τ N h1
  unfold nabAtr nabK at hF ⊢
  rw [Submodule.mem_comap] at hF ⊢
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
    Submodule.coe_subtype] at hF ⊢
  intro w B' hB'
  choose B hB using fun τ => basisAtEx K n _ (hL τ) w
  have hF' := hF w B hB
  have e : B'⁻¹ = (B'⁻¹ * B) * B⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [SetLike.val_smul, map_smul, e, polyAction_mul]
  refine polyAction_scaled_mem_locP_nabStd lam w (B'⁻¹ * B) (N : K) (fun τ => ?_) (fun τ => ?_) _ hF'
  · exact intAt_transition w (hB τ) (hB' τ) (N : K) (hLL' τ)
  · have h3 : ((B'⁻¹ * B) τ)⁻¹ = (B τ)⁻¹ * B' τ := by simp [mul_inv_rev]
    rw [h3]
    exact intAt_transition w (hB' τ) (hB τ) (N : K) (hL'L τ)

end GlobalTheory.NabScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EPowXiExtMemMan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem YD_xiExt (P : PhiMod O K l e a ι) (α : ℕ)
    (hb : ∀ d : P.D, E K l e ^ α • P.xi d ∈ P.Man) {w : Vec K a ι} (hw : w ∈ P.Mext (invL l (S O K e))) :
    YD t ϖ (E K l e ^ α • P.xiExt w) = ∑ k, ϖ.iD t K (fun τ => hatR O (w τ k)) •
      YD t ϖ (E K l e ^ α • P.xi (fun _ => Pi.single k 1)) := by
  funext i
  simp only [YD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [← map_mul]
  rw [← map_sum]
  congr 1
  funext τ
  have hw' : ∀ k, w τ k ∈ Rpi O K l e := fun k => invL_S_le_Rpi l e (mem_tot.1 hw τ k)
  have hb' : ∀ k, E K l e ^ α * P.xi (fun _ => Pi.single k 1) τ i ∈ Rpi O K l e := fun k =>
    mem_Rpi_of_mem_Man (hb (fun _ => Pi.single k 1)) τ i
  have hx : ∀ k, P.xi (fun _ => Pi.single k 1) τ i = P.xiMat τ i k := fun k => by
    rw [P.xi_apply, P.xiExt_apply]
    have : (cst (fun _ => Pi.single k 1 : P.D) : Vec K a ι) τ = Pi.single k 1 := by
      funext j
      change C ((Pi.single k 1 : ι → K) j) = _
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [this]
    simp
  have hs : E K l e ^ α * P.xiExt w τ i = ∑ k, w τ k * (E K l e ^ α * P.xi (fun _ => Pi.single k 1) τ i) := by
    simp only [hx, P.xiExt_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hm : (∑ k, w τ k * (E K l e ^ α * P.xi (fun _ => Pi.single k 1) τ i)) ∈ Rpi O K l e :=
    Subalgebra.sum_mem _ fun k _ => mul_mem (hw' k) (hb' k)
  rw [hs, hatR_of_mem (O := O) hm, Finset.sum_apply]
  simp only [Pi.mul_apply, hatR_of_mem (O := O) (hw' _), hatR_of_mem (O := O) (hb' _), ← map_mul]
  rw [← map_sum]
  congr 1
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  rfl

omit [NeZero a] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in

theorem cst_mem_Mext (P : PhiMod O K l e a ι) (d : P.D) : (cst d : Vec K a ι) ∈ P.Mext (invL l (S O K e)) := by
  refine mem_tot.2 fun τ i => ?_
  exact HasK.C_mem (d τ i)

omit [NeZero a] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in

theorem descN_mem_Mext (P : PhiMod O K l e a ι) (i : ℕ) (w : Vec K a ι) (hw : w ∈ P.Mext (invL l (S O K e))) :
    (fun τ j => descN K i (w τ j)) ∈ P.Mext (invL l (S O K e)) := by
  refine mem_tot.2 fun τ j => ?_
  obtain ⟨n, hn⟩ := mem_tot.1 hw τ j
  refine ⟨n, ?_⟩
  have h3 : (((l : S O K e) : K⟦X⟧)) ^ n = C ((l : K) ^ n) := by simp
  have h := descN_mem_S e i hn
  rwa [h3, ← smul_eq_C_mul, map_smul, smul_eq_C_mul, ← h3] at h

theorem E_pow_xiExt_mem_Man (P : PhiMod O K l e a ι) (α : ℕ) (hα : ∀ v ∈ P.L, E K l e ^ α • v ∈ P.M)
    (w : Vec K a ι) (hw : w ∈ P.Mext (invL l (S O K e))) : E K l e ^ α • P.xiExt w ∈ P.Man := by
  have h1 : P.xiExt w ∈ P.MMl := ((GlobalTheory.BK.xi_trivialises_invL_S O K l e a ι P).2 w).2 hw
  refine P.mem_Man.2 (mem_tot.2 fun τ i => ?_)
  obtain ⟨m, hm, h⟩ := P.mem_extc.1 (mem_tot.1 h1 τ)
  have hc : ∀ k, E K l e ^ α * P.mx τ i k ∈ A O K := fun k => by
    have hv : (Pi.single τ ((P.mx τ).col k) : Vec K a ι) ∈ P.L := mem_tot.2 fun σ => by
      by_cases hσ : σ = τ
      · subst hσ
        rw [Pi.single_eq_same]
        exact Submodule.subset_span ⟨k, rfl⟩
      · rw [Pi.single_eq_of_ne hσ]
        exact zero_mem _
    have h2 := mem_tot.1 (hα _ hv) τ i
    rwa [Pi.smul_apply, Pi.single_eq_same] at h2
  rw [Pi.smul_apply, h, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Subalgebra.sum_mem _ fun k _ => ?_
  rw [← mul_assoc]
  exact mul_mem (invL_S_le_Rpi l e (le_away _ _ (A_le_S l e (hc k)))) (invL_S_le_Rpi l e (hm k))

theorem taylor_vec (P : PhiMod O K l e a ι) (α : ℕ)
    (hdesc : ∀ (i : ℕ) (w : Vec K a ι), w ∈ P.Mext (invL l (S O K e)) →
      (fun τ j => descN K i (w τ j)) ∈ P.Mext (invL l (S O K e)))
    (hman : ∀ w ∈ P.Mext (invL l (S O K e)), E K l e ^ α • P.xiExt w ∈ P.Man)
    (σ : OD l O → OD l O) (ρ : (ι → OD l O) →+ (ι → OD l O)) (hρ : ∀ c y, ρ (c • y) = σ c • ρ y) (c : OD l O)
    (hor : ∀ d : P.D, ρ (YD t ϖ (E K l e ^ α • P.xi d)) = c • YD t ϖ (E K l e ^ α • P.xi d))
    (μ : ℕ → OD l O) (R : ℕ) (J : Ideal (OD l O))
    (hscal : ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ invL l (S O K e)) → σ (ϖ.iD t K (fun τ => hatR O (f τ))) -
      ∑ i ∈ Finset.range R, μ i * ϖ.iD t K (fun τ => hatR O (descN K i (f τ))) ∈ J)
    {w : Vec K a ι} (hw : w ∈ P.Mext (invL l (S O K e))) (j : ι) :
    ρ (YD t ϖ (E K l e ^ α • P.xiExt w)) j - c * ∑ i ∈ Finset.range R, μ i *
      YD t ϖ (E K l e ^ α • P.xiExt (fun τ k => descN K i (w τ k))) j ∈ J := by
  have hb : ∀ d : P.D, E K l e ^ α • P.xi d ∈ P.Man := fun d => hman _ (cst_mem_Mext P d)
  rw [YD_xiExt t ϖ P α hb hw, map_sum]
  simp only [YD_xiExt t ϖ P α hb (hdesc _ w hw), hρ, hor, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine J.sum_mem fun k _ => ?_
  have h := J.mul_mem_left (c * YD t ϖ (E K l e ^ α • P.xi (fun _ => Pi.single k 1)) j)
    (hscal (fun τ => w τ k) fun τ => mem_tot.1 hw τ k)
  convert h using 1
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime]
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def rhoDHom {LL : FinExt l} {ι : Type} (T : QLat LL)
    (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (g : Gl l) :
    (ι → OD l ↥(OL LL)) →+ (ι → OD l ↥(OL LL)) :=
  AddMonoidHom.mk' (rhoD T jD g) fun x y => by
    have h1 : jD (x + y) = jD x + jD y := jD.map_add x y
    have h2 := (TWact (galOD ↥(OL LL) (sQ l g)) T g).map_add (jD x) (jD y)
    have h3 := jD.symm.map_add (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD x)) (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD y))
    exact (congrArg (fun z => jD.symm (TWact (galOD ↥(OL LL) (sQ l g)) T g z)) h1).trans
      ((congrArg jD.symm h2).trans h3)
end GlobalTheory.GalStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinEvalNonZeroDivisorNatCastIsUnit
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

theorem ED_nzd_and_natCast_isUnit : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e),
    (∀ y : OD l O, GlobalTheory.GalStep.ED K t ϖ * y = 0 → y = 0) ∧ ∀ n : ℕ, n ≠ 0 → IsUnit (n : OD l O) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ
  refine ⟨fun y hy => ?_, fun n hn => ?_⟩
  · have hd : ED K t ϖ = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
      rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
      exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
    set d := GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))
    have hinj : Function.Injective (LinearMap.mulLeft ℤ_[l] d) := by
      intro x z hxz
      rw [← sub_eq_zero]
      apply GlobalTheory.BKReal.HatDescent.aDp_ev_eis_mul_eq_zero (a := a) ϖ
      simp only [LinearMap.mulLeft_apply] at hxz
      rw [mul_sub, hxz, sub_self]
    have hT := Module.Flat.lTensor_preserves_injective_linearMap (M := O) _ hinj
    have hmul : ∀ z : OD l O, (LinearMap.mulLeft ℤ_[l] d).lTensor O z = ((1 : O) ⊗ₜ[ℤ_[l]] d) * z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul o β => simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add x w hx hw => rw [map_add, hx, hw, mul_add]
    apply hT
    rw [hmul, map_zero, ← hd, hy]
  · obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l (Fact.out : l.Prime).one_lt.ne'
    have hmu : IsUnit (m : ℤ_[l]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm))
    have hmu' : IsUnit (m : OD l O) := by
      simpa only [map_natCast] using hmu.map (algebraMap ℤ_[l] (OD l O))
    rw [Nat.cast_mul, Nat.cast_pow]
    exact (isUnit_l_OD.pow k).mul hmu'

end GlobalTheory.GalStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfFrobeniusPeriodicMemDeRhamFilZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_frobenius_periodic_mem_deRhamFil_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h d : ℕ), 0 < h → 0 < d → ∀ c : P.R.B, (l : P.R.B) ^ d * P.φB^[h] c = c → (∀ j < h, ev P j c ∈ Fil P 0) → c = 0 := by
  first | exact @GlobalTheory.PMon.no_fil_zero_neg_slope | exact GlobalTheory.PMon.no_fil_zero_neg_slope | (intros; apply GlobalTheory.PMon.no_fil_zero_neg_slope <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiWachLatticeClosedWeakStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleComparison_pi_wachLattice_closed_weak : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T letπ : Set (((HW l).W K s LL h).DD T))) := by
  first | exact @GlobalTheory.WeakClosed.jD_piN_closed | exact GlobalTheory.WeakClosed.jD_piN_closed | (intros; apply GlobalTheory.WeakClosed.jD_piN_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleFunctorExactOnLatticesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleFunctor_exact_on_lattices : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) (O := ↥(OL LL)) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧ ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x := by
  first | exact @GlobalTheory.LatExact.W_exact | exact GlobalTheory.LatExact.W_exact | (intros; apply GlobalTheory.LatExact.W_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisRingHomBoundedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_acris_ring_hom_bounded : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ γ : Per.Acris l →+* bk.DA bk.ρ₀, (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) ∧ ∀ x, ‖γ x‖ ≤ 1 := by
  first | exact @GlobalTheory.AcrisDisc.exists_acris_to_disc | exact GlobalTheory.AcrisDisc.exists_acris_to_disc | (intros; apply GlobalTheory.AcrisDisc.exists_acris_to_disc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgEquivExtendingWittTiltFrobenius
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.TameFrob

theorem exists_algEquiv_iotaO_sigma : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a], ∃ Φ : Om l ≃ₐ[ℚ_[l]] Om l,
    ∀ w : Wq l a, Φ (GlobalTheory.TameFrob.iotaO l a w) = GlobalTheory.TameFrob.iotaO l a (sigma l a w) := by
  intro l _ a _
  let φ : Om l →ₐ[ℚ_[l]] Om l := (frob l a).liftNormal (Om l)
  refine ⟨AlgEquiv.ofBijective φ φ.normal_bijective, fun w => ?_⟩
  have h := AlgHom.liftNormal_commutes (frob l a) (Om l) (iota l a w)
  rw [AlgEquiv.ofBijective_apply]
  exact h.trans (frobRing_iota l a w)

end GlobalTheory.TameFrob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisPlusSeriesWithThetaResiduesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_BcrisPlus_series_with_theta_residues : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧ (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧ ∀ (h : ℕ) (r : ℝ) (y : ℕ → Formalism.Per.Fl l), 2 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧ ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j y := by
  first | exact @GlobalTheory.PSer.series_residues | exact GlobalTheory.PSer.series_residues | (intros; apply GlobalTheory.PSer.series_residues <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusLatticeGeneratorsDdRStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bdRPlus_lattice_generators_ddR : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → (∀ j : Fin d, ∃ (m : ℕ) (k : Fin m → ℤ) (c : Fin m → Per.BdR l) (v : Fin m → Fin d → Per.BdR l), (∀ i (g : ↥(GK K)), ((ρ g).map (Per.zD l)).mulVec (fun r => Per.σD (g : GQ l) (v i r)) = v i) ∧ (∀ i r, v i r ∈ Per.FilD l (k i)) ∧ (∀ i, c i ∈ Per.FilD l (-k i)) ∧ (Pi.single j 1 : Fin d → Per.BdR l) = ∑ i, c i • v i) → ∀ N₀ : ℕ, ∃ (N m : ℕ) (k : Fin m → ℤ) (c : Matrix (Fin d) (Fin m) (↥(OL K))) (β : Matrix (Fin m) (Fin d) (Per.BdR l)), N₀ ≤ N ∧ (∀ i, |k i| ≤ N) ∧ (∀ r s, C.ι (U r s) ∈ Per.FilD l (-(N : ℤ))) ∧ (∀ r i, (U.map C.ι * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈ Per.FilD l (k i)) ∧ (∀ i j, β i j ∈ Per.FilD l (-k i)) ∧ U.map C.ι * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1 := by
  first | exact @GlobalTheory.BdRLatticeGens.exists_lattice_generators | exact GlobalTheory.BdRLatticeGens.exists_lattice_generators | (intros; apply GlobalTheory.BdRLatticeGens.exists_lattice_generators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldContainsUnramifiedWittTameDescenStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a], e + 1 = l ^ a → ¬ l ∣ a → ∀ LL : FinExt l, (∃ LL' : FinExt l, LL.1 ≤ LL'.1 ∧ HasUnr a LL') ∧ (HasUnr a LL → TameDescentExponentData ↥LL.1 l e a) := by
  first | exact @GlobalTheory.TameCoeff.main | exact GlobalTheory.TameCoeff.main | (intros; apply GlobalTheory.TameCoeff.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoordAcrisBcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coord_acris_bcris_alt : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (φ : ↥T.L.T →+ ℤ_[l]), (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → ∃ (ΦA : TW (OCr l O) T →+ Per.Acris l) (ΦB : TW (OB l O) T →+ Per.Bcris l), (∀ (a : Per.Acris l) (w : TW (OCr l O) T), ΦA (((1 : O) ⊗ₜ[ℤ_[l]] a : OCr l O) • w) = a * ΦA w) ∧ (∀ (y : Per.Bcris l) (w : TW (OB l O) T), ΦB (((1 : O) ⊗ₜ[ℤ_[l]] y : OB l O) • w) = y * ΦB w) ∧ (∀ x : ↥T.L.T, ΦB ((1 : OB l O) ⊗ₜ[O] x) = algebraMap ℤ_[l] (Per.Bcris l) (φ x)) ∧ (∀ (N : ℕ) (w : TW (OCr l O) T), ΦA (((l : O) ^ N) • w) = (l : Per.Acris l) ^ N * ΦA w) ∧ (∀ w : TW (OCr l O) T, ΦB (TWincl (toOB l O) T w) = acrisToBcris l (ΦA w)) := by
  first | exact @GlobalTheory.exists_coord_acris_bcris | exact GlobalTheory.exists_coord_acris_bcris | (intros; apply GlobalTheory.exists_coord_acris_bcris <;> assumption)
end

