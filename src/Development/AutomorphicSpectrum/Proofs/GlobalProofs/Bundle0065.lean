import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SelfDualTransport
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0008
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0709
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermModerateGrowthInherited
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod

section General

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.AutomorphicL2Unitary (LeftInv)
open GlobalTheory.Cusp (Cocompact constTermOn)
open GlobalTheory.UAut.ConstAut
open GlobalTheory.ThK.SmoothLev (IsSmModOn)
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isSmModOn_constTermOn (h : IsCMExt F E σ) (hJ : IsHermND σ J) {r : ℕ} {C : Matrix (Fin n) (Fin r) E}
    (d : Fin r → ℕ) (hC : IsIsoCols σ J C) {Γ : Set (GAd σ J)} {φ c : GAd σ J → ℂ}
    (hΓ : ((ratPts σ J ⊓ parFlag σ J C d : Subgroup (GAd σ J)) : Set (GAd σ J)) ⊆ Γ)
    (hφ : IsSmModOn σ J Γ φ) (hc : IsConstTermOn σ J (unipFlag σ J C d) φ c) :
    IsSmModOn σ J (leftGrp σ J C d : Set (GAd σ J)) c ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
  classical
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  have hs : IsSm σ J φ := hφ.smooth
  have hφΓ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ := fun γ hγ => hφ.left γ (hΓ hγ)
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hφΓ
  have hcont : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) :=
    GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic F E σ h n J hJ φ hφ.level hφ.cont hs
  have hleft : ∀ l : List (ℝ → GAd σ J), LeftInv (ratPts σ J ⊓ parFlag σ J C d) (l.foldr lineDer φ) :=
    leftInv_foldr hφΓ
  have hder : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer c = constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := by
    intro l
    induction l with
    | nil => intro _; exact e
    | cons γ l ih =>
      intro hl
      have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')
      have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
      funext x
      have hx := GlobalTheory.CuspLie.hasDerivAt_constTermOn hco (hleft l) (hcont l hl') (hleft (γ :: l)) (hcont (γ :: l) hl)
        (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J γ hγ) (hasDerivAt_foldr h hs hl' hγ) x
      rw [realLine_zero h hγ, mul_one] at hx
      rw [List.foldr_cons, ih hl']
      exact hx.deriv
  have hct : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
    intro l hl
    obtain ⟨c', hc', -⟩ := existsUnique_isConstTermOn h hJ hC d (φ := l.foldr lineDer φ)
      fun γ hγ => hleft l γ ⟨hγ.1, unipFlag_le_parFlag hJ (sigma_sigma h) hC d hγ.2⟩
    rwa [hder l hl, ← (hc'.eq_constTermOn_par h hJ hC (hleft l)).2]
  have hlevel : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧
      ∀ k ∈ U, k ∈ finPts σ J → ∀ g, c (g * k) = c g := by
    obtain ⟨U, hU, hUk⟩ := hφ.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    rw [e, ← GlobalTheory.Cusp.constTermOn_mul_right]
    exact congrArg (fun f => constTermOn _ _ f g) (funext fun y => hUk k hk hf y)
  have hsm : IsSm σ J c := by
    obtain ⟨dd, δ, hδ, hW⟩ := GlobalTheory.T.exists_realOneParamProduct_chart_adelicUnitary F E σ h n J hJ
    intro k γ hγ g
    have := GlobalTheory.T.contDiff_constantTermCocompact_smoothParameterFamily hco (fun x t => φ (x * (List.ofFn fun i => γ i (t i)).prod))
      (fun γ' hγ' x t => by simp only [mul_assoc]; exact hφΓ γ' hγ' _) (fun x => hs k γ hγ x)
      (GlobalTheory.T.continuous_iteratedFDeriv_realOneParamProduct_levelFunction F E σ h n J hJ dd δ hδ hW φ hφ.level hs k γ hγ) g
    simpa [e, GlobalTheory.Cusp.constTermOn_mul_right] using this
  have hgrowth : ∃ M : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ B : ℝ, ∀ g, ‖l.foldr lineDer c g‖ ≤ B * (height σ J g : ℝ) ^ M := by
    obtain ⟨M, hM⟩ := hφ.growth
    obtain ⟨K0, hK0, hs'⟩ := id hco
    haveI := hco.isProbabilityMeasure
    obtain ⟨A, hA⟩ := (hK0.image continuous_subtype_val).exists_bound_of_continuousOn
      (f := fun x => (height σ J x : ℝ)) (NNReal.continuous_coe.comp (continuous_height_GAd σ J)).continuousOn
    refine ⟨M, fun l hl => ?_⟩
    obtain ⟨B, hB⟩ := hM l hl
    refine ⟨max B 0 * max A 0 ^ M, fun g => ?_⟩
    have h1 : ∀ x : unipFlag σ J C d, ‖l.foldr lineDer φ ((x : GAd σ J) * g)‖ ≤
        max B 0 * (max A 0 * (height σ J g : ℝ)) ^ M := by
      intro x
      obtain ⟨γ, hγ, hk⟩ := hs' x
      have e1 : l.foldr lineDer φ ((x : GAd σ J) * g) =
          l.foldr lineDer φ (((γ * x : unipFlag σ J C d) : GAd σ J) * g) := by
        rw [Subgroup.coe_mul, mul_assoc]; exact (hleft l _ hγ _).symm
      have e2 : (height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) : ℝ) ≤ max A 0 := by
        have := hA _ ⟨_, hk, rfl⟩
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_max_left _ _))
      have e3 : (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ≤ max A 0 * height σ J g :=
        calc (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ)
            ≤ height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) * height σ J g := by
              exact_mod_cast height_mul_le σ J _ _
          _ ≤ max A 0 * height σ J g := mul_le_mul_of_nonneg_right e2 (NNReal.coe_nonneg _)
      rw [e1]
      calc _ ≤ B * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M := hB _
        _ ≤ max B 0 * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) e3 _) (le_max_right _ _)
    rw [hder l hl]
    refine (norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure _ _) (.of_forall fun q => h1 q.out)).trans
      (le_of_eq ?_)
    simp [mul_pow, mul_assoc]
  exact ⟨⟨hc.leftInv h hJ hC hφΓ, hlevel, hc.continuous h hJ hC hφΓ hφ.cont, hsm, hgrowth⟩, hct⟩

theorem depth_lt {r t : ℕ} (ht : t ≤ r) {T : Finset (Fin r)} {i j : Fin t} {k : Fin r} (hk : k ∈ T)
    (h1 : j.val ≤ k.val) (h2 : k.val < i.val) :
    (T.filter (· < Fin.castLE ht j)).card < (T.filter (· < Fin.castLE ht i)).card := by
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Fin.lt_def, Fin.val_castLE] at hx ⊢
    exact ⟨hx.1, by omega⟩
  · have h3 := hsub (Finset.mem_filter.2 ⟨hk, Fin.lt_def.2 (by simpa using h2)⟩)
    have h4 := Fin.lt_def.1 (Finset.mem_filter.1 h3).2
    simp only [Fin.val_castLE] at h4
    omega

theorem exists_block_of_subset {r s t : ℕ} (X : Matrix (Fin n) (Fin r) E) {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hs : s ≤ r) (ht : t ≤ r) (hst : s ≤ t) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k)
    {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin t) (Fin t) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular fun i : Fin t => (T.filter (· < Fin.castLE ht i)).card)
    (e : M * adMat F (X.submatrix id (Fin.castLE ht)) = adMat F (X.submatrix id (Fin.castLE ht)) * B) :
    ∃ B' : Matrix (Fin s) (Fin s) (AF F ⊗[F] E),
      (B'.BlockTriangular fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) ∧
      M * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B' := by
  refine ⟨B.submatrix (Fin.castLE hst) (Fin.castLE hst), fun i j hij => ?_, Matrix.ext fun x j => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_notMem_of_card_lt_card hij
    have hk1 := Finset.mem_filter.1 hk
    have h2 : k.val < i.val := by simpa [Fin.lt_def] using hk1.2
    have h1 : j.val ≤ k.val := by
      by_contra hc
      exact hk' (Finset.mem_filter.2 ⟨hk1.1, Fin.lt_def.2 (by simpa using not_le.1 hc)⟩)
    exact hB (depth_lt ht (hST hk1.1) (i := Fin.castLE hst i) (j := Fin.castLE hst j) (by simpa using h1) (by simpa using h2))
  · have e1 := congrFun (congrFun e x) (Fin.castLE hst j)
    have l1 : (M * adMat F (X.submatrix id (Fin.castLE hs))) x j =
        (M * adMat F (X.submatrix id (Fin.castLE ht))) x (Fin.castLE hst j) := rfl
    rw [l1, e1, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hst) (Fin.castLE_injective hst) _ _ (fun i hi => ?_) fun i => rfl
    have hi' : s ≤ i.val := by
      by_contra hc
      exact hi ⟨⟨i.val, not_le.1 hc⟩, rfl⟩
    obtain ⟨k, hk, hjk⟩ := (hS (Fin.castLE hs j)).1 (by simp)
    have hks : k.val < s := (hS k).2 ⟨k, hk, le_rfl⟩
    have hz : B i (Fin.castLE hst j) = 0 :=
      hB (depth_lt ht (hST hk) (by simpa [Fin.le_def] using hjk) (by omega))
    rw [hz, mul_zero]

theorem parFlag_le_of_subset {r s t : ℕ} (X : Matrix (Fin n) (Fin r) E) {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hs : s ≤ r) (ht : t ≤ r) (hst : s ≤ t) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) :
    parFlag σ J (X.submatrix id (Fin.castLE ht)) (fun i : Fin t => (T.filter (· < Fin.castLE ht i)).card) ≤
      parFlag σ J (X.submatrix id (Fin.castLE hs)) (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) :=
  fun _ ⟨⟨B, hB, e⟩, B', hB', e'⟩ =>
    ⟨exists_block_of_subset X hST hs ht hst hS hB e, exists_block_of_subset X hST hs ht hst hS hB' e'⟩

def top {r : ℕ} (S : Finset (Fin r)) : ℕ := S.sup fun k => k.val + 1

theorem top_le {r : ℕ} (S : Finset (Fin r)) : top S ≤ r := Finset.sup_le fun k _ => k.2

theorem top_mono {r : ℕ} {S T : Finset (Fin r)} (h : S ⊆ T) : top S ≤ top T := Finset.sup_mono h

theorem lt_top_iff {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : i.val < top S ↔ ∃ k ∈ S, i ≤ k := by
  rw [top, Finset.lt_sup_iff]
  exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega

theorem leftGrp_eq (h : IsCMExt F E σ) (hJ : IsHermND σ J) {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (S : Finset (Fin r)) :
    leftGrp σ J (X.submatrix id (Fin.castLE (top_le S)))
        (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) =
      GlobalTheory.StdPar.unip σ J X S ⊔ (ratPts σ J ⊓ GlobalTheory.StdPar.levi σ J X Y S) := by
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S (top S) (top_le S) (lt_top_iff S)
    (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) fun _ => rfl
  have hg := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ (top S) (X.submatrix id (Fin.castLE (top_le S)))
    (Y.submatrix id (Fin.castLE (top_le S))) (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective _))).2.2.1
  rw [hg, hu, hl]

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem isSmModOn_constAlong : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → T.Nonempty → ∀ φ c : GA D V → ℂ, IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y T : Set (GA D V)) c ∧ ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c) := by
  intro D V m X Y hW S T hST _ φ c hφ hc
  obtain ⟨h, hJ'⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hJ' V
  obtain ⟨hu, -, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig h _ V.gram hJ m X Y hW T (top T) (top_le T) (lt_top_iff T)
    (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) fun _ => rfl
  have hC := GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (GlobalTheory.SiegelSet.sigma_sigma h) hJ (top_le T)
  have hc' : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.UAut.unipFlag D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
      (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card)) φ c := hu ▸ hc
  have hΓ : ((GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram ⊓ GlobalTheory.UAut.parFlag D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
      (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) : Subgroup (GA D V)) : Set (GA D V)) ⊆
      (leftSub V X Y S : Set (GA D V)) := by
    intro p hp
    have e := leftGrp_eq h hJ hW S
    have : p ∈ GlobalTheory.UAut.leftGrp D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le S)))
        (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) :=
      Subgroup.mem_sup_right ⟨hp.1, parFlag_le_of_subset X hST (top_le S) (top_le T) (top_mono hST) (lt_top_iff S) hp.2⟩
    rw [e] at this
    exact this
  obtain ⟨r1, r2⟩ := isSmModOn_constTermOn h hJ _ hC hΓ hφ hc'
  refine ⟨?_, fun l hl => ?_⟩
  · have e : (leftSub V X Y T : Subgroup (GA D V)) = GlobalTheory.UAut.leftGrp D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
        (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) := (leftGrp_eq h hJ hW T).symm
    rw [e]
    exact r1
  · have := r2 l hl
    rw [← hu] at this
    exact this

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsLocalApproximateIdentity
section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem measurableSet_latV (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
  exact ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2.measurableSet

theorem coordW_latV (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hlam : ∀ v, IsStdV v (lam v)) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    coordW (Fv F v) b (lam v) n M (latV b v) = 1 := by
  classical
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  have hm := measurableSet_latV σ hCM b n M
  have e0 := GlobalTheory.CompanionTheory.SW.WBox.coordW_box F E σ hCM d b lam hlam lf hlf h1 n M ∅ (fun w => latV b w) hm
  have e1 := GlobalTheory.CompanionTheory.SW.WBox.coordW_box F E σ hCM d b lam hlam lf hlf h1 n M {v} (fun w => latV b w) hm
  have hs : {X : Fin n → Fin M → Af F ⊗[F] E | (∀ w ∈ ({v} : Finset _), projV w X ∈ latV b w) ∧ ∀ w, w ∉ ({v} : Finset _) → projV w X ∈ latV b w} =
      {X | (∀ w ∈ (∅ : Finset _), projV w X ∈ latV b w) ∧ ∀ w, w ∉ (∅ : Finset _) → projV w X ∈ latV b w} := by
    ext X
    simp only [Set.mem_setOf_eq, Finset.mem_singleton, Finset.notMem_empty, false_imp_iff, implies_true, true_and, not_false_eq_true, forall_true_left]
    constructor
    · rintro ⟨h, h'⟩ w
      by_cases hw : w = v
      · exact h w hw
      · exact h' w hw
    · exact fun h => ⟨fun w _ => h w, fun w _ => h w⟩
  rw [hs, e0] at e1
  simpa using e1.symm

theorem sfinite_coordW (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (n M : ℕ) : SFinite (coordW (Af F) b lf n M) := by
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  have hKf : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Af F) b) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.1 d b
  haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Af F) hKf lf
  unfold coordW
  infer_instance

theorem lint_fin (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hlam : ∀ v, IsStdV v (lam v))
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1)
    (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞) (hφ : ∀ v, Measurable (φ v)) :
    Measurable (({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)).indicator
      fun Y => ∏ v ∈ S, φ v (projV v Y)) ∧
    ∫⁻ Y, ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)).indicator
      (fun Y => ∏ v ∈ S, φ v (projV v Y)) Y ∂(coordW (Af F) b lf n M) =
      ∏ v ∈ S, ∫⁻ X, φ v X ∂(coordW (Fv F v) b (lam v) n M) := by
  classical
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI hBf := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.2.1 n M
  have hBv : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => by
    obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
  have hSFv : ∀ v, SigmaFinite (coordW (Fv F v) b (lam v) n M) := fun v => by
    obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI := (hlam v).1
    have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Fv F v) b) :=
      (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.1 d b
    haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Fv F v) hK (lam v)
    unfold coordW
    infer_instance
  have hcV : ∀ v, Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) :=
    (GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.1
  have hpv : ∀ v, Measurable (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) := fun v => by
    haveI := hBv v
    exact (hcV v).measurable
  have hlat := measurableSet_latV σ hCM b n M
  set A : Set (Fin n → Fin M → Af F ⊗[F] E) := {Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} with hA
  have hAm : MeasurableSet A := by
    have : A = ⋂ v, ⋂ (_ : v ∉ S), projV v ⁻¹' latV b v := by
      ext Y; simp [hA]
    rw [this]
    exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hpv v (hlat v)
  have hfm : Measurable fun Y : Fin n → Fin M → Af F ⊗[F] E => ∏ v ∈ S, φ v (projV v Y) :=
    Finset.measurable_prod _ fun v _ => (hφ v).comp (hpv v)
  refine ⟨hfm.indicator hAm, ?_⟩
  let ρ : (Fin n → Fin M → Af F ⊗[F] E) → ∀ v : S, (Fin n → Fin M → Fv F v.1 ⊗[F] E) := fun Y v => projV v.1 Y
  have hρ : Measurable ρ := measurable_pi_lambda _ fun v => hpv v.1
  haveI : ∀ v : S, SigmaFinite (coordW (Fv F v.1) b (lam v.1) n M) := fun v => hSFv v.1
  have hmap : ((coordW (Af F) b lf n M).restrict A).map ρ =
      Measure.pi fun v : S => coordW (Fv F v.1) b (lam v.1) n M := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hρ (MeasurableSet.univ_pi hs), Measure.restrict_apply (hρ (MeasurableSet.univ_pi hs))]
    let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
      fun v => if h : v ∈ S then s ⟨v, h⟩ else Set.univ
    have hA' : ∀ v, MeasurableSet (A' v) := fun v => by
      by_cases h : v ∈ S
      · simp only [A', dif_pos h]; exact hs _
      · simp only [A', dif_neg h]; exact MeasurableSet.univ
    have key := GlobalTheory.CompanionTheory.SW.WBox.coordW_box F E σ hCM d b lam hlam lf hlf h1 n M S A' hA'
    have hset : ρ ⁻¹' Set.univ.pi s ∩ A = {X | (∀ v ∈ S, projV v X ∈ A' v) ∧ ∀ v, v ∉ S → projV v X ∈ latV b v} := by
      ext X
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, hA, Set.mem_setOf_eq]
      refine and_congr_left fun _ => ⟨fun h v hv => ?_, fun h v => ?_⟩
      · simpa only [A', dif_pos hv] using h ⟨v, hv⟩
      · have := h v.1 v.2
        simpa only [A', dif_pos v.2] using this
    rw [hset, key, ← Finset.prod_coe_sort S]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [A', dif_pos v.2]
  rw [lintegral_indicator hAm]
  have hG : Measurable fun y : (∀ v : S, (Fin n → Fin M → Fv F v.1 ⊗[F] E)) => ∏ v : S, φ v.1 (y v) :=
    Finset.measurable_prod _ fun v _ => (hφ v.1).comp (measurable_pi_apply v)
  have e1 : ∫⁻ Y in A, ∏ v ∈ S, φ v (projV v Y) ∂(coordW (Af F) b lf n M) =
      ∫⁻ y, ∏ v : S, φ v.1 (y v) ∂(((coordW (Af F) b lf n M).restrict A).map ρ) := by
    rw [lintegral_map hG hρ]
    refine lintegral_congr fun Y => ?_
    rw [← Finset.prod_coe_sort S]
  rw [e1, hmap, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (f := fun v : S => φ v.1) fun v => (hφ v.1).aemeasurable,
    ← Finset.prod_coe_sort S]

section Meas
open GroundTheory.Global
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

abbrev intInf (F : Type) [Field F] [NumberField F] : AddSubgroup (Ainf F) :=
  ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom.range

omit [NumberField E] in

theorem coordW_congr {F : Type} [Field F] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    {m₁ m₂ : MeasurableSpace R} (h : m₁ = m₂) (l₁ : @Measure R m₁) (l₂ : @Measure R m₂) (hl : ∀ s, l₁ s = l₂ s)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    @coordW F E _ _ _ R _ _ _ m₁ d b l₁ n M = @coordW F E _ _ _ R _ _ _ m₂ d b l₂ n M := by
  subst h
  obtain rfl : l₁ = l₂ := Measure.ext fun s _ => hl s
  rfl

theorem std_transfer (laminf : @Measure (Ainf F) measAinf) (hinf : IsStdInf laminf)
    [m : MeasurableSpace (Ainf F)] (hm : m = measAinf) :
    ∃ l : Measure (Ainf F), (∀ s, l s = laminf s) ∧ l.IsAddHaarMeasure ∧
      ∃ D : Set (Ainf F), IsAddFundamentalDomain (intInf F) D l ∧ l D = 1 := by
  subst hm
  obtain ⟨h1, D, h2, h3⟩ := hinf
  exact ⟨laminf, fun _ => rfl, h1, D, h2, h3⟩

theorem isFD_fundamentalSetInfinite (ν : Measure (InfiniteAdeleRing F)) :
    IsAddFundamentalDomain (intInf F) (fundamentalSetInfinite F) ν := by
  refine IsAddFundamentalDomain.mk' ?_ fun x => ?_
  · have hmeas := measurableSet_fundamentalSet F
    have hpre : fundamentalSetInfinite F =
        (fun x : InfiniteAdeleRing F => ((x, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) ⁻¹' fundamentalSet F := by
      ext x
      simp [fundamentalSet, Set.mem_prod, Subring.zero_mem]
    rw [hpre]
    exact (measurable_prodMk_right hmeas).nullMeasurableSet
  · obtain ⟨z, hz, hu⟩ := existsUnique_sub_mem_fundamentalSetInfinite F x
    refine ⟨⟨algebraMap (𝓞 F) (InfiniteAdeleRing F) (-z), -z, rfl⟩, ?_, ?_⟩
    · change algebraMap (𝓞 F) (InfiniteAdeleRing F) (-z) + x ∈ fundamentalSetInfinite F
      rwa [map_neg, neg_add_eq_sub]
    · rintro ⟨_, k, rfl⟩ h
      change algebraMap (𝓞 F) (InfiniteAdeleRing F) k + x ∈ fundamentalSetInfinite F at h
      have hk : -k = z := hu (-k) (by
        change x - algebraMap (𝓞 F) (InfiniteAdeleRing F) (-k) ∈ fundamentalSetInfinite F
        rwa [map_neg, sub_neg_eq_add, add_comm])
      refine Subtype.ext ?_
      change algebraMap (𝓞 F) (InfiniteAdeleRing F) k = algebraMap (𝓞 F) (InfiniteAdeleRing F) (-z)
      rw [← hk, neg_neg]

theorem adele_eq (l : Measure (InfiniteAdeleRing F)) (hH : l.IsAddHaarMeasure)
    (D : Set (Ainf F)) (hD : IsAddFundamentalDomain (intInf F) D l) (hD1 : l D = 1)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    l.prod lf = adeleMeasure F := by
  haveI : Countable (𝓞 F) := inferInstance
  haveI : Countable (intInf F) := by
    have : Function.Surjective ((((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom).rangeRestrict) :=
      AddMonoidHom.rangeRestrict_surjective _
    exact this.countable
  have h2 : l (fundamentalSetInfinite F) = 1 := ((isFD_fundamentalSetInfinite l).measure_eq hD).trans hD1
  set c : ℝ≥0 := Measure.addHaarScalarFactor l (infiniteAdeleMeasure F) with hc
  have hl : l = c • infiniteAdeleMeasure F := Measure.isAddLeftInvariant_eq_smul l (infiniteAdeleMeasure F)
  set s : ℝ≥0 := NNReal.sqrt ‖discr F‖₊ with hs
  have h3 : (c : ℝ≥0∞) * (s : ℝ≥0∞) = 1 := by
    rw [hl, Measure.smul_apply, infiniteAdeleMeasure_fundamentalSetInfinite] at h2
    simpa [ENNReal.smul_def] using h2
  have hset : ({x | ∀ v, x v ∈ v.adicCompletionIntegers F} : Set (Af F)) =
      (integralFiniteAdelesPositiveCompacts F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext x
    exact GroundTheory.Global.mem_integralFiniteAdeles.symm
  have hlf2 : lf = Measure.addHaarMeasure (integralFiniteAdelesPositiveCompacts F) := by
    have := Measure.addHaarMeasure_unique lf (integralFiniteAdelesPositiveCompacts F)
    rw [← hset, h1, one_smul] at this
    exact this
  have hf : ∀ t, lf t = (s : ℝ≥0∞) * finiteAdeleMeasure F t := by
    intro t
    have hs0 : (s : ℝ≥0∞) ≠ 0 := by
      simpa [hs] using sqrt_discr_ne_zero F
    rw [finiteAdeleMeasure, Measure.smul_apply, ← hlf2, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv (sqrt_discr_ne_zero F), ← mul_assoc,
      ENNReal.mul_inv_cancel hs0 ENNReal.coe_ne_top, one_mul]
  haveI : SigmaFinite l := by rw [hl]; infer_instance
  haveI : SigmaFinite lf := by rw [hlf2]; infer_instance
  symm
  refine Measure.prod_eq fun A B _ _ => ?_
  rw [Measure.prod_prod, hf B]
  have hA : l A = (c : ℝ≥0∞) * infiniteAdeleMeasure F A := by
    conv_lhs => rw [hl]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [hA]
  calc (c : ℝ≥0∞) * infiniteAdeleMeasure F A * ((s : ℝ≥0∞) * finiteAdeleMeasure F B)
      = ((c : ℝ≥0∞) * s) * (infiniteAdeleMeasure F A * finiteAdeleMeasure F B) := by ring
    _ = _ := by rw [h3, one_mul]

end Meas

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler

end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitaryIwasawaLeviOne
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi

theorem exists_unitary_iwasawa_leviOne : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}
    (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i), ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      ∀ g ∈ mats (leviOne ε W), ∃ k ∈ maxCpt (mats (leviOne ε W)), ∃ s ∈ mats (leviOne ε W),
        g = k * s ∧ (Uᴴ * s * U).BlockTriangular id :=
  fun {_ _ ε j W} hW hj => GlobalTheory.CompanionTheory.LeviIwa.iwaOn_leviOne ε j W hW hj

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicBlockEmbeddingCompactStatement
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_unipotent_levi_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)), ∀ p ∈ PositivityTheory.ThKR.minPar σ J X, ∃ u ∈ GlobalTheory.StdPar.unip σ J X S, ∃ l ∈ GlobalTheory.StdPar.levi σ J X Y S, p = u * l := by
  first | exact @GlobalTheory.CompanionTheory.Glob.MinParLevi.minPar_eq_unip_mul_levi | exact GlobalTheory.CompanionTheory.Glob.MinParLevi.minPar_eq_unip_mul_levi | (intros; apply GlobalTheory.CompanionTheory.Glob.MinParLevi.minPar_eq_unip_mul_levi <;> assumption)
end

