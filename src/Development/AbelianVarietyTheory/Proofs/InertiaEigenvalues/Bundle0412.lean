import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompleteSpaceFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0179
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0320
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0349
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsSemisimplificationOf
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantTransitionMatrixCover
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.CovTrans

theorem zOm_smul_eq_q {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] [Module ℚ_[l] X]
    [IsScalarTower ℚ_[l] (Om l) X] (c : ℤ_[l]) (x : X) : zOm l c • x = ((c : ℚ_[l])) • x := by
  show (algebraMap ℚ_[l] (Om l) (algebraMap ℤ_[l] ℚ_[l] c)) • x = _
  rw [algebraMap_smul]
  rfl

theorem coord_inj {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] [Module ℚ_[l] X]
    [IsScalarTower ℚ_[l] (Om l) X] {n : ℕ} {v : Fin n → X} (hv : LinearIndependent ℚ_[l] v) {u u' : Fin n → ℤ_[l]}
    (h : ∑ i, zOm l (u i) • v i = ∑ i, zOm l (u' i) • v i) : u = u' := by
  simp only [zOm_smul_eq_q] at h
  have := Fintype.linearIndependent_iff.mp hv (fun i => (u i : ℚ_[l]) - u' i)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext i
  have h2 := this i
  rw [sub_eq_zero] at h2
  exact Subtype.ext h2

theorem dsum {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] {p q : ℕ} (α : Fin p → ℤ_[l])
    (β : Fin p → Fin q → ℤ_[l]) (w : Fin q → X) :
    ∑ s, zOm l (α s) • ∑ i, zOm l (β s i) • w i = ∑ i, zOm l (∑ s, β s i * α s) • w i := by
  simp only [Finset.smul_sum, smul_smul, map_sum, map_mul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
  rw [mul_comm]

theorem transition : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (d : ℕ) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] b → ∀ (m m' : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (ρs' : Fin m' → (Γ →* GL (Fin a) (Om l))) (ι : Fin m → Fin m'), (∀ k, ρs' (ι k) = ρs k) → ∀ (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (t' : Fin m' → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, t' (ι k) = t k) → ∀ (M M' : ℕ), M ≤ M' → ∀ (d₁ d₂ : ℕ) (ρ₁ : Γ →* GL (Fin d₁) ℤ_[l]) (ρ₂ : Γ →* GL (Fin d₂) ℤ_[l]) (bb₁ : Fin d₁ → Fin m → Matrix (Fin a) (Fin a) (Om l)) (bb₂ : Fin d₂ → Fin m' → Matrix (Fin a) (Fin a) (Om l)) (e₁ : Fin d₁ → ℤ_[l]) (e₂ : Fin d₂ → ℤ_[l]), LinearIndependent ℚ_[l] bb₁ → (∀ k, Reads ρ₁ (ρs k) (fun s => bb₁ s k) e₁) → (∀ k, Reads ρ₂ (ρs' k) (fun s => bb₂ s k) e₂) → (∀ s, bb₂ s ∈ GlobalTheory.TraceConjugationCover.latT ρs' t' M') → (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d₁ → ℤ_[l], x = ∑ s, zOm l (z s) • bb₁ s) → ∀ (P₁ : Matrix (Fin d) (Fin d₁) ℤ_[l]) (P₂ : Matrix (Fin d) (Fin d₂) ℤ_[l]) (n N₁ N₂ : ℕ), n ≤ N₁ → n ≤ N₂ → GlobalTheory.TraceConjugationCover.Carries r b ρs t M bb₁ P₁ N₁ → GlobalTheory.TraceConjugationCover.Carries r b ρs' t' M' bb₂ P₂ N₂ → ∃ f : Matrix (Fin d₁) (Fin d₂) ℤ_[l], (∀ g, f * ((ρ₂ g : GL (Fin d₂) ℤ_[l]) : Matrix (Fin d₂) (Fin d₂) ℤ_[l]) = ((ρ₁ g : GL (Fin d₁) ℤ_[l]) : Matrix (Fin d₁) (Fin d₁) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P₁ * f - P₂) i j := by
  intro l _ Γ _ a r d b hb m m' ρs ρs' ι hι t t' ht M M' hM d₁ d₂ ρ₁ ρ₂ bb₁ bb₂ e₁ e₂ hbb₁ hR₁ hR₂ hmem₂ hcoord
    P₁ P₂ n N₁ N₂ hn₁ hn₂ hC₁ hC₂
  have hsm : ∀ {k : Fin m} (c : Om l) (w : Matrix (Fin a) (Fin a) (Om l)),
      (Pi.single k (c • w) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = c • Pi.single k w := by
    intro k c w
    funext k₀
    by_cases h : k₀ = k
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hπL : ∀ y ∈ GlobalTheory.TraceConjugationCover.latL t' M', y ∘ ι ∈ GlobalTheory.TraceConjugationCover.latL t M := by
    intro y hy
    have hle : Submodule.map (LinearMap.funLeft ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) ι) (GlobalTheory.TraceConjugationCover.latL t' M') ≤
        GlobalTheory.TraceConjugationCover.latL t M := by
      rw [GlobalTheory.TraceConjugationCover.latL, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [Set.mem_iUnion, Set.mem_image] at hx
      obtain ⟨k', v, hv, rfl⟩ := hx
      change (Pi.single k' ((l : Om l) ^ M' • v)) ∘ ι ∈ _
      rw [← Finset.univ_sum_single (Pi.single k' ((l : Om l) ^ M' • v) ∘ ι)]
      refine Submodule.sum_mem _ fun k _ => ?_
      by_cases hk : ι k = k'
      · subst hk
        simp only [Function.comp_apply, Pi.single_eq_same]
        have hv' : v ∈ t k := by rw [← ht k]; exact hv
        have e1 : ((l : Om l) ^ M' • v) = zOm l ((l : ℤ_[l]) ^ (M' - M)) • ((l : Om l) ^ M • v) := by
          rw [map_pow, map_natCast, smul_smul, ← pow_add, Nat.sub_add_cancel hM]
        rw [e1, hsm, GlobalTheory.TraceConjugationCover.zOm_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_iUnion.mpr ⟨k, v, hv', rfl⟩))
      · simp [Pi.single_eq_of_ne hk]
    exact hle ⟨y, hy, rfl⟩
  have hdec : ∀ j, ∃ (F : Γ →₀ ℤ_[l]) (y : Fin m' → Matrix (Fin a) (Fin a) (Om l)), y ∈ GlobalTheory.TraceConjugationCover.latL t' M' ∧
      bb₂ j = (F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs' g) + y := by
    intro j
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hmem₂ j)
    obtain ⟨F, hF⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hx
    refine ⟨F, y, hy, ?_⟩
    rw [← hxy, ← hF]
    simp only [GlobalTheory.TraceConjugationCover.zOm_smul]
  choose F y hy hbb using hdec
  have hπF : ∀ (G : Γ →₀ ℤ_[l]), (G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs' g) ∘ ι =
      G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g := by
    intro G
    funext k
    simp [Finsupp.sum, Finset.sum_apply, GlobalTheory.TraceConjugationCover.tup, hι]
  have hπbb : ∀ j, bb₂ j ∘ ι = ((F j).sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y j ∘ ι := by
    intro j
    rw [hbb j, ← hπF]
    rfl
  have hmemT : ∀ j, bb₂ j ∘ ι ∈ GlobalTheory.TraceConjugationCover.latT ρs t M := by
    intro j
    rw [hπbb j]
    refine Submodule.add_mem_sup ?_ (hπL _ (hy j))
    simp only [GlobalTheory.TraceConjugationCover.zOm_smul]
    exact Submodule.finsuppSum_mem _ _ _ _ (fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩))
  choose z hz using fun j => hcoord _ (hmemT j)
  have hcol : ∀ j k, bb₂ j (ι k) = ∑ s, zOm l (z j s) • bb₁ s k := by
    intro j k
    have := congrFun (hz j) k
    simpa [Finset.sum_apply] using this
  refine ⟨Matrix.of fun s j => z j s, ?_, ?_⟩
  · intro g
    ext i j
    have hA : ∀ k, (ρs k g).val * bb₂ j (ι k) =
        ∑ i, zOm l (((ρ₁ g).val * Matrix.of fun s j => z j s) i j) • bb₁ i k := by
      intro k
      have e := fun s => (hR₁ k).equi g s
      try simp only at e
      rw [hcol, Finset.mul_sum]
      simp_rw [Matrix.mul_smul, e]
      rw [dsum]
      simp [Matrix.mul_apply]
    have hB : ∀ k, (ρs k g).val * bb₂ j (ι k) =
        ∑ i, zOm l (((Matrix.of fun s j => z j s) * (ρ₂ g).val) i j) • bb₁ i k := by
      intro k
      rw [← hι k]
      have e := (hR₂ (ι k)).equi g j
      try simp only at e
      rw [e]
      simp_rw [hcol]
      rw [dsum]
      simp [Matrix.mul_apply]
    have key : (fun i => ((Matrix.of fun s j => z j s) * (ρ₂ g).val) i j) =
        fun i => ((ρ₁ g).val * Matrix.of fun s j => z j s) i j := by
      apply GlobalTheory.CovTrans.coord_inj hbb₁
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [← hB k, hA k]
    exact congrFun key i
  · intro i j
    have hsingle : ∑ s, zOm l ((Pi.single j 1 : Fin d₂ → ℤ_[l]) s) • bb₂ s = bb₂ j := by
      simp [Pi.single_apply]
    obtain ⟨w₂, hw₂⟩ := hC₂ (Pi.single j 1) (F j) (y j) (hy j) (by rw [hsingle]; exact hbb j)
    obtain ⟨w₁, hw₁⟩ := hC₁ (fun s => z j s) (F j) (y j ∘ ι) (hπL _ (hy j)) (by rw [← hz j, hπbb j])
    have hP₂ : P₂ *ᵥ Pi.single j 1 = fun i => P₂ i j := by
      funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hP₁ : P₁ *ᵥ (fun s => z j s) = fun i => (P₁ * Matrix.of fun s j => z j s) i j := by
      funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hP₂] at hw₂
    rw [hP₁] at hw₁
    have key : (fun i => (P₁ * Matrix.of fun s j => z j s) i j - P₂ i j) =
        fun i => (l : ℤ_[l]) ^ n * ((l : ℤ_[l]) ^ (N₁ - n) * w₁ i - (l : ℤ_[l]) ^ (N₂ - n) * w₂ i) := by
      apply GlobalTheory.CovTrans.coord_inj hb
      have hs : ∑ i, zOm l ((P₁ * Matrix.of fun s j => z j s) i j - P₂ i j) • b i =
          ∑ i, zOm l ((P₁ * Matrix.of fun s j => z j s) i j) • b i - ∑ i, zOm l (P₂ i j) • b i := by
        simp only [map_sub, sub_smul, Finset.sum_sub_distrib]
      rw [hs, hw₁, hw₂, add_sub_add_left_eq_sub]
      have e1 : (l : Om l) ^ N₁ = (l : Om l) ^ n * (l : Om l) ^ (N₁ - n) := by rw [← pow_add, Nat.add_sub_cancel' hn₁]
      have e2 : (l : Om l) ^ N₂ = (l : Om l) ^ n * (l : Om l) ^ (N₂ - n) := by rw [← pow_add, Nat.add_sub_cancel' hn₂]
      rw [e1, e2]
      simp only [Finset.smul_sum, smul_smul, map_mul, map_sub, map_pow, map_natCast, mul_sub, sub_smul,
        Finset.sum_sub_distrib, mul_assoc]
    have := congrFun key i
    rw [Matrix.sub_apply, this]
    exact Dvd.intro _ rfl

end GlobalTheory.CovTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvaluationConvergentSeriesBcris
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.BanachEval

open PowerSeries Filter GlobalTheory.HWL.Disc

section Letters

variable {O N : Type} [CommRing O] [CommRing N] {n : ℕ} [NeZero n] (f : LetA O n →+* N)

theorem sum_letE : ∑ i, f (letE i) = 1 := by
  rw [← map_sum, ← map_one f]
  exact congrArg f (Finset.univ_sum_single (1 : LetA O n))

theorem sum_letE_mul (x y : ZMod n → N) :
    ∑ i, f (letE i) * (x i * y i) = (∑ i, f (letE i) * x i) * ∑ i, f (letE i) * y i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · have : (letE i : LetA O n) * letE i = letE i := by
      ext1 j
      by_cases h : j = i <;> simp [letE, h]
    rw [mul_mul_mul_comm, ← map_mul, this]
  · intro j _ hj
    have : (letE i : LetA O n) * letE j = 0 := by
      ext1 k
      by_cases h : k = i
      · simp [letE, h, hj.symm]
      · simp [letE, h]
    rw [mul_mul_mul_comm, ← map_mul, this, map_zero, zero_mul]
  · simp

theorem sum_letE_const (a : LetA O n) : ∑ i, f (letE i) * f (fun _ => a i) = f a := by
  simp only [← map_mul]
  rw [← map_sum]
  congr 1
  ext1 j
  simp [letE, Pi.single_apply]

omit [NeZero n] in
theorem letφ_letE (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (i : ZMod n) : letφ φ₀ (letE (i - 1)) = letE i := by
  ext1 j
  change φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = _
  by_cases h : j = i <;> simp [letE, h]

omit [NeZero n] in
theorem letγ_letE (g : O⟦X⟧ →ₐ[O] O⟦X⟧) (i : ZMod n) : letγ g (letE i) = letE i := by
  ext1 j
  change g ((letE i : LetA O n) j) = _
  by_cases h : j = i <;> simp [letE, h]

end Letters

variable {l : ℕ} [Fact l.Prime]

theorem frob_root {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    WittVector.frobenius (WittVector.teichmuller l (AI.εroot (s + 1)) - 1) =
      WittVector.teichmuller l (AI.εroot s) - 1 := by
  rw [map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
    LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  rfl

theorem sc_map {LL : FinExt l} (a : (↥(OL LL))⟦X⟧) : SC (map (algebraMap ↥(OL LL) ↥LL.1) a) :=
  sc_of_le 0 fun k => by simpa using norm_integer_le_one (coeff k a)

theorem sc_log (LL : FinExt l) : SC (logS LL) := sc_lg (norm_natCast_inv_le LL)

theorem frob_injective {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (LL : FinExt l) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := ↥LL.1) P.φB.toLinearMap
    (GlobalTheory.Per.TiedField.tied_field l P AI T).2.2.2.1

theorem crisFrobenius_periodT_eq_prime_smul (P : LocPrime l) (K : FinExt l) : P.φB P.tB = (l : ℚ_[l]) • P.tB := by
  have h := (P.PD K).t_φ
  rwa [P.PD_φ, P.period_datum_t_eq, P.PD_p] at h

set_option maxHeartbeats 1000000 in

theorem exists_eval : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∃ J, IsEval I β J := by
  intro l _ P AI T K s LL hG Γ R I hW β hβ
  obtain ⟨N, _, _, c, b, κ, φ, γ, t, ⟨hκb, hφb, hκφ, hγb, hκγ, hκt⟩, hc, hb, hbo, hκc, ⟨hφ, hφc⟩, hγ, hs, hlog, hcl⟩ :=
    GlobalTheory.T.exists_banachModel_tensor_Acris l P AI T LL β hβ
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨by
    haveI := (P.PD K).finK₀
    exact Module.finrank_pos.ne'⟩
  let μ : ℕ → N := fun s => b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1))
  have hμ : ∀ s, Small (μ s) := hs
  have hc' : Bdd c := hc
  let f : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)) →+* N := b.comp I.io.toRingHom
  have hf : ∀ a, f a = b (I.io a) := fun _ => rfl
  have hfπ : f letπ = μ s := congrArg b I.io_π
  have hint : ∀ a, ev c (μ s) (map (algebraMap ↥(OL LL) ↥LL.1) a) = f (fun _ => a) := fun a =>
    ev_map (algebraMap ↥(OL LL) ↥LL.1) (hμ s) hc' (f.comp (Pi.constRingHom _ _))
      (fun o => (congrArg b (I.io.commutes o)).trans (by exact hbo o)) hfπ (fun _ => hb _) a (sc_map a)
  have hfφ : ∀ a, f (letφ R.φ₀ a) = φ (f a) := (GlobalTheory.T.wachInclusionLayer_io_commutes_frobenius_galois l P AI K s LL Γ R I N b (φ.comp b)).1 hφb
  have hfγ : ∀ (g : ↥(GK K)) a, f (letγ (R.γ₀ (Γ.resΓ g)) a) = γ g (f a) := fun g =>
    (GlobalTheory.T.wachInclusionLayer_io_commutes_frobenius_galois l P AI K s LL Γ R I N b ((γ g).comp b)).2 g (hγb g)
  have hsub : ∀ (ψ : N →+* N) (y : (↥(OL LL))⟦X⟧), Continuous ψ → (∀ x, ψ (c x) = c x) → constantCoeff y = 0 →
      f (fun _ => y) = ψ (μ s) → ∀ a, Conv a →
      ev c (μ s) (subst (map (algebraMap ↥(OL LL) ↥LL.1) y) a) = ψ (ev c (μ s) a) := by
    intro ψ y h1 h2 h3 h4 a ha
    have ha' := (conv_iff_sc a).1 ha
    have h5 := hasSum_subst hc' (hμ s) (y := map (algebraMap ↥(OL LL) ↥LL.1) y)
      (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h3, map_zero])
      (fun k => by simpa using norm_integer_le_one (coeff k y)) ha'
    rw [hint, h4] at h5
    exact h5.unique (hasSum_map hc' (hμ s) ha' ψ h1 h2)
  refine ⟨fun a => κ (∑ i, f (letE i) * ev c (μ s) (a i)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a a' ha ha'
    rw [← map_add, ← Finset.sum_add_distrib]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Pi.add_apply, ev_add hc' (hμ s) ((conv_iff_sc _).1 (ha i)) ((conv_iff_sc _).1 (ha' i)), mul_add]
  · intro a a' ha ha'
    rw [← map_mul, ← sum_letE_mul]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Pi.mul_apply, ev_mul hc' (hμ s) ((conv_iff_sc _).1 (ha i)) ((conv_iff_sc _).1 (ha' i))]
  · intro x a ha
    have e : algebraMap ↥LL.1 (↥LL.1 ⊗[ℚ_[l]] P.R.B) x = κ (c x) := (hκc x).symm
    rw [Algebra.smul_def x (κ _), e, ← map_mul, Finset.mul_sum]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Pi.smul_apply, ev_C_mul hc' (hμ s) x ((conv_iff_sc _).1 (ha i)), mul_left_comm]
  · intro a
    rw [← hκb, ← hf, ← sum_letE_const f a]
    exact congrArg κ (Finset.sum_congr rfl fun i _ => congrArg _ (hint (a i)))
  · intro a ha
    have hy : R.φ₀ X = (1 + X) ^ l - 1 := by rw [R.φ₀_X, R.q₀_def, P.PD_p]
    have hy' : ((1 + X) ^ l - 1 : (↥LL.1)⟦X⟧) = map (algebraMap ↥(OL LL) ↥LL.1) (R.φ₀ X) := by
      simp [hy]
    rw [← hκφ, map_sum φ, ← Equiv.sum_comp (Equiv.subRight (1 : ZMod _))
      (fun i => φ (f (letE i) * ev c (μ s) (a i)))]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Equiv.subRight_apply, map_mul, ← hfφ, letφ_letE, hy',
      hsub φ _ hφ hφc (by simp [hy]) (hfπ ▸ hfφ letπ) _ (ha _)]
  · intro g a ha
    rw [← hκγ, map_sum (γ g)]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, ← hfγ, letγ_letE,
      hsub (γ g) _ (hγ g).1 (hγ g).2 (R.γ₀_X _).1 (hfπ ▸ hfγ g letπ) _ (ha _)]
  · rw [← Finset.sum_mul, sum_letE, one_mul]
    have key : ∀ k : ℕ, κ (ev c (μ k) (logS LL)) = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] ((((l : ℚ_[l]) ^ k)⁻¹) • P.tB) := by
      intro k
      induction k with
      | zero =>
        rw [tendsto_nhds_unique (hasSum_ev hc' (hμ 0) (sc_log LL)).tendsto_sum_nat hlog, hκt]
        simp
      | succ k ih =>
        have h1 := hasSum_map hc' (hμ (k + 1)) (sc_log LL) φ hφ hφc
        have h2 : φ (μ (k + 1)) = μ k := (hφb _ _).trans (by rw [frob_root])
        rw [h2] at h1
        apply frob_injective T LL
        have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
        rw [← hκφ, h1.unique (hasSum_ev hc' (hμ k) (sc_log LL)), ih, Algebra.TensorProduct.map_tmul, map_smul,
          crisFrobenius_periodT_eq_prime_smul P K, smul_smul, map_one, pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hl, mul_one]
    exact key s
  · intro i ζ ι hι hζ a ha e he m
    let π : N →+* P.R.BdR := (Algebra.TensorProduct.productMap ι P.ιB).toRingHom.comp κ
    have hπ : ∀ x, π x = Algebra.TensorProduct.productMap ι P.ιB (κ x) := fun _ => rfl
    have hπc : ∀ x, π (c x) = ι x := fun x => by rw [hπ, hκc]; simp
    have hπE : ∀ j, π (f (letE j)) = if i = j then 1 else 0 := fun j => by
      have h := GlobalTheory.T.productMap_tensorAinfToBcris_wachInclusion_constants l P AI T K s LL hG Γ R I hW β hβ i ι hι (Pi.single j 1)
      have e1 : (fun k => C ((Pi.single j 1 : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) k)) =
          (letE j : LetA ↥(OL LL) _) := by
        ext1 k
        by_cases h : k = j <;> simp [letE, h]
      rw [e1] at h
      rw [hπ, hf, hκb, h]
      by_cases h : i = j <;> simp [h]
    have hπμ : π (μ s) = P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1)) := by
      rw [hπ, hκb, hβ]
      simp
    let τ : N := c (algebraMap ℚ_[l] ↥LL.1 ((l : ℚ_[l]) ^ s)⁻¹) * t
    have hπτ : π τ = (((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB := by
      rw [map_mul, hπc, AlgHom.commutes, hπ, hκt, Algebra.smul_def]
      simp
    have hev : ∀ x : ℕ → ↥LL.1, π (∑ k ∈ Finset.range m, c (x k) * τ ^ k) =
        ∑ k ∈ Finset.range m, ι (x k) * ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k := fun x => by
      simp only [map_sum, map_mul π, map_pow π, hπc, hπτ]
    have hlim : Tendsto (fun M : ℕ => Polynomial.eval₂ c (μ s) (trunc M (a i)) - ∑ k ∈ Finset.range m,
        c (coeff k (Polynomial.aeval (C ζ * exp ↥LL.1 - 1) (trunc M (a i)))) * τ ^ k) atTop
        (nhds (ev c (μ s) (a i) - ∑ k ∈ Finset.range m, c (coeff k e) * τ ^ k)) := by
      refine (tendsto_ev hc' (hμ s) ((conv_iff_sc _).1 (ha i))).sub (tendsto_finset_sum _ fun k _ => ?_)
      exact ((hc'.continuous.tendsto _).comp (tendsto_subtype_rng.2 (he k))).mul_const _
    have hmem := (hcl ι m).mem_of_tendsto hlim (Eventually.of_forall fun M => by
      have h := GlobalTheory.T.polynomial_teichmullerRoot_taylor_modFil l P AI T LL s ζ ι hζ (trunc M (a i)) m
      rw [Set.mem_setOf_eq, ← hπ, map_sub, hev, Polynomial.hom_eval₂, hπμ, show π.comp c = (ι : ↥LL.1 →+* P.R.BdR) from RingHom.ext hπc]
      exact h)
    rw [Set.mem_setOf_eq, ← hπ, map_sub, hev] at hmem
    have e2 : π (∑ j, f (letE j) * ev c (μ s) (a j)) = π (ev c (μ s) (a i)) := by
      simp [map_sum, map_mul π, hπE]
    rw [← hπ, e2]
    exact (Set.ext_iff.1 (P.PD_Fil _ K m) _).1 hmem

end GlobalTheory.HWL.BanachEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveMapIntegersClToWittQuotient
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem dvd_pow_of_ne_zero_untilt (l : ℕ) [Fact l.Prime] (y : Formalism.Per.OC l) (hy : y ≠ 0) :
    ∃ n : ℕ, y ∣ (l : Formalism.Per.OC l) ^ n := by
  have hy' : (y : ℂ_[l]) ≠ 0 := fun h => hy (Subtype.ext h)
  have hpos : 0 < ‖(y : ℂ_[l])‖ := norm_pos_iff.2 hy'
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (GlobalTheory.RingBasics.norm_p_lt (p := l))
  refine ⟨n, ⟨(l : ℂ_[l]) ^ n / y, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div, norm_pow, div_le_one hpos]
    exact hn.le
  · push_cast
    exact (mul_div_cancel₀ _ hy').symm

theorem constantCoeff_natCast_untilt (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [CharP O l] :
    WittVector.constantCoeff ((l : ℕ) : WittVector l O) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

theorem exists_untilt_map : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∃ θ' : OC l →+* (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}), (∀ a : Ainf l, θ' (Per.θ l a) = Ideal.Quotient.mk _ (WittVector.map ψ a)) ∧ Function.Injective θ' ∧ IsDomain (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) ∧ ∀ a : WittVector l O, ((l : ℕ) : WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) ∣ Ideal.Quotient.mk _ a → ψ bk.flat ^ bk.Ep.natDegree ∣ a.coeff 0 := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc
  obtain ⟨w, hw, hE⟩ := GlobalTheory.T.breuilKisin_eisenstein_image_teichmuller_pow l K bk O ψ hu
  obtain ⟨hp, hl⟩ := GlobalTheory.T.teichmullerDistinguished_span_isPrime_and_not_mem l O _ h0 hu hc _ w _ bk.deg_pos hw hE
  have hdom : IsDomain (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) :=
    Ideal.Quotient.isDomain _
  have hker : RingHom.ker (Per.θ l) ≤ RingHom.ker ((Ideal.Quotient.mk
      (Ideal.span {WittVector.map ψ (bk.ev bk.E)})).comp (WittVector.map ψ)) := by
    rw [← bk.span_ev, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  refine ⟨(Per.θ l).liftOfSurjective (theta_onto l) ⟨_, hker⟩, fun a => ?_, ?_, hdom, ?_⟩
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ a
  · rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hne
    obtain ⟨n, z, hz⟩ := dvd_pow_of_ne_zero_untilt l y hne
    have h := congrArg ((Per.θ l).liftOfSurjective (theta_onto l) ⟨_, hker⟩) hz
    rw [map_mul, hy, zero_mul, map_pow, map_natCast] at h
    have h2 := eq_zero_of_pow_eq_zero h
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem] at h2
    exact hl h2
  · rintro a ⟨b, hb⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hb
    obtain ⟨c, hc⟩ := hb
    have h := congrArg WittVector.constantCoeff hc
    rw [hE, map_mul, map_add, map_mul, map_sub, map_mul, constantCoeff_natCast_untilt, zero_mul, zero_mul,
      add_zero, sub_zero, map_pow, WittVector.constantCoeff_apply (WittVector.teichmuller _ _),
      WittVector.teichmuller_coeff_zero] at h
    exact ⟨_, h.symm.trans (mul_comm _ _)⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveRootsOfNcardRootSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem exists_injective_roots_of_ncard_rootSet {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Algebra A O] (t : ℕ) (P : Polynomial A) (α : Fin t → FractionRing O)
    (hinj : Function.Injective (algebraMap A O))
    (hcard : ((P.map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t)
    (hP : P.map ((toFr O).comp (algebraMap A O)) = ∏ c, (Polynomial.X - Polynomial.C (α c))) :
    ∃ β : Fin t → O, Function.Injective β ∧ P.map (algebraMap A O) = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  classical
  have hO : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
  have hA : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective _ _
  set g : A →+* FractionRing O := (algebraMap O (FractionRing O)).comp (algebraMap A O) with hg
  have hgi : Function.Injective g := hO.comp hinj
  change P.map g = _ at hP
  change ((P.map (algebraMap A (FractionRing A))).rootSet _).ncard = t at hcard
  have hmon' : (P.map g).Monic := by
    rw [hP]; exact Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)
  have hmon : P.Monic := Polynomial.monic_of_injective hgi hmon'
  have hdeg : P.natDegree = t := by
    rw [← hmon.natDegree_map g, hP, Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)]
    simp
  have hsep : (P.map (algebraMap A (FractionRing A))).Separable := by
    have hne : P.map (algebraMap A (FractionRing A)) ≠ 0 := (hmon.map _).ne_zero
    rw [← Polynomial.card_rootSet_eq_natDegree_iff_of_splits (K := AlgebraicClosure (FractionRing A)) hne (IsAlgClosed.splits _), hmon.natDegree_map, hdeg, ← hcard, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  obtain ⟨φ, hφ⟩ : ∃ φ : FractionRing A →+* FractionRing O, φ.comp (algebraMap A (FractionRing A)) = g :=
    ⟨IsFractionRing.lift hgi, RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := FractionRing A) hgi a⟩
  have hsep2 : (P.map g).Separable := by
    rw [← hφ, ← Polynomial.map_map]; exact hsep.map
  have hα : Function.Injective α := by
    rw [hP] at hsep2
    exact Polynomial.separable_prod_X_sub_C_iff.mp hsep2
  have hint : ∀ c, ∃ b : O, algebraMap O (FractionRing O) b = α c := by
    intro c
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    refine ⟨P.map (algebraMap A O), hmon.map _, ?_⟩
    rw [← Polynomial.eval_map, Polynomial.map_map, ← hg, hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) (by simp)
  choose β hβ using hint
  refine ⟨β, fun c d h => hα (by rw [← hβ, ← hβ, h]), ?_⟩
  apply Polynomial.map_injective _ hO
  rw [Polynomial.map_map, ← hg, hP, Polynomial.map_prod]
  simp [hβ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsAdicCompletionMapOfFgStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isAdicCompletionMap_of_fg : ∀ (L : Type) [CommRing L] (J : Ideal L), J.FG → ∃ (Q : Type) (_ : CommRing Q) (i : L →+* Q), IsCompl i J := by
  first | exact @GlobalTheory.BSP.isCompl_exists | exact GlobalTheory.BSP.isCompl_exists | (intros; apply GlobalTheory.BSP.isCompl_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsSemisimplificationOfStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semisimplification' : ∀ {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Γ V), ∃ s : Representation k Γ V, GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ := by
  first | exact @GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf | exact GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf | (intros; apply GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKernelLatticeEquivariantModPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernel_lattice_equivariant_modPow : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (d d' n : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (f : Matrix (Fin d') (Fin d') (ℤ_[l])) (ρ'' : Γ →* GL (Fin d') ℤ_[l]), f.det ≠ 0 ∧ (∀ g, f * (ρ'' g).val = (ρ' g).val * f) ∧ ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w := by
  first | exact @GlobalTheory.KerLat.exists_kernel_lattice | exact GlobalTheory.KerLat.exists_kernel_lattice | (intros; apply GlobalTheory.KerLat.exists_kernel_lattice; all_goals assumption)
end

