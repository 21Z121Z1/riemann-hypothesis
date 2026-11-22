import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirLtAddRootNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirLtAddRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1370
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartanEigen_orthonormalFrame_exists : GlobalTheory.RealLift.FrameEx := by
  first | exact @GlobalTheory.RealLift.frameEx_holds | exact GlobalTheory.RealLift.frameEx_holds | (intros; apply GlobalTheory.RealLift.frameEx_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirGlFactorEmbeddingMemCapelliAlgebra
section
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CasCentre

open Finset Polynomial

variable {A : Type} [Ring A] [Algebra ℂ A]

def pS {n : ℕ} (s : Finset (Fin n)) : ℂ[X] := ∏ l ∈ s, (X - C ((l : ℕ) : ℂ))

theorem natDegree_pS {n : ℕ} (s : Finset (Fin n)) : (pS s).natDegree = s.card :=
  natDegree_finsetProd_X_sub_C_eq_card _ _

theorem prod_eq_sum {n : ℕ} (s : Finset (Fin n)) (u : ℂ) :
    ∏ l ∈ s, (u - (l : ℂ)) = ∑ k ∈ range (n + 1), u ^ k * (pS s).coeff k := by
  have h1 : (pS s).eval u = ∏ l ∈ s, (u - (l : ℂ)) := by simp [pS, eval_prod]
  have h2 : (pS s).natDegree < n + 1 := by
    rw [natDegree_pS]; have := Finset.card_le_univ s; simp at this; omega
  rw [← h1, eval_eq_sum_range' h2]
  exact sum_congr rfl fun k _ => mul_comm _ _

theorem coeff_pS_top {n : ℕ} (s : Finset (Fin n)) : (pS s).coeff s.card = 1 := by
  have hm : (pS s).Monic := monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
  rw [← natDegree_pS]; exact hm.coeff_natDegree

theorem coeff_pS_next {n : ℕ} (s : Finset (Fin n)) (hs : 0 < s.card) :
    (pS s).coeff (s.card - 1) = -∑ l ∈ s, (l : ℂ) := by
  have h := prod_X_sub_C_nextCoeff (s := s) (fun l : Fin n => ((l : ℕ) : ℂ))
  rw [nextCoeff_of_natDegree_pos (by rw [natDegree_finsetProd_X_sub_C_eq_card]; exact hs),
    natDegree_finsetProd_X_sub_C_eq_card] at h
  exact h

theorem sum_fin_cast (n : ℕ) : 2 * ∑ l : Fin n, (l : ℂ) = (n : ℂ) * ((n : ℂ) - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Finset.sum_range_id_mul_two n
  rw [Fin.sum_univ_eq_sum_range (fun l => ((l : ℕ) : ℂ)) n]
  have h' : ((∑ i ∈ range n, i : ℕ) : ℂ) * 2 = ((n * (n - 1) : ℕ) : ℂ) := by exact_mod_cast h
  rw [Nat.cast_mul, Nat.cast_sub (by omega)] at h'
  push_cast at h'
  linear_combination h'

theorem cas_mem_of_qdet_mem {n : ℕ} (X : Fin n → Fin n → A) (hX : Formalism.REAL.GlRel X) (S : Subalgebra ℂ A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet X u ∈ S) : Formalism.REAL.Cas X ∈ S := by
  classical
  have hT : ∑ i, X i i ∈ S := GlobalTheory.CapTrace.trace_mem_of_qdet_mem X S h
  rcases lt_or_ge n 2 with hn | hn
  · have e : Formalism.REAL.Cas X = (∑ i, X i i) * (∑ i, X i i) := by
      interval_cases n <;> simp [Formalism.REAL.Cas]
    rw [e]; exact S.mul_mem hT hT
  obtain ⟨Rm, hR⟩ := GlobalTheory.qdet_top_three_orders A n X
  let Cf : ℕ → A := fun k => (pS (univ : Finset (Fin n))).coeff k • (1 : A) +
    ∑ i, (pS (univ.erase i)).coeff k • X i i +
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (pS ((univ.erase i).erase j)).coeff k • (X i i * X j j - X j i * X i j) +
    (if k < n - 2 then Rm k else 0)
  have hexp : ∀ u : ℂ, Formalism.REAL.qdet X u = ∑ k ∈ range (n + 1), u ^ k • Cf k := by
    intro u
    have hRm : ∑ k ∈ range (n + 1), u ^ k • (if k < n - 2 then Rm k else 0) = ∑ d ∈ range (n - 2), u ^ d • Rm d := by
      simp only [smul_ite, smul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext k; simp only [mem_filter, mem_range]; omega
    rw [hR u]
    simp only [Cf, smul_add, sum_add_distrib, hRm, prod_eq_sum, sum_smul, smul_sum, smul_smul]
    congr 1
    congr 1
    · congr 1
      exact sum_comm
    · rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      exact sum_comm
  have hmem : Cf (n - 2) ∈ S :=
    GlobalTheory.CapTrace.coeff_mem (Subalgebra.toSubmodule S) n Cf (fun u => by rw [← hexp]; exact h u) (n - 2) (by omega)
  have hc2 : ∀ i : Fin n, ∀ j ∈ univ.filter (fun j => i < j), (pS ((univ.erase i).erase j)).coeff (n - 2) = 1 := by
    intro i j hj
    have hij : j ≠ i := (mem_filter.1 hj).2.ne'
    have hc : ((univ.erase i).erase j).card = n - 2 := by
      rw [card_erase_of_mem (mem_erase.2 ⟨hij, mem_univ _⟩), card_erase_of_mem (mem_univ _), card_univ,
        Fintype.card_fin]; omega
    rw [← hc]; exact coeff_pS_top _
  have hc1 : ∀ i : Fin n, (pS (univ.erase i)).coeff (n - 2) = -∑ l ∈ univ.erase i, (l : ℂ) := by
    intro i
    have hc : (univ.erase i).card = n - 1 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have := coeff_pS_next (univ.erase i) (by omega)
    rw [hc, show n - 1 - 1 = n - 2 by omega] at this
    exact this
  set c := (pS (univ : Finset (Fin n))).coeff (n - 2)
  have hC : Cf (n - 2) = c • (1 : A) + ∑ i, (pS (univ.erase i)).coeff (n - 2) • X i i +
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (X i i * X j j - X j i * X i j) := by
    simp only [Cf, lt_irrefl, if_false, add_zero]
    congr 1
    exact sum_congr rfl fun i _ => sum_congr rfl fun j hj => by rw [hc2 i j hj, one_smul]
  have h3 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • X i i + (2 : ℂ) • ∑ i, (pS (univ.erase i)).coeff (n - 2) • X i i
      = -(((n : ℂ) - 1) ^ 2) • ∑ i, X i i := by
    rw [smul_sum, smul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← add_smul, hc1, sum_erase_eq_sub (mem_univ _)]
    congr 1
    have := sum_fin_cast n
    linear_combination (-1 : ℂ) * this
  have h1 := GlobalTheory.CapelliCasimir.sq_sub_cas X hX
  have key : Formalism.REAL.Cas X = (∑ i, X i i) * (∑ i, X i i) - (2 : ℂ) • Cf (n - 2) + (2 * c) • (1 : A)
      - (((n : ℂ) - 1) ^ 2) • ∑ i, X i i := by
    linear_combination (norm := module) (-1 : ℂ) • h1 + (2 : ℂ) • hC + h3
  rw [key]
  exact S.sub_mem (S.add_mem (S.sub_mem (S.mul_mem hT hT) (S.smul_mem hmem _)) (S.smul_mem (S.one_mem) _))
    (S.smul_mem hT _)

theorem cas_Eop_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  intro E _ _ _ a τ
  refine cas_mem_of_qdet_mem (Eop τ) (glRel_Eop τ) (Zalg E a) fun u => ?_
  have e : Formalism.REAL.qdet (Eop (a := a) τ) u = cap τ (u - ((a : ℂ) - 1) / 2) := by
    rw [cap]; congr 1; ring
  rw [e]
  exact Algebra.subset_adjoin ⟨τ, _, rfl⟩

end GlobalTheory.CasCentre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirLtAddRootNegStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_lt_add_root_neg : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P' Q' R S, GlobalTheory.RealLift.IsHarmVec (-((κ : ℚ) / 2)) (fun c => GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b c - (κ : ℚ) / 2) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := by
  first | exact @GlobalTheory.SteepSmall.steep_small | exact GlobalTheory.SteepSmall.steep_small | (intros; apply GlobalTheory.SteepSmall.steep_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirLtAddRootStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_lt_add_root : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := by
  first | exact @GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot | exact GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot | (intros; apply GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_at_uniformizer_not_root_of_unity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) := by
  first | exact @GlobalTheory.NuGood.not_root_of_unity | exact GlobalTheory.NuGood.not_root_of_unity | (intros; apply GlobalTheory.NuGood.not_root_of_unity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffDetInvValuationBoundedOfIsCompactGLStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_coeff_det_inv_valuation_bounded_of_isCompact_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (C : Set (GLw n w)), IsCompact C → ∃ γ : WithZero (Multiplicative ℤ), ∀ y ∈ C, (∀ k, Valued.v (y.val.charpoly.coeff k) ≤ γ) ∧ Valued.v (y⁻¹ : GLw n w).val.det ≤ γ := by
  first | exact @GlobalTheory.BCT.charpoly_det_bounded_of_isCompact | exact GlobalTheory.BCT.charpoly_det_bounded_of_isCompact | (intros; apply GlobalTheory.BCT.charpoly_det_bounded_of_isCompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulIntersectionNumberLeSectionDimStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.choose_mul_intersectionNumber_le_sectionDim : ∀ (k : Type) [Field k] [Infinite k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k Y) → ∀ (L : LB Y) (hL : L.IsLB) (N : ℕ) (b : Fin N → L.Sec), (∀ y : Y, ∃ i, y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (b i)) → ∀ (d : ℕ) (F : Y.Modules) [IsFiniteQC F], suppDim F ≤ d → ∀ (j₀ : ℤ), VanishFrom L F j₀ → ∀ m : ℕ, (m.choose d : ℤ) * GlobalTheory.interNum k F (fun _ : Fin d => L) ≤ GlobalTheory.hdim k (GlobalTheory.twistZ F L (j₀ + m)) 0 := by
  first | exact @GlobalTheory.HSCore.choose_mul_interNum_le_hdim | exact GlobalTheory.HSCore.choose_mul_interNum_le_hdim | (intros; apply GlobalTheory.HSCore.choose_mul_interNum_le_hdim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormZeroSetExtensionFieldIffCommonConeZero
section
set_option autoImplicit false

noncomputable section

open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.HSChoice

namespace GlobalTheory.ChowZeroExt

def incIdeal {F : Type} [Field F] (B : ℕ) {N : ℕ} (I : Ideal (MvPolynomial (Fin N) F)) :
    Ideal (MvPolynomial ((Fin B × Fin N) ⊕ (Fin N ⊕ Fin N)) F) :=
  Ideal.span ((rename (fun j => Sum.inr (Sum.inl j)) '' (I : Set (MvPolynomial (Fin N) F))) ∪
    (Set.range (fun i : Fin B => ∑ j, X (Sum.inl (i, j)) * X (Sum.inr (Sum.inl j))) ∪
      {∑ j, X (Sum.inr (Sum.inr j)) * X (Sum.inr (Sum.inl j)) - 1}))

theorem forall_span_iff {F Ω ι : Type} [Field F] [Field Ω] [Algebra F Ω] (S : Set (MvPolynomial ι F))
    (x : ι → Ω) : (∀ g ∈ Ideal.span S, aeval x g = 0) ↔ ∀ g ∈ S, aeval x g = 0 := by
  refine ⟨fun h g hg => h g (Ideal.subset_span hg), fun h g hg => ?_⟩
  have : Ideal.span S ≤ RingHom.ker (aeval x : MvPolynomial ι F →ₐ[F] Ω) :=
    Ideal.span_le.2 fun g hg => h g hg
  exact this hg

theorem forall_incIdeal_iff {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {B N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) F)) (x : (Fin B × Fin N) ⊕ (Fin N ⊕ Fin N) → Ω) :
    (∀ g ∈ incIdeal B I, aeval x g = 0) ↔
      (∀ g ∈ I, aeval (fun j => x (Sum.inr (Sum.inl j))) g = 0) ∧
      (∀ i, ∑ j, x (Sum.inl (i, j)) * x (Sum.inr (Sum.inl j)) = 0) ∧
      ∑ j, x (Sum.inr (Sum.inr j)) * x (Sum.inr (Sum.inl j)) = 1 := by
  rw [incIdeal, forall_span_iff]
  constructor
  · intro h
    refine ⟨fun g hg => ?_, fun i => ?_, ?_⟩
    · have := h _ (Or.inl ⟨g, hg, rfl⟩)
      rwa [aeval_rename] at this
    · simpa using h _ (Or.inr (Or.inl ⟨i, rfl⟩))
    · simpa [sub_eq_zero] using h _ (Or.inr (Or.inr rfl))
  · rintro ⟨h1, h2, h3⟩ g (⟨g, hg, rfl⟩ | ⟨i, rfl⟩ | rfl)
    · rw [aeval_rename]
      exact h1 g hg
    · simpa using h2 i
    · simpa [sub_eq_zero] using h3

theorem exists_dual {Ω : Type} [Field Ω] {N : ℕ} {y : Fin N → Ω} (hy : y ≠ 0) :
    ∃ z : Fin N → Ω, ∑ j, z j * y j = 1 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  refine ⟨Pi.single j (y j)⁻¹, ?_⟩
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
    exact inv_mul_cancel₀ hj
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem ne_zero_of_dual {Ω : Type} [Field Ω] {N : ℕ} {y z : Fin N → Ω} (h : ∑ j, z j * y j = 1) :
    y ≠ 0 := by
  rintro rfl
  simp at h

variable {F : Type} [Field F] {D N d : ℕ} {I : Ideal (MvPolynomial (Fin N) F)}
  {f : MvPolynomial (Fin (D + 1) × Fin N) F}

theorem aeval_eq_zero_of_common_zero (hf : IsChowForm I D d f) {Ω : Type} [Field Ω] [Algebra F Ω]
    (u : Fin (D + 1) × Fin N → Ω) (y : Fin N → Ω) (hy : y ≠ 0) (hI : ∀ g ∈ I, aeval y g = 0)
    (hu : ∀ i, ∑ j, u (i, j) * y j = 0) : aeval u f = 0 := by
  obtain ⟨z, hz⟩ := exists_dual hy
  have key := GlobalTheory.T.vanish_transfer_of_vanish_over_algebraicClosure F _ (incIdeal (D + 1) I) (rename Sum.inl f) (fun x hx => by
    obtain ⟨h1, h2, h3⟩ := (forall_incIdeal_iff I x).1 hx
    rw [aeval_rename]
    exact (hf.zero_iff _).2 ⟨_, ne_zero_of_dual h3, h1, h2⟩) Ω (Sum.elim u (Sum.elim y z))
    ((forall_incIdeal_iff I _).2 ⟨hI, hu, hz⟩)
  rwa [aeval_rename] at key

theorem exists_common_zero (hf : IsChowForm I D d f) {Ω : Type} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (u : Fin (D + 1) × Fin N → Ω) (hu : aeval u f = 0) :
    ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧ ∀ i, ∑ j, u (i, j) * y j = 0 := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.polynomial_solvability_transfer_algClosed_fields F _ _ (Ideal.span {f}) (incIdeal (D + 1) I) (fun v hv => by
    obtain ⟨y, hy, h1, h2⟩ := (hf.zero_iff v).1 (hv f (Ideal.subset_span rfl))
    obtain ⟨z, hz⟩ := exists_dual hy
    exact ⟨Sum.elim y z, (forall_incIdeal_iff I _).2 ⟨h1, h2, hz⟩⟩) Ω u
    ((forall_span_iff _ _).2 (by rintro g rfl; exact hu))
  obtain ⟨h1, h2, h3⟩ := (forall_incIdeal_iff I _).1 hw
  exact ⟨_, ne_zero_of_dual h3, h1, h2⟩

theorem forall_join_iff {Ω : Type} [Field Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω) :
    (∀ i, ∑ j, join s ξ (i, j) * y j = 0) ↔ (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0 := by
  rw [Fin.forall_fin_succ']
  simp [join]

theorem zero_set_ext : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F))
    (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsChowForm I D d f →
    (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω), y ≠ 0 →
      (∀ g ∈ I, aeval y g = 0) → (∀ i, ∑ j, s i j * y j = 0) → ∑ j, ξ j * y j = 0 →
      aeval (join s ξ) f = 0) ∧
    (∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (s : Fin D → Fin N → Ω) (ξ : Fin N → Ω),
      aeval (join s ξ) f = 0 → ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧
        (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0) := by
  intro F _ _ D N d I f hf
  refine ⟨fun Ω _ _ s ξ y hy hI hs hξ => ?_, fun Ω _ _ _ s ξ h => ?_⟩
  · exact aeval_eq_zero_of_common_zero hf _ y hy hI ((forall_join_iff s ξ y).2 ⟨hs, hξ⟩)
  · obtain ⟨y, hy, h1, h2⟩ := exists_common_zero hf _ h
    exact ⟨y, hy, h1, (forall_join_iff s ξ y).1 h2⟩

end GlobalTheory.ChowZeroExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystallineStatement
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_galois_representation_crystalline : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.HeckeLAdicCharacter →
  GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.LocalLanglandsGL →
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
    ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
    ∀ (f : ℂ) (J : (E →+* Qbar l) → Multiset ℤ),
      (∀ τ, (J τ).map (fun k : ℤ => (k : ℂ)) = (m (ι.toRingHom.comp τ)).map (fun z => f - z)) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧
      ((∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
          P.IsLocComp w σ ∧ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w a)) → GlobalTheory.ExpFrame.CrysWith r J) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), P.IsLocComp w σ → ∀ S : Multiset ℂˣ,
          GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w →
            IsFrob (F := E) B (normV w) g →
            (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
              Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ f))).prod := by
  first | exact @GlobalTheory.CsdTwistGal.exists_galRep_csd_twist | exact GlobalTheory.CsdTwistGal.exists_galRep_csd_twist | (intros; apply GlobalTheory.CsdTwistGal.exists_galRep_csd_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffLinearSubstColumnMemIntegralLattice
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.CoeffInt

theorem word_col {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N n t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (w : Matrix (Fin N) (Fin n) K) (g : Fin t → Fin n) :
    word mul (fun i => w.col (g i)) =
      ∑ e : Fin t → Fin N, (∏ i, w (e i) (g i)) • word mul (fun i => Pi.single (e i) 1) := by
  let Φ := (MultilinearMap.mkPiAlgebraFin K t (Module.End K A)).compLinearMap (fun _ => mul)
  have hΦ : ∀ u : Fin t → Fin N → K, word mul u = Φ u := by
    intro u; simp [Φ, word, MultilinearMap.mkPiAlgebraFin_apply]
  have hcol : ∀ i, w.col (g i) = ∑ j, w j (g i) • (Pi.single j 1 : Fin N → K) := by
    intro i; funext k; simp [Matrix.col, Finset.sum_apply, Pi.single_apply]
  rw [hΦ]
  simp_rw [hcol]
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MultilinearMap.map_smul_univ, hΦ]

theorem linSubst_coordP {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N n B t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (w : Matrix (Fin N) (Fin n) K) (c : A →ₗ[K] K)
    (β : Fin t → Fin B) (x : A) :
    linSubst w (coordP mul c β x) =
      ∑ g : Fin t → Fin n, C (c (word mul (fun i => w.col (g i)) x)) *
        ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K) := by
  rw [show (∑ g : Fin t → Fin n, C (c (word mul (fun i => w.col (g i)) x)) *
        ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K)) =
      ∑ g : Fin t → Fin n, ∑ e : Fin t → Fin N, C (c (word mul (fun i => Pi.single (e i) 1) x)) *
        ((∏ i, C (w (e i) (g i))) * ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K)) from ?_]
  · simp only [linSubst, coordP, map_sum, map_mul, aeval_C, map_prod, aeval_X, algebraMap_eq]
    simp_rw [Fintype.prod_sum, Finset.mul_sum, ← Finset.prod_mul_distrib]
    exact Finset.sum_comm
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [word_col, LinearMap.sum_apply, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, ← map_prod, map_mul]
    ring

theorem prod_X_monomial {σ K : Type} [Field K] {t : ℕ} (f : Fin t → σ) :
    ∃ s, (∏ i, (X (f i) : MvPolynomial σ K)) = monomial s 1 := by
  refine Finset.prod_induction _ (fun q => ∃ s, q = monomial s 1) ?_ ?_ ?_
  · rintro _ _ ⟨s, rfl⟩ ⟨s', rfl⟩; exact ⟨s + s', by rw [monomial_mul, one_mul]⟩
  · exact ⟨0, by simp⟩
  · intro i _; exact ⟨_, rfl⟩

end GlobalTheory.HSShort.CoeffInt

open GlobalTheory.HSShort.CoeffInt in

theorem GlobalTheory.HSShort.colCoeff_mem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ κ : S.Col, κ.x ∈ S.M κ.j → ∀ m, ∑ i, coeff m (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) • b i ∈ S.M S.T := by
  intro F A _ _ _ _ _ _ S hS d b c hco κ hx m
  obtain ⟨-, hM⟩ := GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice F A S hS κ.j κ.t (le_of_eq κ.add)
  have tr : ∀ j', j' = S.T → ∀ y' ∈ S.M j', ∃ y ∈ S.M S.T, (y : A) = (y' : A) := by
    rintro j' rfl y' hy'; exact ⟨y', hy', rfl⟩
  have key : ∀ g : Fin κ.t → Fin S.n, ∃ y ∈ S.M S.T,
      (y : A) = word S.mul (fun i => S.w.col (g i)) (κ.x : A) := by
    intro g
    obtain ⟨y, hy, hyeq⟩ := hM g κ.x hx
    obtain ⟨z, hz, hzeq⟩ := tr _ κ.add y hy
    exact ⟨z, hz, hzeq.trans hyeq⟩
  choose Y hY hYeq using key
  choose s hs using fun g : Fin κ.t → Fin S.n =>
    prod_X_monomial (K := F) (fun i => (κ.β i, g i))
  have hcoef : ∀ i, coeff m (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) =
      ∑ g, b.repr (Y g) i * (if s g = m then 1 else 0) := by
    intro i
    rw [linSubst_coordP, coeff_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [coeff_C_mul, hs g, coeff_monomial, ← hYeq g, hco]
  simp_rw [hcoef, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun g _ => ?_
  have hsum : ∑ i, (b.repr (Y g) i * (if s g = m then (1 : F) else 0)) • b i =
      (if s g = m then (1 : F) else 0) • Y g := by
    conv_rhs => rw [← b.sum_repr (Y g), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  rw [hsum]
  split_ifs
  · rw [one_smul]; exact hY g
  · rw [zero_smul]; exact zero_mem _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingOperatorsPolynomialEvalPderiv
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem polEval_pderiv :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [DecidableEq ι] (m d : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V), (∀ i j, d i * m j - m j * d i = if i = j then 1 else 0) →
    (∀ i, d i f₀ = 0) → ∀ (i : ι) (p : MvPolynomial ι ℂ),
      GlobalTheory.CCRFock.polEval m hm f₀ (MvPolynomial.pderiv i p) = d i (GlobalTheory.CCRFock.polEval m hm f₀ p) := by
  intro V _ _ ι _ m d hm f₀ hc h0 i p
  have hX : ∀ (j : ι) (q : MvPolynomial ι ℂ),
      polEval m hm f₀ (MvPolynomial.X j * q) = m j (polEval m hm f₀ q) := by
    intro j q
    simp [polEval, Module.End.mul_apply]
  have h1 : polEval m hm f₀ 1 = f₀ := by simp [polEval]
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hC : (MvPolynomial.C a : MvPolynomial ι ℂ) = a • (1 : MvPolynomial ι ℂ) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [MvPolynomial.pderiv_C, map_zero, hC, map_smul, h1, map_smul, h0, smul_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X q j hq =>
    have hv := LinearMap.congr_fun (hc i j) (polEval m hm f₀ q)
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add] at hv
    rw [mul_comm q, MvPolynomial.pderiv_mul, map_add, hX, hX, hq, hv]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp
    · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij)]
      simp [hij]

end GlobalTheory.CCRFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRealPlaceTorusClassesSignVectorsStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactRealPlace_torusClasses_signVectors : ∀ {D : D7} (V : HSp D) {S : D.what₂.Tau → SPar} (M : DSModel V S) (ρ : D.what₂.Tau)
    (P : PPol D.sp.cm.sig V.rank), CompactSpace (Tor P (placeOf D ρ).Completion) →
    (XSet P (placeOf D ρ).Completion V.gram).Finite ∧
      ∃ (y : XSet P (placeOf D ρ).Completion V.gram → Equiv.Perm (Fin V.rank))
        (θ : XSet P (placeOf D ρ).Completion V.gram → Fin V.rank → ℝ),
        Function.Bijective (fun p : compactWeyl (M.ε ρ) × XSet P (placeOf D ρ).Completion V.gram =>
          (y p.2)⁻¹ * p.1.1) ∧
        (∀ q a, Complex.exp (θ q a * Complex.I) = cxRoots (embOverOf D ρ).1 P ((y q)⁻¹ a)) ∧
        ∀ q, ∃ g : GArch D.sp.cm.sig V.gram (placeOf D ρ), frameMat M ρ (g⁻¹ * gam q.2.choose_spec.choose_spec.2 * g) =
          Matrix.diagonal fun a => Complex.exp (θ q a * Complex.I) := by
  first | exact @GlobalTheory.RealSigns.signs_real | exact GlobalTheory.RealSigns.signs_real | (intros; apply GlobalTheory.RealSigns.signs_real <;> assumption)
end

