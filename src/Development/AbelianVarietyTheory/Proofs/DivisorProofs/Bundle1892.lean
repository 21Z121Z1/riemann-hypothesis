import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexBlockLevel
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.StdLoc

theorem idx_alg (q : ℝ) (hq : q ≠ 0) (c a a' : ℕ) :
    q ^ (c * (a + a') ^ 2) * glVol q (a + a') /
      (q ^ (c * a ^ 2) * glVol q a * (q ^ (c * a' ^ 2) * glVol q a') * (q ^ c) ^ (a * a')) = blockIdx q c a a' := by
  rw [blockIdx]
  have e : c * (a + a') ^ 2 = c * a ^ 2 + c * a' ^ 2 + c * a * a' + c * a * a' := by ring
  have e2 : (q ^ c) ^ (a * a') = q ^ (c * a * a') := by rw [← pow_mul, mul_assoc]
  rw [e, pow_add, pow_add, pow_add, e2]
  have h1 : q ^ (c * a ^ 2) ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ (c * a' ^ 2) ≠ 0 := pow_ne_zero _ hq
  have h3 : q ^ (c * a * a') ≠ 0 := pow_ne_zero _ hq
  by_cases ha : glVol q a = 0
  · simp [ha]
  by_cases hb : glVol q a' = 0
  · simp [hb]
  field_simp

end GlobalTheory.StdLoc

namespace GlobalTheory.StdLoc

theorem glVol_add (q : ℝ) (a' a : ℕ) :
    glVol q (a' + a) = glVol q a' * ∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹) := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, glVol, Finset.prod_Icc_succ_top (by omega), ← glVol, ih, Finset.prod_Icc_succ_top (by omega), mul_assoc, add_assoc]

theorem glVol_pos {q : ℝ} (hq : 1 < q) (n : ℕ) : 0 < glVol q n :=
  Finset.prod_pos fun i hi => sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by simp at hi; omega)))

theorem stdLoc_product {q : ℝ} (hq : 1 < q) (c a a' : ℕ) :
    (∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹))⁻¹ * blockIdx q c a a' * ((q ^ (c * a * a'))⁻¹ * glVol q a) = 1 := by
  have h1 := glVol_pos hq a
  have h2 := glVol_pos hq a'
  have h3 : (0 : ℝ) < q ^ (c * a * a') := pow_pos (by linarith) _
  have h4 : 0 < ∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹) := by
    have := glVol_add q a' a
    have h5 := glVol_pos hq (a' + a)
    rw [this] at h5
    exact pos_of_mul_pos_right h5 h2.le
  rw [blockIdx, add_comm a a', glVol_add]
  generalize ∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹) = P at h4 ⊢
  field_simp

end GlobalTheory.StdLoc

namespace GlobalTheory.StdLoc

open UniqueFactorizationMonoid

theorem absNorm_eq_prod {E : Type} [Field E] [NumberField E] {𝔪 : Ideal (𝓞 E)} (h𝔪 : 𝔪 ≠ ⊥) :
    (Ideal.absNorm 𝔪 : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset, (Ideal.absNorm w : ℝ) ^ (normalizedFactors 𝔪).count w := by
  have h1 : (normalizedFactors 𝔪).prod = 𝔪 := by
    have := prod_normalizedFactors h𝔪
    exact associated_iff_eq.1 this
  conv_lhs => rw [← h1]
  rw [map_multiset_prod, Nat.cast_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
  simp

theorem relIndex_blockLevel {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (𝔪 : Ideal (𝓞 D.host.E)) (a : ℕ)
    (h𝔪 : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (ha : a ≤ P.d) (hJ : IsBlockLevel P 𝔪 a) :
    ((P.J.relIndex (intG D P.d) : ℕ) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      blockIdx (Ideal.absNorm w : ℝ) ((normalizedFactors 𝔪).count w) a (P.d - a) := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_reduction_maxLevel_unitary_mod_ideal D 𝔪 h𝔪 P.d
  have hsurj : Function.Surjective ρ := by
    intro g'
    choose g hg using fun i j => Ideal.Quotient.mk_surjective (I := 𝔪) (((g' : GL (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin P.d) (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) i j)
    have hgm : (Matrix.of g).map (Ideal.Quotient.mk 𝔪) = ((g' : GL (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin P.d) (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) := by
      ext i j; simp [hg]
    have h2 := GlobalTheory.T.exists_maxLevel_unitary_congr_mod_ideal D 𝔪 h𝔪 hcop P.d (Matrix.of g) (by rw [hgm]; exact Matrix.isUnits_det_units g')
    obtain ⟨k, hk, hk'⟩ := h2
    simp only [Matrix.of_apply] at hk'
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Units.ext
    ext i j
    exact ((hρ ⟨k, hk⟩ i j (g i j)).2 (hk' i j)).trans (hg i j)
  have hsub : P.J.subgroupOf (intG D P.d) = (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).comap ρ := by
    have h0 : ∀ x : AE D, x - inc D ((0 : 𝓞 D.host.E) : D.host.E) = x := fun x => by simp
    refine Subgroup.ext fun k => ⟨fun h => ?_, fun h => ?_⟩
    · have h' : (k : GA D P.d) ∈ P.J := h
      show ρ k ∈ blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d
      refine (mem_blockPar _).2 fun i j hj hi => ?_
      have h1 := ((hJ _).1 h').2 i j hj hi
      rw [← h0 ((((k : GA D P.d) : GL (Fin P.d) (AE D)) : Matrix (Fin P.d) (Fin P.d) (AE D)) i j)] at h1
      exact ((hρ k i j 0).2 h1).trans (map_zero _)
    · have h' : ρ k ∈ blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d := h
      show (k : GA D P.d) ∈ P.J
      refine (hJ _).2 ⟨k.2, fun i j hj hi => ?_⟩
      have h1 := (hρ k i j 0).1 (((mem_blockPar _).1 h' i j hj hi).trans (map_zero _).symm)
      rwa [h0] at h1
  have hR : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) :=
    Nat.finite_of_card_ne_zero (by rw [hR]; simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  have hidx : P.J.relIndex (intG D P.d) = (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).index := by
    show (P.J.subgroupOf (intG D P.d)).index = _
    rw [hsub, Subgroup.index_comap_of_surjective _ hsurj]
  have hcm := (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).card_mul_index
  have hP0 : (Nat.card (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hI : ((blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).index : ℝ) =
      (Nat.card (GL (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) : ℝ) / (Nat.card (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d) : ℝ) := by
    rw [eq_div_iff hP0, mul_comm]; exact_mod_cast hcm
  rw [hidx, hI, GlobalTheory.T.card_blockParabolicSubgroupGL _ a P.d ha, hR]
  push_cast
  rw [GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪, GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪, GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪, absNorm_eq_prod h𝔪, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hq : (Ideal.absNorm w : ℝ) ≠ 0 := by
    have hw0 : w ≠ ⊥ := fun h => by
      rw [h] at hw; exact zero_notMem_normalizedFactors _ (Multiset.mem_toFinset.1 hw)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hw0)
  obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le ha
  rw [ha', Nat.add_sub_cancel_left]
  exact idx_alg _ hq _ _ _

end GlobalTheory.StdLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SchrSB

theorem eq_one_of_pow_two_pow (z : ℂ) (h : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IterativeScalingBound.main
  | exact _root_.GlobalTheory.IterativeScalingBound.main
  | (apply _root_.GlobalTheory.IterativeScalingBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IterativeScalingBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IterativeScalingBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IterativeScalingBound.main ..)

theorem isLocallyConstant_addChar {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    (ψ : AddChar G ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have hU : (⇑ψ) ⁻¹' Metric.ball 1 (1 / 2) ∈ nhds (0 : G) := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact Metric.ball_mem_nhds _ (by norm_num)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hU
  have hker : ∀ y ∈ V, ψ y = 1 := by
    intro y hy
    apply eq_one_of_pow_two_pow
    intro k
    have hm : (2 ^ k) • y ∈ V := V.toAddSubgroup.nsmul_mem hy _
    have := hV hm
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, AddChar.map_nsmul_eq_pow] at this
    exact this
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : Filter.Tendsto (fun y => y - x) (nhds x) (nhds 0) := by
    have h := ((continuous_sub_right x).tendsto x)
    rwa [sub_self] at h
  filter_upwards [hx (V.isOpen.mem_nhds V.zero_mem)] with y hy
  have e : y = x + (y - x) := by abel
  rw [e, AddChar.map_add_eq_mul, hker _ hy, mul_one]

theorem continuous_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
  have h : Continuous (GlobalTheory.LatVac.liftV v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  exact hψ.comp h

theorem schr_mem_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ GlobalTheory.WeilM.SB _ := by
  intro F _ _ κ _ ψ hψ v w φ hφ
  have hloc := isLocallyConstant_addChar _ (continuous_psiAt ψ hψ v)
  have hlin : Continuous fun x : κ → Fv F v => x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) :=
    (continuous_id.dotProduct continuous_const).add continuous_const
  refine ⟨?_, ?_⟩
  · exact (hloc.comp_continuous hlin).mul (hφ.1.comp_continuous (continuous_add_const w.1))
  · have hc : HasCompactSupport fun x : κ → Fv F v => φ (x + w.1) :=
      hφ.2.comp_homeomorph (Homeomorph.addRight w.1)
    exact hc.mul_left (f := fun x => GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)))

end GlobalTheory.SchrSB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerFixedFunctionsProportionalOfSelfDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedinger_fixed_functions_proportional_of_selfDual : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψk : AddChar (Fv F v) ℂ), Continuous ψk → ψk ≠ 1 →
    ∀ (S : Set ((κ → Fv F v) × (κ → Fv F v))) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v),
    Λ ≤ AddSubgroup.closure S → c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ f g : (κ → Fv F v) → ℂ, (∀ s ∈ S, schr ψk s f = f) → (∀ s ∈ S, schr ψk s g = g) → f ≠ 0 → ∃ a : ℂ, g = a • f := by
  first | exact @GlobalTheory.SchrFixUniq.proportional_of_fixed | exact GlobalTheory.SchrFixUniq.proportional_of_fixed | (intros; apply GlobalTheory.SchrFixUniq.proportional_of_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerIrreducibleFinitePlaceCompletionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedinger_irreducible_finitePlaceCompletion : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψk : AddChar (Fv F v) ℂ), Continuous ψk → ψk ≠ 1 →
    ∀ N : Submodule ℂ ((κ → Fv F v) → ℂ), N ≤ GlobalTheory.WeilM.SB (κ → Fv F v) → (∀ w, ∀ φ ∈ N, schr ψk w φ ∈ N) → ∀ φ₀ ∈ N, φ₀ ≠ 0 →
      N = GlobalTheory.WeilM.SB (κ → Fv F v) := by
  first | exact @GlobalTheory.SchrIrred.schr_irreducible | exact GlobalTheory.SchrIrred.schr_irreducible | (intros; apply GlobalTheory.SchrIrred.schr_irreducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

namespace GlobalTheory.ThetaSchurF

section Lemmas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}

theorem half_add_half (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y = symplOF σ JS JT ξ₀ x y := by
  simp only [symplOHF, ← add_mul, ← map_add]
  norm_num

theorem symplOF_add_left (x x' y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (x + x') y = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x' y := by
  simp only [symplOF, hOF, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem symplOF_add_right (x y y' : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ x (y + y') = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x y' := by
  simp only [symplOF, hOF, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem symplOF_zero_right (x : WOF F E nS nT) : symplOF σ JS JT ξ₀ x 0 = 0 := by
  simp [symplOF, hOF]

theorem continuous_symplOF_left (y : WOF F E nS nT) : Continuous fun x => symplOF σ JS JT ξ₀ x y := by
  have h := GlobalTheory.HeisThetaF.continuous_symplOHF_left (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) y
  have e : (fun x => symplOF σ JS JT ξ₀ x y) = fun x => symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y :=
    funext fun x => (half_add_half x y).symm
  rw [e]
  exact h.add h

theorem mul_star_psi (hψ : ∀ a, ‖ψ a‖ = 1) (a : AF F) : ψ a * star (ψ a) = 1 := by
  rw [Complex.star_def, Complex.mul_conj', hψ a]
  simp

theorem heis_rat (hskew : ∀ x y : WOF F E nS nT, symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) {γ : WOF F E nS nT} (hγ : γ ∈ ratLF F E nS nT)
    (x : WOF F E nS nT) : heisOF σ JS JT ξ₀ ψ γ f x = ψ (symplOF σ JS JT ξ₀ x γ) * f x := by
  obtain ⟨γ, rfl⟩ := hγ
  have hs : symplOHF σ JS JT ξ₀ (ratWF γ) x = -symplOHF σ JS JT ξ₀ x (ratWF γ) := by
    simp only [symplOHF]
    rw [hskew, mul_neg]
  show ψ (symplOHF σ JS JT ξ₀ x (ratWF γ)) * f (x + ratWF γ) = ψ (symplOF σ JS JT ξ₀ x (ratWF γ)) * f x
  rw [add_comm x, hf.quasi, hs, neg_neg, ← mul_assoc, ← AddChar.map_add_eq_mul, half_add_half]

theorem prod_periodic (hψ : ∀ a, ‖ψ a‖ = 1) {f f' : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ ψ f)
    (hf' : IsThetaFunOF σ JS JT ξ₀ ψ f') {γ : WOF F E nS nT} (hγ : γ ∈ ratLF F E nS nT) (x : WOF F E nS nT) :
    f (γ + x) * star (f' (γ + x)) = f x * star (f' x) := by
  obtain ⟨γ, rfl⟩ := hγ
  show f (ratWF γ + x) * star (f' (ratWF γ + x)) = _
  rw [hf.quasi, hf'.quasi, star_mul']
  linear_combination (f x * star (f' x)) * mul_star_psi hψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) x))

theorem scalar_eq (hψ : ∀ a, ‖ψ a‖ = 1) (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ)
    (M : Module.End ℂ (WOF F E nS nT → ℂ))
    (hM : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (M f))
    (hn : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ)
    (f f' : WOF F E nS nT → ℂ) (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) (hf' : IsThetaFunOF σ JS JT ξ₀ ψ f') :
    ∫ x in 𝓕, M f x * star (M f' x) ∂μ = ∫ x in 𝓕, f x * star (f' x) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hb : ∀ g ∈ GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ, ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C :=
    fun g (hg : IsThetaFunOF σ JS JT ξ₀ ψ g) => by
      have hp : ∀ γ ∈ ratLF F E nS nT, ∀ w, ‖g (γ + w)‖ = ‖g w‖ := by
        rintro _ ⟨γ, rfl⟩ w
        exact (congrArg norm (hg.quasi γ w)).trans (by rw [norm_mul, hψ, one_mul])
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.cont.continuousOn
      refine ⟨C, fun w => ?_⟩
      obtain ⟨γ, hγ, h⟩ := hKc w
      rw [← hp γ hγ w]
      exact hC _ h
  exact GlobalTheory.Mem.LiftPolar.integral_mul_star_eq (μ.restrict 𝓕) (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (fun g (hg : IsThetaFunOF σ JS JT ξ₀ ψ g) => hg.cont.measurable) hb M hM hn f f' hf hf'

theorem prod_eq (hψ : IsCharAF F ψ)
    (hskew : ∀ x y : WOF F E nS nT, symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y)
    (hann : ∀ x : WOF F E nS nT, (∀ γ ∈ ratLF F E nS nT, ψ (symplOF σ JS JT ξ₀ x γ) = 1) ↔ x ∈ ratLF F E nS nT)
    (hth : ∀ w f, IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (heisOF σ JS JT ξ₀ ψ w f))
    (M : Module.End ℂ (WOF F E nS nT → ℂ))
    (hM : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (M f))
    (hc : ∀ w f, IsThetaFunOF σ JS JT ξ₀ ψ f → M (heisOF σ JS JT ξ₀ ψ w f) = heisOF σ JS JT ξ₀ ψ w (M f))
    (hn : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f →
        ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ)
    {f f' : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) (hf' : IsThetaFunOF σ JS JT ξ₀ ψ f')
    (x : WOF F E nS nT) : M f x * star (M f' x) = f x * star (f' x) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) (ratLF F E nS nT) K hK hKc).1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hint : ∀ g g', IsThetaFunOF σ JS JT ξ₀ ψ g → IsThetaFunOF σ JS JT ξ₀ ψ g' →
      Integrable (fun x => g x * star (g' x)) (μ.restrict 𝓕) := fun g g' hg hg' => by
    have hcont : Continuous fun x => g x * star (g' x) := hg.cont.mul hg'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← prod_periodic hψ.2.1 hg hg' hγ w]
    exact hC _ h
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WOF F E nS nT) (ratLF F E nS nT) K hK hKc
    (ratLF F E nS nT) (fun γ x => ψ (symplOF σ JS JT ξ₀ x γ))
    (fun γ => hψ.1.comp (continuous_symplOF_left _))
    (fun γ x y => by simp only [symplOF_add_left, AddChar.map_add_eq_mul])
    (fun γ γ' x => by simp only [AddSubgroup.coe_add, symplOF_add_right, AddChar.map_add_eq_mul])
    (fun x => by simp only [AddSubgroup.coe_zero, symplOF_zero_right, AddChar.map_zero_eq_one])
    (fun γ x => hψ.2.1 _)
    (fun x => by
      rw [← hann x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    μ 𝓕 hμ h𝓕 (fun x => M f x * star (M f' x) - f x * star (f' x))
    (((hM f hf).cont.mul (hM f' hf').cont.star).sub (hf.cont.mul hf'.cont.star))
    (fun γ hγ x => by
      rw [prod_periodic hψ.2.1 hf hf' hγ, prod_periodic hψ.2.1 (hM f hf) (hM f' hf') hγ])
    (fun γ => by
      have e : (fun x => ψ (symplOF σ JS JT ξ₀ x γ) * (M f x * star (M f' x) - f x * star (f' x))) = fun x =>
          M (heisOF σ JS JT ξ₀ ψ γ f) x * star (M f' x) - heisOF σ JS JT ξ₀ ψ γ f x * star (f' x) := by
        funext x
        rw [hc _ f hf, heis_rat hskew hf γ.2, heis_rat hskew (hM f hf) γ.2]
        ring
      rw [e, integral_sub (hint _ _ (hM _ (hth _ f hf)) (hM f' hf')) (hint _ _ (hth _ f hf) hf'),
        scalar_eq hψ.2.1 μ 𝓕 hμ h𝓕 M hM (hn μ 𝓕 hμ h𝓕) _ _ (hth _ f hf) hf', sub_self])
  exact sub_eq_zero.1 (congrFun key x)

end Lemmas

theorem schur : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ M : Module.End ℂ (WOF F E nS nT → ℂ),
      (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f)) →
      (∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ w f) = heisOF σ JS JT ξ₀ B.ψ w (M f)) →
      (∀ (μ : MeasureTheory.Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        MeasureTheory.IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
      ∃ c : ℂ, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ M hM hc hn
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1
  have hinv : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have hskew := GlobalTheory.T.adelicSymplecticTraceForm_alternating_swap F E σ hinv nS nT JS JT hJS hJT ξ₀ hσξ
  have hann := GlobalTheory.T.rational_points_self_annihilator_symplectic_standardChar F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ
  have hth : ∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w f) :=
    fun w f hf => GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS nT JS JT ξ₀ w f hf
  have h2 : ∀ f f', IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ f' → ∀ x y,
      M f x * star (M f' y) = f x * star (f' y) := fun f f' hf hf' x y => by
    have h := prod_eq hψ hskew hann hth M hM hc hn hf (hth (y - x) f' hf') x
    rw [hc _ _ hf'] at h
    simp only [heisOF, add_sub_cancel, star_mul'] at h
    linear_combination B.ψ (symplOHF σ JS JT ξ₀ x (y - x)) * h -
      (M f x * star (M f' y) - f x * star (f' y)) * mul_star_psi hψ.2.1 (symplOHF σ JS JT ξ₀ x (y - x))
  by_cases h0 : ∃ f₀ y, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ y ≠ 0
  · obtain ⟨f₀, y, hf₀, hy⟩ := h0
    have h1 := h2 f₀ f₀ hf₀ hf₀ y y
    have hn1 : ‖M f₀ y‖ = ‖f₀ y‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ y ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]
      exact norm_ne_zero_iff.2 hy
    have hs : star (M f₀ y) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (f₀ y) / star (M f₀ y), fun f hf => ?_⟩
    funext x
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h2 f f₀ hf hf₀, mul_comm]
  · refine ⟨1, fun f hf => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hy⟩
    rw [this, map_zero, smul_zero]

end GlobalTheory.ThetaSchurF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzThetaPolynomialGrowthStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_theta_polynomial_growth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
      ∀ (x : Fin n × Fin d → AF F) (ξ : Fin n × Fin d → F), (∀ i, (x i).2 = (algebraMap F (AF F) (ξ i)).2) →
        om (g, h) Φ x ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  first | exact @GlobalTheory.FinDenom.exists_denominator_of_finite_component | exact GlobalTheory.FinDenom.exists_denominator_of_finite_component | (intros; apply GlobalTheory.FinDenom.exists_denominator_of_finite_component <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzOfSummableSeminormsStatement
section
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_schwartz_of_summable_seminorms : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℕ → SchwartzMap E ℂ),
    (∀ k n, Summable (fun j => SchwartzMap.seminorm ℂ k n (t j))) → Summable t := by
  first | exact @GlobalTheory.ConvSeries.summable_of_summable_seminorm | exact GlobalTheory.ConvSeries.summable_of_summable_seminorm | (intros; apply GlobalTheory.ConvSeries.summable_of_summable_seminorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzSeriesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_schwartz_series : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {ι : Type}
    (u : ι → SchwartzMap V ℂ), (∀ k n : ℕ, Summable (fun i => SchwartzMap.seminorm ℂ k n (u i))) →
    ∃ F : SchwartzMap V ℂ, (∀ x, HasSum (fun i => u i x) (F x)) ∧
      ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, HasSum (fun i => T (u i)) (T F) := by
  first | exact @GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms | exact GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms | (intros; apply GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms <;> assumption)
end

