import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSpanPrincipalCongruenceLevelFunction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0169
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0170
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0156
import Formalism.SharpRestriction.GrowthBounds.DataG
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0173

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSpanPrincipalCongruenceLevelFunctionStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_span_principalCongruenceLevel_functions : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M → ∃ T : Finset X.K, (∀ x ∈ T, Lev X M x) ∧ ∀ f : X.K, Lev X M f → f ∈ Submodule.span (IntermediateField.adjoin Ω {X.jK}) (T : Set X.K) := by
  first | exact @GlobalTheory.KZ.ES.LevFin.exists_finset_span | exact GlobalTheory.KZ.ES.LevFin.exists_finset_span | (intros; apply GlobalTheory.KZ.ES.LevFin.exists_finset_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGammaZeroPartitionWeightStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gammaZeroPartitionWeight : ∀ L : ℕ, 0 < L → ∃ ρ, Wt L ρ := by
  first | exact @GlobalTheory.wt_exists | exact GlobalTheory.wt_exists | (intros; apply GlobalTheory.wt_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJInvariantInModularFunctionFractionFieldStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jInvariant_in_modularFunctionFractionField : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), ∃ a : GlobalTheory.FN.ring ε.range, (a : ℍ → ℂ) = jT ∧ (∀ γ : SL(2, ℤ), T.sl (ofSL γ) (T.io a) = T.io a) ∧ (T.exp (T.io a)).coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → (T.exp (T.io a)).coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, (T.exp (T.io a)).coeff r = n := by
  first | exact @GlobalTheory.FN.j_in_frac | exact GlobalTheory.FN.j_in_frac | (intros; apply GlobalTheory.FN.j_in_frac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerPotentialRelationPadic
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.KumPot

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cast_of_dvd {d M : ℕ} (h : d ∣ M) {x y : ℤ} (hxy : (x : ZMod M) = y) : (x : ZMod d) = y :=
  (ZMod.intCast_eq_intCast_iff _ _ _).2
    (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 h) ((ZMod.intCast_eq_intCast_iff _ _ _).1 hxy))

theorem gamma_le {d M : ℕ} (h : d ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma d := by
  intro γ hγ
  obtain ⟨a, b, c, e⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
  refine CongruenceSubgroup.Gamma_mem.2 ⟨?_, ?_, ?_, ?_⟩
  · simpa using cast_of_dvd h (x := γ 0 0) (y := 1) (by simpa using a)
  · simpa using cast_of_dvd h (x := γ 0 1) (y := 0) (by simpa using b)
  · simpa using cast_of_dvd h (x := γ 1 0) (y := 0) (by simpa using c)
  · simpa using cast_of_dvd h (x := γ 1 1) (y := 1) (by simpa using e)

theorem gamma_le_gam {N l M : ℕ} (hN : N ∣ M) (hl : l ∣ M) : CongruenceSubgroup.Gamma M ≤ Gam N l := by
  intro γ hγ
  obtain ⟨a, -, c, e⟩ := CongruenceSubgroup.Gamma_mem.1 (gamma_le hN hγ)
  obtain ⟨-, -, c', -⟩ := CongruenceSubgroup.Gamma_mem.1 (gamma_le hl hγ)
  exact ⟨(CongruenceSubgroup.Gamma1_mem N γ).2 ⟨a, e, c⟩, CongruenceSubgroup.Gamma0_mem.2 c'⟩

theorem polySlash_eq_self_of_mem_Gamma (l n : ℕ) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma (l ^ n))
    (p : MvPolynomial (Fin 2) (ZMod (l ^ n))) : slP (δ : Matrix (Fin 2) (Fin 2) ℤ) p = p := by
  obtain ⟨a, b, c, e⟩ := CongruenceSubgroup.Gamma_mem.1 hδ
  rw [GlobalTheory.KZ.SlPLaws.polySlash_congr _ 1 p, GlobalTheory.KZ.SlPLaws.polySlash_one']
  intro i j
  fin_cases i <;> fin_cases j <;> simp [a, b, c, e]

theorem toZModPow_eval (l : ℕ) [Fact l.Prime] (n : ℕ) (u : Fin 2 → ℤ_[l]) (p : MvPolynomial (Fin 2) ℤ_[l]) :
    PadicInt.toZModPow n (MvPolynomial.eval u p) =
      MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (MvPolynomial.map (PadicInt.toZModPow n) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem kum_sum (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {ι : Type} (s : Finset ι) (x : ι → X.Khat l)
    (χ : ι → SL(2, ℤ) → ZMod (l ^ n)) (h : ∀ i ∈ s, Kum X l n (x i) (χ i)) :
    Kum X l n (∑ i ∈ s, x i) (∑ i ∈ s, χ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end GlobalTheory.KZ.H3.KumPot

namespace GlobalTheory.KZ.H3.KumPot

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem bset_rel (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] [IsAlgClosed Ω] (hJ : JHol X) (N w : ℕ) (hN : 4 ≤ N)
    (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hw : Odd w) (b : X.Fn l) (hb : b ∈ X.BSet N l w) :
    ∃ F ∈ Pot ℤ_[l] w (Gam N l), Rel X l b F := by
  obtain ⟨⟨c, hcA, hbc⟩, hinv⟩ := hb
  have hcoef := fun γ hγ i => GlobalTheory.T.binaryForm_coeff_of_gamma1CapGamma0_invariant Ω ε X l N w b c hbc γ hγ (hinv γ hγ) i
  obtain ⟨Φ, hΦ, hK⟩ := GlobalTheory.T.kummerCharacters_invariant_compatible_family Ω ε X l hJ N w c hcA hcoef
  obtain ⟨z, hz, hzΦ⟩ := GlobalTheory.T.exists_padic_cocycle_of_compatible_poly_family N l w (by omega) hl2 hlN hw Φ hΦ
  obtain ⟨F, hF, hFz⟩ := GlobalTheory.T.exists_eichlerShimuraPotential_of_homogeneousPolyCocycle ℤ_[l] w N l hN z hz
  refine ⟨F, hF, fun u n => ⟨fun δ => MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (Φ n δ), ?_, ?_⟩⟩
  · have hsum := kum_sum X l n (Finset.univ : Finset (Fin (w + 1))) (fun (i : Fin (w + 1)) => (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i)
      (fun (i : Fin (w + 1)) δ => PadicInt.toZModPow n (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) *
        MvPolynomial.coeff (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))) (Φ n δ))
      (fun i _ => GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n _ _ _ (hK n i))
    rw [← hbc u] at hsum
    convert hsum using 1
    funext δ
    rw [Finset.sum_apply]
    have MX := GlobalTheory.T.binaryMonomialDegree_subst_expansion (ZMod (l ^ n)) w
    conv_lhs => rw [MX.2.1 (Φ n δ) (hΦ.1 n δ)]
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MX.2.2.2.1, map_pow]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · obtain ⟨M1, hM1, hM1'⟩ := hzΦ n
    have hl : 0 < l := (Fact.out : l.Prime).pos
    refine ⟨N * l ^ (n + 1) * M1, by positivity, fun δ hδ τ hτ => ?_⟩
    have hδG : δ ∈ Gam N l := gamma_le_gam (l := l) ⟨l ^ (n + 1) * M1, by ring⟩
      ⟨N * l ^ n * M1, by ring⟩ hδ
    have hδn : δ ∈ CongruenceSubgroup.Gamma (l ^ n) := gamma_le ⟨N * l * M1, by ring⟩ hδ
    have hδ1 : δ ∈ CongruenceSubgroup.Gamma M1 := gamma_le ⟨N * l ^ (n + 1), by ring⟩ hδ
    have e1 := hFz δ hδG τ hτ
    have e2 : MvPolynomial.map (PadicInt.toZModPow n) (z δ) = Φ n δ := hM1' δ hδ1
    have e3 : MvPolynomial.map (PadicInt.toZModPow n) (F (mob (ofSL δ) τ)) =
        MvPolynomial.map (PadicInt.toZModPow n) (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL δ) τ))) := by
      rw [GlobalTheory.KZ.SlPLaws.map_slP, polySlash_eq_self_of_mem_Gamma l n hδn]
    rw [map_sub, toZModPow_eval, toZModPow_eval, e3, ← map_sub, ← map_sub, e1, e2]

end GlobalTheory.KZ.H3.KumPot

theorem GlobalTheory.KZ.H3.exists_pot_rel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ), 4 ≤ N → l ≠ 2 → ¬ l ∣ N → Odd w →
    ∀ b ∈ X.B N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), Rel X l b F := by
  intro Ω _ _ ε X l _ _ hJ N w hN hl2 hlN hw b hb
  have RO := GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable Ω ε X l
  have PL := GlobalTheory.T.eichlerShimuraPotential_submodule_and_base_change ℤ_[l] w (Gam N l)
  induction hb using Submodule.span_induction with
  | mem b hb => exact KumPot.bset_rel X l hJ N w hN hl2 hlN hw b hb
  | zero => exact ⟨0, PL.2.1, RO.2.1⟩
  | add b b' _ _ ih ih' =>
    obtain ⟨F, hF, hR⟩ := ih
    obtain ⟨F', hF', hR'⟩ := ih'
    exact ⟨F + F', PL.1 _ _ hF hF', RO.1 _ _ _ _ hR hR'⟩
  | smul a b _ ih =>
    obtain ⟨F, hF, hR⟩ := ih
    exact ⟨a • F, PL.2.2.1 a F hF, RO.2.2.1 a b F hR⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelFunctionsIntermediateField
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.LevelField

theorem finiteDimensional_adjoin_restrict {F K : Type} [Field F] [Field K] [Algebra F K] (α : K)
    (L : IntermediateField (IntermediateField.adjoin F {α}) K)
    (hL : FiniteDimensional (IntermediateField.adjoin F {α}) L) (hα : α ∈ L.restrictScalars F) :
    FiniteDimensional (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) := by
  letI : Algebra (IntermediateField.adjoin F {α}) (L.restrictScalars F) :=
    inferInstanceAs (Algebra (IntermediateField.adjoin F {α}) L)
  haveI : Module.Finite (IntermediateField.adjoin F {α}) (L.restrictScalars F) := hL
  have hmap : (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map (L.restrictScalars F).val =
      IntermediateField.adjoin F {α} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ c : IntermediateField.adjoin F {α},
      algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c ∈
        IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)} := by
    intro c
    have hc : (c : K) ∈ (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map
        (L.restrictScalars F).val := by rw [hmap]; exact c.2
    obtain ⟨y, hy, hyc⟩ := (IntermediateField.mem_map _).1 hc
    have e : algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c = y := Subtype.ext hyc.symm
    rw [e]
    exact hy
  letI : Algebra (IntermediateField.adjoin F {α}) (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) :=
    ((algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F)).codRestrict
      (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) hmem).toAlgebra
  haveI : IsScalarTower (IntermediateField.adjoin F {α})
      (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite (IntermediateField.adjoin F {α}) _ _

open GlobalTheory.FN.LevelGal in

theorem finiteDimensional_lvl {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) (M : ℕ) (hM : 0 < M) :
    FiniteDimensional (IntermediateField.adjoin Ω {X.jK}) (lvl X M) := by
  let H := (rho X M).range
  haveI : Finite H := finite_range X M hM
  have hbot : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxF : (x : X.K) ∈ IntermediateField.adjoin Ω {X.jK} := by
      refine LevelOneFrac.mem_adjoin_of_sl_inv ε X hj x fun γ => ?_
      have h1 := congrArg Subtype.val (hx (rho X M γ⁻¹) ⟨γ⁻¹, rfl⟩)
      rw [rho_val, inv_inv] at h1
      exact h1
    rw [IntermediateField.mem_bot]
    exact ⟨⟨x, hxF⟩, Subtype.ext rfl⟩
  haveI hfd0 : FiniteDimensional (IntermediateField.fixedField H) (lvl X M) :=
    (inferInstance : FiniteDimensional (FixedPoints.subfield H (lvl X M)) (lvl X M))
  have : FiniteDimensional (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M) :=
    hbot ▸ hfd0
  exact Module.Finite.trans (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M)

theorem exists_level_field : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M →
    ∃ L : IntermediateField Ω X.K, (∀ f : X.K, f ∈ L ↔ ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) ∧
      ∃ hj : X.jK ∈ L, FiniteDimensional (IntermediateField.adjoin Ω {(⟨X.jK, hj⟩ : L)}) L := by
  intro Ω _ _ _ ε X _ hj M hM
  have hjL : X.jK ∈ (GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω := fun γ _ => X.j_inv γ
  exact ⟨(GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω, fun f => Iff.rfl, hjL,
    finiteDimensional_adjoin_restrict X.jK _ (finiteDimensional_lvl ε X hj M hM) hjL⟩

end GlobalTheory.KZ.LevelField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationAlmostEtaleTowerFixerStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_almostEtale_towerFixer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω), ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ IsInt p x) ∧ (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 ∧ ∀ S : Finset Ω, ∃ U : Subgroup ↥(⨅ n, Gn T n), U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix Ω U) ∧ AlmostSep v U := by
  first | exact @GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep | exact GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep | (intros; apply GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FormsOfCharactersIndependent
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.EisM.Indep

theorem qs_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℂ) (ha : ∀ i, PolyB (a i)) :
    qs (∑ i ∈ s, a i) = ∑ i ∈ s, qs (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.EisM.Lin.qs_zero
  | insert i s hi ih =>
    have hp : PolyB (∑ j ∈ s, a j) := by
      clear ih hi
      induction s using Finset.induction_on with
      | empty => simpa using GlobalTheory.EisM.Lin.polyB_zero
      | insert j t hj ih2 =>
        rw [Finset.sum_insert hj]; exact GlobalTheory.EisM.Lin.polyB_add _ _ (ha j) ih2
    rw [Finset.sum_insert hi, Finset.sum_insert hi, GlobalTheory.EisM.Lin.qs_add _ _ (ha i) hp, ih]

theorem exists_gamma (L N : ℕ) (hL : 0 < L) (hNL : N ∣ L) (u : (ZMod N)ˣ) :
    ∃ γ : SL(2, ℤ), γ 1 0 = (L : ℤ) ∧ ((γ 1 1 : ℤ) : ZMod N) = u := by
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hNL u
  have hc : Nat.Coprime (v : ZMod L).val L := ZMod.val_coe_unit_coprime v
  have hc' : IsCoprime (((v : ZMod L).val : ℕ) : ℤ) (L : ℤ) := Nat.isCoprime_iff_coprime.mpr hc
  obtain ⟨x, y, hxy⟩ := hc'
  refine ⟨⟨!![x, -y; (L : ℤ), (((v : ZMod L).val : ℕ) : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hxy
  · simp
  · simp only [SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [← hv, ZMod.unitsMap_val, ZMod.cast_eq_val, Int.cast_natCast]

theorem forms_of_characters_independent : ∀ (k L N : ℕ) (a : DirichletCharacter ℂ N → ℕ → ℂ), 0 < L → N ∣ L →
    (∀ ε, MF k L (ch ε) (a ε)) → (∑ ε, a ε) = 0 → ∀ ε, a ε = 0 := by
  intro k L N a hL hNL hmf hsum ε₀
  have hN : N ≠ 0 := by rintro rfl; exact hL.ne' (Nat.eq_zero_of_zero_dvd hNL)
  haveI : NeZero N := ⟨hN⟩
  set f : DirichletCharacter ℂ N → ℍ → ℂ := fun ε => qs (a ε) with hf
  have hfs : ∑ ε, f ε = 0 := by
    rw [hf, ← qs_finset_sum _ _ (fun ε => (hmf ε).1), hsum]; exact GlobalTheory.EisM.Lin.qs_zero

  have key : ∀ (b : ZMod N) (τ : ℍ), ∑ ε, ε b * f ε τ = 0 := by
    intro b τ
    by_cases hb : IsUnit b
    · obtain ⟨u, rfl⟩ := hb
      obtain ⟨γ, h10, h11⟩ := exists_gamma L N hL hNL u
      have hdiv : (L : ℤ) ∣ γ 1 0 := by rw [h10]
      have hj : ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) ≠ 0 := by
        apply pow_ne_zero
        intro h0
        have him := congrArg Complex.im h0
        simp only [h10, Int.cast_natCast, Complex.add_im, Complex.mul_im, Complex.natCast_re,
          Complex.natCast_im, Complex.intCast_im, zero_mul, add_zero, Complex.zero_im] at him
        have : (0 : ℝ) < (L : ℝ) * (τ : ℂ).im := mul_pos (by exact_mod_cast hL) τ.im_pos
        linarith
      have e : ∀ ε, f ε (γ • τ) = ε (u : ZMod N) * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) * f ε τ := by
        intro ε
        rw [hf]; dsimp only
        rw [(hmf ε).2 γ hdiv τ, ch, h11]
      have h0 : ∑ ε, f ε (γ • τ) = 0 := by
        have := congrFun hfs (γ • τ); simpa [Finset.sum_apply] using this
      simp only [e] at h0
      have h1 : ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) * ∑ ε, ε (u : ZMod N) * f ε τ = 0 := by
        rw [Finset.mul_sum, ← h0]; exact Finset.sum_congr rfl (fun ε _ => by ring)
      exact (mul_eq_zero.mp h1).resolve_left hj
    · exact Finset.sum_eq_zero (fun ε _ => by rw [MulChar.map_nonunit ε hb, zero_mul])
  funext n
  have hq : f ε₀ = 0 := by
    funext τ
    have hT : ∑ b : ZMod N, ε₀⁻¹ b * ∑ ε, ε b * f ε τ = 0 :=
      Finset.sum_eq_zero (fun b _ => by rw [key b τ, mul_zero])
    have hT' : ∑ b : ZMod N, ε₀⁻¹ b * ∑ ε, ε b * f ε τ = ∑ ε, f ε τ * ∑ b : ZMod N, (ε₀⁻¹ * ε) b := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun ε _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [MulChar.coeToFun_mul, Pi.mul_apply]; ring
    rw [hT'] at hT
    rw [Finset.sum_eq_single ε₀] at hT
    · rw [inv_mul_cancel, MulChar.sum_one_eq_card_units] at hT
      have hc : ((Fintype.card (ZMod N)ˣ : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simpa [hc, hN] using hT
    · intro ε _ hne
      rw [MulChar.sum_eq_zero_of_ne_one, mul_zero]
      intro h1; apply hne
      have := congrArg (ε₀ * ·) h1
      simpa using this
    · intro h; exact absurd (Finset.mem_univ _) h
  have := qs_injective (a ε₀) 0 (hmf ε₀).1 GlobalTheory.EisM.Lin.polyB_zero (by rw [GlobalTheory.EisM.Lin.qs_zero]; exact hq)
  simpa using congrFun this n

end GlobalTheory.EisM.Indep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionRingFrobeniusAlgebraMap
section
noncomputable section

open IsLocalRing QuadraticAlgebra

namespace GlobalTheory.SqrtUnif

section Quadratic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}

end Quadratic

section Squares

end Squares

section Witt

variable (p : ℕ) [hp : Fact p.Prime]

theorem fractionRing_frobenius_algebraMap {k : Type*} [Field k] [CharP k p] [PerfectRing k p]
    (x : WittVector p k) : WittVector.FractionRing.frobenius p k (algebraMap _ _ x) =
      algebraMap _ (FractionRing (WittVector p k)) (WittVector.frobenius x) := by
  simp [WittVector.FractionRing.frobenius]

theorem fractionRing_frobenius_pow {n : ℕ} (hn : n ≠ 0) :
    WittVector.FractionRing.frobenius p (GaloisField p n) ^ n = 1 := by
  have h1 : ∀ (m : ℕ) (x : WittVector p (GaloisField p n)),
      ∃ y : WittVector p (GaloisField p n), (∀ i, y.coeff i = x.coeff i ^ p ^ m) ∧
        (WittVector.FractionRing.frobenius p (GaloisField p n) ^ m) (algebraMap _ _ x) =
          algebraMap _ (FractionRing (WittVector p (GaloisField p n))) y := by
    intro m x
    induction m with
    | zero => exact ⟨x, by simp, rfl⟩
    | succ m ih =>
      obtain ⟨y, hy, h⟩ := ih
      refine ⟨WittVector.frobenius y, fun i => ?_, ?_⟩
      · rw [WittVector.coeff_frobenius_charP, hy, ← pow_mul, pow_succ]
      · rw [pow_succ', RingAut.mul_apply, h, fractionRing_frobenius_algebraMap]
  letI := Fintype.ofFinite (GaloisField p n)
  have hc : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p _ hn]
  refine RingEquiv.toRingHom_injective (IsLocalization.ringHom_ext
    (nonZeroDivisors (WittVector p (GaloisField p n))) (RingHom.ext fun x => ?_))
  obtain ⟨y, hy, h⟩ := h1 n x
  have : y = x := by
    ext i
    rw [hy, ← hc, FiniteField.pow_card]
  exact h.trans (by rw [this]; rfl)

end Witt

end GlobalTheory.SqrtUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FunctionFieldClassGroupPowers
section
open Polynomial

namespace GlobalTheory

theorem classGroup_mk0_mul_mul_pow_eq_one_of_span_eq {A : Type} [CommRing A] [IsDedekindDomain A]
    (N : ℕ) (P D C : Ideal A) (f : A) (hP : P ∈ nonZeroDivisors (Ideal A))
    (hD : D ∈ nonZeroDivisors (Ideal A)) (hC : C ∈ nonZeroDivisors (Ideal A))
    (h : Ideal.span {f} = P * D * C ^ N) :
    ClassGroup.mk0 ⟨P, hP⟩ * ClassGroup.mk0 ⟨D, hD⟩ * ClassGroup.mk0 ⟨C, hC⟩ ^ N = 1 := by
  rw [← map_pow, ← map_mul, ← map_mul]
  have hm : P * D * C ^ N ∈ nonZeroDivisors (Ideal A) :=
    mul_mem (mul_mem hP hD) (pow_mem hC N)
  have e : (⟨P, hP⟩ * ⟨D, hD⟩ * ⟨C, hC⟩ ^ N : nonZeroDivisors (Ideal A)) = ⟨P * D * C ^ N, hm⟩ :=
    Subtype.ext (by simp)
  rw [e, ClassGroup.mk0_eq_one_iff, ← h]
  exact ⟨⟨f, rfl⟩⟩

theorem prod_maximal_mem_nonZeroDivisors {A : Type} [CommRing A] [IsDedekindDomain A]
    {I : Type} [Fintype I] (Q : I → Ideal A) (hQ : ∀ i, (Q i).IsMaximal)
    (P₀ : Ideal A) (hP₀ : P₀.IsMaximal) (h₀ : P₀ ≠ ⊥) :
    (∏ i, Q i) ∈ nonZeroDivisors (Ideal A) := by
  refine prod_mem fun i _ => mem_nonZeroDivisors_of_ne_zero ?_
  intro hi
  have hb : (⊥ : Ideal A).IsMaximal := by
    have := hQ i
    rwa [hi] at this
  exact h₀ (hb.eq_of_le hP₀.ne_top bot_le).symm

theorem exists_class_group_mk0_eq_mul_pow :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A] (N : ℕ), 2 ≤ N → ∀ P₀ : Ideal A, P₀.IsMaximal →
      ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal →
        a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A,
          ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N := by
  intro k A _ _ _ _ _ _ _ _ _ _ N hN P₀ hP₀ h₀
  haveI : Algebra.FiniteType k A :=
    Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨r, V, D, Q, f₀, hset, hdeg⟩ := GlobalTheory.T.exists_linear_system_maximalDegree_factorization k A N P₀ (by omega) hP₀
  have hform := GlobalTheory.T.exists_formal_deformation_powerSeries_solution k A N (Fin r) V D P₀ Q f₀ hN hP₀ hset
  obtain ⟨a, ha, hall⟩ := GlobalTheory.T.specialise_generic_solution_almost_all_points k A (PowerSeries k) N (Fin r) V D hN hform
  obtain ⟨-, hVD, hQ, -, -, -, -, -, hf₀, hspan₀, -⟩ := hset
  refine ⟨a, ha, fun P hP haP h => ?_⟩
  obtain ⟨Q', f, hQ', hinj, hne, hDQ', hDP, hfV, hf, hfP, hfQ'⟩ := hall P hP haP
  have hspan := GlobalTheory.T.degree_count_maximalIdeal_generates_product k A N (Fin r) D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hne hDQ' hDP
    hf₀ hf hspan₀ (hVD f hfV) hfP hfQ' (hdeg f hfV hf)
  have hP₀ne : P₀ ≠ ⊥ := nonZeroDivisors.ne_zero h₀
  have hD : D ∈ nonZeroDivisors (Ideal A) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro hD0
    apply hDP
    rw [hD0]
    exact bot_le
  have hC := prod_maximal_mem_nonZeroDivisors Q hQ P₀ hP₀ hP₀ne
  have hC' := prod_maximal_mem_nonZeroDivisors Q' hQ' P₀ hP₀ hP₀ne
  rw [Finset.prod_pow] at hspan hspan₀
  have e := classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P D _ f h hD hC' hspan
  have e₀ := classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P₀ D _ f₀ h₀ hD hC hspan₀
  refine ⟨ClassGroup.mk0 ⟨_, hC⟩ / ClassGroup.mk0 ⟨_, hC'⟩, ?_⟩
  generalize ClassGroup.mk0 ⟨P, h⟩ = p at e ⊢
  generalize ClassGroup.mk0 ⟨P₀, h₀⟩ = p₀ at e₀ ⊢
  generalize ClassGroup.mk0 ⟨D, hD⟩ = d at e e₀
  generalize ClassGroup.mk0 ⟨_, hC⟩ = c at e₀ ⊢
  generalize ClassGroup.mk0 ⟨_, hC'⟩ = c' at e ⊢
  have e' : p * c' ^ N = p₀ * c ^ N := by
    apply mul_right_cancel (b := d)
    rw [mul_right_comm p, mul_right_comm p₀, e, e₀]
  rw [div_pow, ← mul_div_assoc, ← e', mul_div_cancel_right]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumParsevalQExpansionHorizontalLineStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_parseval_qExpansion_horizontal_line : ∀ (h b : ℕ → ℂ) (y : ℝ), PolyB h → PolyB b → 0 < y → HasSum (fun n : ℕ => conj (h n) * b n * (Real.exp (-4 * π * n * y) : ℝ)) (∫ x in (0 : ℝ)..1, conj (qs h (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I))) := by
  first | exact @GlobalTheory.EisM.parseval_line | exact GlobalTheory.EisM.parseval_line | (intros; apply GlobalTheory.EisM.parseval_line <;> assumption)
end

