import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1452
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParametersBoundedEigenfunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.ParamBound

section General

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem heckeVec_map_of_injective {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {K : Subgroup G}
    (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (hρ : ∀ g y, f (ρ g y) = ρ' g (f y)) (h : G → ℂ) (x : V) :
    f (heckeVec ρ K h x) = heckeVec ρ' K h (f x) := by
  unfold heckeVec
  have hs : (Function.support fun c : G ⧸ K => h c.out • ρ' c.out (f x)) =
      Function.support fun c : G ⧸ K => h c.out • ρ c.out x := by
    ext c
    simp only [Function.mem_support, ne_eq, ← hρ, ← map_smul]
    exact not_congr (map_eq_zero_iff f hf)
  by_cases hfin : (Function.support fun c : G ⧸ K => h c.out • ρ c.out x).Finite
  · rw [map_finsum f hfin]
    simp only [map_smul, hρ]
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (hs ▸ hfin), map_zero]

theorem comp_mem_hecke (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    {h' : H → ℂ} (hh : h' ∈ Hecke ℂ K') : h' ∘ e ∈ Hecke ℂ K := by
  classical
  obtain ⟨h1, S, hS⟩ := hh
  refine ⟨fun a b g => ?_, S.image e.symm, fun g hg => ?_⟩
  · show h' (e (a * g * b)) = h' (e g)
    rw [map_mul, map_mul]
    exact h1 ⟨e a, (hK a).1 a.2⟩ ⟨e b, (hK b).1 b.2⟩ (e g)
  · obtain ⟨s, hs, a, b, hab⟩ := hS (e g) hg
    refine ⟨e.symm s, Finset.mem_image_of_mem _ hs, ⟨e.symm a, (hK _).2 (by simp)⟩,
      ⟨e.symm b, (hK _).2 (by simp)⟩, ?_⟩
    apply e.injective
    simp [hab]

theorem isUnitarisable_comp {ρ : Representation ℂ G V} (hρ : IsUnitarisable ρ) (φ : H →* G) :
    IsUnitarisable (ρ.comp φ) := by
  obtain ⟨B, h1, h2, h3⟩ := hρ
  exact ⟨B, h1, h2, fun g => h3 (φ g)⟩

end General

theorem norm_le_of_mem_bcParam {q n : ℕ} (hq : 2 ≤ q) {α : Fin (n / 2) → ℂˣ}
    (hα : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n α) :
    ∀ b ∈ bcParam n α, ‖(b : ℂ)‖ ≤ ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) := by
  intro b hb
  simp only [bcParam, Multiset.mem_add, Multiset.mem_map, Finset.mem_univ_val, true_and,
    Multiset.mem_replicate] at hb
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  rcases hb with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨hn, rfl⟩
  · exact (hα i).2
  · rw [Units.val_inv_eq_inv_val, norm_inv]
    have hpos : 0 < ((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)) := Real.rpow_pos_of_pos hq2 _
    calc ‖(α i : ℂ)‖⁻¹ ≤ (((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)))⁻¹ := inv_anti₀ hpos (hα i).1
      _ = _ := by rw [Real.rpow_neg hq2.le, inv_inv]
  · simp only [Units.val_one, norm_one]
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    exact Real.one_le_rpow (by nlinarith) (by linarith)

theorem exists_param_at (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hJ : SphOff J χ Sb) (f : GA D V → ℂ) (hfm : f ∈ bddAut V)
    (hf0 : f ≠ 0) (hlev : ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (hc : ∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : v ∉ Sb) (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : w.under (𝓞 D.host.F) = v) :
    ∃ B : Multiset ℂˣ, IsParamVec D.sp.cm.sig V.gram (frameLat V) h
        ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) f B ∧
      ∀ b ∈ B, ‖(b : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((V.rank : ℝ) - 1) / 2) := by
  obtain ⟨hfix, heig⟩ := GlobalTheory.T.adelicSphericalEigenfunction_local_heckeAlgebra_eigen D V J χ Sb hJ v hv f hlev c hc
  let ρ : Representation ℂ (Gv V v) (bddAut V) := (bddRep V).comp (embV V v)
  let x : bddAut V := ⟨f, hfm⟩
  have hx0 : x ≠ 0 := fun e => hf0 (congrArg Subtype.val e)
  have hint : ∀ g y, (bddAut V).subtype (ρ g y) =
      ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) g ((bddAut V).subtype y) := fun _ _ => rfl
  have hxfix : x ∈ fixed ρ (Kv V v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ((GlobalTheory.LGrp.mem_fixed.1 hfix) k hk)
  have hxeig : ∀ hh ∈ Hecke ℂ (Kv V v), ∃ a : ℂ, heckeVec ρ (Kv V v) hh x = a • x := fun hh hm => by
    obtain ⟨a, ha⟩ := heig hh hm
    refine ⟨a, Subtype.val_injective ?_⟩
    have := heckeVec_map_of_injective (K := Kv V v) (bddAut V).subtype Subtype.val_injective hint hh x
    exact this.trans ha
  have hρU : IsUnitarisable ρ := isUnitarisable_comp (GlobalTheory.T.boundedAutomorphicRightTranslation_unitarisable_bounded D V).1 _
  have hH := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := fun P _ => by
    haveI := GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rcases (exists_isInertChart _ (isCMExt_host D) v).1 hun with hs | ⟨w', hw'⟩
  · obtain ⟨e, he, -, -⟩ := SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hL.span_eq_top h hs hd
    have hfix' := (mem_fixed_comp_symm (ρ := ρ) e he.2).2 hxfix
    obtain ⟨B, hB, hbd⟩ := GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL D.host.E w V.rank (bddAut V) (ρ.comp e.symm.toMonoidHom)
      (isUnitarisable_comp hρU _) x hx0 hfix' fun h' hh' => by
        rw [heckeVec_comp_symm e he.2 hh'.1 hxfix]
        exact hxeig _ (comp_mem_hecke e he.2 hh')
    exact ⟨B, Or.inl ⟨hs, e, he, hB.map (bddAut V).subtype (fun g y => rfl) hf0⟩, fun b hb => (hbd b hb).1⟩
  · have h' : w'.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext (v.isMaximal.eq_of_le
      (Ideal.comap_ne_top _ w'.isPrime.ne_top) (Ideal.map_le_iff_le_comap.1 (le_of_eq hw'))).symm
    obtain ⟨-, -, huniq, -, -⟩ := (exists_isInertChart _ (isCMExt_host D) v).2 w' h' hw'
    obtain rfl : w = w' := (huniq w).1 h
    obtain ⟨-, ⟨τ, hτ, -⟩, -, hnorm, hconj⟩ := (exists_isInertChart _ (isCMExt_host D) v).2 w h hw'
    obtain ⟨⟨ϖ, hϖ⟩, hch⟩ := hconj τ hτ
    obtain ⟨e, he, -, -⟩ := hch V.rank V.gram (frameLat V) hH hL.fg hL.span_eq_top hd
    have hfix' := (mem_fixed_comp_symm (ρ := ρ) e he.2.2).2 hxfix
    obtain ⟨α, hα, hbd⟩ := GlobalTheory.T.exists_satakeParameter_trivialBound_unramifiedUnitary (w.adicCompletion D.host.E) ϖ τ (qV D.host.F v) V.rank hϖ (bddAut V)
      (ρ.comp e.symm.toMonoidHom) (isUnitarisable_comp hρU _) x hx0 hfix' fun h'' hh'' => by
        rw [heckeVec_comp_symm e he.2.2 hh''.1 hxfix]
        exact hxeig _ (comp_mem_hecke e he.2.2 hh'')
    refine ⟨bcParam V.rank α,
      Or.inr ⟨hw', τ, ϖ, e, α, hϖ, he, hα.map hϖ (bddAut V).subtype (fun g y => rfl) hf0, rfl⟩, ?_⟩
    intro b hb
    rw [hnorm, Nat.cast_pow]
    exact norm_le_of_mem_bcParam hϖ.2.2.2.2.2.1 hbd b hb

end GlobalTheory.FinZeta.ParamBound

namespace GlobalTheory.FinZeta.ParamBound

theorem exists_param_bounded : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ f ∈ bddAut V, f ≠ 0 → (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f) → ∃ B : Fam D.host.E, IsParamFunV V Sb f B ∧ Bounded (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) B V.rank (((V.rank : ℝ) - 1) / 2) := by
  intro D V J χ Sb hJ f hfm hf0 hlev c hc
  classical
  have key := fun (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : v ∉ Sb) (w : HeightOneSpectrum (𝓞 D.host.E))
      (h : w.under (𝓞 D.host.F) = v) => exists_param_at D V J χ Sb hJ f hfm hf0 hlev c hc v hv w h
  let B : Fam D.host.E := fun w =>
    if hw : w.under (𝓞 D.host.F) ∉ Sb then (key _ hw w rfl).choose else 0
  have hB : ∀ w (hw : w.under (𝓞 D.host.F) ∉ Sb), B w = (key _ hw w rfl).choose := fun w hw => dif_pos hw
  refine ⟨B, ?_, ?_⟩
  · intro v hv w h
    subst h
    have hv' : w.under (𝓞 D.host.F) ∉ Sb := hv
    rw [hB w hv']
    exact (key _ hv' w rfl).choose_spec.1
  · intro w hw
    have hw' : w.under (𝓞 D.host.F) ∉ Sb := hw
    rw [hB w hw']
    exact ⟨(IsParamVec.card (key _ hw' w rfl).choose_spec.1).le, (key _ hw' w rfl).choose_spec.2⟩

end GlobalTheory.FinZeta.ParamBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBlocStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_doubledStabilizer_adds_diagonalBlock : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Y : Matrix (Fin d) (Fin d) (AE F E),
      At (evFin F v) Y → (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ ∀ g ∈ GlobalTheory.DblVac.KD σ W v, p * g ∈ GlobalTheory.DblVac.KD σ W v ∧
        GlobalTheory.DblVac.diagonalBlockOfMatrix (p * g) = GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂)) := by
  first | exact @GlobalTheory.DblVacUnip.exists_unip | exact GlobalTheory.DblVacUnip.exists_unip | (intros; apply GlobalTheory.DblVacUnip.exists_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePointMemCongruenceSubgroupOffPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePoint_mem_congruenceSubgroup_offPlaces : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S) → ∀ k : GA D V, k ∈ GfC V → (∀ v ∉ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v) → (∀ v ∈ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k = 1) → Lev.finE V k ∈ congLev D.sp.cm V.gram (GlobalTheory.AdelicU.frameLat V) 𝔪 := by
  first | exact @GlobalTheory.CongOff.finE_mem_congLev_of_off | exact GlobalTheory.CongOff.finE_mem_congLev_of_off | (intros; apply GlobalTheory.CongOff.finE_mem_congLev_of_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gKModuleMapCuspForms_extends_multiplicitySpace : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.ExtExists D := by
  first | exact @GlobalTheory.GKExt.extExists | exact GlobalTheory.GKExt.extExists | (intros; apply GlobalTheory.GKExt.extExists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodCharactersDualStableOfThetaLiftScalars
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.GoodStableGiven

theorem goodStable_of_given : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), Given R F → Formalism.L2.DIV.GoodStable A.X := by
  intro hGC D G _ _ Pl0 T A Ks _ _ _ R F h
  obtain ⟨om, hT⟩ := GlobalTheory.T.exists_tameCharacters_seriesIdempotentsTameLabelled R F h
  exact GlobalTheory.GoodStableDual.goodStable_of_irr R F h.irr h.core.grp om
    (GlobalTheory.GoodIdemTie.idemTie_of_tameTie hGC D om hT)

end GlobalTheory.GoodStableGiven

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfBlockSumExistsInverseIntegralSplitPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfBlockSum_exists_inverse_integral_splitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl F) (π : AE F E →+* Fv F v) (b : GL (Fin d) (Fv F v)),
  (∀ a : AF F, π (algebraMap (AF F) (AE F E) a) = evFin F v a) →
  ∀ (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F)),
  G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) →
  ∀ X : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  IsUnit (G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂ +
    X * (G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂)).det →
  ∀ Y : Matrix (Fin d) (Fin d) (AE F E), Y.map π = (b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) * ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∃ N : Matrix (Fin d) (Fin d) (Fv F v), N * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))).map π = 1 ∧ (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * N * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  first | exact @GlobalTheory.Twist.halfBlockSum_inv_conj_integral | exact GlobalTheory.Twist.halfBlockSum_inv_conj_integral | (intros; apply GlobalTheory.Twist.halfBlockSum_inv_conj_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfBlockSumTwistSubOneSupportedAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfBlockSumTwist_sub_one_supportedAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl F) (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) (Y : Matrix (Fin d) (Fin d) (AE F E)),
  At (evFin F v) (g - 1) → At (evFin F v) Y → At (evFin F v) ((⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))) - 1) := by
  first | exact @GlobalTheory.TwistBlockK.atK_sub_one | exact GlobalTheory.TwistBlockK.atK_sub_one | (intros; apply GlobalTheory.TwistBlockK.atK_sub_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.ArchLineSum

open GlobalTheory.SplitScalar GlobalTheory.LatVac

variable {D : D7}

theorem fstA_realAd (t : ℝ) : fstA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = fstA D.host.F (GlobalTheory.WittLevi.realAd D t) := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective
  show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm _) = _
  rw [RingEquiv.apply_symm_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  ext w
  · show t = InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w.1)).symm t)
    exact ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w.1)).apply_symm_apply t).symm
  · exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)

theorem infPart_realAd (t : ℝ) : infPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t)) =
    infPart D (GlobalTheory.WittLevi.realE D t) := by
  show fstA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E) = fstA D.host.F (GlobalTheory.WittLevi.realAd D t) ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [fstA_realAd]

theorem theta_realAd {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (t : ℝ) :
    θ ρ (infPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t))) = t := by
  rw [infPart_realAd]; exact GlobalTheory.WittLevi.theta_realE hθ ρ t

theorem finPart_smul (u : AF D.host.F) (a : AE D) :
    finPart D (u • a) = (sndA D.host.F u ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a := by
  rw [Algebra.smul_def, map_mul]; rfl

theorem infPart_smul (u : AF D.host.F) (a : AE D) :
    infPart D (u • a) = infPart D (algebraMap (AF D.host.F) (AE D) u) * infPart D a := by
  rw [Algebra.smul_def, map_mul]

set_option synthInstance.maxHeartbeats 400000 in

theorem realAd_smul_eq {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {w : WO S T}
    (hw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) w) (t : ℝ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w = ∑ τ, lineAt θ τ (compAt θ τ w) t := by
  classical
  have hL : ∀ τ, IsLineAt θ τ (compAt θ τ w) (lineAt θ τ (compAt θ τ w)) := fun τ =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)
  ext i j
  rw [← sub_eq_zero]
  apply GlobalTheory.StdUnn.RealComp.eq_zero_of_parts
  · rw [← GlobalTheory.StdUnn.RealComp.theta_zero_iff hθ]
    intro ρ
    rw [(infPart D).map_sub, (θ ρ).map_sub, sub_eq_zero, Matrix.sum_apply, map_sum (infPart D), map_sum (θ ρ)]
    have e1 : ∀ τ, θ ρ (infPart D (lineAt θ τ (compAt θ τ w) t i j)) =
        if ρ = τ then (t : ℂ) * θ ρ (infPart D (w i j)) else 0 := by
      intro τ
      have := congrFun (congrFun ((hL τ).2.2 t ρ) i) j
      change θ ρ (infPart D (lineAt θ τ (compAt θ τ w) t i j)) = _ at this
      rw [this]
      split_ifs with h
      · subst h; rfl
      · rfl
    rw [Finset.sum_congr rfl fun τ _ => e1 τ, Finset.sum_ite_eq Finset.univ ρ, if_pos (Finset.mem_univ _)]
    show θ ρ (infPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w i j)) = _
    rw [infPart_smul, (θ ρ).map_mul, theta_realAd hθ]
  · rw [(finPart D).map_sub, sub_eq_zero, Matrix.sum_apply, map_sum (finPart D)]
    show finPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w i j) = _
    rw [finPart_smul, show sndA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul,
      zero_mul]
    exact (Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hL τ).2.1 t) i) j).symm

end GlobalTheory.ArchLineSum

namespace GlobalTheory.ArchLineSum

open GlobalTheory.SplitScalar GlobalTheory.LatVac

set_option synthInstance.maxHeartbeats 400000 in

theorem hasDerivAt_realAd_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
    ∀ w : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) w → ∀ x : WO S T,
      HasDerivAt (fun t : ℝ => heisO ψ S T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w) f x)
        (∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ w) f x) 0 := by
  intro D ψ θ hψ hθ S T f hf w hw x
  classical
  have hc : Continuous ψ := hψ.1.1
  have hL : ∀ τ, IsLineAt θ τ (compAt θ τ w) (lineAt θ τ (compAt θ τ w)) := fun τ =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)
  let Λ : (D.what₂.Tau → ℝ) →+ WO S T :=
    ∑ τ, (lineAt θ τ (compAt θ τ w)).comp (Pi.evalAddMonoidHom (fun _ : D.what₂.Tau => ℝ) τ)
  have hΛ : ∀ s, Λ s = ∑ τ, lineAt θ τ (compAt θ τ w) (s τ) := fun s => by
    simp [Λ, AddMonoidHom.finset_sum_apply]
  have hΛc : Continuous Λ := by
    rw [show (Λ : (D.what₂.Tau → ℝ) → WO S T) = fun s => ∑ τ, lineAt θ τ (compAt θ τ w) (s τ) from funext hΛ]
    exact continuous_finset_sum _ fun τ _ => (hL τ).1.comp (continuous_apply τ)
  have hΛf : ∀ s, (Λ s).map (finPart D) = 0 := fun s => by
    ext i j
    rw [hΛ]
    show finPart D ((∑ τ, lineAt θ τ (compAt θ τ w) (s τ) : WO S T) i j) = 0
    rw [Matrix.sum_apply, map_sum (finPart D)]
    exact Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hL τ).2.1 (s τ)) i) j
  let G : (D.what₂.Tau → ℝ) → ℂ := fun s => heisO ψ S T (Λ s) f x
  have hχ : ∀ τ, Differentiable ℝ fun t : ℝ => ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) t)) := fun τ => by
    refine GlobalTheory.FockTranslate.differentiable_of_char _
      (hc.comp (continuous_const.mul (continuous_symplO S T continuous_const (hL τ).1))) ?_ ?_
    · rw [map_zero, symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]
    · intro s t
      rw [map_add, symplOH_add_right, AddChar.map_add_eq_mul]
  have hpsi : ∀ s, ψ (symplOH S T x (Λ s)) = ∏ τ, ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) (s τ))) := by
    intro s
    rw [hΛ]
    let φ : WO S T →+ AF D.host.F :=
      ⟨⟨symplOH S T x, by rw [symplOH, symplO_zero_right, mul_zero]⟩, symplOH_add_right S T x⟩
    have key : ∀ (s' : Finset D.what₂.Tau) (g : D.what₂.Tau → WO S T),
        ψ (φ (∑ τ ∈ s', g τ)) = ∏ τ ∈ s', ψ (φ (g τ)) := by
      intro s' g
      induction s' using Finset.induction_on with
      | empty => rw [Finset.sum_empty, Finset.prod_empty, map_zero, AddChar.map_zero_eq_one]
      | insert a s' ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, map_add, AddChar.map_add_eq_mul, ih]
    exact key Finset.univ _
  have hGd : Differentiable ℝ G := by
    have h1 : Differentiable ℝ fun s : D.what₂.Tau → ℝ => ψ (symplOH S T x (Λ s)) := by
      simp only [hpsi]
      have hp : ∀ s' : Finset D.what₂.Tau, Differentiable ℝ fun s : D.what₂.Tau → ℝ =>
          ∏ τ ∈ s', ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) (s τ))) := by
        intro s'
        induction s' using Finset.induction_on with
        | empty => simp only [Finset.prod_empty]; exact differentiable_const _
        | insert a s' ha ih =>
          simp only [Finset.prod_insert ha]
          have hτ : Differentiable ℝ fun s : D.what₂.Tau → ℝ => s a := differentiable_apply a
          exact ((hχ a).comp hτ).mul ih
      exact hp Finset.univ
    have h2 : Differentiable ℝ fun s : D.what₂.Tau → ℝ => f (x + Λ s) := by
      let e := Fintype.equivFin D.what₂.Tau
      let ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) ≃L[ℝ] (D.what₂.Tau → ℝ) :=
        (LinearEquiv.funCongrLeft ℝ ℝ e).toContinuousLinearEquiv
      have hs := hf.smooth _ (Λ.comp (ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) →+ (D.what₂.Tau → ℝ)))
        (hΛc.comp ℓ.continuous) (fun t => hΛf _) x
      have : (fun s : D.what₂.Tau → ℝ => f (x + Λ s)) =
          (fun t => f (x + Λ.comp (ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) →+ (D.what₂.Tau → ℝ)) t)) ∘ ℓ.symm := by
        funext s
        simp
      rw [this]
      exact (hs.differentiable (by simp)).comp ℓ.symm.differentiable
    exact h1.mul h2
  have hfun : (fun t : ℝ => heisO ψ S T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w) f x) =
      G ∘ (fun t : ℝ => fun _ : D.what₂.Tau => t) := by
    funext t
    simp only [Function.comp, G, hΛ]
    rw [realAd_smul_eq hθ hw t]
  have hdiag : HasDerivAt (fun t : ℝ => (fun _ : D.what₂.Tau => t)) (fun _ => (1 : ℝ)) 0 :=
    hasDerivAt_pi.2 fun _ => hasDerivAt_id 0
  have hG0 : HasFDerivAt G (fderiv ℝ G 0) ((fun t : ℝ => fun _ : D.what₂.Tau => t) 0) := (hGd 0).hasFDerivAt
  have hcomp := hG0.comp_hasDerivAt (0 : ℝ) hdiag
  rw [hfun]
  suffices key : fderiv ℝ G 0 (fun _ => 1) = ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ w) f x by
    rw [← key]; exact hcomp
  rw [show (fun _ : D.what₂.Tau => (1 : ℝ)) = ∑ τ, Pi.single τ (1 : ℝ) from (Finset.univ_sum_single _).symm, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hline : HasDerivAt (fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ))
      ((1 : ℝ) • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) 0 := (hasDerivAt_id 0).smul_const _
  have hG0' : HasFDerivAt G (fderiv ℝ G 0) ((fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) 0) := by
    simpa using (hGd 0).hasFDerivAt
  have h3 := hG0'.comp_hasDerivAt (0 : ℝ) hline
  rw [one_smul] at h3
  have e : (G ∘ fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) =
      fun t => heisO ψ S T (lineAt θ τ (compAt θ τ w) t) f x := by
    funext t
    simp only [Function.comp, G, hΛ]
    rw [Finset.sum_eq_single τ (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
    simp
  rw [e] at h3
  exact h3.deriv.symm

end GlobalTheory.ArchLineSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumLocalSphericalZetaUnramifiedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_localSphericalZeta_unramified : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (D : D7) (V : HSp D), V.rank = D.R.r → ∀ (χ : (AE D)ˣ →* Circle), Formalism.L2.Theta.ResEta D χ D.R.nV → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ φ : Gv V v → ℂ, IsLocKer V D.R.nV (val χ) v φ → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gv V v) X), IsUnitarisable ρ → ∀ (x : X) (B : Fam D.host.E), (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsParamVec D.sp.cm.sig V.gram (frameLat V) h ρ x (B w) ∧ ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) → ∀ ℓ : X →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : Gv V v ⧸ Kv V v => φ a.out * starRingEnd ℂ (ℓ (ρ a.out x))) (LvTw B (val χ) v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ) * starRingEnd ℂ (ℓ x)) := by
  first | exact @GlobalTheory.LocZeta.hasSum_localZeta | exact GlobalTheory.LocZeta.hasSum_localZeta | (intros; apply GlobalTheory.LocZeta.hasSum_localZeta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergWords_weilOperator_supNorm_polynomialGrowth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ θ : InfFam D, IsInfFam θ → ∀ d : ℕ, ∃ A : ℕ, ∀ f, IsThetaFunO ψ V W f → ∃ c : ℝ, ∀ (g : GA D V) (h : GA D W), GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) d (ω (g, h) f) ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) := by
  first | exact @GlobalTheory.WeilWordGrowth.sup_words_growth | exact GlobalTheory.WeilWordGrowth.sup_words_growth | (intros; apply GlobalTheory.WeilWordGrowth.sup_words_growth <;> assumption)
end

