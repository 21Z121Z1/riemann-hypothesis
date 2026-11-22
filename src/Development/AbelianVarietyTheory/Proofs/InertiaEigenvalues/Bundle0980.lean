import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField
import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0974
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0978
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0977
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxiliaryPrimeNeTypePrime
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.TwInputs.SmallField

theorem star_mem_of_normal {L : Type} [Field L] [CharZero L] [StarRing L] [IsGalois ℚ L] (M : IntermediateField ℚ L) (hM : IsGalois ℚ M)
    (x : L) (hx : x ∈ M) : star x ∈ M := by
  have h := (IntermediateField.normal_iff_forall_map_le (K := M)).1 hM.to_normal (starRingEnd L).toRatAlgHom
  exact h ⟨x, hx, rfl⟩

theorem exists_over (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ w.asIdeal :=
  _root_.GlobalTheory.HeightOnePrimeMembership.exists_heightOne_mem E hp

end GlobalTheory.TwInputs.SmallField

namespace GlobalTheory.TwInputs.SmallField

theorem exists_finset_rayIn (hR : GlobalTheory.NT.RayField) (P : Pre) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ B : Base, B.toPre = P → (∀ z ∈ S, z ∈ B.fixedCoefficientFieldInComplex) → ∀ C W V S' N G,
      GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn (assemble B C W V S' N G) (B.host.g 0 * B.host.g 1 * B.host.pde * B.host.pde')
        (embLL0 (assemble B C W V S' N G)).fieldRange := by
  let φK : P.host.K →+* ℂ := P.host.φ₀.comp (algebraMap P.host.K P.host.E)
  obtain ⟨Rf, hRf⟩ := Fld.exists_isRayFieldIn φK hR (Fld.natIdeal_ne_bot (E := P.host.K) (Fld.modulus_ne_zero P))
  haveI : NumberField Rf := hRf.numberField
  let b := Module.finBasis ℚ Rf
  refine ⟨Finset.univ.image (fun i => (b i : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    have h : IsAlgebraic ℚ (b i) := Algebra.IsAlgebraic.isAlgebraic _
    exact h.algHom Rf.val
  · intro B hB hS C W V S' N G
    subst hB
    have hle : Rf ≤ B.fixedCoefficientFieldInComplex := by
      intro z hz
      have hsum := congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)
      rw [IntermediateField.coe_sum] at hsum
      simp only [IntermediateField.coe_smul] at hsum
      rw [← hsum]
      exact sum_mem fun i _ => IntermediateField.smul_mem _ (hS _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
    obtain ⟨hm, hNF, hray⟩ := hRf
    letI := Fld.algOf φK Rf hm
    refine ⟨Rf, inferInstance, hNF, Fld.algOf φK Rf hm, hray.1, hray.2, Rf.val.toRingHom, ?_, fun x => ?_⟩
    · ext x
      exact Fld.algOf_apply φK Rf hm x
    · obtain ⟨y, hy, e⟩ := hle x.2
      exact ⟨⟨y, hy⟩, e⟩

end GlobalTheory.TwInputs.SmallField

namespace GlobalTheory.TwInputs.SmallField

theorem one_lt_cond (P : Pre) : 1 < P.host.QS * P.host.q * P.host.d :=
  lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero P.host.condN_ne_zero) P.host.sixteen_dvd_condN)

theorem exists_finset_lam (P : Pre) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ B : Base, B.toPre = P → (∀ z ∈ S, z ∈ B.fixedCoefficientFieldInComplex) → ∀ C W V S' N G,
      (∀ k, AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ≠ B.host.g k) → ∀ cf : CharFrame (assemble B C W V S' N G),
        ∃ Z : GlobalTheory.LamTie.LamDat (assemble B C W V S' N G), Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧
          Z.q0 = AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ∧ ∀ a, (Z.chi a).ValuesIn 0 (embLL0 (assemble B C W V S' N G)) := by
  classical
  by_cases hq : ∀ k, GlobalTheory.EX.DC.q0H P.host ≠ P.host.g k
  swap
  · refine ⟨∅, by simp, fun B hB _ C W V S' N G h => ?_⟩
    subst hB
    exact absurd h hq
  have hqp := (GlobalTheory.EX.DC.globalTwisting_spec_fact P.host).1
  obtain ⟨w0, hw0⟩ := exists_over P.host.E hqp
  have hmod : ∀ p ∈ [P.host.g 0, P.host.g 1, P.host.pde, P.host.pde', GlobalTheory.EX.DC.q0H P.host],
      p ≡ 1 [MOD P.host.QS * P.host.q * P.host.d] := by
    intro p hp
    rw [Nat.ModEq, Nat.mod_eq_of_lt (one_lt_cond P)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [P.g_cond 0, P.g_cond 1, P.pde_cond.1, P.pde_cond.2, GlobalTheory.EX.DC.mod_cond _]
  obtain ⟨hPl, -⟩ := GlobalTheory.LamTie.placesOk_of_modEq_one P.R P.host _ w0 hqp hmod (fun k => hq k)
    (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).2 hw0
  obtain ⟨χ, hχ, hT⟩ := GlobalTheory.LamTie.TeichEx.exists_auxiliaryHeckeCharacter_trivial_tame_part P.R P.host _ w0
    (fun g => (BlochKatoReduction.Gen.NFun P.R : ℤ) + 2 + ∑ j : Fin P.R.m, ⌈|(P.hc g).e j|⌉) hPl
    (UpperTheory.Mu.w_add_one_lt P.host hqp.one_lt 1 (by rw [one_mul]; exact GlobalTheory.EX.DC.mod_cond _))
  obtain ⟨n, hn, hinf⟩ := hχ.inf
  obtain ⟨cc, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm P.R P.host
  obtain ⟨M, hM, hv⟩ := GlobalTheory.Mem.ValAlg.values_in_numberField P.host.F P.host.E cc P.R.Psi (embPsi P.host) hcm χ n 0 hinf
    (fun g => by
      have h1 : (n g : ℚ) = 2 * (((BlochKatoReduction.Gen.NFun P.R : ℤ) + 2 + ∑ j : Fin P.R.m, ⌈|(P.hc g).e j|⌉ : ℤ) : ℚ) := hn g
      have h2 : n g = 2 * ((BlochKatoReduction.Gen.NFun P.R : ℤ) + 2 + ∑ j : Fin P.R.m, ⌈|(P.hc g).e j|⌉) := by exact_mod_cast h1
      exact ⟨(BlochKatoReduction.Gen.NFun P.R : ℤ) + 2 + ∑ j : Fin P.R.m, ⌈|(P.hc g).e j|⌉, by omega⟩)
  rw [Int.cast_zero, zero_div] at hv
  haveI := hM
  obtain ⟨α, hα, gα⟩ := GlobalTheory.Mem.DatHecke.exists_gen M
  refine ⟨{α}, by simpa using hα, fun B hB hS C W V S' N G _ cf => ?_⟩
  subst hB
  obtain ⟨x, hx, ex⟩ := hS α (Finset.mem_singleton_self _)
  have hM' : ∀ z ∈ M, ∃ y, embLL0 (assemble B C W V S' N G) y = z := gα B.LL0 (embLL0 (assemble B C W V S' N G)) ⟨⟨x, hx⟩, by exact ex⟩
  refine ⟨⟨cf, _, w0, fun _ g => (BlochKatoReduction.Gen.NFun B.R : ℤ) + 2 + ∑ j : Fin B.R.m, ⌈|(B.hc g).e j|⌉, fun _ => χ⟩,
    ⟨hPl, fun _ => hχ, fun j a g => ?_⟩, fun _ => hT, rfl, rfl, fun _ => GlobalTheory.Mem.Col2.InEx.valuesIn_of hv _ hM'⟩
  show (BlochKatoReduction.Gen.NFun B.R : ℚ) + 1 < (B.hc g).e j + (((BlochKatoReduction.Gen.NFun B.R : ℤ) + 2 + ∑ j : Fin B.R.m, ⌈|(B.hc g).e j|⌉ : ℤ) : ℚ)
  have h1 : ⌈|(B.hc g).e j|⌉ ≤ ∑ j' : Fin B.R.m, ⌈|(B.hc g).e j'|⌉ :=
    Finset.single_le_sum (f := fun j' => ⌈|(B.hc g).e j'|⌉) (fun j' _ => Int.ceil_nonneg (abs_nonneg _)) (Finset.mem_univ j)
  have h2 : -(B.hc g).e j ≤ ((⌈|(B.hc g).e j|⌉ : ℤ) : ℚ) := (neg_le_abs _).trans (Int.le_ceil _)
  have h3 : ((⌈|(B.hc g).e j|⌉ : ℤ) : ℚ) ≤ ((∑ j' : Fin B.R.m, ⌈|(B.hc g).e j'|⌉ : ℤ) : ℚ) := by exact_mod_cast h1
  push_cast at h3 ⊢
  linarith

end GlobalTheory.TwInputs.SmallField

namespace GlobalTheory.TwInputs.SmallField

theorem lg_rayIn (hR : GlobalTheory.NT.RayField) (K : Ctx) : large₂ K fun B _ _ => ∀ C W V S' N G,
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn (assemble B C W V S' N G) (B.host.g 0 * B.host.g 1 * B.host.pde * B.host.pde')
      (embLL0 (assemble B C W V S' N G)).fieldRange := by
  choose S hS gS using exists_finset_rayIn hR
  exact ⟨fun B _ _ => S B, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ => hS B, by simp,
    fun B _ _ _ hH _ _ => gS B.toPre B rfl hH.1⟩

theorem lg_lam (K : Ctx) : large₂ K fun B _ _ => ∀ C W V S' N G,
    (∀ k, AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ≠ B.host.g k) → ∀ cf : CharFrame (assemble B C W V S' N G),
      ∃ Z : GlobalTheory.LamTie.LamDat (assemble B C W V S' N G), Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧
        Z.q0 = AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ∧ ∀ a, (Z.chi a).ValuesIn 0 (embLL0 (assemble B C W V S' N G)) := by
  choose S hS gS using exists_finset_lam
  exact ⟨fun B _ _ => S B, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ => hS B, by simp,
    fun B _ _ _ hH _ _ => gS B.toPre B rfl hH.1⟩

theorem lg_fieldOk (hR : GlobalTheory.NT.RayField) (K : Ctx) : large₂ K fun B f _ => ∀ C W V S' N G,
    ValLL0 (assemble B C W V S' N G) (Fr.at ⟨B, C, W, V, S', N, G⟩ f) ∧
    (∀ X : RealSide (assemble B C W V S' N G), X.R.C = Fr.at ⟨B, C, W, V, S', N, G⟩ f → FieldOk X) ∧
    ((∀ k, AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ≠ B.host.g k) →
      ∃ Z : GlobalTheory.LamTie.LamDat (assemble B C W V S' N G), Z.Ok ∧ Z.Teich ∧ Z.C = Fr.at ⟨B, C, W, V, S', N, G⟩ f ∧
        Z.q0 = AbsolutelyIrreducibleSpan.q0 (assemble B C W V S' N G) ∧ ∀ a, (Z.chi a).ValuesIn 0 (embLL0 (assemble B C W V S' N G))) := by
  refine (((GlobalTheory.Mem.Col2.InEx.lg_colIn K).inter (lg_rayIn hR K)).inter (lg_lam K)).imp fun B f T _ h C W V S' N G => ?_
  obtain ⟨⟨⟨-, hval, -⟩, hray⟩, hlam⟩ := h
  refine ⟨hval C W V S' N G, fun X hX => ⟨B.coeffGaloisSubfield_isGalois, fun x => star_mem_of_normal B.LL0 B.coeffGaloisSubfield_isGalois _ x.2, ?_,
    hray C W V S' N G, fun k z hz => ?_,
    ⟨B.toPre.level_split _ B.host.pde_level.1, B.toPre.level_split _ B.host.pde_level.2⟩⟩, fun hq => hlam C W V S' N G hq _⟩
  · rw [hX]
    exact hval C W V S' N G
  · have h0 : B.host.g k * (B.host.g k - 1) ≠ 0 :=
      mul_ne_zero (B.host.g_prime k).ne_zero (by have := (B.host.g_prime k).two_le; omega)
    obtain ⟨x, hx, e⟩ := B.roots_Ks (B.host.g k * (B.host.g k - 1)) (by fin_cases k <;> simp)
    obtain ⟨y, hy⟩ := GlobalTheory.Mem.Col2.InEx.root_mem (embLL0 (assemble B C W V S' N G)) h0 ⟨⟨x, B.Ks_le hx⟩, e⟩ hz
    exact ⟨y, hy⟩

end GlobalTheory.TwInputs.SmallField

namespace GlobalTheory.TwInputs.SmallField

open Formalism.MainNotions.N Formalism.L2 Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem auxiliary_prime_ne_type_prime (K : Ctx) (C5 c6 Cb : ℝ) (h : K.Good C5 c6 Cb) (P : Pre) (hP : K.Over P) (k : Fin 2) :
    GlobalTheory.EX.DC.q0H P.host ≠ P.host.g k := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := hP
  exact h.ok.small.2.2.2.1 k

theorem cf_eq_at (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) :
    TC.cf w.I w.l Z = Fr.at (w.st Z) f := by
  obtain ⟨px, I, ok, rfl, S_eq, xr, pins, l, l0, δ, ex, fld, val⟩ := w
  rfl

theorem evLgG_fieldOk : PrN → EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt),
    (∀ X : GlobalTheory.TwInputs.RealSide (w.st Z).toD7, X.R.C = (TC.cf w.I w.l Z) → GlobalTheory.TwInputs.FieldOk X) ∧
    ∃ L : GlobalTheory.LamTie.LamDat (w.st Z).toD7, L.C = (TC.cf w.I w.l Z) ∧ L.Ok ∧ L.Teich ∧ L.q0 = AbsolutelyIrreducibleSpan.q0 (w.st Z).toD7 ∧
      ∀ a, (L.chi a).ValuesIn 0 (embLL0 (w.st Z).toD7) := by
  intro hP
  refine evG_good.imp fun K C5 c6 Cb hG _ => ?_
  refine (lg_fieldOk hP.rayF K).imp fun B f _ hO h _ T w Z => ?_
  obtain ⟨-, h1, h2⟩ := h w.C Z.W Z.V Z.S Z.N Z.G
  rw [cf_eq_at]
  obtain ⟨L, a, b, c, d, e⟩ := h2 (auxiliary_prime_ne_type_prime K C5 c6 Cb hG B.toPre hO)
  exact ⟨h1, L, c, a, b, d, e⟩

end GlobalTheory.TwInputs.SmallField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedCuspidalHolomorphicLeSpanAlgebraicCuspSec
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.SmallWtSpan

theorem holSub0_le_span_cuspSec : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ w : WeightFamilies.Wt D j, w.LastPos → 0 < w.n → holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n)}) := by
  intro D T hT j hj σ hσ w hw hn P hP
  have hdom := dom_wtA w
  obtain ⟨b, m, N, t, hbm, ht, hunit, hprod⟩ := GlobalTheory.T.exists_section_family_no_common_zero_large_weight D T hT j hj σ hσ _ _ hdom
  have hP' := Submodule.mem_inf.mp hP
  have h2 := GlobalTheory.GlueSpan.span_of_products D T hT j hj σ hσ _ b _ m N t hdom hbm ht hunit P hP'.2
    (fun i => hprod P hP i)
  exact GlobalTheory.T.holomorphic_sections_span_le D T hT j hj σ hσ w hw hn (Submodule.mem_inf.mpr ⟨hP, h2⟩)

end GlobalTheory.SmallWtSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideWithE
section
noncomputable section

namespace GlobalTheory.ChoiceRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Choice

variable {D : D7}

abbrev Tgt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) : Type :=
  FractionRing (c.Oe w) ⊗[D.ntw.Ok (c.twI w) (c.k' w)]
    D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))

def BasisAt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ)
    (e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) : Prop :=
  ∀ b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j),
    LinearIndependent (FractionRing (c.Oe w)) (fun i => e (b i)) ∧
      Submodule.span (FractionRing (c.Oe w)) (Set.range fun i => e (b i)) = ⊤

def latT (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) : Submodule (c.Oe w) (Tgt c w j) :=
  Submodule.span (c.Oe w)
      ((TensorProduct.mk (D.ntw.Ok (c.twI w) (c.k' w)) (FractionRing (c.Oe w))
          (D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))) 1) ''
        (D.nexp.MtLat (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))) :
          Set (D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))))))

def latS (w : D.what₂.places.Pl) (j : ℕ) : Set (D.what₂.MtL (D.what₂.muTw w) j) :=
  {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen}

def LatAt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ)
    (e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) (t : FractionRing (c.Oe w)) : Prop :=
  Submodule.span (c.Oe w) (e '' latS w j) = Submodule.span (c.Oe w) ((fun y => t • y) '' (latT c w j : Set (Tgt c w j)))

theorem BasisAt.smul {c : NChoice D} {w : D.what₂.places.Pl} {j : ℕ}
    {e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j} (h : BasisAt c w j e) (u : (FractionRing (c.Oe w))ˣ) :
    BasisAt c w j ((u : FractionRing (c.Oe w)) • e) := by
  intro b
  obtain ⟨h1, h2⟩ := h b
  refine ⟨?_, ?_⟩
  · convert h1.units_smul (fun _ => u) using 1
    funext i
    simp [LinearMap.smul_apply, Units.smul_def]
  · have h3 : (Set.range fun i => ((u : FractionRing (c.Oe w)) • e) (b i)) =
        (u : FractionRing (c.Oe w)) • Set.range fun i => e (b i) := by
      rw [← Set.range_smul]; rfl
    rw [h3, Submodule.span_smul_eq_of_isUnit _ _ u.isUnit, h2]

theorem LatAt.smul_inv {c : NChoice D} {w : D.what₂.places.Pl} {j : ℕ}
    {e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j} (u : (FractionRing (c.Oe w))ˣ)
    (h : LatAt c w j e (u : FractionRing (c.Oe w))) :
    Submodule.span (c.Oe w) ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • e) '' latS w j) = latT c w j := by
  let f : Tgt c w j →ₗ[c.Oe w] Tgt c w j :=
    { toFun := fun y => ((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • y
      map_add' := fun _ _ => smul_add _ _ _
      map_smul' := fun r y => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (FractionRing (c.Oe w)) r y, ← algebraMap_smul (FractionRing (c.Oe w)) r,
          smul_smul, smul_smul, mul_comm] }
  have h1 : ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • e) '' latS w j) = f '' (e '' latS w j) := by
    rw [Set.image_image]; rfl
  rw [h1, Submodule.span_image, h, ← Submodule.span_image, Set.image_image]
  have h2 : (fun y => f ((u : FractionRing (c.Oe w)) • y)) = id := by
    funext y
    show ((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • ((u : FractionRing (c.Oe w)) • y) = y
    rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [h2, Set.image_id, Submodule.span_eq]

def withE (c : NChoice D) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) : NChoice D :=
  { c with
    eMt := E
    eMt_basis := fun w j hw h1 h2 b => hb w j hw h1 h2 b
    eMt_lat := fun w j hw h1 h2 => hl w j hw h1 h2 }

def tupWithE {cf : CharFrame D} {c : NChoice D} (tp : TupTied D cf c) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) : TupTied D cf (withE c E hb hl) :=
  { tp with }

theorem choiceSide_withE {cf : CharFrame D} {mt : MtFam D} {exp : NExpTied D} {c : NChoice D} {tp : TupTied D cf c}
    (h : GlobalTheory.HeightCounting.ChoiceSide D cf mt exp c tp) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) :
    GlobalTheory.HeightCounting.ChoiceSide D cf mt exp (withE c E hb hl) (tupWithE tp E hb hl) :=
  ⟨⟨h.nct.twOf_eq, h.nct.twSide_eq, h.nct.Q_eq, h.nct.psi_eq, h.nct.embedding_baseField_condition⟩,
    ⟨h.choice.twI_conj, h.choice.sd_place, h.choice.emb_side, h.choice.sd_conj, h.choice.one, h.choice.conj⟩,
    h.off, h.adm, h.psi, h.eMt_level⟩

open Classical in

def pick (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)) :
    ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j
  | w, 0 => c.eMt w 0
  | w, k + 1 => if h : D.what₂.muAt w ≠ D.what₂.mu0 ∧ k < D.R.m then G w h.1 ⟨k, h.2⟩ else c.eMt w (k + 1)

theorem pick_eq (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1))
    (w : D.what₂.places.Pl) (hw : D.what₂.muAt w ≠ D.what₂.mu0) (i : Fin D.R.m) : pick c G w (i.1 + 1) = G w hw i := by
  simp only [pick, dif_pos (And.intro hw i.2)]

theorem pick_prop (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1))
    (p : ∀ w j, (D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) → Prop)
    (h : ∀ w hw (i : Fin D.R.m), p w (i.1 + 1) (G w hw i)) :
    ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → p w j (pick c G w j) := by
  intro w j hw h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := h w hw ⟨k, by omega⟩
  rwa [← pick_eq c G w hw ⟨k, by omega⟩] at this

end Choice

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {S : RatDat D.ntw}

def ThetaAt (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (YS : NExpRealS R cG S) (c : NChoice D) (w : D.what₂.places.Pl)
    (i : Fin D.R.m) (e : D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)) (t : FractionRing (c.Oe w)) :
    Prop :=
  ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (i.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK S (i.1 + 1)),
    (R.FW i).j (sg0 D A3.A) ((YS.fi i).e (∑ k, a k • (show ↥(S.A (i.1 + 1)).WK from f k).1)) =
      Y.mj.eW i (D.what₂.thetaP (D.what₂.muTw w) (i.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (i.1 + 1) x)) →
    NChoice.thPe D c w (i.1 + 1) (e x) =
      t • ∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
        (YS.eF (c.twI w) (i.1 + 1) (c.sd w) (by omega) (by omega)).symm ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)

theorem ThetaAt.smul_inv {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {YS : NExpRealS R cG S} {c : NChoice D}
    {w : D.what₂.places.Pl} {i : Fin D.R.m} {e : D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)}
    (u : (FractionRing (c.Oe w))ˣ) (h : ThetaAt Y YS c w i e (u : FractionRing (c.Oe w))) :
    ThetaAt Y YS c w i ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w))) • e) 1 := by
  intro x hx n a f hf
  rw [one_smul, LinearMap.smul_apply, map_smul, h x hx n a f hf, smul_smul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

theorem emtTheta_withE {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {YS : NExpRealS R cG S} {c : NChoice D}
    (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j)
    (h : ∀ w (i : Fin D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ThetaAt Y YS c w i (E w (i.1 + 1)) 1) :
    GlobalTheory.HeightCounting.EMtTheta Y YS (withE c E hb hl) := by
  intro w i hw x hx n a f hf
  have := h w i hw x hx n a f hf
  rw [one_smul] at this
  exact this

end Rows

end GlobalTheory.ChoiceRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactHoweDualityIsotypicMemOfStableSubspace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.HoweGen

theorem cvType_mem_of_stable : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (U : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank)), (∀ u ∈ GinfC (Vc D i), ∀ P ∈ U, ∀ P' : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → P' ∈ U) → (∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → P ∈ U → P' ∈ U) → (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W), R.ioP i x w ∈ U) → ∀ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) → ∀ w, φ w ∈ U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t U hstab hlie hio φ hφ w
  have hadd : ∀ a b : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t (a + b) = R.ptP i t a + R.ptP i t b := by
    intro a b; unfold RealDat.ptP; simp
  have hsmul : ∀ (c : ℂ) (a : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t (c • a) = c • R.ptP i t a := by
    intro c a; unfold RealDat.ptP; simp
  have hzero : R.ptP i t 0 = 0 := by simpa using hsmul 0 0
  let M : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) :=
    { carrier := {ψ | (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) ∧ ∀ w, ψ w ∈ U}
      add_mem' := by
        rintro ψ₁ ψ₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
        refine ⟨fun u hu w' => ?_, fun w => ?_⟩
        · simp only [LinearMap.add_apply, hadd, h₁ u hu w', h₂ u hu w', map_add]
        · simp only [LinearMap.add_apply]; exact U.add_mem (h₁' w) (h₂' w)
      zero_mem' := by
        refine ⟨fun u hu w' => ?_, fun w => ?_⟩
        · simp only [LinearMap.zero_apply, hzero, map_zero]
        · simp only [LinearMap.zero_apply]; exact U.zero_mem
      smul_mem' := by
        rintro c ψ ⟨h₁, h₁'⟩
        refine ⟨fun u hu w' => ?_, fun w => ?_⟩
        · simp only [LinearMap.smul_apply, hsmul, h₁ u hu w', map_smul]
        · simp only [LinearMap.smul_apply]; exact U.smul_mem c (h₁' w) }
  have hioM : ∀ x, R.ioP i x ∈ M := fun x =>
    ⟨fun u hu w' => ((hG.core.thP.ioP i t).1 u hu x w').symm, fun w => hio x w⟩
  have hne : M ≠ ⊥ := by
    obtain ⟨v, w₀, -, -, hv⟩ := (hG.core.thP.ioP i t).2.2
    intro hM
    have h0 : R.ioP i (PiTensorProduct.tprod ℂ v) ∈ (⊥ : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)) := hM ▸ hioM _
    rw [Submodule.mem_bot] at h0
    apply GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) i
    rw [← hv, h0]
    rfl
  have hφM : φ ∈ M := GlobalTheory.T.howeDuality_compactPair_realPlaces_irreducible D G Pl0 T A Ks R F hG hF i t M (fun ψ hψ => hψ.1)
    (fun ψ hψ τ Y hY ψ' hd => ⟨GlobalTheory.T.fockPolynomial_lieDerivative_equivariant D G Pl0 T A Ks R F hG hF i t τ Y hY ψ ψ' hψ.1 hd,
      fun w => hlie τ Y hY (ψ w) (ψ' w) (fun z => hd w z) (hψ.2 w)⟩) hne φ hφ
  exact hφM.2 w

end GlobalTheory.HoweGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaLiftsIsConjugateCuspExpansionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_thetaLifts_isConjugateCuspExpansion : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) := by
  first | exact @GlobalTheory.ConjClassSum.conj_lifts | exact GlobalTheory.ConjClassSum.conj_lifts | (intros; apply GlobalTheory.ConjClassSum.conj_lifts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitScalarSmulCoreIntegralAdelicFormPlacesStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitScalar_smul_coreIntegralAdelicForm_places : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), κ.LastPos → ∀ (q : Ideal (𝓞 T.Q.c.F)), q.IsPrime → ∀ (P : Set (HeightOneSpectrum (𝓞 T.Q.c.F))), P.Finite → ∀ ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n {p | p.asIdeal = q}, ∃ t : 𝓞 T.Q.c.F, t ∉ q ∧ T.σ₀ (t : T.Q.c.F) • ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n P := by
  first | exact @GlobalTheory.ScaleInt.smul_mem_baseInt | exact GlobalTheory.ScaleInt.smul_mem_baseInt | (intros; apply GlobalTheory.ScaleInt.smul_mem_baseInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_sections_span_restriction : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ φ ∈ C.ratForms a n, (∀ k ∈ T.Kf j σ, ∀ h, φ (h * k) = φ h) → ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V j σ) → ℂ)), (∀ i, ψ i ∈ baseForms T j σ a n) ∧ φ = ∑ i, C.σ₂ (x i) • ψ i := by
  first | exact @GlobalTheory.CoverFormDesc.cover_form_desc | exact GlobalTheory.CoverFormDesc.cover_form_desc | (intros; apply GlobalTheory.CoverFormDesc.cover_form_desc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmPartialLEqDivEntireStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n m : ℕ) (σ : CG E n) (σ' : CG E m), 1 ≤ m → m < n → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ F H : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (F x / H x) := by
  first | (exact @GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div) | (exact GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div) | (intros; apply GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLPoleAtOneConjStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π → ∃ L : ℝ → ℝ, (∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat π w.1) ((sat π w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (L x : ℂ) ∧ 1 ≤ L x) ∧ ContinuousOn L (Set.Ioi 1) ∧ ∃ c : ℝ, 0 < c ∧ Tendsto (fun x => (x - 1) * L x) (𝓝[>] 1) (𝓝 c) := by
  first | (exact @GlobalTheory.RSPole.rs_pole_conj) | (exact GlobalTheory.RSPole.rs_pole_conj) | (intros; apply GlobalTheory.RSPole.rs_pole_conj  <;> assumption)
end

