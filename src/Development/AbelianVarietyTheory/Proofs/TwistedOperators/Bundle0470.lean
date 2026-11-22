import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
import GroundTheory.GlobalFields.TateThesis.Bundle0002
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0458
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarOfCommuteSchrodingerOperators
section
noncomputable section

open MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil

theorem fderiv_gaussianSchwartz_single_add {l : Type} [Fintype l] [DecidableEq l] (j : l) (x : EuclideanSpace ℝ l) :
    fderiv ℝ (⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))) x (EuclideanSpace.single j 1) +
      2 * Real.pi * (x j : ℂ) * GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) x = 0 := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ l => -Real.pi * ‖y‖ ^ 2)
      (-Real.pi • (2 • (innerSL ℝ) x ∘L ContinuousLinearMap.id ℝ _)) x :=
    ((hasFDerivAt_id x).norm_sq).const_mul (-Real.pi)
  have h2 := (ofRealCLM.hasFDerivAt (x := Real.exp (-Real.pi * ‖x‖ ^ 2))).comp x h1.exp
  have e : ⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)) =
      (ofRealCLM : ℝ →L[ℝ] ℂ) ∘ fun y : EuclideanSpace ℝ l => Real.exp (-Real.pi * ‖y‖ ^ 2) := by
    funext y; simp
  rw [e, h2.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

theorem inner_toLp_map_of_integral_norm_sq : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l),
    (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    ∀ f g, inner ℂ ((S f).toLp 2 volume) ((S g).toLp 2 volume) = inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  intro l _ S hiso f g
  set U := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l)) with hU
  have hn : ∀ h : Sch l, ‖U (S h)‖ = ‖U h‖ := by
    intro h
    simp only [hU, SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num), SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [hiso]
  have e1 : (S f).toLp 2 volume = U (S f) := rfl
  have e2 : (S g).toLp 2 volume = U (S g) := rfl
  have e3 : f.toLp 2 volume = U f := rfl
  have e4 : g.toLp 2 volume = U g := rfl
  rw [e1, e2, e3, e4, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  simp only [← map_add, ← map_sub, ← map_smul, hn]

theorem exists_eq_smul_of_commute_rhoFun : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l),
    (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    (∀ w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(S f₁) = rhoFun w ⇑(S f)) → ∃ c : ℂ, ∀ f, S f = c • f := by
  intro l _ S hiso hcomm
  classical
  have hl : ∀ g : Sch l, ∫⁻ x, ‖g x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2) := by
    intro g
    rw [ofReal_integral_eq_lintegral_ofReal ((g.memLp (2 : ℕ) volume).integrable_norm_pow (by norm_num))
      (.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hbound : ∀ f, ∫⁻ x, ‖S f x‖ₑ ^ 2 ≤ 1 * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
    intro f
    rw [one_mul, hl, hl, hiso]
  have hd := GlobalTheory.T.derived_action_intertwines_of_group l LinearMap.id S 1 ENNReal.one_ne_top hbound (by simpa using hcomm)
  set G : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hG
  have hN : ∀ (j : l) (h : Sch l) x, (dRho (Pi.single (Sum.inl j) 1) h - I • dRho (Pi.single (Sum.inr j) 1) h) x =
      fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x := by
    intro j h x
    rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, dRho_single_inl, dRho_single_inr,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
    ring_nf
    rw [I_sq]
    ring
  have hSG : ∀ j (x : EuclideanSpace ℝ l), fderiv ℝ (⇑(S G)) x (EuclideanSpace.single j 1) +
      2 * Real.pi * (x j : ℂ) * S G x = 0 := by
    intro j x
    have h0 : dRho (Pi.single (Sum.inl j) 1) G - I • dRho (Pi.single (Sum.inr j) 1) G = 0 := by
      ext y
      rw [hN, hG, fderiv_gaussianSchwartz_single_add]
      rfl
    have := congrArg S h0
    rw [map_sub, map_smul, hd, hd, map_zero] at this
    rw [← hN, LinearMap.id_apply, LinearMap.id_apply] at *
    rw [this]
    rfl
  set c : ℂ := S G 0 with hc
  have hSGc : S G = c • G := by
    ext x
    rw [GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_add_eq_zero' l (S G) hSG x, SchwartzMap.smul_apply, smul_eq_mul, hG, GroundTheory.Global.gaussianSchwartz_apply]
  have hrho : ∀ w, S (rhoSch w G) = c • rhoSch w G := by
    intro w
    ext x
    rw [hcomm w G (rhoSch w G) (coe_rhoSch w G), hSGc, SchwartzMap.smul_apply, coe_rhoSch]
    simp only [rhoFun, SchwartzMap.smul_apply, smul_eq_mul]
    ring
  have key : ∀ f : Sch l, (starRingEnd ℂ c) • S f = f := by
    intro f
    rw [← sub_eq_zero]
    apply GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian l
    intro w
    have hsm : ∀ (a : ℂ) (g : Sch l), (a • g).toLp 2 volume = a • g.toLp 2 volume := fun a g =>
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_smul a g
    have hsub : ∀ (g g' : Sch l), (g - g').toLp 2 volume = g.toLp 2 volume - g'.toLp 2 volume := fun g g' =>
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_sub g g'
    have hp := inner_toLp_map_of_integral_norm_sq l S hiso (rhoSch w G) f
    rw [hrho, hsm, inner_smul_left] at hp
    rw [hsub, hsm, inner_sub_right, inner_smul_right, hp, sub_self]
  have hc0 : starRingEnd ℂ c ≠ 0 := by
    intro h0
    have := congrArg (fun g : Sch l => g 0) (key G)
    simp [h0, hG] at this
  exact ⟨(starRingEnd ℂ c)⁻¹, fun f => by rw [← key f, smul_smul, inv_mul_cancel₀ hc0, one_smul, key]⟩

end GlobalTheory.RealWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteMatrixIotaEqFinitePart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

noncomputable section
namespace GlobalTheory.SeeConjGroup

theorem fmat_iota_eq_finE : ∀ {D : D7} (κ : GA D (Yc D 0)), (GlobalTheory.SeeConjGroup.II D).fmat ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = (finE (Yc D 0) κ).val := by
  intro D κ
  have e : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D κ) = κ := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ
  have hf := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  rw [e] at hf
  have hv := congrArg Units.val hf
  exact hv.symm ▸ rfl
end GlobalTheory.SeeConjGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableDiagonalModSmall
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjRead

theorem flagV_pair_table : ∀ {M A : Type} [Zero M] [Ring A] (p : M → M → A) (sm : A → Prop) (ρ k n : ℕ), n = 2 * ρ + k + 1 → ∀ (e f : Fin ρ → M) (b b' : Fin k → M) (z : M), PairTable p sm e f b b' z → ∀ a c : Fin n, sm (p (flagV ρ k n f e b' z a) (flagV ρ k n e f b z c) - if a = c then sgnD ρ k a else 0) := by
  intro M A _ _ p sm ρ k n hn e f b b' z hT a c
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16⟩ := hT
  subst hn
  have ha := a.isLt
  have hc := c.isLt
  have d1 : ∀ (x y : Fin ρ), x.1 = y.1 → sm (p (f x) (e y) - 1) := by
    intro x y h; have := t1 x y; rwa [if_pos (Fin.ext h)] at this
  have o1 : ∀ (x y : Fin ρ), x.1 ≠ y.1 → sm (p (f x) (e y) - 0) := by
    intro x y h; have := t1 x y; rwa [if_neg (fun hh => h (congrArg Fin.val hh))] at this
  have d6 : ∀ (x y : Fin k), x.1 = y.1 → sm (p (b' x) (b y) - 1) := by
    intro x y h; have := t6 x y; rwa [if_pos (Fin.ext h)] at this
  have o6 : ∀ (x y : Fin k), x.1 ≠ y.1 → sm (p (b' x) (b y) - 0) := by
    intro x y h; have := t6 x y; rwa [if_neg (fun hh => h (congrArg Fin.val hh))] at this
  have d16 : ∀ (x y : Fin ρ), x.1 = y.1 → sm (p (e x) (f y) - 1) := by
    intro x y h; have := t16 x y; rwa [if_pos (Fin.ext h)] at this
  have o16 : ∀ (x y : Fin ρ), x.1 ≠ y.1 → sm (p (e x) (f y) - 0) := by
    intro x y h; have := t16 x y; rwa [if_neg (fun hh => h (congrArg Fin.val hh))] at this
  have d11 : sm (p z z - -1) := by rw [sub_neg_eq_add]; exact t11
  by_cases hac : a.1 = c.1
  · rw [if_pos (Fin.ext hac)]
    unfold flagV sgnD
    split_ifs <;> first
      | omega
      | exact d11
      | exact d1 _ _ (by dsimp only; omega)
      | exact d6 _ _ (by dsimp only; omega)
      | exact d16 _ _ (by dsimp only; omega)
  · rw [if_neg (fun hh => hac (congrArg Fin.val hh))]
    unfold flagV
    split_ifs <;> first
      | omega
      | exact o1 _ _ (by dsimp only; omega)
      | exact o6 _ _ (by dsimp only; omega)
      | exact o16 _ _ (by dsimp only; omega)
      | (rw [sub_zero]; first
          | exact t2 _ _ | exact t3 _ | exact t4 _ _ | exact t5 _ _ | exact t7 _ | exact t8 _ _
          | exact t9 _ | exact t10 _ | exact t12 _ | exact t13 _ _ | exact t14 _ _ | exact t15 _)

end GlobalTheory.SeeConjRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentNeOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead.RevTab

open Classical Formalism.L2.SG.HidaSetting

theorem pairTable_of {M A : Type} [Ring A] (p : M → M → A) (Z sm : A → Prop) (hZ : ∀ c, Z c → sm c)
    (hadd : ∀ a b, sm a → sm b → sm (a + b)) {ρ k : ℕ} (e f : Fin ρ → M) (b b' : Fin k → M) (z : M) (u : A)
    (hu : sm (u - 1))
    (t1 : ∀ a c, Z (p (f a) (e c) - if a = c then 1 else 0)) (t2 : ∀ a j, Z (p (f a) (b j))) (t3 : ∀ a, Z (p (f a) z))
    (t4 : ∀ a c, Z (p (f a) (f c)))
    (t5 : ∀ i a, Z (p (b' i) (e a))) (t6 : ∀ i j, Z (p (b' i) (b j) - if i = j then u else 0)) (t7 : ∀ i, Z (p (b' i) z))
    (t8 : ∀ i a, Z (p (b' i) (f a)))
    (t9 : ∀ a, Z (p z (e a))) (t10 : ∀ j, Z (p z (b j))) (t11 : Z (p z z + 1)) (t12 : ∀ a, Z (p z (f a)))
    (t13 : ∀ a c, Z (p (e a) (e c))) (t14 : ∀ a j, Z (p (e a) (b j))) (t15 : ∀ a, Z (p (e a) z))
    (t16 : ∀ a c, Z (p (e a) (f c) - if a = c then 1 else 0)) :
    PairTable p sm e f b b' z := by
  refine ⟨fun a c => hZ _ (t1 a c), fun a j => hZ _ (t2 a j), fun a => hZ _ (t3 a), fun a c => hZ _ (t4 a c),
    fun i a => hZ _ (t5 i a), fun i j => ?_, fun i => hZ _ (t7 i), fun i a => hZ _ (t8 i a),
    fun a => hZ _ (t9 a), fun j => hZ _ (t10 j), hZ _ t11, fun a => hZ _ (t12 a),
    fun a c => hZ _ (t13 a c), fun a j => hZ _ (t14 a j), fun a => hZ _ (t15 a), fun a c => hZ _ (t16 a c)⟩
  have h := hZ _ (t6 i j)
  by_cases hij : i = j
  · simp only [hij, if_true] at h ⊢
    have := hadd _ _ h hu
    rwa [show p (b' j) (b j) - u + (u - 1) = p (b' j) (b j) - 1 by abel] at this
  · simpa only [hij, if_false] using h

variable {D : D7}

theorem smallAt_add {PP : Pl D.host.E} {a b : EAf D} (ha : SmallAt PP a) (hb : SmallAt PP b) : SmallAt PP (a + b) := by
  unfold SmallAt at *
  rw [RingHom.map_add]
  exact Valuation.map_add_lt _ ha hb

theorem smallAt_of_mul {PP : Pl D.host.E} {g : ℕ} (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) {t : EAf D}
    (ht : t ∈ GlobalTheory.StdFrames.OA D) : SmallAt PP ((g : EAf D) * t) := by
  unfold SmallAt
  have hv : Valued.v (g : PP.adicCompletion D.host.E) < 1 := by
    have := (PP.valuation_lt_one_iff_mem (K := D.host.E) (g : 𝓞 D.host.E)).2 hg
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
    simpa using this
  rw [RingHom.map_mul, map_natCast, Valuation.map_mul]
  have h1 := (GlobalTheory.AdIsom.mem_OA t).1 ht PP
  calc Valued.v (g : PP.adicCompletion D.host.E) * Valued.v (GlobalTheory.StdFrames.cpt PP t)
      ≤ Valued.v (g : PP.adicCompletion D.host.E) * 1 := mul_le_mul_of_nonneg_left h1 zero_le'
    _ = Valued.v (g : PP.adicCompletion D.host.E) := mul_one _
    _ < 1 := hv

end GlobalTheory.SeeConjRead.RevTab

namespace GlobalTheory.SeeConjRead.RevTab

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf
open scoped TensorProduct

section Cong

variable {I : Formalism.MainNotions.S.AutInst} {g : ℕ}

theorem zmod_swap {x y : VA I} {d : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F} (h : ZMod' I g (hA I x y - d)) :
    ZMod' I g (hA I y x - sigA I d) := by
  have := unitaryCongruence.Z_sig I g h
  rwa [map_sub, ← unitaryCongruence.hA_symm] at this

theorem zmod_swap0 {x y : VA I} (h : ZMod' I g (hA I x y)) : ZMod' I g (hA I y x) := by
  have := unitaryCongruence.Z_sig I g h
  rwa [← unitaryCongruence.hA_symm] at this

theorem zmod_swap_delta {ρ : ℕ} {x y : VA I} {a c : Fin ρ} (h : ZMod' I g (hA I x y - if c = a then 1 else 0)) :
    ZMod' I g (hA I y x - if a = c then 1 else 0) := by
  have := zmod_swap h
  by_cases hac : a = c
  · subst hac
    simpa using this
  · simpa [hac, Ne.symm hac] using this

theorem zmod_diag {k : ℕ} {bw bwd : Fin k → VA I} {ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F}
    (hD : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0)) (i j : Fin k) :
    ZMod' I g (hA I (bw (Fin.rev i)) (bwd (Fin.rev j)) - if i = j then sigA I ew else 0) := by
  have := zmod_swap (hD (Fin.rev j) (Fin.rev i))
  by_cases hij : i = j
  · subst hij
    simpa using this
  · have h2 : ¬ Fin.rev j = Fin.rev i := fun h => hij (Fin.rev_injective h).symm
    simpa [hij, h2] using this

end Cong

variable {D : D7}

theorem smallAt_sg_sub_one {PP : Pl D.host.E} {g : ℕ} (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) {ew : EAf D}
    (hc0 : ∃ t ∈ GlobalTheory.StdFrames.OA D, 1 - ew - GlobalTheory.StdFrames.sg D ew = (g : EAf D) * t) (hid : ew * ew = ew)
    (hne : GlobalTheory.StdFrames.cpt PP ew ≠ 1) : SmallAt PP (GlobalTheory.StdFrames.sg D ew - 1) := by
  have h0 : GlobalTheory.StdFrames.cpt PP ew = 0 := by
    have h1 := congrArg (GlobalTheory.StdFrames.cpt PP) hid
    rw [map_mul] at h1
    have h2 : GlobalTheory.StdFrames.cpt PP ew * (GlobalTheory.StdFrames.cpt PP ew - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne
  obtain ⟨t, ht, hc⟩ := hc0
  have hs := smallAt_of_mul hg ht
  rw [← hc] at hs
  have e1 : GlobalTheory.StdFrames.sg D ew - 1 = -(1 - ew - GlobalTheory.StdFrames.sg D ew) - ew := by ring
  unfold SmallAt at *
  rw [e1, map_sub, map_neg, h0, sub_zero, Valuation.map_neg]
  exact hs

end GlobalTheory.SeeConjRead.RevTab

namespace GlobalTheory.SeeConjRead

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf RevTab

theorem pairTable_rev : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) ≠ 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (fun i => bwdT X h (Fin.rev i)) (fun i => bwT X h (Fin.rev i)) (z0T X h) := by
  intro D X h PP hg hne
  have hc0 : ZMod' X.B.I X.B.g (1 - X.ew - sigA X.B.I X.ew) := by
    have hz := X.vectorsInLattice.2.1
    have h2 : ZMod' X.B.I X.B.g (hA X.B.I X.z0 ((1 - X.ew - sigA X.B.I X.ew) • X.z0)) :=
      unitaryCongruence.mL_Qs X.B.I X.B.g hz (X.ew_full _ hz)
    rw [unitaryCongruence.hA_smul_right] at h2
    have hint : (1 - X.ew - sigA X.B.I X.ew) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
      sub_mem (sub_mem (one_mem _) X.ew_int) (unitaryCongruence.sigA_mem _ X.ew_int)
    have h4 := unitaryCongruence.Z_sub X.B.I X.B.g (unitaryCongruence.Z_smul X.B.I X.B.g hint X.formsAtZero.1) h2
    rwa [show (1 - X.ew - sigA X.B.I X.ew) * (hA X.B.I X.z0 X.z0 + 1) -
      (1 - X.ew - sigA X.B.I X.ew) * hA X.B.I X.z0 X.z0 = 1 - X.ew - sigA X.B.I X.ew by ring] at h4
  have hG := X.gramIntegral
  have hZ := X.formsAtZero
  have hW := X.weightVectorsIntegral
  have hD := X.bw_dual
  have hgq := X.g_eq
  have hid := X.ew_idem
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h hc0 hG hZ hW hD hgq hid hne ⊢
  subst h
  subst hgq
  refine pairTable_of (hY D) (ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1)) (SmallAt PP)
    (fun c ⟨t, ht, hc⟩ => hc ▸ smallAt_of_mul hg ht) (fun a b => smallAt_add) _ _ _ _ _ _
    (smallAt_sg_sub_one hg hc0 hid hne)
    (fun a c => zmod_swap_delta (hG c a).2.2) (fun a j => ((hW (Fin.rev j)).2.2 a).2.2.2) (fun a => (hZ.2 a).2)
    (fun a c => (hG a c).2.1)
    (fun i a => zmod_swap0 ((hW (Fin.rev i)).2.2 a).1) (fun i j => zmod_diag hD i j)
    (fun i => zmod_swap0 (hW (Fin.rev i)).1) (fun i a => zmod_swap0 ((hW (Fin.rev i)).2.2 a).2.1)
    (fun a => zmod_swap0 (hZ.2 a).1) (fun j => (hW (Fin.rev j)).2.1) hZ.1 (fun a => zmod_swap0 (hZ.2 a).2)
    (fun a c => (hG a c).1) (fun a j => ((hW (Fin.rev j)).2.2 a).2.2.1) (fun a => (hZ.2 a).1)
    (fun a c => (hG a c).2.2)

end GlobalTheory.SeeConjRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem smallAt_natCast_mul {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal) {t : EAf D}
    (ht : t ∈ GlobalTheory.StdFrames.OA D) : SmallAt PP ((N : EAf D) * t) := by
  unfold SmallAt
  rw [map_mul, map_natCast, Valuation.map_mul]
  have hv : Valued.v (N : PP.adicCompletion D.host.E) < 1 := by
    have := (PP.valuation_lt_one_iff_mem (K := D.host.E) (N : 𝓞 D.host.E)).2 hN
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
    simpa using this
  have ht' := (GlobalTheory.AdIsom.mem_OA t).1 ht PP
  exact lt_of_le_of_lt (mul_le_of_le_one_right' ht') hv

theorem sg_hY {D : D7} (x y : Fin (Yc D 0).rank → EAf D) : GlobalTheory.StdFrames.sg D (hY D x y) = hY D y x := by
  have := GlobalTheory.AdIsom.cjA_hA (Yc D 0) y x
  rw [GlobalTheory.AdIsom.hA_eq, GlobalTheory.AdIsom.hA_eq] at this
  exact this

theorem smallAt_of_mul {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal) {c : EAf D}
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, c = (N : EAf D) * t) : SmallAt PP c := by
  obtain ⟨t, ht, rfl⟩ := h
  exact smallAt_natCast_mul hN ht

theorem smallAt_hY_of_swap {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {x y : Fin (Yc D 0).rank → EAf D} {d : EAf D} (hd : GlobalTheory.StdFrames.sg D d = d)
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x - d = (N : EAf D) * t) : SmallAt PP (hY D x y - d) := by
  obtain ⟨t, ht, e⟩ := h
  have e' := congrArg (GlobalTheory.StdFrames.sg D) e
  rw [map_sub, sg_hY, hd, map_mul, map_natCast] at e'
  rw [e']
  exact smallAt_natCast_mul hN (GlobalTheory.AdIsom.cjA_mem ht)

theorem smallAt_hY_of_swap0 {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {x y : Fin (Yc D 0).rank → EAf D} (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x = (N : EAf D) * t) :
    SmallAt PP (hY D x y) := by
  have := smallAt_hY_of_swap hN (x := x) (y := y) (d := 0) (map_zero _) (by simpa using h)
  simpa using this

theorem smallAt_hY_of_swap_delta {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {ι : Type} [DecidableEq ι] {a c : ι} {x y : Fin (Yc D 0).rank → EAf D}
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x - (if c = a then 1 else 0) = (N : EAf D) * t) :
    SmallAt PP (hY D x y - if a = c then 1 else 0) := by
  refine smallAt_hY_of_swap hN (by split_ifs <;> simp) ?_
  simpa only [eq_comm (a := a)] using h

theorem smallAt_sub_of_cpt {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {ι : Type} [DecidableEq ι] {i j : ι} {c e : EAf D} (he : GlobalTheory.StdFrames.cpt PP e = 1)
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, c - (if i = j then e else 0) = (N : EAf D) * t) :
    SmallAt PP (c - if i = j then 1 else 0) := by
  obtain ⟨t, ht, e'⟩ := h
  have h1 : GlobalTheory.StdFrames.cpt PP (c - if i = j then 1 else 0) = GlobalTheory.StdFrames.cpt PP ((N : EAf D) * t) := by
    rw [← e']
    split_ifs <;> simp [he]
  have h2 := smallAt_natCast_mul hN ht
  unfold SmallAt at h2 ⊢
  rwa [h1]

theorem pairTable_of_cpt_one : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (bwT X h) (bwdT X h) (z0T X h) := by
  intro D X h PP hg hew
  have F0g := X.gramIntegral
  have F0z := X.formsAtZero
  have F0W := X.weightVectorsIntegral
  have bd := X.bw_dual
  have ge := X.g_eq
  rcases X with ⟨⟨I⟩⟩
  dsimp only at h F0g F0z F0W bd ge hew ⊢
  subst h
  subst ge
  refine ⟨fun a c => smallAt_hY_of_swap_delta hg (F0g c a).2.2, fun a j => smallAt_of_mul hg ((F0W j).2.2 a).2.1,
    fun a => smallAt_of_mul hg (F0z.2 a).2, fun a c => smallAt_of_mul hg (F0g a c).2.1,
    fun i a => smallAt_hY_of_swap0 hg ((F0W i).2.2 a).2.2.1, fun i j => smallAt_sub_of_cpt hg hew (bd i j),
    fun i => smallAt_hY_of_swap0 hg (F0W i).2.1, fun i a => smallAt_hY_of_swap0 hg ((F0W i).2.2 a).2.2.2,
    fun a => smallAt_hY_of_swap0 hg (F0z.2 a).1, fun j => smallAt_of_mul hg (F0W j).1, smallAt_of_mul hg F0z.1,
    fun a => smallAt_hY_of_swap0 hg (F0z.2 a).2, fun a c => smallAt_of_mul hg (F0g a c).1,
    fun a j => smallAt_of_mul hg ((F0W j).2.2 a).1, fun a => smallAt_of_mul hg (F0z.2 a).1,
    fun a c => smallAt_of_mul hg (F0g a c).2.2⟩

end GlobalTheory.SeeConjRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormsOfBoundedAdelicFunctionNormBoundedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_of_bounded_adelic_function_norm_bounded : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → ∃ K : ℝ, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, C.X.pnorm (wtOf C.X C.hr c c' S.rank) (F L) x ≤ K := by
  first | exact @GlobalTheory.AdSpan.BddForms.pnorm_le_of_bdd | exact GlobalTheory.AdSpan.BddForms.pnorm_le_of_bdd | (intros; apply GlobalTheory.AdSpan.BddForms.pnorm_le_of_bdd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelValueSumWeightTriangularFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeKernel_value_sum_weight_triangular_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), admitted l P p → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.TotalAt Xo c P p i → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.FunAt Xo c P p i → ∀ f ∈ sec Xo c a n, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (y y' : FrPt Xo c Ω), FrBor t y y' → hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y' = wchar (ex Dw a n) t * hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y := by
  first | exact @GlobalTheory.HeckeWeight.hkVal_frBor | exact GlobalTheory.HeckeWeight.hkVal_frBor | (intros; apply GlobalTheory.HeckeWeight.hkVal_frBor <;> assumption)
end

