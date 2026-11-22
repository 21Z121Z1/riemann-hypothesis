import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0726
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0453
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
import Development.AbelianVarietyTheory.Counterexamples.ThetaValuation.UniformMultiplier
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfActs
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

noncomputable section

namespace GlobalTheory.HoweLocal.LocUnitNonsplit

variable {F : Type} [Field F] [NumberField F]

theorem lintegral_eq_of_acts {κ : Type} [Fintype κ] (v : Pl F)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (hT : ∀ ν : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∀ Φ ∈ schA F κ, ∫⁻ x, ‖T Φ x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂ν)
    {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) (hφ₁ : φ₁ ∈ SB (κ → Fv F v))
    (hact : Acts (evFin F v) T φ φ₁)
    (μ : @Measure (κ → Fv F v) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mV : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  let ev : (κ → AF F) → (κ → Fv F v) := fun x i => evFin F v (x i)
  have hevc : Continuous ev :=
    continuous_pi fun i => (GlobalTheory.LatAtClosed.continuous_evFin' v).comp (continuous_apply i)
  have hevm : Measurable ev := hevc.measurable
  let φ₀ : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1
  have hφ₀ : φ₀ ∈ SB (κ → Fv F v) := GlobalTheory.StdVacuum.indicator_mem_SB v
  have hφ₀0 : φ₀ 0 = 1 := by
    show Set.indicator _ 1 0 = 1
    rw [Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} from
      fun k => zero_mem _)]
    rfl
  let lift : (κ → Fv F v) → (κ → AF F) := fun a i => GlobalTheory.LatVac.liftV v (a i)
  have hlc : Continuous lift :=
    continuous_pi fun i => (GlobalTheory.LatAtClosed.continuous_liftV v).comp (continuous_apply i)
  have hat : ∀ a, At (evFin F v) (lift a) := fun a u hu => by
    funext i; exact GlobalTheory.LatVac.at_liftV v (a i) u hu
  have hevl : ∀ a, ev (lift a) = a := fun a => by
    funext i; exact GlobalTheory.LatVac.evFin_liftV v (a i)
  have hev_add : ∀ x y, ev (x + y) = ev x + ev y := fun x y => by
    funext i; exact map_add (evFin F v) (x i) (y i)

  have hRc : Continuous R := by
    have e : R = fun x => tens (evFin F v) φ₀ R (x - lift (ev x)) := by
      funext x
      have h1 : R (x - lift (ev x)) = R x := by
        rw [sub_eq_add_neg]
        refine (hR φ₀ hφ₀).1 x _ ?_
        intro u hu
        rw [smul_neg, hat (ev x) u hu, neg_zero]
      have h2 : (fun i => evFin F v ((x - lift (ev x)) i)) = 0 := by
        funext i
        show evFin F v (x i - GlobalTheory.LatVac.liftV v (evFin F v (x i))) = 0
        rw [map_sub, GlobalTheory.LatVac.evFin_liftV, sub_self]
      show R x = φ₀ (fun i => evFin F v ((x - lift (ev x)) i)) * R (x - lift (ev x))
      rw [h2, hφ₀0, one_mul, h1]
    rw [e]
    exact (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hR φ₀ hφ₀).2).comp
      (continuous_id.sub (hlc.comp hevc))
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (κ → AF F), ν.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  let d : (κ → AF F) → ENNReal := fun x => ‖R x‖ₑ ^ 2
  have hd : Measurable d := hRc.measurable.enorm.pow_const 2
  let m : Measure (κ → Fv F v) := (ν.withDensity d).map ev
  have hmint : ∀ f : (κ → Fv F v) → ENNReal, Measurable f → ∫⁻ y, f y ∂m = ∫⁻ x, d x * f (ev x) ∂ν := by
    intro f hf
    rw [lintegral_map hf hevm]
    exact lintegral_withDensity_eq_lintegral_mul ν hd (hf.comp hevm)
  have hsq : ∀ ψ' ∈ SB (κ → Fv F v), ∫⁻ y, ‖ψ' y‖ₑ ^ 2 ∂m = ∫⁻ x, ‖tens (evFin F v) ψ' R x‖ₑ ^ 2 ∂ν := by
    intro ψ' hψ'
    rw [hmint _ (hψ'.1.continuous.measurable.enorm.pow_const 2)]
    congr 1
    funext x
    simp only [tens, d, ev, enorm_mul, mul_pow]
    ring

  haveI hinv : m.IsAddLeftInvariant := by
    constructor
    intro a
    ext s hs
    rw [Measure.map_apply (measurable_const_add a) hs]
    have hs' : MeasurableSet ((fun y => a + y) ⁻¹' s) := measurable_const_add a hs
    rw [← lintegral_indicator_one hs', ← lintegral_indicator_one hs, hmint _ (measurable_one.indicator hs'),
      hmint _ (measurable_one.indicator hs)]
    refine Eq.trans ?_ (lintegral_add_right_eq_self (fun x => d x * s.indicator 1 (ev x)) (lift a))
    congr 1
    funext x
    have e1 : d (x + lift a) = d x := by
      show ‖R (x + lift a)‖ₑ ^ 2 = ‖R x‖ₑ ^ 2
      rw [(hR φ₀ hφ₀).1 x _ (hat a)]
    have e2 : ev (x + lift a) = a + ev x := by rw [hev_add, hevl, add_comm]
    show d x * ((fun y => a + y) ⁻¹' s).indicator 1 (ev x) = d (x + lift a) * s.indicator 1 (ev (x + lift a))
    rw [e1, e2]
    rfl

  let U : Set (κ → Fv F v) := φ₀ ⁻¹' {1}
  have hUo : IsOpen U := hφ₀.1.isOpen_fiber 1
  have hU0 : (0 : κ → Fv F v) ∈ U := hφ₀0
  have hUm : m U < ⊤ := by
    calc m U = ∫⁻ y, U.indicator 1 y ∂m := (lintegral_indicator_one hUo.measurableSet).symm
    _ ≤ ∫⁻ y, ‖φ₀ y‖ₑ ^ 2 ∂m := lintegral_mono fun y => by
        by_cases hy : y ∈ U
        · rw [Set.indicator_of_mem hy]
          have h1 : φ₀ y = 1 := hy
          rw [h1]; simp
        · simp [hy]
    _ = ∫⁻ x, ‖tens (evFin F v) φ₀ R x‖ₑ ^ 2 ∂ν := hsq φ₀ hφ₀
    _ < ⊤ := by
        have hL := GlobalTheory.TorusDilate.memLp_of_mem_schA ν hν (hR φ₀ hφ₀).2
        have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hL.eLpNorm_lt_top
        simpa using h2
  haveI : IsLocallyFiniteMeasure m := ⟨fun y => ⟨(fun z => -y + z) ⁻¹' U,
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (hUo.mem_nhds (by simpa using hU0)),
    by rw [measure_preimage_add]; exact hUm⟩⟩

  let c := m.addHaarScalarFactor μ
  have hmc : ∀ ψ' ∈ SB (κ → Fv F v), ∫⁻ y, ‖ψ' y‖ₑ ^ 2 ∂m = c * ∫⁻ y, ‖ψ' y‖ₑ ^ 2 ∂μ := by
    intro ψ' hψ'
    have hc : Continuous fun y => ‖ψ' y‖ ^ 2 := hψ'.1.continuous.norm.pow 2
    have hcs : HasCompactSupport fun y => ‖ψ' y‖ ^ 2 :=
      hψ'.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    have key := Measure.integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport m μ hc hcs
    have conv : ∀ ρ : Measure (κ → Fv F v), IsFiniteMeasureOnCompacts ρ →
        ∫⁻ y, ‖ψ' y‖ₑ ^ 2 ∂ρ = ENNReal.ofReal (∫ y, ‖ψ' y‖ ^ 2 ∂ρ) := by
      intro ρ _
      rw [ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hcs)
        (Filter.Eventually.of_forall fun _ => by positivity)]
      congr 1
      funext y
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rw [conv m inferInstance, key, ← conv _ inferInstance, lintegral_smul_measure]
    rfl
  have hc0 : (c : ENNReal) ≠ 0 := by
    intro h0
    have h1 := hmc φ₀ hφ₀
    rw [h0, zero_mul, hsq φ₀ hφ₀] at h1
    refine GlobalTheory.TorusDilate.lintegral_sq_ne_zero ν hν
      (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hR φ₀ hφ₀).2) ?_ h1
    show φ₀ (fun i => evFin F v ((0 : κ → AF F) i)) * R 0 ≠ 0
    have h2 : (fun i => evFin F v ((0 : κ → AF F) i)) = 0 := by funext i; exact map_zero _
    rw [h2, hφ₀0, one_mul]
    exact hR0
  have hU := hT ν hν _ (hR φ hφ).2
  rw [hact R (hR φ hφ)] at hU
  have hmm : ∫⁻ y, ‖φ₁ y‖ₑ ^ 2 ∂m = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂m := by rw [hsq φ₁ hφ₁, hsq φ hφ, hU]
  rw [hmc φ₁ hφ₁, hmc φ hφ] at hmm
  exact (ENNReal.mul_right_inj hc0 ENNReal.coe_ne_top).1 hmm

end GlobalTheory.HoweLocal.LocUnitNonsplit

open GlobalTheory.HoweLocal.LocUnitNonsplit in

theorem GlobalTheory.HoweLocal.LocUnitNonsplit.isUnitaryOn_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a b : ℕ)
    (JA : Matrix (Fin a) (Fin a) E) (B : Spc F E b) (κ : Type) [Fintype κ]
    (dA : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F B.J)) κ) (ψ : AddChar (AF F) ℂ)
    (omB : UA σ B.J →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → IsUSplitting (adeleClass F) ψ dA (actB (cA σ)) omB →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
    ∀ (eB : UAtGrp σ B (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)),
      GlobalTheory.HoweLocal.IsCompIso σ B v eB →
    ∀ omL : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J) →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) ∧
        Acts (evFin F v) (omB (eB.symm g).1) φ (omL g φ)) →
    ∀ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (GlobalTheory.HoweLocal.Jv v B.J)) κ,
      (∀ x, co.e x = GlobalTheory.LatVac.locCo dA v (x.map (GlobalTheory.HoweLocal.liftE v))) →
    IsUnitaryOn (sbClass (Fv F v)) omL := by
  intro F E _ _ _ _ _ σ a b JA B κ _ dA ψ omB hstd hsplit v hv _ eB hcomp omL hL co hco
  intro μ hμ g φ hφ
  exact lintegral_eq_of_acts v (omB (eB.symm g).1) (fun ν hν Φ hΦ => hsplit.unit ν hν _ Φ hΦ) hφ (hL g φ hφ).1
    (hL g φ hφ).2 μ hμ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffAdjointFrameMatrixInte
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.QHalfLat

variable {D : D7}
open scoped Matrix

theorem frMapAdj_gen {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {c : AE D} {α : Af D.host.F}
    (hα : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {a : D.host.E} (hca : toEAf D (c * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {s : Fin S.rank → D.host.E} (hs : s ∈ ΛS) {t : Fin T.rank → D.host.E} (ht : t ∈ ΛT) :
    IsIntM (frMapAdj S T βS βT (c • GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.ConjHalfInt.map_gen, GlobalTheory.ConjHalfInt.adj_shape, Matrix.mul_smul, Matrix.smul_mul]
  refine GlobalTheory.ConjHalfInt.isIntM_smul (GlobalTheory.PlaceVec.cF_mem_int (mul_mem hca hα)) ?_
  have hA : (S.gram⁻¹).map (eToEAf D) *
      ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      Matrix.of fun m (_ : Fin 1) => eToEAf D (s m) := by
    ext m z
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, GlobalTheory.ConjHalfInt.cF_eToEAf,
      ← map_mul, ← map_sum]
    rw [GlobalTheory.ConjHalfInt.gram_inv_star]
  have hB : ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D) =
      Matrix.of fun (_ : Fin 1) m => eToEAf D (∑ l, star (t l) * T.gram l m) := by
    ext z m
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, GlobalTheory.ConjHalfInt.cF_eToEAf,
      ← map_mul, ← map_sum]
  have e : (βS⁻¹).val * (S.gram⁻¹).map (eToEAf D) *
      (((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ *
        ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ) *
      (T.gram.map (eToEAf D) * βT.val) =
      ((βS⁻¹).val * ((S.gram⁻¹).map (eToEAf D) *
        ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ)) *
      ((((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D)) *
        βT.val) := by
    simp only [Matrix.mul_assoc]
  rw [e, hA, hB]
  exact GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int fS hs) (GlobalTheory.ConjHalfInt.pair_row_int hT fT ht)

theorem isIntM_adj_of_mem {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {c : AE D} (hc : ∀ a ∈ D.host.AA, toEAf D (c * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {x : WO S T} (hx : IsHalf c x)
    (hl : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    IsIntM (frMapAdj S T βS βT x) := by
  have hx' : c • x = x := Matrix.ext hx
  rw [← hx']
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapAdj S T βS βT (c • u))) ?_ ?_ ?_ ?_ hl
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      exact frMapAdj_gen hS hT fS fT hα' (hc a ha) hs ht
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
    exact fun i j => neg_mem (hu i j)

theorem placesOK_of {e : AE D} {Q : Finset (Pl D.host.E)} (he : IsIdemSum e Q)
    (hQ : ∀ PP ∈ Q, ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) : GlobalTheory.ExportSeries.PlacesOK Q ∅ := by
  refine ⟨⟨Q, subset_rfl, Finset.empty_subset _, (⟨e, he⟩ : ∃ e : AE D, IsIdemSum e Q)⟩, Finset.disjoint_empty_right _, ?_⟩
  rintro PP (hPP | hPP) PP' hPP'
  · rcases hPP' with rfl | hc
    · exact GlobalTheory.HalfCompare.primeToAA_of_not_mem (hQ _ hPP)
    · rw [(GlobalTheory.IdemSupport.isConjPl_iff PP PP').1 hc]
      refine GlobalTheory.HalfCompare.primeToAA_of_not_mem ?_
      rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact hQ PP hPP
  · simp at hPP

end GlobalTheory.QHalfLat

open GlobalTheory.QHalfLat in

theorem GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ t : WO (Vc D i) (Wc D i), IsHalf (cA D eQ) t → (IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (t)) ↔ t ∈ lattice₂ R i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i _ Q hQt eQ he t ht
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hSW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hFV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i) := hBV.1
  have hFW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i) := hBW.1
  obtain ⟨t0, ht0⟩ := hQt
  have hbad : ∀ PP ∈ Q, ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => hG.2 t0 PP (ht0 hPP)
  have hP := placesOK_of he hbad
  have hid : GlobalTheory.ExportSeries.idem Q = eQ :=
    GlobalTheory.DatumFourier.idemSum_unique (Vc D i) he (show GlobalTheory.ExportSeries.SplitSet Q from ⟨eQ, he⟩).isIdemSum
  have ht' : IsHalf (cA D (GlobalTheory.ExportSeries.idem Q)) t := by rw [hid]; exact ht
  constructor
  · intro hi
    exact GlobalTheory.ConjLatAdj.mem_latO_of_adj_int hSV hSW hFV hFW hP ht' hi
  · intro hl
    exact isIntM_adj_of_mem hSV hSW hFV hFW (fun a ha => GlobalTheory.ConjHalfInt.toEAf_cA_idem_mul_mem hP ha) ht' hl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffFrameMatrixIntegralOnH
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HalfLatInt

variable {D : D7}

theorem toEAf_idem_mul_mem {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {a : D.host.E}
    (ha : a ∈ D.host.AA) : toEAf D (e * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  exact GlobalTheory.ConjHalfInt.toEAf_mul_mem ((hes PP hPP).2 : GlobalTheory.IdemSupport.Comparison₂ PP (es PP))
    (GlobalTheory.HalfCompare.primeToAA_of_not_mem (hP PP hPP)) ha

theorem isIntM_of_mem {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {x : WO S T}
    (hx : IsHalf e x) (hl : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    IsIntM (frMapO S T βS βT x) := by
  have hx' : e • x = x := Matrix.ext hx
  rw [← hx']
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapO S T βS βT (e • u))) ?_ ?_ ?_ ?_ hl
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      unfold frMapO
      rw [GlobalTheory.ConjHalfInt.map_gen, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc (βT⁻¹).val, Matrix.mul_assoc]
      exact GlobalTheory.ConjHalfInt.isIntM_smul (mul_mem (toEAf_idem_mul_mem he hP ha) hα')
        (GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int fT ht)
          (GlobalTheory.ConjHalfInt.pair_row_int hS fS hs))
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapO_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.ConjHalfInt.frMapO_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapO_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapO_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.ConjHalfInt.frMapO_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapO_neg]
    exact fun i j => neg_mem (hu i j)

open GlobalTheory.ExportSeries.Model in

theorem isIntM_adj {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {x : WO S T} (h : IsIntM (frMapO S T βS βT x)) : IsIntM (frMapAdj S T βS βT x) := by
  have e : x.map (toEAf D) = βT.val * frMapO S T βS βT x * (βS⁻¹).val := by
    unfold frMapO
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  have := int_mul (int_mul (gram_frame_int S hS fS).2 (int_ct h)) (gram_frame_int T hT fT).1
  rw [GlobalTheory.PlaceVec.frMapAdj_eq]
  change IsIntM (_ * ct (x.map (toEAf D)) * _)
  rw [e, ct_mul, ct_mul]
  simpa only [Matrix.mul_assoc] using this

theorem mem_of_isIntM {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {x : WO S T}
    (hx : IsHalf e x) (h : IsIntM (frMapO S T βS βT x)) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have hN : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  refine GlobalTheory.DatumFourier.mem_latO_of_int hS hT fS fT (Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj he) hN
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) ?_ ?_ (isIntM_adj hS hT fS fT h)
  · intro PP' hPP' hm
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hPP'
    have h2 : Formalism.L2.DIV.starOHom ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hm
    rw [map_natCast] at h2
    exact hP PP hPP (GlobalTheory.HalfCompare.mem_of_dvd h2 (Dvd.intro_left _ rfl))
  · intro i j
    rw [Formalism.L2.Theta.cA_cA]
    exact hx i j

end GlobalTheory.HalfLatInt

theorem GlobalTheory.HalfLatInt.isIntM_iff_mem_latP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ x → (IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x)) ↔ x ∈ lattice₂ R i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i _ Q hQ eQ he x hx
  obtain ⟨t, hQt⟩ := hQ
  have hSV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hSW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hP : ∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => hG.2 t PP (hQt hPP)
  exact ⟨GlobalTheory.HalfLatInt.mem_of_isIntM hSV hSW hBV.1 hBW.1 he hP hx,
    GlobalTheory.HalfLatInt.isIntM_of_mem hSV hBV.1 hBW.1 he hP hx⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatPIffMulVec
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev uAt {D : D7} {J : CoreJ D} {G : Type} (r : TwoRuns J G) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Fin D.R.m) :=
  (r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Build

theorem mem_localLattice_iff_mulVec {r : ℕ} (D : D7) {Λ Λ' : Submodule (𝓞 D.host.E) (Fin r → D.host.E)}
    (A : Matrix (Fin r) (Fin r) D.host.E) (h : ∀ w, w ∈ Λ ↔ A.mulVec w ∈ Λ') (w : Fin r → D.host.E) :
    w ∈ lattice₂ D Λ ↔ A.mulVec w ∈ lattice₂ D Λ' := by
  simp only [mem_latP]
  refine forall₂_congr fun a _ => ?_
  rw [h, Matrix.mulVec_smul]

theorem chi_one_of_toData {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xd : DataX E r) (X : Data E r)
    (e : Xd.toData = X) (h : ∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) : ∀ la, ∀ γ ∈ Xd.Γ, Xd.χ la γ = 1 := by
  subst e
  exact h

theorem nonempty_place (D : D7) : Nonempty (HeightOneSpectrum (𝓞 D.what₂.LL)) := by
  obtain ⟨I, hb, ht⟩ := (Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top).1 (NumberField.RingOfIntegers.not_isField D.what₂.LL)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I ht.ne
  exact ⟨⟨P, hP.isPrime, fun e => hb.ne' (le_bot_iff.1 (e ▸ hIP))⟩⟩

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem exists_dataX_latP (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (k : (uAt r v i).Comp) :
    ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (uAt r v i).X k ∧ Xx.L' = lattice₂ D ((uAt r v i).X k).Λ := by
  obtain ⟨X, ⟨h1, -, h3⟩, -⟩ := GlobalTheory.ModelLatticeCheck.holds_by_value D (r.used v).full.toCore (h.laws v).p.toLawsCore
    ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ (r.used v).full.σ₀ (r.used v).full.toCore.good_σ₀ k
  refine ⟨X, h1, ?_⟩
  rw [GlobalTheory.ModelLatExamples.eq_latP D X.Λ X.L' h3]
  show lattice₂ D X.toData.Λ = _
  rw [h1]

end Build

end GlobalTheory.ShareOn

end
end

