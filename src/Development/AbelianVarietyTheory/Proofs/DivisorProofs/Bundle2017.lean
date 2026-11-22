import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTransportCmPreservesAdmissibleForms
section
noncomputable section

open scoped TensorProduct Matrix ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilAdmCM

variable {F : Type} [Field F] [NumberField F]

theorem std_fin (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) :=
  GlobalTheory.T.standardTraceAdelicAddChar_finite_rational_eq_exp F ψ hψ x

theorem std_beta (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) :
    ∃ β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧ ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0 :=
  GlobalTheory.T.standardAddChar_archimedean_eq_exp_nondegenerate F ψ hψ

theorem fixed_invariant_compactSupport (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))
    (hM : IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))) :
    ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) (K : Set (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact K ∧ ∀ Φ : (κ → AF F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 F m) Φ = Φ) →
        (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 :=
  GlobalTheory.WeilAdm.fixed_schroedinger_invariant_compactSupport_bounded_annihilator ψ
    (fun O hO => GlobalTheory.ScalarAnnih.exists_compact_annihilator_finiteAdeles_traceChar F ψ hψ.1 (std_fin ψ hψ) O hO) κ M hM

theorem realcont (ps : AddChar (AF F) ℂ) (hψ : IsStd ps) (κ : Type) [Fintype κ]
    (L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ]
      ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (A : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hA : ∀ f, ∫⁻ z, ‖A f z‖ₑ ^ 2 ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2)
    (hI : ∀ v (f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ), ⇑f' = GlobalTheory.WeilAdm.schrInf F ps v ⇑f →
      ⇑(A f') = GlobalTheory.WeilAdm.schrInf F ps (L v) ⇑(A f)) :
    Continuous A := by
  obtain ⟨β, hβ1, hnd⟩ := std_beta ps hψ
  obtain ⟨n, Q, P, hQP⟩ := GlobalTheory.T.exists_linear_model_archimedean_schroedinger_standard F ps β hβ1 hnd κ
  obtain ⟨c, hc⟩ := GlobalTheory.T.lintegral_sq_comp_continuousLinearEquiv_mixedSpace F κ n Q
  let CQ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q
  let CQi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q.symm
  have hCQ : ∀ f, ⇑(CQ f) = ⇑f ∘ ⇑Q := fun f => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q f
  have hCQi : ∀ g, ⇑(CQi g) = ⇑g ∘ ⇑Q.symm := fun g => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q.symm g
  have hQQ : ∀ f, CQi (CQ f) = f := fun f => by
    ext z; rw [hCQi, hCQ]; simp
  have hQQ' : ∀ g, CQ (CQi g) = g := fun g => by
    ext z; rw [hCQ, hCQi]; simp
  let A' : GlobalTheory.RealWeil.Sch (Fin n) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin n) := CQ.toLinearMap ∘ₗ A ∘ₗ CQi.toLinearMap
  have hA'apply : ∀ g, A' g = CQ (A (CQi g)) := fun g => rfl
  let L' : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) := P.trans (L.trans P.symm)
  have hbound : ∀ g, ∫⁻ x, ‖A' g x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
    intro g
    have e1 : ∫⁻ x, ‖A' g x‖ₑ ^ 2 = c * ∫⁻ z, ‖A (CQi g) z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hA'apply, hCQ, Function.comp_apply]
    have e2 : ∫⁻ x, ‖g x‖ₑ ^ 2 = c * ∫⁻ z, ‖CQi g z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hCQi, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [e1, e2, ← mul_assoc, mul_comm C c, mul_assoc]
    exact mul_le_mul' le_rfl (hA _)
  have hint : ∀ w (g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑g →
      ⇑(A' g') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g) := by
    intro w g g' hg
    have h1 : ⇑(CQi g') = GlobalTheory.WeilAdm.schrInf F ps (P w) ⇑(CQi g) := by
      have := congrArg (fun u => u ∘ ⇑Q.symm) (hQP w ⇑(CQi g))
      simp only [Function.comp_assoc, ContinuousLinearEquiv.self_comp_symm, Function.comp_id] at this
      rw [this, hCQi, hg, ← hCQ, hQQ']
    have h2 := hI (P w) (CQi g) (CQi g') h1
    have hL' : P (L' w) = L (P w) := P.apply_symm_apply _
    have h3 : ⇑(A (CQi g')) = GlobalTheory.WeilAdm.schrInf F ps (P (L' w)) ⇑(A (CQi g)) := by
      rw [h2]
      exact congrArg (fun v => GlobalTheory.WeilAdm.schrInf F ps v ⇑(A (CQi g))) hL'.symm
    calc ⇑(A' g') = ⇑(A (CQi g')) ∘ ⇑Q := hCQ _
      _ = GlobalTheory.WeilAdm.schrInf F ps (P (L' w)) ⇑(A (CQi g)) ∘ ⇑Q := congrArg (· ∘ ⇑Q) h3
      _ = GlobalTheory.RealWeil.rhoFun (L' w) (⇑(A (CQi g)) ∘ ⇑Q) := hQP _ _
      _ = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g) := congrArg (GlobalTheory.RealWeil.rhoFun (L' w)) (hCQ _).symm
  have hcont : Continuous A' :=
    GlobalTheory.T.continuous_of_lie_intertwine_l2 (Fin n) L' A' C hC hbound (GlobalTheory.T.derived_action_intertwines_of_group (Fin n) L'.toLinearMap A' C hC hbound hint)
  have hAeq : ⇑A = fun f => CQi (A' (CQ f)) := by
    funext f
    rw [hA'apply, hQQ, hQQ]
  rw [hAeq]
  exact CQi.continuous.comp (hcont.comp CQ.continuous)

open GlobalTheory.WeilAdm in
set_option maxHeartbeats 1000000 in

theorem weilAdmissible_of_heisenberg_unitary (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    (B : ((κ → AF F) × (κ → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F)))
    (O : Module.End ℂ ((κ → AF F) → ℂ))
    (hpres : ∀ φ ∈ GlobalTheory.WeilM.schA F κ, O φ ∈ GlobalTheory.WeilM.schA F κ)
    (himpl : ∀ w, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, O (GlobalTheory.WeilM.schr ψ w φ) = GlobalTheory.WeilM.schr ψ (B w) (O φ))
    (hunit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ x, ‖O φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) :
    ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ O ∈ (GlobalTheory.WeilM.adeleClass F).adm κ := by
  intro l hl g hg
  obtain ⟨M, hMo, hM⟩ := GlobalTheory.WeilAdm.pureA_fixed_fin F ψ hψ.1 κ g hg
  obtain ⟨M', hM'o, hM'⟩ := GlobalTheory.WeilAdm.fintrans F κ B M hMo
  obtain ⟨U, K, hUo, hUc, hK, hfix⟩ := fixed_invariant_compactSupport ψ hψ κ M' hM'o
  obtain ⟨R, hRsb, hdec⟩ := GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator F κ U K hUo hUc hK
  obtain ⟨L, hL⟩ := GlobalTheory.WeilAdm.infLin_main F κ B
  obtain ⟨μ, hμ, C, c, hC, hc0, hcT, hpure, hslice⟩ := GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds F κ g hg U hUo
  have hpA : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hfixed : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ m ∈ M',
      GlobalTheory.WeilM.schr ψ (finE2 F m) (O (GlobalTheory.WeilM.pureA F f g)) = O (GlobalTheory.WeilM.pureA F f g) := by
    intro f m hm
    obtain ⟨m0, hm0, hB⟩ := hM' m hm
    rw [← hB, ← himpl _ _ (hpA f), hM m0 hm0]
  have hs : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (r : κ → FiniteAdeleRing (𝓞 F) F),
      ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ z,
        s z = slice F (O (GlobalTheory.WeilM.pureA F f g)) r z :=
    fun f r => exists_schwartz_slice _ (hpres _ (hpA f)) r
  choose sl hsl using hs
  let A : (κ → FiniteAdeleRing (𝓞 F) F) →
      (SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :=
    fun r =>
    { toFun := fun f => sl f r
      map_add' := fun f f' => by
        ext z
        rw [SchwartzMap.add_apply, hsl, hsl, hsl, show ⇑(f + f') = ⇑f + ⇑f' from funext fun _ => rfl, pureA_add, map_add]
        rfl
      map_smul' := fun a f => by
        ext z
        rw [SchwartzMap.smul_apply, hsl, hsl, show ⇑(a • f) = a • ⇑f from funext fun _ => rfl, pureA_smul, map_smul]
        rfl }
  have hA : ∀ r f, ⇑(A r f) = slice F (O (GlobalTheory.WeilM.pureA F f g)) r := fun r f => funext (hsl f r)
  have hcont : ∀ r, Continuous (A r) := by
    intro r
    refine realcont ψ hψ κ L (A r) (C / c) (ENNReal.div_ne_top hC hc0) (fun f => ?_) (fun v f f' hf => ?_)
    · have h1 := hslice _ (hpres _ (hpA f)) (hfix _ (hfixed f)).1 r
      rw [hunit μ hμ _ (hpA f)] at h1
      have h2 := h1.trans (hpure f)
      rw [hA, ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hcT), mul_comm]
      exact h2
    · rw [hA, hA, hf, pureA_schrInf, himpl _ _ (hpA f), hL, slice_schr]
  have hT : ∀ r ∈ R, ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      l (GlobalTheory.WeilM.pureA F f (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ))) = T f :=
    fun r hr => hl _ (hRsb r hr)
  choose T hT using hT
  refine ⟨∑ r ∈ R.attach, (T r.1 r.2).comp ⟨A r.1, hcont r.1⟩, fun f => ?_⟩
  have hΦ := hdec (O (GlobalTheory.WeilM.pureA F f g)) (hfix _ (hfixed f)).1 (hfix _ (hfixed f)).2
  rw [LinearMap.comp_apply, hΦ, map_sum, ContinuousLinearMap.sum_apply, ← Finset.sum_attach R]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← hA, hT r.1 r.2]
  rfl

end GlobalTheory.WeilAdmCM

namespace GlobalTheory.WeilAdmCM

theorem transport_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              ∀ p, ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ om p ∈ (adeleClass F).adm κ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ _ co hco om htr p l hl
  have hP : (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) ∧
      ∀ p w, ∀ φ ∈ schA F κ, om p (co.rho B.ψ w φ) = co.rho B.ψ (actAB (cA σ) p w) (om p φ) :=
    GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hU : IsUnitaryOn (adeleClass F) om :=
    GlobalTheory.T.weilDatumTransport_cmExtension_isUnitaryOn F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ co hco om htr
  refine weilAdmissible_of_heisenberg_unitary B.ψ hB.std κ (co.e.symm.trans ((GlobalTheory.WeilAdm.actLin _ p).trans co.e)) (om p) (hP.1 p)
    (fun w φ hφ => ?_) (fun μ hμ φ hφ => hU μ hμ p φ hφ) l hl
  have h := hP.2 p (co.e.symm w) φ hφ
  simp only [GlobalTheory.WeilM.Darboux.rho, LinearEquiv.apply_symm_apply] at h
  exact h

end GlobalTheory.WeilAdmCM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepSmoothAtFinitePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_mem_uAt {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) :
    (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  show u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
  simp

theorem mul_mem_uAt {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R)
    {g h : UA σ X.J} (hg : g ∈ UAt σ X ev) (hh : h ∈ UAt σ X ev) : g * h ∈ UAt σ X ev := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    show mat g * mat h - 1 = _
    noncomm_ring
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem inv_mem_uAt {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R)
    {g : UA σ X.J} (hg : g ∈ UAt σ X ev) : g⁻¹ ∈ UAt σ X ev := by
  intro u hu
  have h1 : mat g⁻¹ * mat g = 1 := by
    show ((g⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)).1 = 1
    rw [inv_mul_cancel]; rfl
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

end GlobalTheory.SmoothAtPlace

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def locGrp {σ : E →ₐ[F] E} {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) :
    Subgroup (UA σ X.J × UA σ W.J) where
  carrier := {x | x.1 ∈ UAt σ X (evFin F v) ∧ x.2 ∈ UAt σ W (evFin F v)}
  one_mem' := ⟨one_mem_uAt X _, one_mem_uAt W _⟩
  mul_mem' ha hb := ⟨mul_mem_uAt X _ ha.1 hb.1, mul_mem_uAt W _ ha.2 hb.2⟩
  inv_mem' ha := ⟨inv_mem_uAt X _ ha.1, inv_mem_uAt W _ ha.2⟩

def tensL {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (R : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ := tens (evFin F v) φ R
  map_add' φ ψ := funext fun x => by simp [tens, add_mul]
  map_smul' c φ := funext fun x => by simp [tens, mul_assoc]

def locOp {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (R : (κ → AF F) → ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Module.End ℂ ((κ → Fv F v) → ℂ) :=
  (R 0)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun (t : κ → Fv F v) i => GlobalTheory.LatVac.liftV v (t i)) ∘ₗ T ∘ₗ tensL v R)

theorem tens_liftV {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {R : (κ → AF F) → ℂ} (φ : (κ → Fv F v) → ℂ)
    (hR : Rest (evFin F v) φ R) (t : κ → Fv F v) :
    tens (evFin F v) φ R (fun i => GlobalTheory.LatVac.liftV v (t i)) = φ t * R 0 := by
  have h1 := hR.1 0 (fun i => GlobalTheory.LatVac.liftV v (t i)) fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (t i) u hu
  rw [zero_add] at h1
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, h1]

theorem locOp_eq {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0) {φ φ₁ : (κ → Fv F v) → ℂ}
    (hR : Rest (evFin F v) φ R) (hR₁ : Rest (evFin F v) φ₁ R) {T : Module.End ℂ ((κ → AF F) → ℂ)}
    (h : Acts (evFin F v) T φ φ₁) : locOp v R T φ = φ₁ := by
  funext t
  have := h R hR
  simp only [locOp, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply]
  change (R 0)⁻¹ • T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)) = φ₁ t
  rw [this, tens_liftV v φ₁ hR₁ t, smul_eq_mul]
  field_simp

end GlobalTheory.SmoothAtPlace

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_fst (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (a : Fv F v) : (GlobalTheory.LatVac.liftV v a).1 = 0 := rfl

open scoped Classical in

theorem continuous_locOp {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} (hW : M.IsWeil B.ψ χX χW om) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (R : (Fin n × Fin d → AF F) → ℂ) (φ : (Fin n × Fin d → Fv F v) → ℂ)
    (hΦ : tens (evFin F v) φ R ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d))
    (lam : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ) :
    Continuous fun x : UA σ X.J × UA σ W.J => lam (locOp v R (om x) φ) := by
  let L : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun (t : Fin n × Fin d → Fv F v) i => GlobalTheory.LatVac.liftV v (t i))
  have hl : lam ∘ₗ L ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨lam (fun t => g (fun i => (GlobalTheory.LatVac.liftV v (t i)).2)) •
      ((BoundedContinuousFunction.evalCLM ℂ 0).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    have e : L (GlobalTheory.WeilM.pureA F f g) = f 0 • (fun t => g (fun i => (GlobalTheory.LatVac.liftV v (t i)).2)) := by
      funext t
      simp only [L, LinearMap.funLeft_apply, GlobalTheory.WeilM.pureA, liftV_fst, map_zero, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [LinearMap.comp_apply, e, map_smul, smul_eq_mul, _root_.smul_apply, smul_eq_mul, mul_comm]
    rfl
  have hc := hW.2.2 (lam ∘ₗ L) hl _ hΦ
  have h2 : Continuous fun x : UA σ X.J × UA σ W.J => (R 0)⁻¹ * (lam ∘ₗ L) (om x (tens (evFin F v) φ R)) :=
    continuous_const.mul hc
  refine h2.congr fun x => ?_
  simp only [locOp, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_eq_mul]
  rfl

end GlobalTheory.SmoothAtPlace

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem weil_smooth_at : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    (∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) →
      x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁) →
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∃ U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
      ∀ x ∈ U, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) → x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) →
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v hActs φ hφ
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  let H := locGrp (σ := σ) X W v
  let V := GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)
  have key : ∀ x ∈ H, ∀ ψ ∈ V, locOp v R (om x) ψ ∈ V ∧ Acts (evFin F v) (om x) ψ (locOp v R (om x) ψ) := by
    intro x hx ψ hψ
    obtain ⟨ψ₁, hψ₁, hA⟩ := hActs x hx.1 hx.2 ψ hψ
    rw [locOp_eq v hR0 (hR ψ hψ) (hR ψ₁ hψ₁) hA]
    exact ⟨hψ₁, hA⟩
  classical
  let S : UA σ X.J × UA σ W.J → Module.End ℂ V := fun x =>
    if hx : x ∈ H then (locOp v R (om x)).restrict (fun ψ hψ => (key x hx ψ hψ).1) else LinearMap.id
  have hS : ∀ x (hx : x ∈ H) (ψ : V), ((S x ψ : V) : (Fin n × Fin d → Fv F v) → ℂ) = locOp v R (om x) ψ := by
    intro x hx ψ
    simp only [S, dif_pos hx]
    rfl
  have hmul : ∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y := by
    intro x hx y hy
    ext ψ : 1
    apply Subtype.ext
    rw [hS _ (H.mul_mem hx hy), Module.End.mul_apply, hS _ hx, hS _ hy]
    have h1 := key y hy ψ ψ.2
    have h2 := key x hx _ h1.1
    refine locOp_eq v hR0 (hR ψ ψ.2) (hR _ h2.1) fun r hr => ?_
    have hr' : Rest (evFin F v) (locOp v R (om y) ψ) r := ⟨hr.1, by
      rw [← h1.2 r hr]
      exact (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil).pres y _ hr.2⟩
    rw [map_mul, Module.End.mul_apply, h1.2 r hr, h2.2 r hr']
  have hone : S 1 = 1 := by
    ext ψ : 1
    apply Subtype.ext
    rw [hS 1 H.one_mem]
    exact locOp_eq v hR0 (hR ψ ψ.2) (hR ψ ψ.2) fun r _ => by rw [map_one]; rfl
  have hcont : ∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set (UA σ X.J × UA σ W.J)) := by
    intro l w
    obtain ⟨lam, hlam⟩ := LinearMap.exists_extend l
    refine (continuous_locOp hP.weil v R w.1 (hR w.1 w.2).2 lam).continuousOn.congr fun x hx => ?_
    have : S x w = ⟨locOp v R (om x) w, (key x hx w w.2).1⟩ := Subtype.ext (hS x hx w)
    rw [this, ← hlam]
    rfl
  have hbasis : ∀ U ∈ 𝓝 (1 : UA σ X.J × UA σ W.J), ∃ K : Subgroup (UA σ X.J × UA σ W.J), K ≤ H ∧
      IsCompact (K : Set (UA σ X.J × UA σ W.J)) ∧
      (∃ O : Set (UA σ X.J × UA σ W.J), IsOpen O ∧ (1 : UA σ X.J × UA σ W.J) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧
      (K : Set (UA σ X.J × UA σ W.J)) ⊆ U := by
    intro U hU
    rw [show (1 : UA σ X.J × UA σ W.J) = (1, 1) from rfl, nhds_prod_eq] at hU
    obtain ⟨U1, hU1, U2, hU2, hsub⟩ := Filter.mem_prod_iff.1 hU
    obtain ⟨K1, hK1H, hK1c, ⟨O1, hO1, h1O1, hO1K⟩, hK1U⟩ := GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace hσ X v U1 hU1
    obtain ⟨K2, hK2H, hK2c, ⟨O2, hO2, h1O2, hO2K⟩, hK2U⟩ := GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace hσ W v U2 hU2
    refine ⟨K1.prod K2, fun x hx => ⟨hK1H _ hx.1, hK2H _ hx.2⟩, ?_,
      ⟨O1 ×ˢ O2, hO1.prod hO2, ⟨h1O1, h1O2⟩, fun x hx hxH => ⟨hO1K _ hx.1 hxH.1, hO2K _ hx.2 hxH.2⟩⟩,
      fun x hx => hsub ⟨hK1U hx.1, hK2U hx.2⟩⟩
    rw [Subgroup.coe_prod]
    exact hK1c.prod hK2c
  obtain ⟨U, hU, hfix⟩ := GlobalTheory.T.exists_nhds_fix_of_continuous_coefficients GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded H S hmul hone hcont hbasis ⟨φ, hφ⟩
  refine ⟨U, hU, fun x hxU hx1 hx2 => ?_⟩
  have hx : x ∈ H := ⟨hx1, hx2⟩
  have e := congrArg Subtype.val (hfix x hxU hx)
  rw [hS x hx] at e
  have := (key x hx φ hφ).2
  rwa [e] at this

end GlobalTheory.SmoothAtPlace
end
end

