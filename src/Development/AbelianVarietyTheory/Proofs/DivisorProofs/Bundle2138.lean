import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2115
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0364
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityFiniteOfUnitary
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct

open GlobalTheory.HoweAdelic in
theorem _root_.GlobalTheory.T.howe_duality_finite_of_unitary : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityFinite := by
  intro hP hH F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe v hv
  have memX : ∀ g, g ∈ Subgroup.closure (UAt σ X (evFin F v)) ↔ g ∈ UAt σ X (evFin F v) := fun g =>
    ⟨fun hg => (mem_UAtGrp σ X _ g).1 ((Subgroup.closure_le (K := UAtGrp σ X (evFin F v))).2
      (fun x hx => (mem_UAtGrp σ X _ x).2 hx) hg), fun hg => Subgroup.subset_closure hg⟩
  have memW : ∀ h, h ∈ Subgroup.closure (UAt σ W (evFin F v)) ↔ h ∈ UAt σ W (evFin F v) := fun h =>
    ⟨fun hh => (mem_UAtGrp σ W _ h).1 ((Subgroup.closure_le (K := UAtGrp σ W (evFin F v))).2
      (fun x hx => (mem_UAtGrp σ W _ x).2 hx) hh), fun hh => Subgroup.subset_closure hh⟩
  obtain ⟨om', hact⟩ := GlobalTheory.ThK.LocalHom.exists_localHom F E σ n d X W M ψ χX χW om hψ hwe v
  have hHD := GlobalTheory.HoweLocal.howeDualityFor_closure hP hH F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW
    hwe v hv om' hact
  have hpres : ∀ x, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' x φ ∈ SB _ := fun x φ hφ => (hact x.1 x.2 φ hφ).1
  obtain ⟨⟨L, hL⟩, hsum⟩ := GlobalTheory.HoweTrivial.chain_bounded_and_sup_proper om' hHD hpres
  have uniq : ∀ (T : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ) (φ φ₁ φ₂ : (Fin n × Fin d → Fv F v) → ℂ),
      φ ∈ SB _ → Acts (evFin F v) T φ φ₁ → Acts (evFin F v) T φ φ₂ → φ₁ = φ₂ := fun T φ φ₁ φ₂ hφ h1 h2 =>
    GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ φ₂ hφ fun r hr => (h1 r hr).symm.trans (h2 r hr)
  have haug : augAt om v = locAug om' := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
      have h2 := (hact ⟨g, (memX g).2 hg⟩ 1 φ hφ).2
      rw [show ((1 : Subgroup.closure (UAt σ W (evFin F v))) : UA σ W.J) = 1 from rfl] at h2
      rw [uniq _ φ φ₁ _ hφ hA h2]
      exact Submodule.subset_span ⟨⟨g, (memX g).2 hg⟩, φ, hφ, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro z ⟨g, φ, hφ, rfl⟩
      have h2 := hact g 1 φ hφ
      exact Submodule.subset_span ⟨g.1, (memX _).1 g.2, φ, hφ, _, h2.1, h2.2, rfl⟩
  have hsub : ∀ N, ThetaSub om v N ↔ IsLocSub om' N := by
    intro N
    refine ⟨fun ⟨h1, h2, h3⟩ => ⟨haug ▸ h1, h2, fun h φ hφ => ?_⟩, fun ⟨h1, h2, h3⟩ => ⟨haug ▸ h1, h2, ?_⟩⟩
    · have h4 := hact 1 h φ (h2 hφ)
      exact h3 h.1 ((memW _).1 h.2) φ hφ _ h4.1 h4.2
    · intro h hh φ hφ φ₁ hφ₁ hA
      have h4 := hact 1 ⟨h, (memW h).2 hh⟩ φ (h2 hφ)
      rw [uniq _ φ φ₁ _ (h2 hφ) hA h4.2]
      exact h3 ⟨h, (memW h).2 hh⟩ φ hφ
  refine ⟨⟨L, fun m N hN hT => hL m N hN fun i => (hsub _).1 (hT i)⟩, fun N N' h h' hN hN' => ?_⟩
  exact hsum N N' ((hsub N).1 h) ((hsub N').1 h') hN hN'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthTensorProductFactors
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensAlg

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_eq_toLinearMap (w : T) (L : Module.End ℂ (V w)) :
    atPl w L = (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L := rfl

theorem atPl_one (w : T) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  unfold atPl
  have h : Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id := by
    funext i
    by_cases hi : i = w
    · subst hi; simp; rfl
    · simp [hi]
  rw [h]; exact PiTensorProduct.map_id

theorem atPl_sub_smul (w : T) (L : Module.End ℂ (V w)) (c : ℂ) (y : ⨂[ℂ] i, V i) :
    atPl w (L - c • 1) y = atPl w L y - c • y := by
  rw [atPl_eq_toLinearMap, map_sub, map_smul, ← atPl_eq_toLinearMap, ← atPl_eq_toLinearMap, atPl_one]
  simp

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (v : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v w (L (v w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp
  · simp [hi]

theorem atPl_tprod_eq_zero (w : T) (L : Module.End ℂ (V w)) (v : ∀ i, V i) (h : L (v w) = 0) :
    atPl w L (PiTensorProduct.tprod ℂ v) = 0 := by
  rw [atPl_tprod, h]
  exact MultilinearMap.map_update_zero _ _ _

theorem tensAll_mono {H H' : ∀ w, Submodule ℂ (V w)} (h : ∀ w, H w ≤ H' w) : tensAll H ≤ tensAll H' := by
  apply Submodule.span_mono
  rintro y ⟨f, hf, rfl⟩
  exact ⟨f, fun w => h w (hf w), rfl⟩

theorem iInf_hwSub_le {R S : T → ℕ} (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w))
    (μ : ∀ w, Ix (R w) (S w) → ℚ) :
    (⨅ w, hwSub (actAt w (a w)) (μ w)) ≤ tensAll (fun w => hwSub (a w) (μ w)) := by
  intro y hy
  rw [Submodule.mem_iInf] at hy
  refine GlobalTheory.T.mem_piTensorSpanAllFactors_of_jointKernel T V
    (fun w => {l | (∃ c, l = a w (Eab c c) - ((μ w c : ℚ) : ℂ) • 1) ∨ ∃ c d, posC c d ∧ l = a w (Eab c d)})
    (fun w => hwSub (a w) (μ w)) ?_ y ?_
  · intro w x hx
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    refine ⟨fun c => ?_, fun c d hcd => ?_⟩
    · exact hx _ (Or.inl ⟨c, rfl⟩)
    · exact hx _ (Or.inr ⟨c, d, hcd, rfl⟩)
  · intro w l hl
    have hyw := hy w
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hyw
    rcases hl with ⟨c, rfl⟩ | ⟨c, d, hcd, rfl⟩
    · rw [atPl_sub_smul]
      have h1 := hyw.1 c
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, actAt_apply] at h1
      exact h1
    · have h2 := hyw.2 c d hcd
      rw [actAt_apply] at h2
      exact h2

end GlobalTheory.HoweR.TensAlg

namespace GlobalTheory.HoweR

open GlobalTheory.HoweR.TensAlg in

theorem howeAlg_tensAny : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w))
    (C : ∀ w, Submodule ℂ (V w)), (∀ w, Pack (a w) (C w)) → HoweAlg (fun w => actAt w (a w)) (tensAny C) := by
  intro T _ _ V _ _ R S a C hP
  have hG := GlobalTheory.T.isGoodGlRep_piTensorActionAtFactor_and_commute T V R S a (fun w => (hP w).1)
  choose α β α' β' hQ using fun w => (hP w).2.2.1
  choose μ v hv hgen hmul using fun w => (hP w).2.2.2.2
  refine GlobalTheory.T.howeAlg_of_cyclic_highest_weight T R S (⨂[ℂ] i, V i) (fun w => actAt w (a w)) hG.1 hG.2 (tensAny C) α β α' β'
    (fun w => GlobalTheory.T.glActionQuadraticRelationModulo_piTensorAtFactor T V C w (R w) (S w) (a w) _ _ _ _ (hQ w)) ?_ ?_
  · intro B
    choose U hUfd hU using fun w => (hP w).2.2.2.1 B
    refine ⟨tensAll U, (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V U C).2.1 hUfd, fun ν hν => ?_⟩
    exact (iInf_hwSub_le a ν).trans
      ((tensAll_mono (fun w => hU w (ν w) (fun c => hν w c))).trans (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V U C).1)
  · refine ⟨μ, PiTensorProduct.tprod ℂ v, fun w => ?_,
      fun N hN hC hvN => GlobalTheory.T.tprod_cyclic_modulo_spanSomeFactor T V R S a C v hgen N hN hC hvN, ?_⟩
    · have h := hv w
      simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at h ⊢
      refine ⟨fun c => ?_, fun c d hcd => ?_⟩
      · rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, actAt_apply, ← atPl_sub_smul]
        exact atPl_tprod_eq_zero w _ v (h.1 c)
      · rw [actAt_apply]
        exact atPl_tprod_eq_zero w _ v (h.2 c d hcd)
    · refine (iInf_hwSub_le a μ).trans ((tensAll_mono (fun w => hmul w)).trans ?_)
      refine (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V (fun w => Submodule.span ℂ {v w}) C).1.trans ?_
      exact sup_le_sup_right ((GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V (fun w => Submodule.span ℂ {v w}) C).2.2 v) _

end GlobalTheory.HoweR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweQuotientFiniteLengthFockPolynomialsStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeQuotientFiniteLength_fockPolynomials : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  first | exact @GlobalTheory.HoweR.fock_pack | exact GlobalTheory.HoweR.fock_pack | (intros; apply GlobalTheory.HoweR.fock_pack <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraRest
section
namespace GlobalTheory.PrimeMembershipExistence

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ p : ℕ, Nat.Prime p ∧
      (p : NumberField.RingOfIntegers K) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal w := by

  have hP := w.isPrime
  have hn0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hmem := Ideal.absNorm_mem w.asIdeal
  rw [← Nat.prod_factorization_pow_eq_self hn0, Finsupp.prod, Nat.cast_prod] at hmem
  obtain ⟨p, hp, hpm⟩ := hP.prod_mem_iff.1 hmem
  rw [Nat.support_factorization] at hp
  rw [Nat.cast_pow] at hpm
  exact ⟨p, Nat.prime_of_mem_primeFactors hp, hP.mem_of_pow_mem _ hpm⟩

end GlobalTheory.PrimeMembershipExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexBoundParameterRequirementsEventuallyFamilyStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexBoundParameterRequirements_eventually_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, GlobalTheory.IndexAssembly.SizeRows (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def := by
  first | exact @GlobalTheory.OntoSizeRows.sizeRows_along | exact GlobalTheory.OntoSizeRows.sizeRows_along | (intros; apply GlobalTheory.OntoSizeRows.sizeRows_along <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePartIdentityStatement
section
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_part_identity : Bundle → SetAt → InfK → IPa @Comparison₂ := by
  first | exact @GlobalTheory.QuotientNormCoisometry.ipa_tie | exact GlobalTheory.QuotientNormCoisometry.ipa_tie | (intros; apply GlobalTheory.QuotientNormCoisometry.ipa_tie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityFittedIdentity
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.BigTop.Fun.IntTie

theorem gBig_dep {Q : GP} (h : GBig @Q) :
    GBig fun {D} {T} {Lc} {sc} G μ₀ C x b => 1 ≤ sc.cDep ∧ sc.cDep ≤ C ∧ @Q D T Lc sc G μ₀ C x b := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨max CF0 1, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  exact ⟨max C0 CF, x0, fun C hC D large₂ he hx hR T Lc μ hL G =>
    ⟨le_of_max_le_right hCF, le_of_max_le_right hC, h C (le_of_max_le_left hC) D large₂ he hx hR T Lc μ hL G⟩⟩

theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun {D} {T} {Lc} {sc} G μ₀ C x b => @Q D T Lc sc G μ₀ C x b ∧ @Q' D T Lc sc G μ₀ C x b := by
  obtain ⟨a, h⟩ := h
  obtain ⟨a', h'⟩ := h'
  refine ⟨max a a', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C1, max x0 x1, fun C hC D large₂ he hx hR T Lc μ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hL G,
     h' C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hL G⟩⟩

theorem integralNormBound_mono {K : Type} [Field K] [NumberField K] {ι : Type} {dl : Formalism.PairingDivisionLocalBalance.Pl K → ℝ} {zA zA' : ι → K}
    {B B' : ℝ} (h : NonArchimedeanDefectBound dl zA zA' B) (hB : B ≤ B') : NonArchimedeanDefectBound dl zA zA' B' :=
  ⟨h.1, fun F => (h.2.1 F).trans hB, h.2.2⟩

end GlobalTheory.BigTop.Fun.IntTie

open GlobalTheory.BigTop.Fun.IntTie in

theorem GlobalTheory.BigTop.Fun.int_tie (hS : SetAt)
    (hd : Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hB : BotSmall) (hN : BotNe) : GlobalTheory.BigTop.Fun.Int @Comparison₂ := by
  have hQ := GlobalTheory.T.fitted_ties_bound_eventual _ hS hd (gBig_dep (gBig_and hB hN))
  refine Lf.mono hQ ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH _ hd
  refine ⟨hd, fun hq => ?_⟩
  obtain ⟨h1, h2, ⟨-, -, hsmall⟩, hne⟩ := hq
  change 1 ≤ CF at h1
  change CF ≤ C at h2
  obtain ⟨a, ha⟩ := hd.2
  have hsq := ha.sq
  obtain ⟨S, del, -, -, hNI, hdl⟩ := hsq.int
  obtain ⟨δ, t0, hP⟩ := hsq.norms
  choose P P' hb hz hz' using hP
  have hI := hNI δ t0 D.what₂.LL D.what₂.embLL (Sq D) P P' d.zA d.zA'
    (fun ij => hsmall δ t0 _ (P ij) (P' ij) _ ij.1 ij.2 _ (hb ij))
    (fun ij => hne δ t0 _ (P ij) (P' ij) ij.1 ij.2 (hb ij))
    (fun ij => ⟨hz ij, hz' ij⟩)
  rw [← hdl] at hI
  show NonArchimedeanDefectBound d.dl d.zA d.zA' (d.O.bDel C p.Z.b)
  refine integralNormBound_mono hI ?_
  clear hQ hne hsmall hb hz hz' hNI
  have eN : (d.O.N : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ) := by
    have := D.R.m_add_three_le_k
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    norm_cast
    show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (GlobalTheory.ChiGrid.sLen D) + 1)
    unfold GlobalTheory.ChiGrid.sLen
    rw [hr]
    congr 3
    omega
  have eB : d.O.Bw = (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) := hsq.weight
  have eS : d.O.cS = Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := by
    rw [GlobalTheory.FunObj.SqNum.log_levQ]
    rfl
  have ef : (d.O.f : ℝ) = D.R.f := rfl
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * Real.log ((D.R.f : ℝ) * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ))) +
      D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) * Real.log p.Z.b +
      D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) ^ 2 * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) *
        Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := ⟨_, rfl⟩
  have e1 : d.O.bDel C p.Z.b = C * X := by
    unfold FunData.bDel
    rw [eN, eB, eS, ef, hX]
    ring
  have e2 : GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) = CF * X := by
    unfold GlobalTheory.NormSum.intBound
    rw [hX]
    ring
  have h0 := hI.2.1 ∅
  rw [Finset.sum_empty] at h0
  change 0 ≤ GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) at h0
  change GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) ≤ _
  rw [e1, e2]
  rw [e2] at h0
  have hX0 : 0 ≤ X := (mul_nonneg_iff_of_pos_left (by linarith)).1 h0
  exact mul_le_mul_of_nonneg_right h2 hX0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntermediateFieldPadicIntegersEqNormLeOne
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameOf

theorem intEmb_range_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] Lf],
    Function.Injective (intEmb Lf) ∧ ∀ x, x ∈ Set.range (intEmb Lf) ↔ x ∈ Lf ∧ ‖x‖ ≤ 1 := by
  intro l _ Lf _
  refine ⟨fun a b h => Subtype.ext (Subtype.ext h), fun x => ?_⟩
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(a : Lf).2, ?_⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le]
    have ha : IsIntegral ℤ_[l] (a : Lf) := a.2
    exact ha.map (Lf.val.restrictScalars ℤ_[l])
  · rintro ⟨hx, hn⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le] at hn
    have hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : Lf) :=
      (isIntegral_algHom_iff (Lf.val.restrictScalars ℤ_[l]) Subtype.val_injective).1 hn
    exact ⟨⟨⟨x, hx⟩, hi⟩, rfl⟩

end GlobalTheory.FrameOf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ChiGrid
open GlobalTheory.SqTop (twPl Qn)
open GlobalTheory.Square (IsAwayUnit)
open GlobalTheory.RowTest (LocIn NumbersIn)

namespace GlobalTheory.KappaArith

theorem isAwayUnit_of_pow_eq_one {K : Type} [Field K] (m : ℕ) {z : K} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) :
    IsAwayUnit m z := by
  have hint : IsIntegral ℤ z :=
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hz]⟩
  let a : 𝓞 K := ⟨z, hint⟩
  have ha : (a : K) = z := rfl
  refine ⟨a, 0, 0, ⟨a ^ (n - 1), ?_⟩, by simp [ha]⟩
  rw [pow_zero]
  apply RingOfIntegers.ext
  have e1 : ((a * a ^ (n - 1) : 𝓞 K) : K) = z * z ^ (n - 1) := by rw [← ha]; norm_cast
  rw [e1, ← pow_succ', Nat.sub_add_cancel hn, hz]
  rfl

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc)

def AwayIm (D : D7) (m : ℕ) (z : ℂ) : Prop := ∃ ζ : D.what₂.LL, IsAwayUnit m ζ ∧ D.what₂.embLL ζ = z

theorem awayIm_one (m : ℕ) : AwayIm D m 1 := ⟨1, IsAwayUnit.one m, map_one _⟩

theorem AwayIm.mul {m : ℕ} {z z' : ℂ} (h : AwayIm D m z) (h' : AwayIm D m z') : AwayIm D m (z * z') := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  exact ⟨a * b, ha.mul hb, map_mul _ _ _⟩

theorem AwayIm.prod {m : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, AwayIm D m (f i)) :
    AwayIm D m (∏ i ∈ s, f i) :=
  Finset.prod_induction f (AwayIm D m) (fun _ _ => AwayIm.mul) (awayIm_one m) h

theorem awayIm_val {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (x : (w.adicCompletion D.host.E)ˣ) :
    AwayIm D m ((Lc.xiH t).loc w x : ℂ) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨ζ, hζ⟩ := hx w x
  have h1 : ((Lc.xiH t).loc w x) ^ n = 1 := by
    have : ((Lc.xiH t) ^ n).loc w x = 1 := by rw [show (Lc.xiH t) ^ n = 1 from ho]; rfl
    exact this
  have h2 : ζ ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, hζ, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one])
  exact ⟨ζ, isAwayUnit_of_pow_eq_one m hn h2, hζ⟩

end GlobalTheory.KappaArith

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralAbsNormPowMulOnIdStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isIntegral_absNorm_pow_mul_onId_of_coprime : ∀ (E : Type) [Field E] [NumberField E] (ψ : Formalism.L2.Host.HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ) (n : I → ℤ), ψ.HasInf φs n → (∀ v, ψ.TameAt v) → ∀ b : ℕ, b ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) → ∀ cc : Ideal (𝓞 E), cc ≠ ⊥ → cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤ → ∃ K : ℕ, IsIntegral ℤ (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId | exact GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId | (intros; apply GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalAtPlaceConjProductStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalAtPlace_conj_product : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i i' : ok × ℕ) (a b c d : Bridge.Gf V), (pl i.1).under (𝓞 D.host.F) = (pl i'.1).under (𝓞 D.host.F) → isLocEnv V pl ok i a → isLocEnv V pl ok i' b → isLocEnv V pl ok i' c → isLocEnv V pl ok i d → isLocEnv V pl ok i ((c * d)⁻¹ * (a * b)) := by
  first | exact @GlobalTheory.FrameProdLoc.isLocEnv_prod | exact GlobalTheory.FrameProdLoc.isLocEnv_prod | (intros; apply GlobalTheory.FrameProdLoc.isLocEnv_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JUnifAndLUnifOfTieIn
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem jUnif_and_lUnif_of_tieIn : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ ∧ (GeoAct T R κ v₀ → (topR T R κ v₀).LUnif) := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hpb hnV
  have hlp := GlobalTheory.HolDict.lastPos_of_kapIs D κ hT.kap
  exact ⟨GlobalTheory.T.cuspFormReadings_independent_spanning_all_embeddings h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb hlp hnV,
    GlobalTheory.T.uniformisationRow_coreForms_of_geometricAction h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb hlp hnV⟩

end GlobalTheory.HolDict
end

