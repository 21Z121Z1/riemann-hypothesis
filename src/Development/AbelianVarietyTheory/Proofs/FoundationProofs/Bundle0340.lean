import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstantTermAlongFlagEqZeroOfCuspidal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cusp

theorem constTerm_eq_zero_of_mem_cuspCont (D : D7) (V : HSp D) (φ : GA D V → ℂ) (h : φ ∈ cuspCont V) (𝔉 : IsoFlag V)
    (h𝔉 : 𝔉.Proper) : constTerm 𝔉 φ = 0 := by
  have hi : (⟨1, Nat.succ_lt_succ h𝔉⟩ : Fin (𝔉.k + 1)) ≠ 0 := Fin.ne_of_val_ne one_ne_zero
  have h0 : constTermOn (GQ V) (NA (.single (𝔉.isIsotropic hi))) φ = 0 :=
    (isCuspFun_iff h.2.1).1 h.2.2 _ (𝔉.isIsotropic hi)
  funext x
  refine (Stages.constTermOn_stages (GA D V) (GQ V) (NA 𝔉) (NA (.single (𝔉.isIsotropic hi)))
    (𝔉.unip_single_le D.sp.cm _ hi) (fun p hp n hn => IsoFlag.conj_mem_unip ?_ hn) (cocompact_flag D V 𝔉)
    (cocompact_single _) φ h.2.1 h.1 x).trans ?_
  · rw [IsoFlag.par_single]
    exact 𝔉.par_le_parab D.sp.cm _ _ (𝔉.unip_le_par D.sp.cm _ hp)
  · rw [h0]
    exact (cocompact_flag D V 𝔉).constTermOn_const 0 x

end GlobalTheory.Cusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCharFnAndIsPseudoCoeffOfCompact
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace
open scoped ComplexConjugate ContDiff InnerProductSpace

noncomputable section

namespace GlobalTheory.Orb

variable {H : Type} [Group H] [TopologicalSpace H]
  {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] {D : H →* (V →L[ℂ] V)} {π : H →* (U →L[ℂ] U)}

theorem continuous_trace_rep (hD : IsUnitaryRep D) :
    Continuous fun g => LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) := by
  simp only [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V)]
  exact continuous_finset_sum _ fun i _ => continuous_const.inner (hD.continuous_apply _)

omit [TopologicalSpace H] in

theorem trace_rep_conj (x s : H) :
    LinearMap.trace ℂ V (D (x⁻¹ * s * x) : V →ₗ[ℂ] V) = LinearMap.trace ℂ V (D s : V →ₗ[ℂ] V) := by
  have h := Representation.char_conj (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp D) s x⁻¹
  rwa [inv_inv] at h

variable [MeasurableSpace H] [BorelSpace H] {μ : Measure H}

theorem hasTrace_repOp_of_finiteDimensional [CompleteSpace V] [IsFiniteMeasureOnCompacts μ] (hD : IsUnitaryRep D)
    {f : H → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    HasTrace (repOp D μ f) (∫ g, f g * LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) ∂μ) := by
  refine ⟨isTraceClass_of_finiteDimensional _, ?_⟩
  simp only [trace_eq_linearMap_trace, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V), Finset.mul_sum,
    ContinuousLinearMap.coe_coe, hD.inner_repOp hf hc]
  exact (integral_finsetSum _ fun i _ => (hf.mul (continuous_const.inner
    (hD.continuous_apply _))).integrable_of_hasCompactSupport hc.mul_right).symm

variable [IsTopologicalGroup H] [CompactSpace H] [μ.IsHaarMeasure]

theorem integral_conj_trace_mul_trace (hD : IsUnitaryRep D) (hi : IsTopIrreducible D) :
    ∫ g, conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) * LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) ∂μ = μ.real univ := by
  let ρ : Representation ℂ H V := ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp D
  have := hi.1
  have : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule h)⟩
  have : ρ.IsIrreducible := ⟨fun S => (hi.2 S.toSubmodule ⟨S.toSubmodule.closed_of_finiteDimensional,
    fun g v hv => S.apply_mem_toSubmodule g hv⟩).imp (fun h => Subrepresentation.toSubmodule_injective h)
      fun h => Subrepresentation.toSubmodule_injective h⟩
  have h := integral_conj_character_mul_character_self (haarProb H) ρ hD.continuous_apply hD.norm_apply
  conv_lhs => rw [eq_smul_haarProb μ]
  rw [integral_smul_measure]
  exact (congrArg _ h).trans (by simp [Measure.real])

theorem integral_inner_smul_eq_zero [CompleteSpace V] [CompleteSpace U] (hD : IsUnitaryRep D) (hi : IsTopIrreducible D)
    (hπ : IsUnitaryRep π) (hi' : IsTopIrreducible π) (hne : ¬ IsUnitEquiv π D) (e x : V) (v : U) :
    ∫ g, ⟪D g e, x⟫_ℂ • π g v ∂μ = 0 := by
  have hI : ∀ z : V, Integrable (fun g => ⟪D g e, z⟫_ℂ • π g v) μ := fun z =>
    integrable_of_continuous_of_compactSpace μ
      (((hD.continuous_apply e).inner continuous_const).smul (hπ.continuous_apply v))
  let T : V →ₗ[ℂ] U :=
    { toFun := fun x => ∫ g, ⟪D g e, x⟫_ℂ • π g v ∂μ
      map_add' := fun x y => by
        rw [← integral_add (hI x) (hI y)]
        simp [add_smul]
      map_smul' := fun c x => by simp [mul_smul, integral_smul] }
  have hT : LinearMap.toContinuousLinearMap T ∈ AutMult.homIn D π ⊤ := AutMult.mem_homIn_top.2 fun g x => by
    change ∫ k, ⟪D k e, D g x⟫_ℂ • π k v ∂μ = π g (∫ k, ⟪D k e, x⟫_ℂ • π k v ∂μ)
    rw [← integral_mul_left_eq_self _ g, ← (π g).integral_comp_comm (hI x)]
    simp only [map_mul, ContinuousLinearMap.mul_apply, AutMult.inner_map_map hD, map_smul]
  have h0 : AutMult.homIn D π ⊤ = ⊥ := AutMult.multIn_eq_zero_iff.1 (by_contra fun h =>
    hne (AutMult.uEquiv_of_multIn_ne_zero ⟨‹_›, hD, hi⟩ ⟨‹_›, hπ, hi'⟩ h).symm)
  rw [h0, Submodule.mem_bot] at hT
  exact DFunLike.congr_fun hT x

theorem repOp_conj_trace_eq_zero [CompleteSpace V] [CompleteSpace U] (hD : IsUnitaryRep D) (hi : IsTopIrreducible D)
    (hπ : IsUnitaryRep π) (hi' : IsTopIrreducible π) (hne : ¬ IsUnitEquiv π D) (c : ℂ) :
    repOp π μ (fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / c) = 0 := by
  ext v
  rw [hπ.repOp_apply (f := fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / c)
    ((Complex.continuous_conj.comp (continuous_trace_rep hD)).div_const c)
    (HasCompactSupport.of_compactSpace _)]
  simp only [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V), map_sum, inner_conj_symm, div_eq_inv_mul,
    mul_smul, integral_smul, Finset.sum_smul, ContinuousLinearMap.coe_coe]
  have hI : ∀ e : V, Integrable (fun g => ⟪D g e, e⟫_ℂ • π g v) μ := fun e =>
    integrable_of_continuous_of_compactSpace μ
      (((hD.continuous_apply e).inner continuous_const).smul (hπ.continuous_apply v))
  rw [integral_finsetSum _ fun i _ => hI _]
  simp [integral_inner_smul_eq_zero hD hi hπ hi' hne]

theorem isCharFn_and_isPseudoCoeff_of_compact [T2Space H] [SecondCountableTopology H] [CompleteSpace V]
    {n : Type} [Fintype n] [DecidableEq n] {ι : H →* Matrix n n ℂ} (hι : Continuous (matCoord ι))
    (hD : IsUnitaryRep D) (hi : IsTopIrreducible D)
    (hχ : (fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V))) ∈ CcMat ι) :
    IsCharFn ι μ D (fun g => LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) ∧
      IsPseudoCoeff ι μ D fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / μ.real univ := by
  have h0 : (μ.real univ : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨(isOpen_univ.measure_pos μ univ_nonempty).ne', measure_ne_top _ _⟩
  have hc := continuous_trace_rep hD
  have hf : Continuous fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / μ.real univ :=
    (Complex.continuous_conj.comp hc).div_const _
  have hΘ : IsCharFn ι μ D (fun g => LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) :=
    ⟨hc.locallyIntegrable, fun s _ => hc.continuousAt, fun f hf' =>
      hasTrace_repOp_of_finiteDimensional hD (continuous_of_mem_ccSmooth hι hf') hf'.1⟩
  refine ⟨hΘ, ?_, ?_, fun U _ _ _ π hπ hirr _ hne => ?_, fun s _ hT => absurd (isClosed_cent s).isCompact hT,
    _, hΘ, fun s _ hT dt _ _ => ?_⟩
  · simp only [div_eq_inv_mul]
    exact (CcMat ι).smul_mem (μ.real univ : ℂ)⁻¹ hχ
  · convert hasTrace_repOp_of_finiteDimensional (μ := μ) hD hf (HasCompactSupport.of_compactSpace _) using 1
    simp only [div_mul_eq_mul_div, integral_div, integral_conj_trace_mul_trace hD hi, div_self h0]
  · rw [repOp_conj_trace_eq_zero hD hi hπ hirr hne]
    exact ⟨isTraceClass_zero, trace_zero⟩
  · haveI : CompactSpace (cent s) := isCompact_iff_compactSpace.1 hT
    convert hasOrbInt_of_finite (dh := μ) (dt := dt)
      (f := fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / μ.real univ)
      ((hf.comp (f := fun x => x⁻¹ * s * x) (by fun_prop)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) using 2
    simp only [trace_rep_conj, integral_const, Complex.real_smul]
    field_simp

example [MeasurableSpace Circle] [BorelSpace Circle] (ν : Measure Circle) [ν.IsHaarMeasure] :
    IsPseudoCoeff circleMat ν (charRep (MonoidHom.id Circle)) fun z =>
      conj (LinearMap.trace ℂ ℂ (charRep (MonoidHom.id Circle) z : ℂ →ₗ[ℂ] ℂ)) / ν.real univ := by
  have e : ∀ z i j, matCoord circleMat z i j = z := fun z i j => by
    fin_cases i; fin_cases j; simp [matCoord, circleMat]; rfl
  have h := AutMult.isIrrUnitary_charRep (χ := MonoidHom.id Circle) continuous_id
  refine (isCharFn_and_isPseudoCoeff_of_compact
    (continuous_pi fun i => continuous_pi fun j => by simp only [e]; exact continuous_subtype_val) h.unitary h.irred
    ⟨HasCompactSupport.of_compactSpace _, fun y => conj (y 0 0), ?_, fun z => by simp [e, charRep]⟩).2
  exact Complex.conjCLE.contDiff.comp (by fun_prop)

end GlobalTheory.Orb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NoThetaLiftDiscreteSeriesSmallerTowerMember
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.TowerDrop

theorem archimedeanRallisFourth_of_discreteSeriesBlattner : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFourth X := by
  intro X _ _ hD h5
  refine ⟨fun t al be ga de hd i hi hr hs MM f hf => ?_,
    fun t al be ga de hd i hi hr hs MM f hf => ?_⟩
  · exact ((GlobalTheory.LowerTower.no_map_lower X hD h5 t al be ga de hd.1 i hi).1 hr hs) MM f hf
  · have hA := hd.1
    have ht : 1 ≤ t := hA.1
    have hn : 1 ≤ al.length + be.length + ga.length + de.length := hA.2.1
    have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
    obtain ⟨-, hpar, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
    obtain ⟨-, -, hsign, -⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA
    have hno := (GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi).2.1 hr hs
    refine GlobalTheory.LowerTower.tensNo_first X hD h5 (by omega) _ hpar 0 ?_ hno MM f hf
    rw [GlobalTheory.SmallerSource.cPair_sub hr hs]
    refine fun a => ⟨(hsign a).1, fun h => (hsign a).2 (lt_of_le_of_ne h fun h0 => ?_)⟩
    have := hA.2.2.2.2.2.2.2.2.2.2 _ (GlobalTheory.LowerTower.lamA_mem al be ga de a)
    rw [h0, abs_zero] at this
    linarith

end GlobalTheory.TowerDrop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLie

theorem hasDerivAt_constTermOn {G : Type} [Group G] [TopologicalSpace G] {Γ N : Subgroup G} [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] [LocallyCompactSpace N]
    (hc : Cocompact Γ N) {φ ψ : G → ℂ} (hφ : LeftInv Γ φ) (hφc : Continuous φ) (hψ : LeftInv Γ ψ) (hψc : Continuous ψ)
    {u : ℝ → G} (hu : Continuous u) (hd : ∀ g t, HasDerivAt (fun s => φ (g * u s)) (ψ (g * u t)) t) (x : G) :
    HasDerivAt (fun s => constTermOn Γ N φ (x * u s)) (constTermOn Γ N ψ (x * u 0)) 0 := by
  have := hc.isProbabilityMeasure
  obtain ⟨K, hK, hs⟩ := id hc
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn
    (f := fun p : N × ℝ => ψ (p.1 * (x * u p.2))) (by fun_prop)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := probMeasure Γ N) (bound := fun _ => C)
    (F := fun s q => φ ((q.out : N) * (x * u s))) (F' := fun s q => ψ ((q.out : N) * (x * u s)))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) (.of_forall fun s => (hc.integrable hφ hφc _).1) (hc.integrable hφ hφc _)
    (hc.integrable hψ hψc _).1 (.of_forall fun q s hs' => ?_) (integrable_const C) (.of_forall fun q s _ => ?_)).2
  · obtain ⟨γ, hγ, hk⟩ := hs q.out
    exact (congrArg norm (leftInv_integrand hψ (x * u s) γ hγ q.out)).ge.trans
      (hC (_, s) ⟨hk, Metric.ball_subset_closedBall hs'⟩)
  · simpa only [mul_assoc] using hd ((q.out : N) * x) s

variable {D : D7} {θ : InfF D} {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} {φ : GA D V → ℂ}

theorem gelf_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (hφ : φ ∈ SmFun θ V) (τ' : D.what₂.Tau) (k : ℕ) :
    gelf θ V τ' k (Rder θ V τ X φ) = Rder θ V τ X (gelf θ V τ' k φ) := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain ⟨c, hc, hg⟩ := GlobalTheory.SmoothForms.exists_gelf R τ'
  let ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, (GlobalTheory.SmoothForms.smooth_iff R φ).1 hφ⟩
  let X' : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, hX⟩
  have e : ∀ f : GlobalTheory.SmoothForms.SmF θ V, Rder θ V τ X f.1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X') f).1 := fun f => GlobalTheory.SmoothForms.Rder_eq R τ X' f.1
  have hcomm : Commute (GlobalTheory.SmoothForms.envRep R τ' (c k))
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X')) := by
    rw [← GlobalTheory.SmoothForms.envRep_ι]
    by_cases h : τ' = τ
    · subst h
      have hm : c k ∈ Subalgebra.center ℂ _ := hc ▸ Algebra.subset_adjoin ⟨k, rfl⟩
      exact Commute.map (Subalgebra.mem_center_iff.1 hm _).symm _
    · exact GlobalTheory.SmoothForms.envRep_comm R h _ _
  change gelf θ V τ' k (Rder θ V τ X ψ.1) = Rder θ V τ X (gelf θ V τ' k ψ.1)
  rw [e ψ, hg, hg, e]
  exact congrArg (fun S : Module.End ℂ (GlobalTheory.SmoothForms.SmF θ V) => (S ψ).1) hcomm.eq

theorem fg_comap {W : Submodule ℂ (GA D V → ℂ)} (hW : FiniteDimensional ℂ W) :
    (W.comap (SmFun θ V).subtype).FG :=
  Module.Finite.iff_fg.1 (FiniteDimensional.of_injective ((SmFun θ V).subtype.restrict (q := W) fun _ hx => hx)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : W => z.1) h)))

theorem derEnd_coe (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (f : SmFun θ V) : (derEnd hθ τ X f).1 = Rder θ V τ X f.1 :=
  GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX f.1

theorem isAutFunSm_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (h : IsAutFunSm θ V φ) :
    IsAutFunSm θ V (Rder θ V τ X φ) := by
  refine { left := fun γ hγ => GlobalTheory.Mem.Lift.Rder_left (h.left γ hγ) τ X, level := ?_, cont := ?_,
           smooth := Rder_mem h.smooth hX, zfin := ?_, growth := ?_ }
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hf τ X φ) g
    rw [show rTr V k φ = φ from funext (e k hk hf)] at this
    exact this.symm
  · exact GlobalTheory.Size.continuous_rWord hθ h.smooth h.cont (GlobalTheory.Grow.unifModGrowth_of_isAutFunSm hθ h) (l := [(τ, X)])
      fun p hp => by rw [List.mem_singleton.1 hp]; exact hX
  · obtain ⟨W, hW, m, s⟩ := h.zfin
    refine ⟨((W.comap (SmFun θ V).subtype).map (derEnd hθ τ X)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 (((fg_comap hW).map _).map _),
      ⟨_, ⟨⟨φ, h.smooth⟩, m, rfl⟩, derEnd_coe hθ hX _⟩, ?_⟩
    rintro τ' k _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨_, ⟨⟨_, (linOnSm_gelf τ' k).mem _ f.2⟩, s τ' k _ hf, rfl⟩, ?_⟩
    rw [Submodule.subtype_apply, Submodule.subtype_apply, derEnd_coe hθ hX, derEnd_coe hθ hX, gelf_Rder hθ hX f.2]
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using
      hN (l ++ [(τ, X)]) (GlobalTheory.Mem.Lift.append_mem_lie hl hX) x

theorem isKFinite_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) {K : Subgroup (GA D V)} (hK : K ≤ GinfC V)
    (hs : φ ∈ SmFun θ V) (h : GlobalTheory.Doubling.IsKFinite K φ) : GlobalTheory.Doubling.IsKFinite K (Rder θ V τ X φ) := by
  obtain ⟨W, hW, m⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h
  refine GlobalTheory.Doubling.isKFinite_iff.2
    ⟨(Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 ((Submodule.FG.map₂ _ Module.Finite.fg_top (fg_comap hW)).map _), fun k hk => ?_⟩
  have hr : ∀ k ∈ K, IsRealPt θ k := fun k hk => ⟨hK hk, FockCompare.RealAction.infMat_mem_UH hθ V k⟩
  have hi := hr _ (inv_mem hk)
  refine ⟨_, Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := adAt θ k⁻¹ τ X))
    (n := ⟨rTr V k φ, rTr_mem hθ (hr k hk) hs⟩) (m k hk), ?_⟩
  rw [Submodule.subtype_apply, derEnd_coe hθ (adAt_mem hi hX)]
  funext g
  have := congrFun (Rder_rTr hθ hi hX (rTr V k φ)) (g * k)
  rw [show rTr V k⁻¹ (rTr V k φ) = φ from funext fun y => by simp [rTr]] at this
  rw [this, rTr, mul_inv_cancel_right]

theorem isCuspFun_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) :
    IsCuspFun V (Rder θ V τ X φ) := by
  have h' := isAutFunSm_Rder hθ hX h
  refine (isCuspFun_iff h'.left).2 fun W hW => funext fun x => ?_
  have h0 : constTermOn (GQ V) (NA (.single hW)) φ = 0 := (isCuspFun_iff h.left).1 hc W hW
  have := hasDerivAt_constTermOn (cocompact_single hW) h.left h.cont h'.left h'.cont (GlobalTheory.Mem.Lift.continuous_oneP hθ hX)
    (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder h.smooth hX)) x
  rw [h0, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at this
  exact this.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))

theorem rder_mem_autForms_cuspForms : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (K : Subgroup (GA D V)), K ≤ GinfC V → ∀ τ, ∀ X ∈ lieAt V τ, (∀ φ ∈ autForms θ V K, Rder θ V τ X φ ∈ autForms θ V K) ∧ ∀ φ ∈ cuspForms θ V K, Rder θ V τ X φ ∈ cuspForms θ V K := by
  intro D θ hθ V K hK τ X hX
  refine ⟨fun φ h => ⟨isAutFunSm_Rder hθ hX h.1, isKFinite_Rder hθ hX hK h.1.smooth h.2⟩, fun φ h => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_cuspForms.1 h
  exact mem_cuspForms.2 ⟨⟨isAutFunSm_Rder hθ hX h1, isCuspFun_Rder hθ hX h1 h2⟩, isKFinite_Rder hθ hX hK h1.smooth h3⟩

end GlobalTheory.CuspLie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TestVectorAdelicPairTranslatesMovedLatticeVacuumStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testVector_adelicPair_translates_movedLatticeVacuum : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), ∀ (g : GA D P.a) (g' : GA D P.d) L₁ L₁', Moves D (g : GL (Fin P.a) (AE D)) L₁ → Moves D (g' : GL (Fin P.d) (AE D)) L₁' → ∃ (c : ℂ) (k : ℕ) (r : Fin k → Qbar) (y : Fin k → VC D P.a P.d), 0 < Q → (Mod1All c ∧ (∀ i, Q • y i ∈ La D (tor0 D cc δ) L₁ L₁') ∧ (∀ i, IsIntegral ℤ ((Q : Qbar) ^ (P.a * P.d) * r i)) ∧ (∀ ρ : Qbar →+* ℂ, (∑ i, ‖ρ (r i)‖) ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d)) ∧ (P.W.Om g g' P.F = fun z => c * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (y i) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d) (La D (tor0 D cc δ) L₁ L₁') P.e0) z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ‖lamC lam c‖ = 1) := by
  first | exact @GlobalTheory.ArchFree.expand.om_expand | exact GlobalTheory.ArchFree.expand.om_expand | (intros; apply GlobalTheory.ArchFree.expand.om_expand <;> assumption)
end

