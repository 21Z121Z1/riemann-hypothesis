import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsHaarZetaValueAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLw
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstantOneNotCuspidalOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ConstOneMemCuspFormsOfAnisotropic
section
noncomputable section

open scoped NNReal ComplexConjugate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Filter Topology Set Metric MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.Mem.Th (InfF CptF)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis.DblModel

variable {D : D7} {V : HSp D}

theorem const_one_mem_cuspForms_of_anisotropic (h : IsAniso V) (θ : InfF D) (A : CptF V) : (1 : GA D V → ℂ) ∈ Cusp.A0 θ V A :=
  Cusp.mem_cuspForms.2 ⟨⟨isAutFunSm_const θ V 1, fun r C hC => absurd hC (h r C)⟩, .of_invariant fun _ _ _ => rfl⟩

theorem hypotheses_inhabited (D : D7) (n b : ℕ) :
    ∃ (V : HSp D) (a : GL (Fin V.rank) (AE D)) (μ : (AE D)ˣ →* Circle) (θ : InfF D) (A : CptF V) (m : Measure (GA D V)),
      V.rank = n ∧ IsMaj V a ∧ IsHeckeChar D μ ∧ ResEta D μ b ∧ IsInfFam θ ∧ V.SigOK ∧ Cusp.IsCartanFrame V A ∧
        m.IsHaarMeasure ∧ (1 : GA D V → ℂ) ∈ Cusp.A0 θ V A := by
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  let V : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n
  have h1 : IsHeckeChar D (η ^ b) := ⟨by
    have : ((η ^ b : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ b := by funext x; simp
    rw [this]; exact hη.1.1.pow b, fun x => by rw [MonoidHom.pow_apply, hη.1.2 x, one_pow]⟩
  have hr := hη.2.2.1
  have h2 : ResEta D (η ^ b) b := ⟨hr.1, fun e he a => by rw [MonoidHom.pow_apply, hr.2 e he a, pow_one]⟩
  obtain ⟨a, ha⟩ := exists_isMaj V
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hV : V.SigOK := Examples₂.posSpace_sigOK _ _
  obtain ⟨A, hA⟩ := Cusp.exists_isCartanFrame V hV
  exact ⟨V, a, _, θ, A, Measure.haar, rfl, ha, h1, h2, hθ, hV, hA, inferInstance,
    const_one_mem_cuspForms_of_anisotropic (ThetaMean.Model.isAniso_posSpace n) θ A⟩

theorem resEta_one (D : D7) (b : ℕ) : ResEta D 1 (2 * b) := by
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  exact resEta_parity (n := 0) ⟨hη.2.2.1.1, fun _ _ _ => rfl⟩ (by omega)

theorem exists_regular_one_not_zero (V : HSp D) (s₀ : ℂ) :
    ∃ Φ, EisContinues V Φ ∧ EisRegularAt V Φ s₀ 1 ∧ ¬ EisRegularAt V Φ s₀ 0 := by
  obtain ⟨Φ, h1, h2, -⟩ := Model.exists_family V Measure.haar fun s => (s - s₀)⁻¹
  have h3 : ∀ g, IsMerExt (eisSer V Φ g) univ fun s => (s - s₀)⁻¹ := fun g =>
    ⟨isRightDomain_univ, fun s _ => by fun_prop, 0, fun s _ => (h1 s g).symm⟩
  have hc : EisContinues V Φ := ⟨h2.1, fun g => ⟨_, h3 g⟩⟩
  refine ⟨Φ, hc, ⟨1, fun _ _ => 1, one_pos, fun s _ hs g => ?_, fun _ => differentiableOn_const _, continuousOn_const,
    1, 0, fun _ _ _ => by simp⟩, fun h => ?_⟩
  · have : eisCont V Φ s g = (s - s₀)⁻¹ := (HolValueAt.valueAt ⟨_, (h3 g).isExtAt trivial,
      (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 hs), rfl⟩).cont_eq
    rw [this, pow_one, mul_inv_cancel₀ (sub_ne_zero.2 hs)]
  · obtain ⟨c, hc⟩ := ((h3 1).isExtAt trivial).poleLE_iff.1 ((h.eisPoleLE hc).2 1)
    have h4 : Tendsto (fun s => (s - s₀) * ((s - s₀) ^ 0 * (s - s₀)⁻¹)) (𝓝[≠] s₀) (𝓝 1) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => by simp [sub_ne_zero.2 hs])
    have h5 := ((tendsto_nhdsWithin_of_tendsto_nhds (s := {s₀}ᶜ) (continuous_sub_right s₀).continuousAt.tendsto).mul hc)
    simpa using tendsto_nhds_unique h5 h4

theorem petCoef_one (m : Measure (GA D V)) : petCoef V m 1 1 = fun _ => (((autMeasure V m).real univ : ℝ) : ℂ) := by
  funext g
  simp [petCoef, Cusp.petersson, pet, AutomorphicL2Unitary.descend, rTr]

theorem basicIdentity_value_smul {μ : (AE D)ˣ →* Circle} {m : Measure (GA D V)} [SigmaFinite m]
    {Φ : GA D (dblSp V) → ℂ} {f₁ f₂ : GA D V → ℂ} (h : BasicIdentity V μ m Φ f₁ f₂) (c : ℝ≥0) :
    dblInt V μ (c • m) (eis V Φ) f₁ f₂ = zetaH D.sp.cm.sig (gram_hdbl V) (c • m) Φ (petCoef V (c • m) f₁ f₂) := by
  have e : autMeasure V (c • m) = c • autMeasure V m := quotMeasure_smul (c : ENNReal)
  have e2 : ∀ g, petCoef V (c • m) f₁ f₂ g = (c : ℂ) * petCoef V m f₁ f₂ g := fun g => by
    change ∫ _, _ ∂autMeasure V (c • m) = _
    rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]; rfl
  rw [dblInt_smul_measure, h.2.2, zetaH_eq, zetaH_eq, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul,
    sq, mul_assoc, ← integral_const_mul]
  congr 2
  funext g
  rw [e2, map_mul, Complex.conj_ofReal]
  ring

theorem dblInt_sph_pos (hP : Published.DoublingMethod) (h0 : 0 < V.rank) (hA : IsAniso V) (hV : V.SigOK)
    {a : GL (Fin V.rank) (AE D)} (ha : IsMaj V a) (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a))
    (m : Measure (GA D V)) [m.IsHaarMeasure] {σ : ℝ} (hσ : (V.rank : ℝ) / 2 < σ) :
    0 < (dblInt V 1 m (eis V (sph V a σ)) 1 1).re := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨A, hC⟩ := Cusp.exists_isCartanFrame V hV
  obtain ⟨-, h2, h3⟩ := basicIdentity_of_mem hP h0 ha hI (μ := 1) ⟨continuous_const, fun _ => rfl⟩ (resEta_one D 0)
    (sph_mem hI σ) (by simpa using hσ) hθ hV hC m (const_one_mem_cuspForms_of_anisotropic hA θ A) (const_one_mem_cuspForms_of_anisotropic hA θ A)
  have hv : 0 < (autMeasure V m).real univ :=
    ENNReal.toReal_pos (NeZero.ne _) (measure_ne_top _ _)
  have e : (fun g => sph V a σ (ioH _ D.sp.cm.sig (gram_hdbl V) (g, 1)) * conj (petCoef V m 1 1 g)) = fun g =>
      (((hgt V a (io V (g, 1)) : ℝ) ^ (σ + (V.rank : ℝ) / 2) * (autMeasure V m).real univ : ℝ) : ℂ) := by
    funext g
    rw [petCoef_one, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    push_cast; rfl
  rw [zetaConvH_iff, e] at h2
  rw [h3, zetaH_eq, e, integral_complex_ofReal, Complex.ofReal_re]
  have hp : ∀ g, 0 < (hgt V a (io V (g, 1)) : ℝ) ^ (σ + (V.rank : ℝ) / 2) * (autMeasure V m).real univ := fun g =>
    mul_pos (Real.rpow_pos_of_pos (hgtH_pos _) _) hv
  refine (integral_pos_iff_support_of_nonneg (fun g => (hp g).le) (by simpa using h2.re)).2 ?_
  rw [show Function.support _ = univ from eq_univ_of_forall fun g => (hp g).ne']
  exact isOpen_univ.measure_pos m univ_nonempty

theorem not_basicIdentity_one [Infinite (GQ V)] (m : Measure (GA D V)) [m.IsHaarMeasure] :
    ¬ BasicIdentity V 1 m 1 1 1 := fun b => by
  have hd := isFundamentalDomain_stdDom (GQ V) m
  have h : m univ = ⊤ := by
    rw [hd.measure_eq_tsum univ]
    simp only [smul_set_univ, univ_inter]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (hd.measure_ne_zero (NeZero.ne m))
  have h2 := b.2.1
  rw [zetaConvH_iff, petCoef_one] at h2
  simp only [Pi.one_apply, one_mul, Complex.conj_ofReal] at h2
  rcases integrable_const_iff.1 h2 with h3 | h3
  · exact Model.vol_ne_zero V m h3
  · exact measure_ne_top m _ h

theorem conclusion_zero (V : HSp D) (a : GL (Fin V.rank) (AE D)) (μ : (AE D)ˣ →* Circle) (s₁ s₀ : ℂ)
    (m : Measure (GA D V)) (f₁ f₂ : GA D V → ℂ) :
    EisRegularAt V (flat V a 0 s₁) s₀ 0 ∧ BasicIdentity V μ m (flat V a 0 s₁ s₀) f₁ f₂ := by
  have h1 : flat V a 0 s₁ = fun _ _ => 0 := by
    funext s g
    exact (flatH_apply _ _ _ _).trans (by simp)
  have h2 : eis V (fun _ => 0) = fun _ => 0 := by
    funext g
    simp [eis, cosetSum, term]
  have h3 : dblIntegrandQ V μ (fun _ => 0) f₁ f₂ = fun _ => 0 := funext fun _ => by simp [dblIntegrandQ, dblIntegrand]
  rw [h1]
  refine ⟨⟨1, fun _ _ => 0, one_pos, fun s _ _ g => ?_, fun _ => differentiableOn_const _, continuousOn_const,
    0, 0, fun _ _ _ => by simp⟩, ?_⟩
  · have : eisSer V (fun _ _ => (0 : ℂ)) g = fun _ => 0 := funext fun s => congrFun h2 g
    rw [eisCont, this, (holValueAt_const 0 s).valueAt.cont_eq, mul_zero]
  · simp only [BasicIdentity, h2, DblConv, dblInt, h3, zetaConvH_iff, zetaH_eq, zero_mul, integral_zero,
      integrable_zero, and_true]
    exact ⟨⟨fun _ _ _ => by simp [dblIntegrand], integrable_zero _ _ _⟩, integrable_zero _ _ _⟩

end GlobalTheory.Eis.DblModel

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FirstClauseRankZero
section
noncomputable section

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelFormula.Model

variable {D : D7}

theorem two_mul_finrank_le {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) (W : Submodule E B.V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0) : 2 * Module.finrank E W ≤ B.rank := by
  let b := Module.finBasis E W
  have hl : LinearIndependent E fun i => B.hT (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h1 : B.hT ((∑ i, star (c i) • b i : W) : B.V) = 0 := by
      rw [← hc]; simp [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]
    have h2 : (∑ i, star (c i) • b i : W) = 0 := Subtype.ext (B.nondeg.1 _ fun y => by rw [h1]; rfl)
    simpa using Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 i
  have h3 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range fun i => B.hT (b i)))
  rw [finrank_span_eq_card hl, Fintype.card_fin, B.rank_eq] at h3
  have h4 : W ≤ (Submodule.span E (Set.range fun i => B.hT (b i))).dualCoannihilator := fun y hy => by
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; exact hW _ (b i).2 _ hy
    | zero => rfl
    | add _ _ _ _ h h' => rw [LinearMap.add_apply, h, h', add_zero]
    | smul _ _ _ h => rw [LinearMap.smul_apply, h, smul_zero]
  have := Submodule.finrank_mono h4
  omega

theorem bddAbove_witt {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    BddAbove {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0} :=
  ⟨B.rank, by rintro _ ⟨W, rfl, hW⟩; have := two_mul_finrank_le B W hW; omega⟩

theorem two_mul_wittIdx_le {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    2 * Formalism.MainNotions.SchurIrreducible.wittIdx B ≤ B.rank := by
  obtain ⟨W, h, hW⟩ := Nat.sSup_mem (s := {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧
    ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0}) ⟨_, ⊥, rfl, by simp⟩ (bddAbove_witt B)
  rw [Formalism.MainNotions.SchurIrreducible.wittIdx, ← h]
  exact two_mul_finrank_le B W hW

theorem range_of_two_mul_lt {A B : HSp D} (h : 2 * A.rank < B.rank) : A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
  have := two_mul_wittIdx_le B
  omega

abbrev pos (D : D7) (n : ℕ) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n

theorem wittIdx_pos (n : ℕ) : Formalism.MainNotions.SchurIrreducible.wittIdx (pos D n) = 0 :=
  Formalism.MainNotions.J.wittIdx_zero _ (Formalism.MainNotions.J.aniso_of_definite _ D.host.φ₀ (D.sp.cm.cmUnram.2.1 D.host.φ₀)
    (Examples₂.posSpace_sigOK _ _) fun _ => .inl rfl)

theorem wittIdx_dblSp (V : HSp D) : Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp V) = V.rank := by
  have h1 : 2 * Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp V) ≤ V.rank + V.rank := two_mul_wittIdx_le (dblSp V)
  let f : V.V →ₗ[D.host.E] (dblSp V).V := LinearMap.prod LinearMap.id LinearMap.id
  have hf : Function.Injective f := fun x y h => congrArg Prod.fst h
  have h2 : V.rank ≤ Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp V) := le_csSup (bddAbove_witt _)
    ⟨LinearMap.range f, (LinearMap.finrank_range_of_inj hf).trans V.rank_eq, by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      change V.hT x y + -V.hT x y = 0
      exact add_neg_cancel _⟩
  omega

theorem data_exist (H : GlobalTheory.Published.WeilRepresentationUnitaryPair) (A B : HSp D) :
    ∃ (m : Measure (GA D B)) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle)
      (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (f : WO (dblSp A) B → ℂ)
      (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)),
      m.IsHaarMeasure ∧ IsWeilDatumO ψ (dblSp A) B 1 χ ω ∧ IsThetaFunO ψ (dblSp A) B f ∧ f ≠ 0 ∧
        IsCovolOne (ratL B A) ν 𝓖 := by
  obtain ⟨ψ, A', B', χ, ω', -, -, -, -, hA, hB, -, h', -⟩ := GlobalTheory.ThetaMean.Model.hypotheses_inhabited H D A.rank B.rank
  obtain ⟨ω, hω⟩ := H D ψ (dblSp A) B 1 χ h'.std h'.hecS h'.hecT
    (by have := h'.resS; change ResEta D 1 (A'.rank + A'.rank) at this; rwa [hA] at this) (hB ▸ h'.resT)
  obtain ⟨f, hf, h0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hω.std (dblSp A) B
  obtain ⟨ν, 𝓖, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D B.rank A.rank
  exact ⟨Measure.haar, ψ, χ, ω, f, ν, 𝓖, inferInstance, hω, hf, h0, hν⟩

theorem ranges_inhabited (D : D7) :
    (∃ A B : HSp D, 1 ≤ A.rank ∧ Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∧ 2 * A.rank < B.rank) ∧
    (∃ A B : HSp D, 1 ≤ A.rank ∧ Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∧ 1 ≤ B.rank ∧ B.rank ≤ A.rank) ∧
    (∃ A B : HSp D, 1 ≤ A.rank ∧ 0 < Formalism.MainNotions.SchurIrreducible.wittIdx B ∧ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank ∧
      2 * A.rank < B.rank) :=
  ⟨⟨pos D 1, pos D 3, le_rfl, wittIdx_pos 3, show 2 * 1 < 3 by decide⟩, ⟨pos D 1, pos D 1, le_rfl, wittIdx_pos 1, le_rfl, le_rfl⟩,
    ⟨pos D 1, dblSp (pos D 2), le_rfl, by rw [wittIdx_dblSp]; exact show 0 < 2 by decide,
      by rw [wittIdx_dblSp]; exact show 1 + 2 < 2 + 2 by decide, show 2 * 1 < 2 + 2 by decide⟩⟩

theorem plane_excluded (D : D7) : ¬ (Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp (pos D 1)) = 0 ∨
    (pos D 1).rank + Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp (pos D 1)) < (dblSp (pos D 1)).rank) := by
  rw [wittIdx_dblSp]; exact show ¬ (1 = 0 ∨ 1 + 1 < 1 + 1) by decide

theorem swSection_eq (A B : HSp D) (ν 𝓖 ω f) : swSection A B ν 𝓖 ω f = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec A B ω ν 𝓖 f := rfl

theorem integrableOn_valZero {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {f : WO (dblSp A) B → ℂ} {ν 𝓖}
    (hν : IsCovolOne (ratL B A) ν 𝓖) (hf : IsThetaFunO ψ (dblSp A) B f) : IntegrableOn (fun y => f (lagr A B y)) 𝓖 ν :=
  GlobalTheory.ThetaMean.integrableOn_lagr hν hf

theorem exists_evalSeminorm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x : κ → AdeleRing (𝓞 F) F)
    (c : NNReal) : ∃ ν : Seminorm ℂ (WeilM.schA F κ), IsContSeminorm ν ∧ ∀ φ, ν φ = c * ‖φ.1 x‖ := by
  refine ⟨c • (normSeminorm ℂ ℂ).comp ((LinearMap.proj x).comp (WeilM.schA F κ).subtype), fun g => ?_, fun φ => rfl⟩
  have h := (continuous_eval_const (F := BoundedContinuousFunction (κ → mixedEmbedding.mixedSpace F) ℂ)
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ).continuous
  exact continuous_const.mul (h.mul continuous_const).norm

theorem first_clause_rank_zero (A B : HSp D) (hB : B.rank = 0) (m : Measure (GA D B)) [m.IsHaarMeasure] (d : ℕ)
    (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    ∃ ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)), IsContSeminorm ν ∧
      ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d),
        absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) := by
  have : IsEmpty (Fin B.rank) := by rw [hB]; infer_instance
  obtain ⟨ν, h1, h2⟩ := exists_evalSeminorm (F := D.host.F) (κ := Fin B.rank × Fin A.rank × Fin d) 0
    (autMeasure B m Set.univ).toNNReal
  refine ⟨ν, h1, fun φ => le_of_eq ?_⟩
  have h3 : descend (GQ B) (absTheta B (φ.1 ∘ coord ε)) = fun _ => ‖φ.1 0‖ₑ := funext fun q => by
    have hs : Subsingleton (Matrix (Fin B.rank) (Fin A.rank) D.host.E) := ⟨fun x y => Matrix.ext fun i => isEmptyElim i⟩
    rw [AutomorphicL2Unitary.descend, absTheta, tsum_eq_single 0 fun b hb => (hb (Subsingleton.elim _ _)).elim]
    exact congrArg (fun z => ‖φ.1 z‖ₑ) (funext fun p => isEmptyElim p.1)
  rw [absThetaInt, h3, lintegral_const, h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_toNNReal (measure_ne_top _ _), ofReal_norm, mul_comm]

theorem absThetaInt_lt_top (H : GlobalTheory.Published.WeilSiegelFormulaUnitary) (A B : HSp D) (m : Measure (GA D B)) [m.IsHaarMeasure]
    (hA : 1 ≤ A.rank) (h : 2 * A.rank < B.rank) {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)) : absThetaInt B m (φ.1 ∘ coord ε) < ⊤ :=
  let ⟨_, _, e⟩ := (H D A B m inferInstance hA (.inr (range_of_two_mul_lt h))).1 d ε
  (e φ).trans_lt ENNReal.ofReal_lt_top

theorem formula (H : GlobalTheory.Published.WeilSiegelFormulaUnitary) {A B : HSp D} (m : Measure (GA D B)) [m.IsHaarMeasure]
    (hA : 1 ≤ A.rank) (h : 2 * A.rank < B.rank) {ψ χ ω f} (hω : IsWeilDatumO ψ (dblSp A) B 1 χ ω)
    (hf : IsThetaFunO ψ (dblSp A) B f) {ν 𝓖} (hν : IsCovolOne (ratL B A) ν 𝓖) (g : GA D (dblSp A)) :
    EisConv A (swSection A B ν 𝓖 ω f) g ∧ eis A (swSection A B ν 𝓖 ω f) g = GlobalTheory.ThetaMean.thetaMean ω m f g :=
  (((H D A B m inferInstance hA (.inr (range_of_two_mul_lt h))).2 ψ χ ω hω f hf).2 h ν 𝓖 hν).2 g

end GlobalTheory.SiegelFormula.Model

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsTraceClassOfRankZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.Orb GlobalTheory.AdelicU GlobalTheory.SplitWeil GlobalTheory.Cusp.Model GlobalTheory.CuspDecay.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspSpectrum.Model

theorem exists_measure (D : D7) (V : HSp D) :
    ∃ μ : Measure (GA D V), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant :=
  ⟨Measure.haar, inferInstance, AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V _ inferInstance⟩

theorem exists_ne_zero : ∃ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (_ : μ.IsHaarMeasure)
    (_ : μ.IsMulRightInvariant), V.rank = 1 ∧ ∃ f ∈ CcGA V, RcuspOp V μ f ≠ 0 := by
  obtain ⟨D⟩ := Mem.nonempty_record_of_locStage
  obtain ⟨μ, _, _⟩ := exists_measure D (line D)
  obtain ⟨v, hv, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (L2cusp_ne_bot μ (wittIndex_line D))
  obtain ⟨f, hf, h⟩ := exists_RcuspOp_ne_zero (v := ⟨v, hv⟩) fun e => h0 (congrArg Subtype.val e)
  exact ⟨D, line D, μ, ‹_›, ‹_›, rfl, f, hf, fun e => h (by rw [e]; rfl)⟩

theorem exists_isotropic : ∃ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (_ : μ.IsHaarMeasure)
    (_ : μ.IsMulRightInvariant), wittIndex V = 1 ∧ L2cusp V μ ≠ ⊤ ∧ ∃ f ∈ CcGA V, f 1 = 1 := by
  obtain ⟨D⟩ := Mem.nonempty_record_of_locStage
  obtain ⟨μ, _, _⟩ := exists_measure D (plane D)
  obtain ⟨φ, hφ, -, h1, -⟩ := exists_bump_ccAd (J := (plane D).gram) (isCMExt_host D) univ_mem
  exact ⟨D, plane D, μ, ‹_›, ‹_›, wittIndex_plane D, L2cusp_plane_ne_top μ, _, hφ, by simp [h1]⟩

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem RcuspOp_one {v : L2cusp V μ} (hv : (v : DividedPowerChartLift V μ) = constantOneDividedPowerChartLift V μ) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    RcuspOp V μ f v = (∫ g, f g ∂μ) • v := by
  have h1 : ∀ g, Rcusp V μ g v = v := fun g => Subtype.ext (by
    change RG V μ g (v : DividedPowerChartLift V μ) = _
    rw [hv]
    exact right_translate_toL2 (memL2_const (Γ := GQ V) (μ := μ) 1) g)
  rw [(isRepOp_RcuspOp hf v).2]
  simp only [h1]
  exact integral_smul_const f v

theorem isTraceClass_of_rank_zero (h : V.rank = 0) (f : GA D V → ℂ) : IsTraceClass (RcuspOp V μ f) := by
  have : IsEmpty (Fin V.rank) := h ▸ inferInstanceAs (IsEmpty (Fin 0))
  have hs : Subsingleton (GA D V) := ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
  have hq : Subsingleton (Quot (GQ V)) := ⟨fun a b => by
    rw [← mk_sec a, ← mk_sec b, Subsingleton.elim (sec _ a) (sec _ b)]⟩
  have : FiniteDimensional ℂ (DividedPowerChartLift V μ) := by
    refine Module.Finite.of_surjective (LinearMap.toSpanSingleton ℂ _ (constantOneDividedPowerChartLift V μ)) fun F => ?_
    refine ⟨F (mk _ 1), Lp.ext ?_⟩
    filter_upwards [Lp.coeFn_smul (F (mk _ 1)) (constantOneDividedPowerChartLift V μ), (memL2_const (Γ := GQ V) (μ := μ) 1).coeFn_toL2] with q a b
    rw [LinearMap.toSpanSingleton_apply, a, Pi.smul_apply, show constantOneDividedPowerChartLift V μ q = _ from b, Subsingleton.elim q (mk _ 1)]
    simp [AutomorphicL2Unitary.descend]
  exact isTraceClass_of_finiteDimensional _

end GlobalTheory.CuspSpectrum.Model

end
end

