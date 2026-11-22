import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0139
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0134
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0327
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantBoxApproximation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0315

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasFiniteLengthOfSubsingleton
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

section Small

variable {Γ G V U : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

theorem hasFiniteLength_of_subsingleton [Subsingleton V] (ρ : Representation ℂ G V) : HasFiniteLength ρ := by
  have : Subsingleton ρ.asModule := inferInstanceAs (Subsingleton V)
  rw [HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, inferInstance⟩

theorem coinv_of_subsingleton [Subsingleton V] (τ : Representation ℂ (Γ × G) V) (ψ : Γ →* ℂˣ) :
    HasFiniteLength (coinv τ ψ) :=
  have : Subsingleton (V ⧸ twRel (τ.comp (MonoidHom.inl Γ G)) ψ) := Submodule.Quotient.subsingleton_iff.2 (Subsingleton.elim _ _)
  hasFiniteLength_of_subsingleton _

theorem coinv_of_equiv {τ : Representation ℂ (Γ × G) V} {τ' : Representation ℂ (Γ × G) U} (E : τ.Equiv τ')
    (ψ : Γ →* ℂˣ) (h : HasFiniteLength (coinv τ' ψ)) : HasFiniteLength (coinv τ ψ) := by
  let τ₀ : Representation ℂ (Γ × G) PUnit := Representation.trivial ℂ _ _
  let i : τ₀.IntertwiningMap τ := ⟨0, fun g => by ext v; simp⟩
  refine GlobalTheory.T.finite_length_coinvariants_exact Γ G PUnit V U τ₀ τ τ' i E.toIntertwiningMap E.toLinearEquiv.surjective
    (fun x => ?_) ψ (coinv_of_subsingleton _ _) h
  constructor
  · intro hx
    refine ⟨0, ?_⟩
    have : E.toLinearEquiv x = 0 := hx
    exact ((E.toLinearEquiv.map_eq_zero_iff).1 this).symm ▸ rfl
  · rintro ⟨y, rfl⟩
    show E.toLinearEquiv 0 = 0
    simp

end Small

section Strata

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem stratum_finiteLength (hI : InductionFiniteLength k) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ) (κ : ℕ)
    (ψ : GL a k →* ℂˣ) : HasFiniteLength (coinv (omegaOn a b μ {κ}) ψ) := by
  by_cases hκ : κ ≤ Fintype.card b
  · let e : Fin κ ⊕ Fin (Fintype.card b - κ) ≃ b :=
      (stdSum (Nat.add_sub_cancel' hκ)).trans (Fintype.equivFin b).symm
    obtain ⟨E⟩ := GlobalTheory.T.omega_equiv_induced_fibre k a b (Fin κ) (Fin (Fintype.card b - κ)) e κ (Fintype.card_fin κ).symm μ hμ
    refine coinv_of_equiv E ψ (GlobalTheory.T.coinvariants_finite_of_smooth_levi k hI _ _ b _ _ e _ (GlobalTheory.T.fibre_representation_smooth k a _ _ μ hμ κ) ψ ?_)
    let τ := fibRep (k := k) a (Fin κ) (Fin (Fintype.card b - κ)) μ κ
    let ω : GL a k →* ℂˣ := (fibChar a (Fin κ) (Fin (Fintype.card b - κ)) μ).comp (MonoidHom.inl _ _)
    have hfin := GlobalTheory.T.finite_twisted_rank_quotient k a (Fin κ) κ (Fintype.card_fin κ).symm (ψ * ω⁻¹)
    have hle : twRel (rightRep (k := k) a (Fin κ) κ) (ψ * ω⁻¹) ≤ twRel (τ.comp (MonoidHom.inl _ _)) ψ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, φ, rfl⟩
      have h1 : ∀ φ' : SB (RankIn k a (Fin κ) {κ}), τ (g, 1) φ' = (ω g : ℂ) • rightRep (k := k) a (Fin κ) κ g φ' := by
        intro φ'
        refine Subtype.ext (funext fun y => ?_)
        show (fibRep a (Fin κ) (Fin (Fintype.card b - κ)) μ κ (g, 1, 1) φ').1 y = _
        rw [fibRep_apply]
        rfl
      have h2 : rightRep (k := k) a (Fin κ) κ g φ - (((ψ * ω⁻¹) g : ℂˣ) : ℂ) • φ =
          ((ω g)⁻¹ : ℂˣ).1 • (τ (g, 1) φ - (ψ g : ℂ) • φ) := by
        rw [h1, smul_sub, smul_smul, smul_smul]
        simp [mul_comm]
      rw [SetLike.mem_coe, h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, φ, rfl⟩)
    exact Module.Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
  · have : IsEmpty (RankIn k a b {κ}) := ⟨fun x => hκ (by
      have h := rank_le_card_height x.1
      rw [show x.1.rank = κ from x.2] at h
      exact h)⟩
    have : Subsingleton (SB (RankIn k a b {κ})) :=
      ⟨fun f g => Subtype.ext (funext fun x => isEmptyElim x)⟩
    exact coinv_of_subsingleton _ _

theorem filt_finiteLength (hI : InductionFiniteLength k) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (ψ : GL a k →* ℂˣ) (N : ℕ) (j κ : ℕ) (h : κ + j = N) :
    HasFiniteLength (coinv (filt a b μ (Set.Iio N) κ).toRepresentation ψ) := by
  induction j generalizing κ with
  | zero =>
    obtain rfl : κ = N := h
    have : Subsingleton (filt a b μ (Set.Iio κ) κ).toSubmodule :=
      ⟨fun f g => Subtype.ext (Subtype.ext (funext fun x =>
        (f.2 x x.2).trans (g.2 x x.2).symm))⟩
    exact coinv_of_subsingleton _ _
  | succ j ih =>
    have hs : ∀ r, r ∈ ({κ} : Set ℕ) ↔ κ ≤ r ∧ r < κ + 1 := fun r => by
      rw [Set.mem_singleton_iff]; omega
    have hmn : κ + 1 ≤ N := by omega
    have hle : (filt a b μ (Set.Iio N) (κ + 1)).toSubmodule ≤ (filt a b μ (Set.Iio N) κ).toSubmodule :=
      fun Φ hΦ x hx => hΦ x (Nat.lt_succ_of_lt hx)
    let i : (filt a b μ (Set.Iio N) (κ + 1)).toRepresentation.IntertwiningMap
        (filt a b μ (Set.Iio N) κ).toRepresentation :=
      ⟨Submodule.inclusion hle, fun g => by ext; rfl⟩
    refine GlobalTheory.T.finite_length_coinvariants_exact _ _ _ _ _ _ _ _ i (resFilt μ hmn hs) (resFilt_surjective μ hmn hs) (fun Φ => ?_) ψ
      (ih (κ + 1) (by omega)) (stratum_finiteLength hI hμ κ ψ)
    constructor
    · intro h0
      have := (ker_resFilt μ hmn hs Φ).1 h0
      exact ⟨⟨Φ.1, this⟩, rfl⟩
    · rintro ⟨Ψ, rfl⟩
      exact (ker_resFilt μ hmn hs _).2 Ψ.2

def toFilt (μ : kˣ →* ℂˣ) (N : ℕ) (hN : ∀ x : Matrix b a k, x.rank < N) :
    (omega a b μ).Equiv (filt a b μ (Set.Iio N) 0).toRepresentation :=
  .mk
    { toFun := fun Φ => ⟨⟨fun x => Φ.1 x.1, comp_mem_SB_of_isInducing IsInducing.subtypeVal Φ isClosed_univ
          (fun _ => trivial) fun x _ _ => ⟨⟨x, hN x⟩, rfl⟩⟩, fun _ hx => absurd hx (Nat.not_lt_zero _)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun Ψ => ⟨fun x => Ψ.1.1 ⟨x, hN x⟩, comp_mem_SB_of_isInducing
          ((IsInducing.subtypeVal.of_comp_iff (f := fun x : Matrix b a k => (⟨x, hN x⟩ : RankIn k a b (Set.Iio N)))).1 IsInducing.id) Ψ.1 isClosed_univ (fun _ => trivial)
          fun x _ _ => ⟨x.1, rfl⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } (fun _ => rfl)

end Strata

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

abbrev thetaQuot (μ χ : kˣ →* ℂˣ) := coinv (omega a b μ⁻¹) (detChar a χ)

variable {a b}

theorem twRel_omega (μ χ : kˣ →* ℂˣ) :
    twRel ((omega a b μ⁻¹).comp (MonoidHom.inl _ _)) (detChar a χ) =
      Submodule.span ℂ {w : SB (Matrix b a k) | ∃ (g : GL a k) (Φ : SB (Matrix b a k)),
        w.1 = om μ g 1 Φ.1 - (χ (GeneralLinearGroup.det g) : ℂ) • Φ.1} := by
  unfold twRel
  refine congrArg (Submodule.span ℂ) (Set.ext fun w => ?_)
  constructor
  · rintro ⟨g, Φ, rfl⟩
    refine ⟨g, Φ, ?_⟩
    have := omega_eq_om μ⁻¹ g (1 : GL b k) Φ
    rw [inv_inv] at this
    exact congrArg₂ (· - ·) this rfl
  · rintro ⟨g, Φ, h⟩
    refine ⟨g, Φ, Subtype.ext ?_⟩
    have := omega_eq_om μ⁻¹ g (1 : GL b k) Φ
    rw [inv_inv] at this
    exact h.trans (congrArg₂ (· - ·) this.symm rfl)

theorem thetaQuot_mk (μ χ : kˣ →* ℂˣ) (h : GL b k) (Φ Ψ : SB (Matrix b a k)) (hΨ : Ψ.1 = om μ 1 h Φ.1) :
    thetaQuot a b μ χ h (Submodule.Quotient.mk Φ) = Submodule.Quotient.mk Ψ := by
  have := omega_eq_om μ⁻¹ (1 : GL a k) h Φ
  rw [inv_inv] at this
  exact congrArg Submodule.Quotient.mk (Subtype.ext (this.trans hΨ.symm))

theorem thetaQuot_finiteLength (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {μ : kˣ →* ℂˣ}
    (hμ : IsSmoothChar μ) (χ : kˣ →* ℂˣ) : HasFiniteLength (thetaQuot a b μ χ) := by
  have hI : InductionFiniteLength k := (hBZ k).2.2.1
  have hN : ∀ x : Matrix b a k, x.rank < Fintype.card a + 1 := fun x =>
    Nat.lt_succ_of_le (rank_le_card_width x)
  exact coinv_of_equiv (toFilt μ⁻¹ _ hN) _
    (filt_finiteLength hI hμ.inv _ (Fintype.card a + 1) (Fintype.card a + 1) 0 (by omega))

variable (a b)

abbrev thetaQuotSwap (μ χ : kˣ →* ℂˣ) :=
  coinv ((omega a b μ⁻¹).comp (MulEquiv.prodComm (M := GL b k) (N := GL a k)).toMonoidHom) (detChar b χ)

variable {a b}

theorem thetaQuotSwap_finiteLength (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {μ : kˣ →* ℂˣ}
    (hμ : IsSmoothChar μ) (χ : kˣ →* ℂˣ) : HasFiniteLength (thetaQuotSwap a b μ χ) :=
  GlobalTheory.T.finite_length_coinvariants_swap k a b μ χ (thetaQuot_finiteLength hBZ hμ χ⁻¹)

theorem main (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (n r : ℕ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (χ : kˣ →* ℂˣ) : HasFiniteLength (thetaQuot (k := k) (Fin r) (Fin n) μ χ) ∧
      HasFiniteLength (thetaQuotSwap (k := k) (Fin r) (Fin n) μ χ) :=
  ⟨thetaQuot_finiteLength hBZ hμ χ, thetaQuotSwap_finiteLength hBZ hμ χ⟩

end Main

end GlobalTheory.CompanionTheory.ThetaGLLen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealElementMapsClosedSystemDown
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
  GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step.Maps

section Pull

variable {X : Scheme.{0}} {P : X.Modules}

lemma le_pullback_of_factors {Y T : Subobject P} (φ : P ⟶ P) (h : T.Factors (Y.arrow ≫ φ)) :
    Y ≤ (Subobject.pullback φ).obj T := by
  rw [Subobject.pullback_obj]
  exact Subobject.le_mk_of_comm
    (pullback.lift (T.factorThru (Y.arrow ≫ φ) h) Y.arrow (Subobject.factorThru_arrow _ _ _))
    (pullback.lift_snd _ _ _)

lemma factors_of_le_pullback {Y T : Subobject P} (φ : P ⟶ P)
    (h : Y ≤ (Subobject.pullback φ).obj T) : T.Factors (Y.arrow ≫ φ) := by
  rw [Subobject.pullback_obj] at h
  have e : Y.arrow ≫ φ = (Y.ofLE _ h ≫ (Subobject.underlyingIso (pullback.snd T.arrow φ)).hom ≫
      pullback.fst T.arrow φ) ≫ T.arrow := by
    rw [← Subobject.ofLE_arrow h, ← Subobject.underlyingIso_hom_comp_eq_mk]
    simp only [Category.assoc, pullback.condition]
  rw [e]
  exact Subobject.factors_comp_arrow _

lemma restrictTop_whole (r : Γ(X, ⊤)) : restrictTop (X := X) ⊤ r = r := by
  unfold GroundTheory.Arith.SchemeCoh.restrictTop
  simp

end Pull

section Mul

attribute [local instance] algebraOfOver

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
  [X.Over (Spec (.of A))]

lemma exists_smulHom_eq (P : X.Modules) {a : A} (ha : a ∈ I ^ 1) :
    ∃ m : P ⟶ idealPow I P 1, m ≫ idealPowι I P 1 = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
  rw [← span_idealGen (I ^ 1)] at ha
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp ha
  have ht : (∑ i, GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) (c i)) ≫
      biproduct.ι (fun _ : Fin (idealGenNum (I ^ 1)) => P) i) ≫ idealSumMap P (I ^ 1) =
      GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
    unfold idealSumMap
    rw [Preadditive.sum_comp]
    simp only [Category.assoc, biproduct.ι_desc, smulHom_comp_smulHom]
    rw [← smulHom_sum, ← hc, map_sum]
    simp only [smul_eq_mul, map_mul]
  refine ⟨kernel.lift _ (GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a)) ?_, ?_⟩
  · rw [← ht, Category.assoc, cokernel.condition, comp_zero]
  · exact kernel.lift_ι _ _ _

lemma factors_powSub (P : X.Modules) (n : ℕ) {a : A} (ha : a ∈ I ^ 1) :
    (powSub I P (n + 1)).Factors ((powSub I P n).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a)) := by
  show (Subobject.mk (idealPowι I P (n + 1))).Factors _
  rw [Subobject.mk_factors_iff]
  refine ⟨(Subobject.underlyingIso (idealPowι I P n)).hom ≫ idealPowMul I P (n := n) a ha, ?_⟩
  show ((Subobject.underlyingIso (idealPowι I P n)).hom ≫ idealPowMul I P (n := n) a ha) ≫
    idealPowι I P (n + 1) = _
  rw [Category.assoc, idealPowMul_ι, ← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
  rfl

theorem mapsDown_toFunctions {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules} (_ : P.IsQuasicoherent)
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (a : A) (ha : a ∈ I) :
    MapsDown S (toFunctions (X := X) (A := A) ⊤ a) := by
  have ha1 : a ∈ I ^ 1 := by rwa [pow_one]
  have hr : toFunctions (X := X) (A := A) ⊤ a = algebraMap A Γ(X, ⊤) a := by
    simp only [GroundTheory.Arith.SchemeCoh.toFunctions, RingHom.comp_apply]
    exact restrictTop_whole _
  rw [hr]
  intro e
  cases e with
  | zero =>
    show (S 0).Factors ((⊤ : Subobject P).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P _)
    apply Subobject.factors_of_le _ (hS.pow_le 0)
    obtain ⟨m, hm⟩ := exists_smulHom_eq I P ha1
    show (Subobject.mk (idealPowι I P 1)).Factors _
    rw [Subobject.mk_factors_iff]
    refine ⟨(⊤ : Subobject P).arrow ≫ m, ?_⟩
    show ((⊤ : Subobject P).arrow ≫ m) ≫ idealPowι I P 1 = _
    rw [Category.assoc, hm]
  | succ e =>
    show (S (e + 1)).Factors ((S e).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P _)
    apply factors_of_le_pullback
    rw [hS.succ e]
    apply sup_le
    · apply le_pullback_of_factors
      rw [← GroundTheory.Arith.SchemeCoh.smulHom_comp]
      exact Subobject.factors_comp_arrow _
    · apply le_pullback_of_factors
      apply Subobject.factors_of_le _ (hS.pow_le (e + 1))
      exact factors_powSub I P (e + 1) ha1

end Mul

end GlobalTheory.CompanionTheory.GE.Step.Maps
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq
section
noncomputable section

open MeasureTheory Filter
open scoped ENNReal
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotNorm

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
  {H : Subgroup G} {μH : Measure H} [SFinite μH] [μH.IsInvInvariant]

theorem ae_lt_top_of_normaliser {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    ∀ᵐ g ∂μG, ρ g < ∞ := by
  have hmulH : Measurable fun p : H × G => (p.1 : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  set E : Set G := {g | ρ g = ∞} with hEdef
  have hE : MeasurableSet E := hρ.1 (measurableSet_singleton ∞)
  have hind : Measurable (E.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hE
  have hzero : ∀ g : G, ∫⁻ h : H, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μH = 0 := by
    intro g
    have hm : Measurable fun h : H => ρ ((h : G) * g) :=
      hρ.1.comp (measurable_subtype_coe.mul_const g)
    have hfin : ∀ᵐ h : H ∂μH, ρ ((h : G) * g) < ∞ :=
      ae_lt_top hm (by rw [hρ.2 g]; exact ENNReal.one_ne_top)
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hfin] with h hh
    simp [hEdef, Set.indicator, hh.ne]
  have key : ∫⁻ h : H, ∫⁻ g, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μG ∂μH = 0 := by
    rw [lintegral_lintegral_swap]
    · simp [hzero]
    · exact (hind.comp hmulH).aemeasurable
  have h2 : ∀ h : H, ∫⁻ g, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μG = μG E := fun h => by
    rw [lintegral_mul_left_eq_self (E.indicator (1 : G → ℝ≥0∞)) (h : G),
      lintegral_indicator_one hE]
  simp only [h2, lintegral_const] at key
  have hne : μH Set.univ ≠ 0 := by
    intro h0
    have h1 := hρ.2 1
    rw [Measure.measure_univ_eq_zero.1 h0] at h1
    simp at h1
  have hE0 : μG E = 0 := (mul_eq_zero.1 key).resolve_right hne
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hE0] with g hg
  exact lt_top_iff_ne_top.2 hg

theorem integral_nonneg_normaliser_eq {f : G → ℝ} (hf : Measurable f) (hf0 : ∀ g, 0 ≤ f g)
    (hfH : ∀ h ∈ H, ∀ g, f (h * g) = f g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫ g, f g * (ρ g).toReal ∂μG = ∫ g, f g * (ρ' g).toReal ∂μG := by
  have aux : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      ∫ g, f g * (σ g).toReal ∂μG = (∫⁻ g, ENNReal.ofReal (f g) * σ g ∂μG).toReal := by
    intro σ hσ
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun g => mul_nonneg (hf0 g) ENNReal.toReal_nonneg)
      (hf.mul hσ.1.ennreal_toReal).aestronglyMeasurable]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_of_normaliser (μG := μG) hσ] with g hg
    rw [ENNReal.ofReal_mul (hf0 g), ENNReal.ofReal_toReal hg.ne]
  rw [aux hρ, aux hρ', lintegral_normaliser_eq (F := fun g => ENNReal.ofReal (f g))
    hf.ennreal_ofReal (fun h hh g => by simp only [hfH h hh g]) hρ hρ']

theorem integrable_normaliser_iff {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μG ↔
      Integrable (fun g => F g * ((ρ' g).toReal : ℂ)) μG := by
  have aux : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      ∫⁻ g, ‖F g * ((σ g).toReal : ℂ)‖ₑ ∂μG = ∫⁻ g, ‖F g‖ₑ * σ g ∂μG := by
    intro σ hσ
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_of_normaliser (μG := μG) hσ] with g hg
    rw [enorm_mul, ← ofReal_norm_eq_enorm ((σ g).toReal : ℂ), Complex.norm_real,
      Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hg.ne]
  have hm : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      AEStronglyMeasurable (fun g => F g * ((σ g).toReal : ℂ)) μG := fun hσ =>
    (hF.mul (Complex.measurable_ofReal.comp hσ.1.ennreal_toReal)).aestronglyMeasurable
  have heq := lintegral_normaliser_eq (μG := μG) (F := fun g => ‖F g‖ₑ) hF.enorm
    (fun h hh g => by simp only [hFH h hh g]) hρ hρ'
  simp only [Integrable, hm hρ, hm hρ', true_and, hasFiniteIntegral_iff_enorm, aux hρ, aux hρ', heq]

theorem integral_real_normaliser_eq {f : G → ℝ} (hf : Measurable f)
    (hfH : ∀ h ∈ H, ∀ g, f (h * g) = f g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ')
    (hi : Integrable (fun g => f g * (ρ g).toReal) μG)
    (hi' : Integrable (fun g => f g * (ρ' g).toReal) μG) :
    ∫ g, f g * (ρ g).toReal ∂μG = ∫ g, f g * (ρ' g).toReal ∂μG := by
  have part : ∀ {σ : G → ℝ≥0∞} {u : G → ℝ}, IsQuotNormaliser H μH σ → Measurable u →
      (∀ g, |u g| ≤ |f g|) → Integrable (fun g => f g * (σ g).toReal) μG →
      Integrable (fun g => u g * (σ g).toReal) μG := by
    intro σ u hσ hu hle h
    refine h.mono (hu.mul hσ.1.ennreal_toReal).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hle g) (abs_nonneg _)
  have hp : Measurable fun g => max (f g) 0 := hf.max measurable_const
  have hn : Measurable fun g => max (-f g) 0 := hf.neg.max measurable_const
  have hpl : ∀ g, |max (f g) 0| ≤ |f g| := fun g => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnl : ∀ g, |max (-f g) 0| ≤ |f g| := fun g => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have dec : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      Integrable (fun g => f g * (σ g).toReal) μG →
      ∫ g, f g * (σ g).toReal ∂μG =
        ∫ g, max (f g) 0 * (σ g).toReal ∂μG - ∫ g, max (-f g) 0 * (σ g).toReal ∂μG := by
    intro σ hσ h
    rw [← integral_sub (part hσ hp hpl h) (part hσ hn hnl h)]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    have : f g = max (f g) 0 - max (-f g) 0 := (max_zero_sub_max_neg_zero_eq_self (f g)).symm
    simp only
    rw [← sub_mul, ← this]
  rw [dec hρ hi, dec hρ' hi',
    integral_nonneg_normaliser_eq hp (fun g => le_max_right _ _)
      (fun h hh g => by simp only [hfH h hh g]) hρ hρ',
    integral_nonneg_normaliser_eq hn (fun g => le_max_right _ _)
      (fun h hh g => by simp only [hfH h hh g]) hρ hρ']

theorem integral_normaliser_eq_of {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μG = ∫ g, F g * ((ρ' g).toReal : ℂ) ∂μG := by
  have hiff := integrable_normaliser_iff (μG := μG) hF hFH hρ hρ'
  by_cases hi : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μG
  · have hi' := hiff.1 hi
    have ere : ∀ {σ : G → ℝ≥0∞}, Integrable (fun g => F g * ((σ g).toReal : ℂ)) μG →
        Integrable (fun g => (F g).re * (σ g).toReal) μG ∧
          (∫ g, F g * ((σ g).toReal : ℂ) ∂μG).re = ∫ g, (F g).re * (σ g).toReal ∂μG := by
      intro σ h
      have h1 := Complex.reCLM.integrable_comp h
      have h2 := Complex.reCLM.integral_comp_comm h
      simp only [Complex.reCLM_apply, Complex.re_mul_ofReal] at h1 h2
      exact ⟨h1, h2.symm⟩
    have eim : ∀ {σ : G → ℝ≥0∞}, Integrable (fun g => F g * ((σ g).toReal : ℂ)) μG →
        Integrable (fun g => (F g).im * (σ g).toReal) μG ∧
          (∫ g, F g * ((σ g).toReal : ℂ) ∂μG).im = ∫ g, (F g).im * (σ g).toReal ∂μG := by
      intro σ h
      have h1 := Complex.imCLM.integrable_comp h
      have h2 := Complex.imCLM.integral_comp_comm h
      simp only [Complex.imCLM_apply, Complex.im_mul_ofReal] at h1 h2
      exact ⟨h1, h2.symm⟩
    apply Complex.ext
    · rw [(ere hi).2, (ere hi').2]
      exact integral_real_normaliser_eq (Complex.measurable_re.comp hF)
        (fun h hh g => by simp only [Function.comp, hFH h hh g]) hρ hρ' (ere hi).1 (ere hi').1
    · rw [(eim hi).2, (eim hi').2]
      exact integral_real_normaliser_eq (Complex.measurable_im.comp hF)
        (fun h hh g => by simp only [Function.comp, hFH h hh g]) hρ hρ' (eim hi).1 (eim hi').1
  · rw [integral_undef hi, integral_undef (fun h => hi (hiff.2 h))]

theorem quotIntegral_eq {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    quotIntegral μG H μH F = ∫ g, F g * ((ρ g).toReal : ℂ) ∂μG := by
  have hex : ∃ ρ, IsQuotNormaliser H μH ρ := ⟨ρ, hρ⟩
  rw [quotIntegral, dif_pos hex]
  exact integral_normaliser_eq_of hF hFH hex.choose_spec hρ

theorem integral_normaliser_eq : PositivityTheory.Rg.BcB.D4.NormEq := by
  intro G _ _ _ _ _ _ _ μ _ H μH _ _ F ρ₁ ρ₂ hF hFH hρ₁ hρ₂
  exact integral_normaliser_eq_of (μG := μ) hF hFH hρ₁ hρ₂

end GlobalTheory.CompanionTheory.QuotNorm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethSwapStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_swap : ∀ {K : Type} [Field K] {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)), KunE pr → KunE (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kunE_swap | exact GlobalTheory.CompanionTheory.KunGlue.kunE_swap | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kunE_swap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLatticeBaseStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_lattice_base : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), 1 ≤ k → ∀ s, k ≤ s → LatBase (lev h k).γ l s := by
  first | exact @GlobalTheory.CompanionTheory.LatCBase.latBase_lev | exact GlobalTheory.CompanionTheory.LatCBase.latBase_lev | (intros; apply GlobalTheory.CompanionTheory.LatCBase.latBase_lev <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantBoxApproximationStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_constant_box_approximation : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (ι : Type) [Fintype ι] (ψ : (ι → Fv F v) → ℝ), Continuous ψ → HasCompactSupport ψ → ∃ B : ℝ, 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → ∃ (k : ℕ) (C : Finset (ι → Fv F v)), (∀ y, |ψ y - ∑ c ∈ C, ψ c * boxInd v k c y| ≤ δ * ∑ c ∈ C, boxInd v k c y) ∧ (C.card : ℝ) * (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ Fintype.card ι)⁻¹ ≤ B ∧ |(∫ y, ψ y ∂(Measure.pi fun _ => lam)) - ∑ c ∈ C, ψ c * (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ Fintype.card ι)⁻¹| ≤ δ * B := by
  first | exact @GlobalTheory.CompanionTheory.Equi.LocApprox.loc_approx | exact GlobalTheory.CompanionTheory.Equi.LocApprox.loc_approx | (intros; apply GlobalTheory.CompanionTheory.Equi.LocApprox.loc_approx <;> assumption)
end

