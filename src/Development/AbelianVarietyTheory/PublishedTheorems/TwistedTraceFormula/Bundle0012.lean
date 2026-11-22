import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspidalOrbitalIntegrals
section
noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.Published

def CuspidalOrbitalIntegrals : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (h : IsSqIntIrr ε σ) (μ : Measure (UJ ε)) [μ.IsHaarMeasure],
    ∀ f ∈ CcMat (ujMat ε), IsBiFinite (KG ε) f → HasPseudoTraces ε μ (ujRep h.2.2.1) f →
    ∀ Θ : UJ ε → ℂ, IsCharFn (ujMat ε) μ (ujRep h.2.2.1) Θ → ∀ s, IsRegSS (ujMat ε s) →
      ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
        (IsCompact (cent s : Set (UJ ε)) → HasOrbInt μ s dt f (conj (Θ s) / dt.real Set.univ)) ∧
        (¬ IsCompact (cent s : Set (UJ ε)) → HasOrbInt μ s dt f 0)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
section
noncomputable section

open scoped NNReal ComplexConjugate
open Filter Topology Set Metric MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.Mem.Th (InfF CptF)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis

variable {D : D7} (V : HSp D)

def EisRegularAt (Φ : ℂ → GA D (dblSp V) → ℂ) (s₀ : ℂ) (k : ℕ) : Prop :=
  ∃ (r : ℝ) (H : ℂ → GA D (dblSp V) → ℂ), 0 < r ∧
    (∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * eisCont V Φ s g) ∧
    (∀ g, DifferentiableOn ℂ (H · g) (ball s₀ r)) ∧
    ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball s₀ r ×ˢ univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ r, ∀ g, ‖H s g‖ ≤ C * Grow.height (dblSp V) g ^ N

def petCoef (m : Measure (GA D V)) (f₁ f₂ : GA D V → ℂ) : GA D V → ℂ := fun g => Cusp.petersson V m (rTr V g f₁) f₂

def BasicIdentity (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)) (Φ : GA D (dblSp V) → ℂ) (f₁ f₂ : GA D V → ℂ) : Prop :=
  DblConv V μ m (eis V Φ) f₁ f₂ ∧ ZetaConvH D.sp.cm.sig (gram_hdbl V) m Φ (petCoef V m f₁ f₂) ∧
    dblInt V μ m (eis V Φ) f₁ f₂ = zetaH D.sp.cm.sig (gram_hdbl V) m Φ (petCoef V m f₁ f₂)

end GlobalTheory.Eis

namespace GlobalTheory.Published

open GlobalTheory.Eis

def DoublingMethod : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a →
    HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
    ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ →
      (EisContinues V (flat V a φ s₁) ∧ ∀ s₀, ∃ k, EisRegularAt V (flat V a φ s₁) s₀ k) ∧
      (V.rank < b → EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1) ∧
      ∀ θ : InfF D, IsInfFam θ → V.SigOK → ∀ A : CptF V, Cusp.IsCartanFrame V A →
        ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ ∈ Cusp.A0 θ V A, ∀ f₂ ∈ Cusp.A0 θ V A,
          (∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂) ∧
          ZetaContinues V μ m (flat V a φ s₁) f₁ f₂

end GlobalTheory.Published

namespace GlobalTheory.Eis

theorem dslope_family {X : Type} [TopologicalSpace X] {H : ℂ → X → ℂ} {w : X → ℝ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ∀ x, DifferentiableOn ℂ (H · x) (ball s₀ r))
    (hc : ContinuousOn (fun p : ℂ × X => H p.1 p.2) (ball s₀ r ×ˢ univ))
    (hb : ∀ s ∈ ball s₀ r, ∀ x, ‖H s x‖ ≤ w x) (h0 : ∀ x, H s₀ x = 0) :
    (∀ x, DifferentiableOn ℂ (dslope (H · x) s₀) (ball s₀ (r / 2))) ∧
    ContinuousOn (fun p : ℂ × X => dslope (H · p.2) s₀ p.1) (ball s₀ (r / 2) ×ˢ univ) ∧
    ∀ s ∈ ball s₀ (r / 2), ∀ x, ‖dslope (H · x) s₀ s‖ ≤ w x / r := by
  have hsub : ball s₀ (r / 2) ⊆ ball s₀ r := ball_subset_ball (by linarith)
  have hsub' : closedBall s₀ (r / 2) ⊆ ball s₀ r := closedBall_subset_ball (by linarith)
  have h1 : ∀ x, DifferentiableOn ℂ (dslope (H · x) s₀) (ball s₀ r) := fun x =>
    (Complex.differentiableOn_dslope (ball_mem_nhds _ hr)).2 (hd x)
  refine ⟨fun x => (h1 x).mono hsub, ?_, fun s hs x => Complex.norm_dslope_le_div_of_mapsTo_ball (hd x)
    (fun z hz => by simpa [h0] using hb z hz x) (hsub hs)⟩
  rintro ⟨s₁, x₀⟩ ⟨hs₁, -⟩
  have h2 : ContinuousWithinAt (fun p : ℂ × X => dslope (H · x₀) s₀ p.1) (ball s₀ (r / 2) ×ˢ univ) (s₁, x₀) :=
    (((h1 x₀).continuousOn.continuousAt (isOpen_ball.mem_nhds (hsub hs₁))).comp_of_eq continuousAt_fst rfl).continuousWithinAt
  have h3 : Tendsto (fun p : ℂ × X => dslope (H · p.2) s₀ p.1 - dslope (H · x₀) s₀ p.1)
      (𝓝[ball s₀ (r / 2) ×ˢ univ] (s₁, x₀)) (𝓝 0) := by
    refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
    have h4 : ∀ᶠ x in 𝓝 x₀, ∀ z ∈ closedBall s₀ (r / 2), ‖H z x - H z x₀‖ < ε * (r / 4) := by
      refine (isCompact_closedBall s₀ (r / 2)).eventually_forall_of_forall_eventually fun z hz => ?_
      have h5 : ∀ y, ContinuousAt (fun p : ℂ × X => H p.1 p.2) (z, y) := fun y =>
        hc.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hsub' hz, trivial⟩)
      have h6 : ContinuousAt (fun p : X × ℂ => ‖H p.2 p.1 - H p.2 x₀‖) (x₀, z) :=
        (((h5 x₀).comp_of_eq (f := fun p : X × ℂ => (p.2, p.1)) (by fun_prop) rfl).sub
          ((h5 x₀).comp_of_eq (f := fun p : X × ℂ => (p.2, x₀)) (by fun_prop) rfl)).norm
      exact h6.eventually (gt_mem_nhds (by simpa using by positivity))
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (continuousAt_snd.eventually h4)] with p hp h4
    have h7 := Complex.norm_dslope_le_div_of_mapsTo_ball (f := fun z => H z p.2 - H z x₀) (R₂ := ε * (r / 4))
      (((hd _).sub (hd _)).mono hsub) (fun z hz => by simpa [h0] using (h4 z (ball_subset_closedBall hz)).le) hp.1
    have h8 : dslope (fun z => H z p.2 - H z x₀) s₀ p.1 = dslope (H · p.2) s₀ p.1 - dslope (H · x₀) s₀ p.1 := by
      rcases eq_or_ne p.1 s₀ with e | e
      · rw [e, dslope_same, dslope_same, dslope_same]
        exact deriv_fun_sub ((hd _).differentiableAt (ball_mem_nhds _ hr)) ((hd _).differentiableAt (ball_mem_nhds _ hr))
      · simp only [dslope_of_ne _ e, slope_def_field]; ring
    rw [← h8]
    refine h7.trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hε hr]
  simpa [ContinuousWithinAt] using h3.add h2

variable {D : D7} {V : HSp D} {Φ : ℂ → GA D (dblSp V) → ℂ} {s₀ : ℂ} {j k : ℕ}

theorem EisRegularAt.succ (h : EisRegularAt V Φ s₀ k) : EisRegularAt V Φ s₀ (k + 1) := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h
  refine ⟨r, fun s g => (s - s₀) * H s g, hr, fun s hs h0 g => by simp only [e s hs h0]; ring,
    fun g => (differentiableOn_id.sub_const _).mul (hd g), (by fun_prop : ContinuousOn (fun x : ℂ × _ => x.1 - s₀) _).mul hc,
    r * C, N, fun s hs g => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (mem_ball_iff_norm.1 hs).le (hb s hs g) (norm_nonneg _) hr.le

theorem EisRegularAt.pred (h : EisRegularAt V Φ s₀ (k + 1)) (hp : EisPoleLE V Φ s₀ j) (hj : j ≤ k) :
    EisRegularAt V Φ s₀ k := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h
  have h0 : ∀ g, H s₀ g = 0 := fun g => by
    obtain ⟨E, hE, -⟩ := id (hp.2 g)
    obtain ⟨c, hc⟩ := hE.poleLE_iff.1 (hp.2 g)
    have h1 : Tendsto (fun s => (s - s₀) ^ (k + 1 - j)) (𝓝[≠] s₀) (𝓝 0) :=
      (Continuous.tendsto' (by fun_prop) s₀ 0 (by simp; omega)).mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {s₀}ᶜ))) ((zero_mul c ▸ h1.mul hc).congr' ?_)
    filter_upwards [hE.cont_eventuallyEq, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)]
      with s h2 h3 h4
    rw [e s h4 h3, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega), ← h2]
    rfl
  obtain ⟨h1, h2, h3⟩ := dslope_family hr hd hc hb h0
  refine ⟨r / 2, fun s g => dslope (H · g) s₀ s, half_pos hr, fun s hs hs' g => ?_, h1, h2, C / r, N, fun s hs g => ?_⟩
  · have := sub_ne_zero.2 hs'
    simp only [dslope_of_ne _ hs', slope_def_field, h0, e s (ball_subset_ball (by linarith) hs) hs']
    field_simp
    ring
  · rw [div_mul_eq_mul_div]; exact h3 s hs g

theorem EisRegularAt.of_poleLE (h : EisRegularAt V Φ s₀ k) (hp : EisPoleLE V Φ s₀ j) : EisRegularAt V Φ s₀ j := by
  rcases le_total k j with hk | hk
  · exact Nat.le_induction h (fun _ _ => EisRegularAt.succ) j hk
  · exact Nat.decreasingInduction (motive := fun i _ => j ≤ i → EisRegularAt V Φ s₀ i)
      (fun i _ ih hi => (ih (by omega)).pred hp hi) (fun _ => h) hk le_rfl

theorem EisRegularAt.of_eisValueAt {ψ : GA D (dblSp V) → ℂ} (h : EisRegularAt V Φ s₀ k) (hv : EisValueAt V Φ s₀ ψ) :
    ∃ r : ℝ, 0 < r ∧ (∀ g, DifferentiableOn ℂ (eisCont V Φ · g) (ball s₀ r)) ∧
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => eisCont V Φ x.1 x.2) (ball s₀ r ×ˢ univ) ∧
      ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ r, ∀ g, ‖eisCont V Φ s g‖ ≤ C * Grow.height (dblSp V) g ^ N := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h.of_poleLE (eisValueAt_iff_eisPoleLE.1 hv).1
  have e' : ∀ s ∈ ball s₀ r, ∀ g, eisCont V Φ s g = H s g := fun s hs g => by
    rcases eq_or_ne s s₀ with rfl | h0
    · refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] s)
        ((hv.2 g).analyticAt_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hr)] with z h1 h2
      rw [e z h2 h1, pow_zero, one_mul]; rfl
    · rw [e s hs h0, pow_zero, one_mul]
  exact ⟨r, hr, fun g => (hd g).congr fun s hs => e' s hs g, hc.congr fun x hx => e' _ hx.1 _, C, N,
    fun s hs g => e' s hs g ▸ hb s hs g⟩

theorem EisRegularAt.eisPoleLE (h : EisRegularAt V Φ s₀ k) (hE : EisContinues V Φ) : EisPoleLE V Φ s₀ k := by
  obtain ⟨r, H, hr, e, hd, -⟩ := h
  refine ⟨hE.1, fun g => ?_⟩
  obtain ⟨E, hE⟩ := hE.2 g
  refine (hE.isExtAt trivial).poleLE_iff.2 ⟨H s₀ g, (((hd g).continuousOn.continuousAt
    (ball_mem_nhds _ hr)).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_⟩
  filter_upwards [(hE.isExtAt (s₀ := s₀) trivial).cont_eventuallyEq, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)] with s h2 h3 h4
  rw [e s h4 h3, ← h2]; rfl

section Consequences

variable (hP : Published.DoublingMethod) (h0 : 0 < V.rank) {a : GL (Fin V.rank) (AE D)} (ha : IsMaj V a)
  (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a)) {μ : (AE D)ˣ →* Circle} {b : ℕ} (hμ : IsHeckeChar D μ)
  (hb : ResEta D μ b) {s₁ : ℂ} {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s₁)
include hP h0 ha hI hμ hb hφ

theorem basicIdentity_of_mem (hs : (V.rank : ℝ) / 2 < s₁.re) {θ : InfF D} (hθ : IsInfFam θ) (hV : V.SigOK) {A : CptF V}
    (hA : Cusp.IsCartanFrame V A) (m : Measure (GA D V)) [hm : m.IsHaarMeasure] {f₁ f₂ : GA D V → ℂ}
    (h₁ : f₁ ∈ Cusp.A0 θ V A) (h₂ : f₂ ∈ Cusp.A0 θ V A) : BasicIdentity V μ m φ f₁ f₂ := by
  simpa only [flatH_self] using ((hP D V h0 a ha hI μ b hμ hb s₁ φ hφ).2.2 θ hθ hV A hA m hm f₁ h₁ f₂ h₂).1 s₁ hs

end Consequences

end GlobalTheory.Eis

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
section
noncomputable section

open scoped NNReal
open MeasureTheory Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSW

variable {D : D7}

section SlopeTestRemainingChoices

variable {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r)

def stab : Subgroup (GA D T) where
  carrier := {q | ∃ α : GL (Fin r) (AE D), mt T q ⬝ d.jX = d.jX ⬝ α.1}
  one_mem' := ⟨1, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  mul_mem' := fun ⟨α, h⟩ ⟨β, h'⟩ => ⟨α * β, by
    rw [mt_mul, Matrix.mul_assoc, h', cancel₂ h, Units.val_mul, Matrix.mul_assoc]⟩
  inv_mem' := fun {q} ⟨α, h⟩ => ⟨α⁻¹, by
    have e := cancel₂ h (α⁻¹).1
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at e
    conv_lhs => rw [← e, cancel₂ (mt_inv_mul T q), Matrix.one_mul]⟩

theorem eq_of_mul_jX {q : GA D T} {α : Mx D r r} (h : mt T q ⬝ d.jX = d.jX ⬝ α) : α = d.pX ⬝ (mt T q ⬝ d.jX) := by
  rw [h, cancel₂ d.pX_jX, Matrix.one_mul]

def onX : stab d →* GL (Fin r) (AE D) :=
  MonoidHom.mk' (fun q => q.2.choose) fun p q => Units.ext <| by
    have h1 := p.2.choose_spec
    have h2 := q.2.choose_spec
    have h3 := (p * q).2.choose_spec
    generalize p.2.choose = α, q.2.choose = β, (p * q).2.choose = γ at *
    rw [eq_of_mul_jX d h3, Subgroup.coe_mul, mt_mul, Matrix.mul_assoc, h2, cancel₂ h1, Matrix.mul_assoc,
      cancel₂ d.pX_jX, Matrix.one_mul, Units.val_mul]

theorem mul_jX (q : stab d) : mt T q ⬝ d.jX = d.jX ⬝ (onX d q).1 := q.2.choose_spec

theorem levi_mem (α : GL (Fin r) (AE D)) : d.levi α ∈ stab d := ⟨α, d.levi_jX α⟩

theorem onX_levi (α : GL (Fin r) (AE D)) : onX d ⟨_, levi_mem d α⟩ = α :=
  Units.ext ((eq_of_mul_jX d (mul_jX d _)).trans (eq_of_mul_jX d (d.levi_jX α)).symm)

def absDet : stab d →* ℝ≥0 := (absA D).comp (Matrix.GeneralLinearGroup.det.comp (onX d))

def HasIw (K : Subgroup (GA D T)) : Prop := ∀ h : GA D T, ∃ q : stab d, ∃ k ∈ K, h = q * k

theorem continuous_onX : Continuous (onX d) := by
  have h : Continuous fun q : stab d => (onX d q).1 :=
    (continuous_const.matrix_mul (((continuous_mt T).comp continuous_subtype_val).matrix_mul continuous_const)).congr
      fun q => (eq_of_mul_jX d (mul_jX d q)).symm
  exact Units.continuous_iff.2 ⟨h, (h.comp continuous_inv).congr fun q => by simp⟩

theorem continuous_absDet : Continuous (absDet d) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact continuous_absE.comp (Units.continuous_iff.2
    ⟨(Units.continuous_val.comp (continuous_onX d)).matrix_det,
      (Units.continuous_coe_inv.comp (continuous_onX d)).matrix_det.congr fun p => by
        rw [MonoidHom.comp_apply, ← map_inv]; rfl⟩)

theorem isClosed_stab : IsClosed (stab d : Set (GA D T)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have h1 : IsClosed {q : GA D T | mt T q ⬝ d.jX = d.jX ⬝ (d.pX ⬝ (mt T q ⬝ d.jX))} :=
    isClosed_eq ((continuous_mt T).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_const.matrix_mul ((continuous_mt T).matrix_mul continuous_const)))
  have key : ∀ p q : GA D T, mt T q ⬝ d.jX = d.jX ⬝ (d.pX ⬝ (mt T q ⬝ d.jX)) → mt T p * mt T q = 1 →
      d.pX ⬝ (mt T p ⬝ d.jX) * (d.pX ⬝ (mt T q ⬝ d.jX)) = 1 := fun p q hq e => by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hq, cancel₂ e, Matrix.one_mul, d.pX_jX]
  convert h1.inter (h1.preimage continuous_inv) using 1
  refine Set.ext fun q => ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨⟨_, _, key q q⁻¹ h.2 (mt_mul_inv T q),
    key q⁻¹ q h.1 (mt_inv_mul T q)⟩, h.1⟩⟩
  · obtain ⟨α, h⟩ := h
    exact h.trans (congrArg _ (eq_of_mul_jX d h))
  · obtain ⟨α, h⟩ := inv_mem h
    exact h.trans (congrArg _ (eq_of_mul_jX d h))

variable (b : GL (Fin T.rank) (AE D))

theorem HasIw.isIwasawa {d : HypDec T T₀ r} {b : GL (Fin T.rank) (AE D)} (h : HasIw d (Kmax T b)) :
    IsIwasawa (absDet d) (Kmax T b) :=
  haveI := isLattice_frameLat_host T
  isIwasawa_of_isCompact (isClosed_stab d) (continuous_absDet d) (isCompact_levelAll (AdelicU.isCMExt_host D) _ _ _) h

def rhoH (T : HSp D) (r : ℕ) : ℝ := ((T.rank : ℝ) - r) / 2

def sphericalSection (s : ℂ) : GA D T → ℂ := fun h => npow (iwAbs (absDet d) (Kmax T b) h) (s + rhoH T r)

def sphericalEisenstein (h : GA D T) : ℂ → ℂ := fun s => cosetSum (stab d) (GQ T) (sphericalSection d b s) h

def EisensteinRegularAt (s₀ : ℂ) (k : ℕ) : Prop :=
  ∃ (ε : ℝ) (A : ℂ → GA D T → ℂ), 0 < ε ∧
    (∀ s ∈ Metric.ball s₀ ε, s ≠ s₀ → ∀ h, A s h = (s - s₀) ^ k * cont (sphericalEisenstein d b h) s) ∧
    (∀ h, DifferentiableOn ℂ (A · h) (Metric.ball s₀ ε)) ∧
    ContinuousOn (fun x : ℂ × GA D T => A x.1 x.2) (Metric.ball s₀ ε ×ˢ Set.univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ ε, ∀ h, ‖A s h‖ ≤ C * Grow.height T h ^ N

def eisensteinResidue : ℂ := laurent (sphericalEisenstein d b 1) (rhoH T r) (-1)

def EisensteinContinues : Prop :=
  (∀ s : ℂ, rhoH T r < s.re → ∀ h, CosetConv (stab d) (GQ T) (sphericalSection d b s) h) ∧ (∀ h, Continues (sphericalEisenstein d b h)) ∧
    (∀ s₀, ∃ k, EisensteinRegularAt d b s₀ k) ∧ eisensteinResidue d b ≠ 0 ∧
    ∀ h, PoleLE (sphericalEisenstein d b h) (rhoH T r) 1 ∧ ResidueAt (sphericalEisenstein d b h) (rhoH T r) (eisensteinResidue d b)

theorem sphericalSection_levi_mul {d : HypDec T T₀ r} {b : GL (Fin T.rank) (AE D)} (h : HasIw d (Kmax T b)) (s : ℂ)
    (α : GL (Fin r) (AE D)) {k : GA D T} (hk : k ∈ Kmax T b) :
    sphericalSection d b s (d.levi α * k) = npow (absA D (Matrix.GeneralLinearGroup.det α)) (s + rhoH T r) := by
  have := h.isIwasawa.iwAbs_mul ⟨_, levi_mem d α⟩ hk
  rw [absDet, MonoidHom.comp_apply, MonoidHom.comp_apply, onX_levi] at this
  exact congrArg (npow · _) this

end SlopeTestRemainingChoices

section Schwartz

variable {S T T' : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))

def projK {K : Subgroup (GA D T)} (ν : Measure K) (φ : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ∫ k, om (1, (k : GA D T)) φ w ∂ν

def ikeda (ψ : AddChar (AF D.host.F) ℂ) {t : ℕ} (d : HypDec T T' t) (μ : Measure (Mx D t S.rank))
    (𝓕 : Set (Mx D t S.rank)) (φ : WO S T → ℂ) : WO S T' → ℂ := d.mixT S ψ μ 𝓕 φ 0

theorem ikeda_apply (ψ : AddChar (AF D.host.F) ℂ) {t : ℕ} (d : HypDec T T' t) (μ : Measure (Mx D t S.rank))
    (𝓕 : Set (Mx D t S.rank)) (φ : WO S T → ℂ) (w : WO S T') :
    ikeda ψ d μ 𝓕 φ w = ∫ ξ in 𝓕, φ (d.jX ⬝ ξ + d.j0 ⬝ w) ∂μ := by
  refine integral_congr_ae (.of_forall fun ξ => (d.integrandT_eq φ 0 ξ w).trans ?_)
  rw [map_zero, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  rfl

variable (θ : InfFam D) (τ : D.what₂.Tau)

def centreAct (T : HSp D) (p : MvPolynomial ℕ ℂ) (f : GA D T → ℂ) : GA D T → ℂ := polyAct (gelf θ T τ) p f

def omCentreS (p : MvPolynomial ℕ ℂ) (φ : WO S T → ℂ) : WO S T → ℂ :=
  fun w => centreAct θ τ S p (fun g => om (g, 1) φ w) 1

def omCentreT (p : MvPolynomial ℕ ℂ) (φ : WO S T → ℂ) : WO S T → ℂ :=
  fun w => centreAct θ τ T p (fun h => om (1, h) φ w) 1

theorem omCentreT_C (c : ℂ) (φ : WO S T → ℂ) : omCentreT om θ τ (MvPolynomial.C c) φ = c • φ := by
  funext w
  by_cases hc : c = 0
  · simp [omCentreT, centreAct, polyAct, hc]
  · simp [omCentreT, centreAct, polyAct, opPow, MvPolynomial.support_C, hc, show ((1 : GA D S), (1 : GA D T)) = 1 from rfl]

end Schwartz

section Integrals

variable {S T T₀ : HSp D} {r : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
  (m : Measure (GA D T))

def ThetaPairConv (φ : WO S T → ℂ) (E : GA D T → ℂ) (g : GA D S) : Prop :=
  Integrable (descend (GQ T) fun h => thetaKO om g h φ * E h) (autMeasure T m)

def thetaPair (φ : WO S T → ℂ) (E : GA D T → ℂ) (g : GA D S) : ℂ :=
  ⨍ q, descend (GQ T) (fun h => thetaKO om g h φ * E h) q ∂autMeasure T m

def thetaInt (φ : WO S T → ℂ) : GA D S → ℂ := thetaPair om m φ 1

variable (θ : InfFam D) (τ : D.what₂.Tau) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D))

def IsRegElt (zG zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ) : Prop :=
  (∀ φ, IsThetaFunO ψ S T φ → omCentreS om θ τ zG φ = omCentreT om θ τ zH φ) ∧
  (∀ φ, IsThetaFunO ψ S T φ → ∀ g, Grow.RapidDec T fun h => thetaKO om g h (omCentreT om θ τ zH φ)) ∧
  (∀ s, centreAct θ τ T zH (sphericalSection d b s) = P.eval s • sphericalSection d b s) ∧ P ≠ 0

def regInt (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ) (φ : WO S T → ℂ) (g : GA D S) : ℂ → ℂ :=
  fun s => (eisensteinResidue d b * P.eval s)⁻¹ * thetaPair om m (omCentreT om θ τ zH φ) (fun h => sphericalEisenstein d b h s) g

def RegIntProps (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ) (φ : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T (omCentreT om θ τ zH φ) ∧ ∀ g,
    Continues (regInt om m θ τ d b zH P φ g) ∧ PoleLE (regInt om m θ τ d b zH P φ g) (rhoH T r) 1 ∧
    ∀ (s : ℂ) (E : GA D T → ℂ), (∀ h, HolValueAt (sphericalEisenstein d b h) s (E h)) →
      ThetaPairConv om m (omCentreT om θ τ zH φ) E g ∧
      (P.eval s ≠ 0 → HolValueAt (regInt om m θ τ d b zH P φ g) s
        ((eisensteinResidue d b * P.eval s)⁻¹ * thetaPair om m (omCentreT om θ τ zH φ) E g))

def regRes (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ) (φ : WO S T → ℂ) : GA D S → ℂ :=
  fun g => laurent (regInt om m θ τ d b zH P φ g) (rhoH T r) (-1)

end Integrals

end GlobalTheory.RegSW

namespace GlobalTheory.Published

open GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)

def RegularisedSiegelWeilFirstTerm : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V T T' : HSp D) (t : ℕ) (d : HypDec T T' t),
    T.rank + T'.rank = 2 * V.rank → T'.rank < T.rank → 0 < T'.rank →
  ∀ (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp V) × GA D T →* Module.End ℂ (WO (dblSp V) T → ℂ))
    (ω' : GA D (dblSp V) × GA D T' →* Module.End ℂ (WO (dblSp V) T' → ℂ)),
    IsWeilDatumO ψ (dblSp V) T 1 χ ω → IsWeilDatumO ψ (dblSp V) T' 1 χ ω' →
  ∀ (a : GL (Fin V.rank) (AE D)) (b : GL (Fin T.rank) (AE D)), IsMaj V a → IsMaj T b →
    HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → HasIw d (Kmax T b) →
  ∀ (μ₀ : Measure (WO V T)) (𝓕₀ : Set (WO V T)), IsCovolOne (ratL T V) μ₀ 𝓕₀ →
  ∀ (μ₁ : Measure (Mx D t (dblSp V).rank)) (𝓕₁ : Set (Mx D t (dblSp V).rank)), IsCovolOne (ratMx D _ _) μ₁ 𝓕₁ →
  ∀ (ν : Measure (Kmax T b)), ν.IsHaarMeasure → IsProbabilityMeasure ν →
  ∀ (m : Measure (GA D T')), m.IsHaarMeasure →
    (∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsThetaFunO ψ (dblSp V) T (projK ω ν φ) ∧
      IsThetaFunO ψ (dblSp V) T' (ikeda ψ d μ₁ 𝓕₁ φ)) ∧
    (∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsKFinVec ω (Khat V a) φ →
      EisPoleLE V (flat V a (swSec V T ω μ₀ 𝓕₀ φ) (sZero V T)) (sZero V T) 1) ∧
    (IsAniso T' → (∀ φ', IsThetaFunO ψ (dblSp V) T' φ' → ∀ g, ThetaPairConv ω' m φ' 1 g) ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsKFinVec ω (Khat V a) φ →
        EisCoeffAt V (flat V a (swSec V T ω μ₀ 𝓕₀ φ) (sZero V T)) (sZero V T) (-1)
          (κ • thetaInt ω' m (ikeda ψ d μ₁ 𝓕₁ (projK ω ν φ)))) ∧
    ∀ (T₀ : HSp D) (r' : ℕ) (d₀ : HypDec T' T₀ r'), IsAniso T₀ → 0 < r' →
    ∀ b' : GL (Fin T'.rank) (AE D), IsMaj T' b' → HasIw d₀ (Kmax T' b') → ∀ θ : InfFam D, IsInfFam θ →
      EisensteinContinues d₀ b' ∧ (∀ τ, ∃ zG zH P, IsRegElt ψ ω' θ τ d₀ b' zG zH P) ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ τ zG zH P, IsRegElt ψ ω' θ τ d₀ b' zG zH P →
        (∀ φ', IsThetaFunO ψ (dblSp V) T' φ' → RegIntProps ψ ω' m θ τ d₀ b' zH P φ') ∧
        ∀ φ, IsThetaFunO ψ (dblSp V) T φ → IsKFinVec ω (Khat V a) φ →
          EisCoeffAt V (flat V a (swSec V T ω μ₀ 𝓕₀ φ) (sZero V T)) (sZero V T) (-1)
            (κ • regRes ω' m θ τ d₀ b' zH P (ikeda ψ d μ₁ 𝓕₁ (projK ω ν φ)))

example (D : D7) : ∃ (V T T' : HSp D) (t : ℕ) (_ : HypDec T T' t),
    T.rank + T'.rank = 2 * V.rank ∧ T'.rank < T.rank ∧ 0 < T'.rank :=
  ⟨diagSp D 2 ![false, false] 2 0, _, _, 1, hypDecThree D, rfl, (by decide : 1 < 3), Nat.one_pos⟩

end GlobalTheory.Published

end
end

