import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0027
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0957
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExistsBorelOrthonormalMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalSectionBoundedNonzeroMultiple
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspBound

theorem exists_mul_mem_closure {O K Ω : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field Ω] [Algebra K Ω] (S : Set Ω) {x : Ω} (hx : x ∈ Algebra.adjoin K S) :
    ∃ κ : O, κ ≠ 0 ∧ algebraMap K Ω (algebraMap O K κ) * x ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ S) := by
  have hmem : ∀ u : O, algebraMap K Ω (algebraMap O K u) ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ S) :=
    fun u => Subring.subset_closure (Or.inl ⟨u, rfl⟩)
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    exact ⟨1, one_ne_zero, by rw [map_one, map_one, one_mul]; exact Subring.subset_closure (Or.inr hx)⟩
  | algebraMap r =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) r
    have hb0 : algebraMap O K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← map_mul, mul_div_cancel₀ _ hb0]
    exact hmem a
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, h1⟩ := hx
    obtain ⟨t, ht, h2⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : algebraMap K Ω (algebraMap O K (s * t)) * (x + y) =
        algebraMap K Ω (algebraMap O K t) * (algebraMap K Ω (algebraMap O K s) * x) +
        algebraMap K Ω (algebraMap O K s) * (algebraMap K Ω (algebraMap O K t) * y) := by
      simp only [map_mul]; ring
    rw [e]
    exact add_mem (mul_mem (hmem t) h1) (mul_mem (hmem s) h2)
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, h1⟩ := hx
    obtain ⟨t, ht, h2⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : algebraMap K Ω (algebraMap O K (s * t)) * (x * y) =
        (algebraMap K Ω (algebraMap O K s) * x) * (algebraMap K Ω (algebraMap O K t) * y) := by
      simp only [map_mul]; ring
    rw [e]
    exact mul_mem h1 h2

theorem inV_iff' (T : CDVR) (x : T.Fr) : InV T x ↔ 0 ≤ vV T.V x := by
  by_cases h0 : x = 0
  · subst h0; simp [InV, vV]
  have hne := valV_ne_zero (V := T.V) h0
  constructor
  · rintro ⟨a, rfl⟩
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have h2 := (WithZero.log_le_log hne one_ne_zero).2 h1
    rw [WithZero.log_one] at h2
    unfold vV; omega
  · intro h
    have h4 : valV T.V x ≤ 1 := by
      refine (WithZero.log_le_log hne one_ne_zero).1 ?_
      rw [WithZero.log_one]
      unfold vV at h
      omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h4

theorem inV_of_overLa' {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T : CDVR}
    {io : K →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) (a : (la.valuation K).valuationSubring) : InV T (io a) := by
  rw [inV_iff', ho.2]
  refine mul_nonneg (Nat.cast_nonneg e) ?_
  by_cases h0 : (a : K) = 0
  · simp [h0, vLa]
  have hne : la.valuation K (a : K) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h2 := (WithZero.log_le_log hne one_ne_zero).2 a.2
  rw [WithZero.log_one] at h2
  unfold vLa; omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem inV_iff_of_frBor {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {T : CDVR}
    {io : c.F →+* T.Fr} (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ)
    (h : letI := io.toAlgebra; FrBor t y.1 y'.1) : InV T (evI y f) ↔ InV T (evI y' f) := by
  obtain ⟨hE, hU, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have h1 := unitIndep_of hE.wt hU a n f hf T io y y' t h 1
  have key : ∀ x : T.Fr, InV T x ↔ 0 ≤ nval T.V 1 x := fun x => by
    by_cases h0 : x = 0
    · subst h0; simp [nval_zero, InV]
    · rw [nval_of_ne h0, inV_iff', EReal.coe_nonneg]; simp
  rw [key, key, h1]

theorem inV_of_mem_B {O : Type} [CommRing O] {β : O →+* c.F} (P : GlobalTheory.Reg.PChart Xo c β) {e : P.Ω} {T : CDVR}
    {io : c.F →+* T.Fr} (ψ : P.R e →+* T.Fr) (hψ : ∀ k, ψ (algebraMap c.F _ k) = io k) (hO : ∀ a, InV T (io (β a)))
    (hg : ∀ g : P.R e, (g : P.Ω) ∈ P.gens → InV T (ψ g)) (s : P.R e) (hs : (s : P.Ω) ∈ P.B) : InV T (ψ s) := by
  have hle : P.B ≤ (((algebraMap T.V T.Fr).range.comap ψ).map (P.R e).val.toRingHom) := by
    refine Subring.closure_le.2 ?_
    rintro w (⟨o, rfl⟩ | hw)
    · refine ⟨algebraMap c.F _ (β o), ?_, rfl⟩
      show ψ (algebraMap c.F _ (β o)) ∈ (algebraMap T.V T.Fr).range
      rw [hψ]; exact hO o
    · exact ⟨⟨w, Algebra.subset_adjoin (Or.inr hw)⟩, hg _ hw, rfl⟩
  obtain ⟨w, hw, hw'⟩ := hle hs
  obtain rfl : w = s := Subtype.ext hw'
  exact hw

end GlobalTheory.CuspBound

namespace GlobalTheory.CuspBound

set_option maxHeartbeats 1000000 in

theorem exists_bddAll_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ κ : c.F, κ ≠ 0 ∧ BddAll Xo c la κ f := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
  obtain ⟨J, hJ, P, hC, hreg⟩ := GlobalTheory.T.exists_integral_chart_cover_cuspForm_no_pole E H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
  haveI := Fintype.ofFinite J
  choose κ hκ0 hκ using fun j =>
    exists_mul_mem_closure (O := (la.valuation c.F).valuationSubring) (K := c.F) ((P j).gens : Set (P j).Ω) (hreg j)
  have hF := cusp_le_sec Xo c U a n hf
  refine ⟨algebraMap (la.valuation c.F).valuationSubring c.F (∏ j, κ j), ?_, ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective _ c.F)).2 (Finset.prod_ne_zero_iff.2 fun j _ => hκ0 j)
  intro T io m ho y _
  letI := io.toAlgebra
  obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hev := GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hF
  let W : ValuationSubring T.Fr := (valV T.V).valuationSubring
  have hW : ∀ x, x ∈ W ↔ InV T x := fun x =>
    ⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h,
      by rintro ⟨a, rfl⟩; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a⟩
  have hO : ∀ a : (la.valuation c.F).valuationSubring, InV T (io (algebraMap _ c.F a)) := fun a => inV_of_overLa' ho a
  obtain ⟨j, e, he, ψ, z, t, hgW, hz, ht⟩ := hC T.Fr W (fun a => (hW _).2 (hO a)) y.1
  have hzI : Integral T io z := (P j).int e he T io ψ (fun a => hO a) (fun g hg => (hW _).1 (hgW g hg)) z hz
  let z' : IntFr Xo c T io := ⟨z, hE.test _ z, hzI⟩
  set κ' := algebraMap (la.valuation c.F).valuationSubring c.F (∏ j, κ j) with hκ'
  rw [← evI_smul, inV_iff_of_frBor (Submodule.smul_mem _ κ' hF) y z' t ht, evI_smul]
  show InV T (io κ' * evR Xo c f z)
  rw [(hev _).1 _ ψ _ _ hz]
  let s : (P j).R e := algebraMap c.F _ κ' * evR Xo c f ((P j).y e he)
  have hs : ψ s = io κ' * ψ (evR Xo c f ((P j).y e he)) := by
    simp only [s, map_mul, AlgHom.commutes]; rfl
  rw [← hs]
  refine inV_of_mem_B (P j) ψ.toRingHom (fun k => ψ.commutes k) hO
    (fun g hg => (hW _).1 (hgW g hg)) s ?_
  have hyg : evR Xo c f (P j).yg = ((P j).R e).val (evR Xo c f ((P j).y e he)) :=
    (hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)
  obtain ⟨d, hd'⟩ : κ j ∣ ∏ i, κ i := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have e1 : ((s : (P j).R e) : (P j).Ω) = algebraMap c.F (P j).Ω (algebraMap _ c.F d) *
      (algebraMap c.F (P j).Ω (algebraMap _ c.F (κ j)) * evR Xo c f (P j).yg) := by
    rw [hyg]
    simp only [s, hκ', hd', map_mul, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_val]
    ring
  rw [e1]
  exact mul_mem (Subring.subset_closure (Or.inl ⟨d, rfl⟩)) (hκ j)

end GlobalTheory.CuspBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqConstMulOfNormOne
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverConst

theorem eq_const_mul_of_norm_one : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} (U : Set V), IsOpen U → IsPreconnected U → ∀ (P₂ P : ι → V → ℂ) (g : V → ℂ), (∀ i, DifferentiableOn ℂ (P₂ i) U) → (∀ i, DifferentiableOn ℂ (P i) U) → (∀ x ∈ U, ‖g x‖ = 1) → (∀ i, ∀ x ∈ U, P₂ i x = g x * P i x) → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ i, ∀ x ∈ U, P₂ i x = u * P i x := by
  intro V _ _ ι U hU hc P₂ P g hP₂ hP hg1 hg
  by_cases h : ∃ i, ∃ x ∈ U, P i x ≠ 0
  swap
  · push_neg at h
    refine ⟨1, by simp, fun i x hx => ?_⟩
    rw [hg i x hx, h i x hx]
    simp
  obtain ⟨i₀, x₀, hx₀, hne⟩ := h
  have hcont : ContinuousAt (P i₀) x₀ := (hP i₀).continuousOn.continuousAt (hU.mem_nhds hx₀)
  have hnb : ∀ᶠ y in nhds x₀, y ∈ U ∧ P i₀ y ≠ 0 := (hU.eventually_mem hx₀).and (hcont.eventually_ne hne)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnb
  have hx₀b : x₀ ∈ Metric.ball x₀ ε := Metric.mem_ball_self hε
  let q : V → ℂ := fun y => P₂ i₀ y * (P i₀ y)⁻¹
  have hqd : DifferentiableOn ℂ q (Metric.ball x₀ ε) :=
    ((hP₂ i₀).mono (fun y hy => (hball y hy).1)).mul (((hP i₀).mono (fun y hy => (hball y hy).1)).inv
      (fun y hy => (hball y hy).2))
  have hqg : ∀ y ∈ Metric.ball x₀ ε, q y = g y := fun y hy => by
    simp only [q]
    rw [hg i₀ y (hball y hy).1, mul_assoc, mul_inv_cancel₀ (hball y hy).2, mul_one]
  have hmax : IsMaxOn (norm ∘ q) (Metric.ball x₀ ε) x₀ := fun y hy => by
    simp only [Set.mem_setOf_eq, Function.comp_apply]
    rw [hqg y hy, hqg x₀ hx₀b, hg1 _ (hball y hy).1, hg1 _ (hball x₀ hx₀b).1]
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball x₀ ε).isPreconnected
    Metric.isOpen_ball hqd hx₀b hmax
  refine ⟨g x₀, hg1 x₀ hx₀, fun i => ?_⟩
  have hzero : ∀ y ∈ U, (fun y => P₂ i y - g x₀ * P i y) y = 0 := by
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hU hc ((hP₂ i).sub ((hP i).const_mul (g x₀))) hx₀ ?_
    filter_upwards [Metric.ball_mem_nhds x₀ hε] with y hy
    have e : g y = g x₀ := by
      rw [← hqg y hy, ← hqg x₀ hx₀b]
      exact heq hy
    simp only [Pi.zero_apply]
    rw [hg i y (hball y hy).1, e]
    ring
  intro x hx
  have := hzero x hx
  simp only at this
  exact sub_eq_zero.1 this

theorem psi_and_weight_eq : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (k₂ : C.U₂.Comp) (k : (T.U j σ).Comp), (∀ τ : D.host.E →+* ℂ, τ ∈ (C.U₂.X k₂).Ψ ↔ τ ∈ ((T.U j σ).X k).Ψ) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ) (i : Fin D.R.r), laU C.U₂ a n k₂ ⟨τ, h₂⟩ i = laU (T.U j σ) a n k ⟨τ, h₁⟩ i := by
  intro D T hL j hj σ hσ C hC k₂ k
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ
  have hrel : relab C.d.c₂ C.σ₂ = relab T.Q.c σ := by
    funext τ
    ext x
    have e := congrArg (fun φ : T.Q.c.F →+* ℂ => φ (embF T.Q.c τ x)) hC.2.2.1
    simp only [RingHom.comp_apply] at e
    show C.σ₂ (embF C.d.c₂ τ x) = σ (embF T.Q.c τ x)
    rw [← e]
    congr 1
  refine ⟨fun τ => by rw [(hU₂.2.1 k₂).2 τ, (hU₁.2.1 k).2 τ], fun a n τ h₂ h₁ i => ?_⟩
  unfold laU
  rw [(hU₂.2.1 k₂).1, (hU₁.2.1 k).1, hrel]

theorem cover_scalar_const : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∀ k₂ : C.U₂.Comp, ∃ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X k₂).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X k).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X k₂).Gm v w) ∧ (∀ h, (C.dict₂ h).1 = k₂ → (T.dict j σ h).1 = k) ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = u * rdU (T.U j σ) f k x' := by
  intro D T hL j hj σ hσ C hC n k₂
  obtain ⟨k, γ, hΛ, hh, hd, hx⟩ := GlobalTheory.T.levelCover_component_readings_unit_modulus_scalar D T hL j hj σ hσ C hC k₂
  obtain ⟨hΨ, hla⟩ := psi_and_weight_eq D T hL j hj σ hσ C hC k₂ k
  refine ⟨k, γ, hΛ, hh, hd, ?_⟩
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ

  let G : Frame (C.U₂.X k₂).Ψ D.R.r → Frame ((T.U j σ).X k).Ψ D.R.r := fun x τ =>
    ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩ : Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hGrel : ∀ x (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ),
      mat (G x) ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩ := by
    intro x τ h₂ h₁
    rfl
  have hGdom : ∀ x ∈ (C.U₂.X k₂).dom, G x ∈ ((T.U j σ).X k).dom := fun x hx' => (hx x (G x) hx' (hGrel x)).1
  have hGdiff : Differentiable ℂ G := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    simp only [G, mat, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    fun_prop

  let ι := {p : ((D.host.E →+* ℂ) × ℕ → ℕ) × Rul (T.Q.Xo j) T.Q.c × Rul C.d.Xo₂ C.d.c₂ //
    Dom p.1 n ∧ p.2.1 ∈ sec (T.Q.Xo j) T.Q.c p.1 n ∧ p.2.2 ∈ sec C.d.Xo₂ C.d.c₂ p.1 n ∧ C.IsPull p.2.1 p.2.2}
  let P₂ : ι → Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun i => rdU C.U₂ i.1.2.2 k₂
  let P : ι → Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun i x => rdU (T.U j σ) i.1.2.1 k (G x)
  have hP₂d : ∀ i, DifferentiableOn ℂ (P₂ i) (C.U₂.X k₂).dom := fun i =>
    (hU₂.2.2.2.2.1 i.1.1 n i.2.1 i.1.2.2 i.2.2.2.1 k₂).1
  have hPd : ∀ i, DifferentiableOn ℂ (P i) (C.U₂.X k₂).dom := fun i =>
    (hU₁.2.2.2.2.1 i.1.1 n i.2.1 i.1.2.1 i.2.2.1 k).1.comp hGdiff.differentiableOn hGdom
  have hg : ∀ x ∈ (C.U₂.X k₂).dom, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i : ι, P₂ i x = c * P i x := by
    intro x hxd
    obtain ⟨b, hb, hyd, hyo⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_borel_orthonormal_move (C.U₂.X k₂) hxd
    obtain ⟨-, t, -, hmod, hrel⟩ := hx (rmul x b) (G (rmul x b)) hyd (hGrel _)
    have ht1 : ‖t‖ = 1 := hmod (fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_diagonal_minor_one _ hyo τ i)
    refine ⟨t ^ n, by rw [norm_pow, ht1, one_pow], ?_⟩
    rintro ⟨⟨a, f, f₂⟩, hDom, hf, hf₂, hP⟩
    let b₁ : Frame ((T.U j σ).X k).Ψ D.R.r := fun τ => b ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have hb₁ : b₁ ∈ Bor ((T.U j σ).X k).Ψ D.R.r := fun τ => hb ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have e1 := hrel n a hDom f hf f₂ hf₂ hP
    have e2 : rdU C.U₂ f₂ k₂ (rmul x b) = bchar (laU C.U₂ a n k₂) b * rdU C.U₂ f₂ k₂ x :=
      (hU₂.2.2.2.2.1 a n hDom f₂ hf₂ k₂).2.1 x hxd b hb
    have e3 : G (rmul x b) = rmul (G x) b₁ := by
      funext τ
      simp only [G, rmul, b₁, mat]
      exact (Matrix.mul_assoc ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1) (mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩) (mat b ⟨τ.1, (hΨ τ.1).2 τ.2⟩)).symm
    have e4 : rdU (T.U j σ) f k (rmul (G x) b₁) = bchar (laU (T.U j σ) a n k) b₁ * rdU (T.U j σ) f k (G x) :=
      (hU₁.2.2.2.2.1 a n hDom f hf k).2.1 (G x) (hGdom x hxd) b₁ hb₁
    have e5 : bchar (laU C.U₂ a n k₂) b = bchar (laU (T.U j σ) a n k) b₁ := by
      unfold bchar
      refine Fintype.prod_equiv (Equiv.subtypeEquivRight (fun τ => hΨ τ)) _ _ (fun τ => ?_)
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [hla a n τ.1 τ.2 ((hΨ τ.1).1 τ.2) i]
      rfl
    have e6 : bchar (laU C.U₂ a n k₂) b ≠ 0 := by
      unfold bchar
      refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
      have hdet : (mat b τ).det ≠ 0 := (hb τ).1
      rw [Matrix.det_of_upperTriangular (M := mat b τ) (fun a c h => (hb τ).2 a c h)] at hdet
      simpa [mat] using Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
    show rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k (G x)
    apply mul_left_cancel₀ e6
    rw [← e2, e1, e3, e4, ← e5]
    ring
  classical
  let g : Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun x => if h : x ∈ (C.U₂.X k₂).dom then (hg x h).choose else 1
  have hg1 : ∀ x ∈ (C.U₂.X k₂).dom, ‖g x‖ = 1 := fun x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.1
  have hgr : ∀ i, ∀ x ∈ (C.U₂.X k₂).dom, P₂ i x = g x * P i x := fun i x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.2 i
  obtain ⟨u, hu1, hu⟩ := eq_const_mul_of_norm_one (C.U₂.X k₂).dom (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected D.R.r (C.U₂.X k₂)).isPreconnected P₂ P g hP₂d hPd hg1 hgr
  refine ⟨u, hu1, fun x x' hxd hrel' => ⟨(hx x x' hxd hrel').1, ?_⟩⟩
  have hx' : x' = G x := by
    funext τ
    exact hrel' τ.1 ((hΨ τ.1).2 τ.2) τ.2
  intro a hDom f hf f₂ hf₂ hP
  rw [hx']
  exact hu ⟨(a, f, f₂), hDom, hf, hf₂, hP⟩ x hxd

end GlobalTheory.CoverConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeReadAsCosetSums
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.DIV Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeReadRational

section SlopeTestRemainingChoices

open Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem hkC_eq_heckeScalar {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) : hkC R i P k = heckeScalar R i P k := by
  rw [hkC, heckeScalar, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]

theorem heckeOn_mem_wall_of_hkData {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    {i : Fin D.R.m} (hβ' : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb) (hHW : R.models_HW)
    (σ : D.what₂.LL →+* ℂ) {P : Formalism.L2.DIV.Pl D.host.E} {k : ℕ} {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))}
    (hd : IsHkData R i P k α Rc) (z : (R.HW i σ).H) :
    heckeOn (R.MW i σ) Rc ((R.HW i σ).e z) ∈ R.Wall i σ := by
  obtain ⟨hso, -, -, ⟨e, ϖ, he, -, -, hα⟩, hR⟩ := hd
  obtain ⟨c, hβ⟩ := hβ'
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hSb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  have hp : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have hq := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Wc D i)).2.2.1 P e _ hp
  obtain ⟨large₂, hLg⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Wc D i)).1 _ hq.1 hq.2.1).1
  have hK : ∀ g, g ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) ⊓ large₂ ↔ g ∈ locPart (Wc D i) (KsphC (Wc D i) ∅) e := by
    intro g
    have h1 := ((GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places (Wc D i) (R.βW i) _ _ (R.datWp i R.triv) hβ).2 P e _ hp hN hoff).1 g
    exact ⟨fun h => ⟨(h1 ((hLg g).1 h.2)).1 h.1, (hLg g).1 h.2⟩, fun h => ⟨(h1 h.2).2 h.1, (hLg g).2 h.2⟩⟩
  have hoL := GlobalTheory.HeckeModel.offAt_of_place hβ he hN hoff hLg hK
  have hαL : α ∈ large₂ := (hLg α).2 hα.2.1
  obtain ⟨A₀, hA₀⟩ := GlobalTheory.HeckeSup.exists_local_isDC hoL.splits hαL hR
  have key : heckeOn (R.MW i σ) Rc ((R.HW i σ).e z) = heckeOn (R.MW i σ) A₀ ((R.HW i σ).e z) := by
    ext v : 1
    show heckeLin (Wc D i) Rc ((R.HW i σ).e z v) = heckeLin (Wc D i) A₀ ((R.HW i σ).e z v)
    exact funext fun h => GlobalTheory.HeckeModel.sum_eq_of_isDC hR (hoL.splits.isDC hαL hA₀) ⟨1, 1, by simp⟩
      (GlobalTheory.HeckeSup.model_inv_cl hHW i σ z v) h
  rw [key]
  exact GlobalTheory.HeckeModel.heckeOn_mem_mult hoL (fun g hg => hq.2.2.1 g ((hLg g).1 hg)) hαL hA₀
    (show (R.HW i σ).e z ∈ R.Wall i σ from (hHW i σ).2.1 ▸ LinearMap.mem_range_self _ z)

end SlopeTestRemainingChoices

section Main

open Formalism.IndefR.Mult

set_option maxHeartbeats 1600000 in

theorem rationalHecke_of_readsCusp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Formalism.L2.Pj.CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, Formalism.IndefR.FWT.JEvAt T R κ v₀ i (sg0 D A) hV) → Function.Injective ((R.FW i).j (sg0 D A)) → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, GlobalTheory.HeckeSup.ReadsCusp T R κ i (Formalism.IndefR.FWT.res T (sg0 D A)) hV) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R i := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ fw i hT hlev hfam hmod hex _ hR P hP k hk
  have hHW : R.models_HW := hmod.HW
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i :=
    fw.laws.spaceW _ (inR i) _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  obtain ⟨p, m, hp, hpP, -⟩ := GlobalTheory.HeckeSup.exists_prime_under P
  have hoff := GlobalTheory.HeckeSup.not_dvd_level fw.laws hpP hP.2
  have hsp := GlobalTheory.HeckeSup.split_of_ne (H := T.Q.H) hP.1.1
  have hn : (κ i).n = D.R.nV := (fw.kap i (D.eTau.symm 1)).2.2
  have htr : ∀ f : Cu T κ i, ∃ g ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T ((i : ℕ) + 1) P.asIdeal p k
        (hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV) f g := by
    intro f
    obtain ⟨g, hg, hfg⟩ := GlobalTheory.HeckeSup.exists_transform hT GlobalTheory.ThetaTransport.heckePointLaws fw.laws i
      ⟨P.isMaximal, hsp, hp, hpP, hoff⟩ hk ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) (dom_wtA (κ i)) f f.2
    rw [show hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k (κ i).n =
      hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV by rw [hn]] at hfg
    exact ⟨g, hg, hfg⟩
  choose g hg hfg using htr
  have hEI := GlobalTheory.EvalAtUnitVector.evInj T R v₀ hHW fw.hv₀ i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  have hread : ∀ f : Cu T κ i, ∀ Rc, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.IsCosetSys R i P k Rc →
      (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i ⟨g f, hg f⟩ : (R.FW i).WK)) =
        GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc
          ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i f : (R.FW i).WK))) := by
    rintro f Rc ⟨α, hα, hRc⟩
    have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData R i P k α Rc := ⟨hP.1, hP.2, hk, hα, hRc⟩
    have h1 := hR hV P p k α Rc hd ⟨hP.1, hp, hpP, hoff, hk, hα, hRc⟩ f f.2 (g f) (hg f) (hfg f)
    rw [hkC_eq_heckeScalar] at h1
    obtain ⟨z', hz'⟩ : ∃ z', (R.HW i (sg0 D A)).e z' = heckeOn (R.MW i (sg0 D A)) Rc
        ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i f : (R.FW i).WK))) := by
      rw [← LinearMap.mem_range, (hHW i _).2.1]
      exact heckeOn_mem_wall_of_hkData (hlev.βW i) hfam.Sb hHW _ hd _
    have e1 : (R.FW i).j (sg0 D A) (fw.e i ⟨g f, hg f⟩ : (R.FW i).WK) = GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • z' := by
      apply hEI
      refine (GlobalTheory.HeckeSup.baseEmbedding_reading_eval_adelicFunction fw hV (hex hV) ⟨g f, hg f⟩).trans ?_
      funext h
      rw [h1 h, ← GlobalTheory.HeckeSup.baseEmbedding_reading_eval_adelicFunction fw hV (hex hV) f]
      unfold evAt
      rw [map_smul, hz']
      simp [heckeOn, postOn, heckeLin]
      exact Or.inl rfl
    rw [e1, map_smul, hz']
  obtain ⟨n, b, hbK, -, hKspan, hLind, hLspan⟩ := fw.ks i
  let B : Module.Basis (Fin n) D.what₂.LL (Fin (R.nW i) → D.what₂.LL) := Module.Basis.mk hLind hLspan.ge
  have hB : ∀ l, B l = b l := fun l => Module.Basis.mk_apply hLind hLspan.ge l
  let f0 : Fin n → Cu T κ i := fun l => (fw.e i).symm ⟨b l, hbK l⟩
  let yv : Fin n → Fin (R.nW i) → D.what₂.LL := fun l => (fw.e i ⟨g (f0 l), hg (f0 l)⟩ : (R.FW i).WK)
  let hL := B.constr D.what₂.LL yv
  have hLb : ∀ l, hL (b l) = yv l := fun l => by rw [← hB l]; exact B.constr_basis _ _ _
  have hb0 : ∀ l, (fw.e i (f0 l) : Fin (R.nW i) → D.what₂.LL) = b l := fun l => by simp [f0]
  refine ⟨hL, fun Rc hRc => ?_, fun x hx => ?_⟩
  · have hext := B.ext (f₁ := ((R.HW i (sg0 D A)).e.comp ((R.FW i).j (sg0 D A))).comp hL)
      (f₂ := ((GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc).comp (R.HW i (sg0 D A)).e).comp
        ((R.FW i).j (sg0 D A))) fun l => by
      rw [hB l]
      simp only [LinearMap.comp_apply, LinearMap.smul_apply]
      rw [hLb l, ← hb0 l]
      exact hread (f0 l) Rc hRc
    intro x
    have := LinearMap.congr_fun hext x
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using this
  · rw [← hKspan] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [hLb]
      exact (fw.e i _).2
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul D.what₂.LL a x, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ a hx

end Main

end GlobalTheory.HeckeReadRational
end
end

