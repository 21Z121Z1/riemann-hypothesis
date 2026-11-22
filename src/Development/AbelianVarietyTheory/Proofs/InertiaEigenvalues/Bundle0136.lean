import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0122
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0123
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountProdOfIdempotentSeparable
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0005
import GroundTheory.LocalFields.UnramifiedNormSurj
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportMixedModelPartial
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

theorem psi_isLocallyConstant {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    IsLocallyConstant (fun x => ψ x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
  have h1 : ψ (y - x) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hy).le)
  calc ψ y = ψ (x + (y - x)) := by rw [add_sub_cancel]
    _ = ψ x := by rw [AddChar.map_add_eq_mul, h1, mul_one]

theorem isOpen_setOf_eq_of_isLocallyConstant {Y : Type} [TopologicalSpace Y] {g h : Y → ℂ}
    (hg : IsLocallyConstant g) (hh : IsLocallyConstant h) : IsOpen {p | g p = h p} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  filter_upwards [(IsLocallyConstant.iff_eventually_eq g).1 hg p,
    (IsLocallyConstant.iff_eventually_eq h).1 hh p] with q h1 h2
  show g q = h q
  rw [h1, h2]; exact hp

theorem isTest_partialFourier {X F : Type} [TopologicalSpace X] [T2Space X] [NontriviallyNormedField F]
    [ProperSpace F] {r : ℕ} [MeasurableSpace (Fin r → F)] (μ : Measure (Fin r → F))
    (hμ : ∀ (g : (Fin r → F) → ℂ) (w : Fin r → F), ∫ b, g (b + w) ∂μ = ∫ b, g b ∂μ)
    (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (f : X × (Fin r → F) → ℂ) (hf : IsTest f) :
    IsTest (fun p : X × (Fin r → F) => ∫ b, f (p.1, b) * ψ (b ⬝ᵥ p.2) ∂μ) := by
  obtain ⟨hfl, hfc⟩ := hf
  have hK : IsCompact (tsupport f) := hfc
  have hψl := psi_isLocallyConstant ψ hψ

  have hn1 : IsOpen {q : (X × (Fin r → F)) × (Fin r → F) | f (q.1.1, q.1.2 + q.2) = f q.1} :=
    isOpen_setOf_eq_of_isLocallyConstant (hfl.comp_continuous (by fun_prop))
      (hfl.comp_continuous continuous_fst)
  obtain ⟨u1, v1, -, hv1, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := (0 : Fin r → F))) hn1 (by
      rintro ⟨p, w⟩ ⟨-, hw⟩
      simp only [Set.mem_singleton_iff] at hw
      subst hw
      simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hv1 0 (h0v rfl)
  have inv1 : ∀ x b (w : Fin r → F), ‖w‖ < δ → f (x, b + w) = f (x, b) := by
    intro x b w hw
    have hwv : w ∈ v1 := hball (by simpa using hw)
    by_cases hxb : (x, b) ∈ tsupport f
    · exact huv (⟨hKu hxb, hwv⟩ : ((x, b), w) ∈ u1 ×ˢ v1)
    · by_cases hxbw : (x, b + w) ∈ tsupport f
      · have hmw : -w ∈ v1 := hball (by simpa using hw)
        have := huv (⟨hKu hxbw, hmw⟩ : ((x, b + w), -w) ∈ u1 ×ˢ v1)
        simp only [Set.mem_setOf_eq, add_neg_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hxb, image_eq_zero_of_notMem_tsupport hxbw]
  have hzero : ∀ x b, b ∉ Prod.snd '' tsupport f → f (x, b) = 0 := fun x b hb =>
    image_eq_zero_of_notMem_tsupport (fun h => hb ⟨_, h, rfl⟩)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨x0, u0⟩
    have hdot : Continuous fun q : (X × (Fin r → F)) × (Fin r → F) => q.2 ⬝ᵥ q.1.2 := by
      unfold dotProduct; fun_prop
    have hdot0 : Continuous fun q : (X × (Fin r → F)) × (Fin r → F) => q.2 ⬝ᵥ u0 := by
      unfold dotProduct; fun_prop
    have hn2 : IsOpen {q : (X × (Fin r → F)) × (Fin r → F) |
        f (q.1.1, q.2) * ψ (q.2 ⬝ᵥ q.1.2) = f (x0, q.2) * ψ (q.2 ⬝ᵥ u0)} :=
      isOpen_setOf_eq_of_isLocallyConstant
        ((hfl.comp_continuous (by fun_prop)).comp₂ (hψl.comp_continuous hdot) (· * ·))
        ((hfl.comp_continuous (by fun_prop)).comp₂ (hψl.comp_continuous hdot0) (· * ·))
    obtain ⟨u2, v2, hu2, -, hxu, hKv, hu2n⟩ :=
      generalized_tube_lemma (isCompact_singleton (x := (x0, u0))) (hK.image continuous_snd) hn2 (by
        rintro ⟨p, b⟩ ⟨hp, -⟩
        simp only [Set.mem_singleton_iff] at hp
        subst hp
        simp)
    filter_upwards [hu2.mem_nhds (hxu rfl)] with p hp
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    by_cases hb : b ∈ Prod.snd '' tsupport f
    · exact hu2n (⟨hp, hKv hb⟩ : (p, b) ∈ u2 ×ˢ v2)
    · simp only [hzero _ _ hb, zero_mul]
  · obtain ⟨a, ha, -⟩ := hψ.2
    refine HasCompactSupport.intro
      ((hK.image continuous_fst).prod (isCompact_closedBall (0 : Fin r → F) (‖a‖ / δ))) ?_
    rintro ⟨x, u⟩ hxu
    rw [Set.mem_prod, not_and_or] at hxu
    rcases hxu with hx | hu
    · have h0 : ∀ b, f (x, b) = 0 := fun b =>
        image_eq_zero_of_notMem_tsupport (fun h => hx ⟨_, h, rfl⟩)
      simp [h0]
    · rw [mem_closedBall_zero_iff, not_le] at hu
      obtain ⟨i, hi⟩ : ∃ i, ‖a‖ / δ < ‖u i‖ := by
        by_contra h
        push_neg at h
        exact (not_le.2 hu) ((pi_norm_le_iff_of_nonneg (by positivity)).2 h)
      have hui : u i ≠ 0 := by
        intro h
        rw [h, norm_zero] at hi
        exact (not_lt.2 (by positivity)) hi
      classical
      have hw : ‖(Pi.single i (a / u i) : Fin r → F)‖ < δ := by
        rw [Pi.norm_single, norm_div, div_lt_iff₀ (norm_pos_iff.2 hui)]
        rw [div_lt_iff₀ hδ] at hi
        linarith
      have hwu : (Pi.single i (a / u i) : Fin r → F) ⬝ᵥ u = a := by
        rw [single_dotProduct]; field_simp
      have key := hμ (fun b => f (x, b) * ψ (b ⬝ᵥ u)) (Pi.single i (a / u i))
      have hsh : ∀ b, f (x, b + Pi.single i (a / u i)) * ψ ((b + Pi.single i (a / u i)) ⬝ᵥ u) =
          (f (x, b) * ψ (b ⬝ᵥ u)) * ψ a := by
        intro b
        rw [inv1 x b _ hw, add_dotProduct, AddChar.map_add_eq_mul, hwu]
        ring
      simp only [hsh, integral_mul_const] at key
      show ∫ b, f (x, b) * ψ (b ⬝ᵥ u) ∂μ = 0
      by_contra hI
      exact ha (mul_left_cancel₀ hI (key.trans (mul_one _).symm))

end GlobalTheory.JR.WeilMix

namespace GlobalTheory.JR.WeilMix

theorem ptrB_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ,
    IsTest f → IsTest (WeilMix.ptrB M ψ f) := by
  intro F E _ _ _ _ hU r M ψ hψ f hf
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let eH : Gl r F ≃ₜ (Matrix (Fin r) (Fin r) F × (Fin r → F) × F) × (Fin r → F) :=
    { toFun := fun Y => ((Y.1, Y.2.2.1, Y.2.2.2), Y.2.1)
      invFun := fun p => (p.1.1, p.2, p.1.2.1, p.1.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hμ : ∀ (g : (Fin r → F) → ℂ) (w : Fin r → F),
      ∫ b, g (b + w) ∂(Measure.pi fun _ : Fin r => M.μF) = ∫ b, g b ∂(Measure.pi fun _ : Fin r => M.μF) :=
    fun g w => integral_add_right_eq_self g w
  have hg : IsTest (f ∘ eH.symm) := ⟨hf.1.comp_continuous eH.symm.continuous, hf.2.comp_homeomorph eH.symm⟩
  have h1 := isTest_partialFourier (Measure.pi fun _ : Fin r => M.μF) hμ ψ hψ (f ∘ eH.symm) hg
  exact ⟨h1.1.comp_continuous eH.continuous, h1.2.comp_homeomorph eH⟩

end GlobalTheory.JR.WeilMix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitTraceFormDiscrUnramifiedExtStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_traceForm_discr_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (π : K.O) (π' : K'.O), algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) → IsLocalRing.maximalIdeal K.O = Ideal.span {π} → IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} → letI : Algebra K.E K'.E := φ.toAlgebra; ∀ w : Module.Basis (Fin d) K.E K'.E, (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) → ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u = (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)).det := by
  first | exact @GlobalTheory.UnitLemma.Unr.ResDisc.discr_trace_isUnit | exact GlobalTheory.UnitLemma.Unr.ResDisc.discr_trace_isUnit | (intros; apply GlobalTheory.UnitLemma.Unr.ResDisc.discr_trace_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnitStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → Function.Bijective (fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a)) ∧ ∀ a : A.K, (∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a)) ∧ (Delta (A.invK τ p lam a) ≠ 0 ↔ IsUnit a) := by
  first | exact @GlobalTheory.JR.EtInv.invK_regular_iff_isUnit | exact GlobalTheory.JR.EtInv.invK_regular_iff_isUnit | (intros; apply GlobalTheory.JR.EtInv.invK_regular_iff_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KrasnerLemmaDecompositionGroupStabilizerVersionStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krasnerLemma_decompositionGroup_stabilizer_version : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (β β' : Ω), (∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) → ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by
  first | exact @GlobalTheory.krasner_stabiliser | exact GlobalTheory.krasner_stabiliser | (intros; apply GlobalTheory.krasner_stabiliser <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountAndGramDetSignNormClassStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCount_and_gramDetSign_norm_class : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (u : B.Aˣ), B.N (x * (u * B.σ (u : B.A))) = B.N x ∧ K.eta (B.gramDet (x * (u * B.σ (u : B.A)))) = K.eta (B.gramDet x) := by
  first | exact @GlobalTheory.UnitLemma.NormClass.N_norm_class | exact GlobalTheory.UnitLemma.NormClass.N_norm_class | (intros; apply GlobalTheory.UnitLemma.NormClass.N_norm_class <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountProdOfIdempotentSeparableStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCount_prod_of_idempotent_separable : ∀ (K : UQ) (B₁ B₂ : InvAlg K), ((1, 0) : B₁.A × B₂.A) ∈ Algebra.adjoin K.O ({(B₁.g, B₂.g)} : Set (B₁.A × B₂.A)) → (B₁.P * B₂.P).Separable → ∀ (x₁ : B₁.A) (x₂ : B₂.A), IsUnit x₁ → IsUnit x₂ → B₁.σ x₁ = x₁ → B₂.σ x₂ = x₂ → (B₁.prod B₂).N (x₁, x₂) = B₁.N x₁ * B₂.N x₂ := by
  first | exact @GlobalTheory.UnitLemma.ProdCount.N_prod | exact GlobalTheory.UnitLemma.ProdCount.N_prod | (intros; apply GlobalTheory.UnitLemma.ProdCount.N_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LetterSandwichOfFrobMatrices
section
noncomputable section

namespace GlobalTheory.WachLettersCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

attribute [local instance] letterModule

theorem mul_letE (i : ZMod n) (a : LetA O n) : a * letE i = Pi.single i (a i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  rw [mul_letE]; simp [letE]

theorem mem_Nl_iff (i : ZMod n) (x : W.DD T) :
    x ∈ W.Nl T i ↔ x ∈ W.N T ∧ (letE i : LetA O n) • x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(W.N T).smul_mem _ hy, ?_⟩
    change (letE i : LetA O n) • ((letE i : LetA O n) • y) = (letE i : LetA O n) • y
    rw [smul_smul, letE_mul_self]
  · rintro ⟨hx, he⟩
    exact ⟨x, hx, he⟩

theorem letE_smul_mem (i : ZMod n) {x : W.DD T} (hx : x ∈ W.N T) :
    (letE i : LetA O n) • x ∈ W.Nl T i := ⟨x, hx, rfl⟩

theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

theorem γD_smulA (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem γA_letE (g : W.Gam) (i : ZMod n) : W.γA g (letE i) = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [LocWach.γA, letγ, letE]
  · simp [LocWach.γA, letγ, letE, h]

include W in

theorem neZero_letters : NeZero n := by
  have := PD.finK₀
  exact ⟨by rw [W.n_eq]; exact Module.finrank_pos.ne'⟩

theorem isUnit_Q : IsUnit (algebraMap (LetA O n) W.EE W.Q) := by
  have hq : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
    have h1 : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
      funext i
      simpa [letπ, LocWach.q] using W.q₀_def
    set x := algebraMap (LetA O n) W.EE letπ with hx
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq PD.hp (1 : W.EE) x
    obtain ⟨u, hu⟩ : IsUnit (x ^ PD.p) := W.EE_π.pow _
    have := W.EE_complete
    have hj : ((PD.p : ℕ) : W.EE) ∈ Ideal.jacobson (⊥ : Ideal W.EE) :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
        (Ideal.mem_span_singleton_self _)
    have h2 := (Ideal.mem_jacobson_bot.1 hj) (x * r * (↑u⁻¹ : W.EE))
    have h3 : x * algebraMap (LetA O n) W.EE W.q =
        (((PD.p : ℕ) : W.EE) * (x * r * (↑u⁻¹ : W.EE)) + 1) * u := by
      rw [hx, ← map_mul, h1, map_sub, map_pow, map_add, map_one, ← hx, hr, ← hu]
      have := u.inv_mul
      linear_combination (-((PD.p : ℕ) : W.EE) * x * r) * this
    exact isUnit_of_mul_isUnit_right (h3 ▸ h2.mul u.isUnit)
  have key : ∀ k : ℕ, IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) W.q)) := by
    intro k
    induction k with
    | zero => simpa using hq
    | succ k ih =>
      rw [pow_succ', AlgHom.mul_apply]
      have := W.φE_ext ((W.φA ^ k) W.q)
      exact this ▸ ih.map W.φE
  exact key _

theorem Q_pow_smul_cancel (m : ℕ) {x y : W.DD T} (h : W.Q ^ m • x = W.Q ^ m • y) : x = y := by
  rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE (W.Q ^ m) y, map_pow] at h
  exact ((isUnit_Q W).pow m).smul_left_cancel.1 h

variable {W T}

theorem φD_fixed (i : ZMod n) {x : W.DD T} (hx : x ∈ W.Nl T (i - 1)) :
    (letE i : LetA O n) • W.φD T x = W.φD T x := by
  rw [← phi_letE W i, ← φD_smulA, ((mem_Nl_iff W T _ x).1 hx).2]

theorem letE_smul_φpull (i : ZMod n) {y : W.DD T} (hy : y ∈ W.φpull T) :
    (letE i : LetA O n) • y ∈ phiPullLetter W T i := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [← phi_letE W i, ← φD_smulA]
    exact Submodule.subset_span ⟨_, letE_smul_mem W T _ hz, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

variable (W T)

end Generic

end GlobalTheory.WachLettersCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierLinear
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

theorem integrable_mixedModel_partialFourier_integrand {F : Type} [NontriviallyNormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] {r : ℕ} (μ : Measure F) [μ.IsAddHaarMeasure]
    (ψ : AddChar F ℂ) (hψ : IsLocallyConstant (fun x => ψ x))
    (f : Gl r F → ℂ) (hf : IsTest f) (Y : Gl r F) :
    Integrable (fun b : Fin r → F => f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1))
      (Measure.pi fun _ : Fin r => μ) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hc : Continuous (fun b : Fin r → F => f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1)) := by
    refine Continuous.mul ?_ ?_
    · exact hf.1.continuous.comp (by fun_prop)
    · exact hψ.continuous.comp (by fun_prop)
  refine hc.integrable_of_hasCompactSupport ?_
  have hK : IsCompact ((fun Z : Gl r F => Z.2.1) '' tsupport f) := hf.2.isCompact.image (by fun_prop)
  refine HasCompactSupport.intro hK ?_
  intro b hb
  have : (Y.1, b, Y.2.2.1, Y.2.2.2) ∉ tsupport f := fun h => hb ⟨_, h, rfl⟩
  simp [image_eq_zero_of_notMem_tsupport this]

end GlobalTheory.JR.WeilMix

theorem GlobalTheory.JR.WeilMix.ptrB_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by
  intro F E _ _ _ _ hU r M ψ hψ c f f' hf hf'
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  have hlc : IsLocallyConstant (fun x => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1
  funext Y
  have h1 := WeilMix.integrable_mixedModel_partialFourier_integrand M.μF ψ hlc f hf Y
  have h2 := WeilMix.integrable_mixedModel_partialFourier_integrand M.μF ψ hlc f' hf' Y
  simp only [WeilMix.ptrB, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
  rw [integral_add (h1.const_mul c) h2, integral_const_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelWeylElementEqPartialFourier
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.negB (WeilMix.ptrB M ψ (WeilMix.rowAct (wS F) (WeilMix.ptrB M ψ f))) = fourG M ψ f := by
  intro F E _ _ _ _ hU r M ψ hψ f hf
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hψc : Continuous (fun x => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1.continuous
  funext Y
  obtain ⟨A, b, c, l⟩ := Y
  have hw : ((wS F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl
  simp only [WeilMix.negB, WeilMix.ptrB, WeilMix.rowAct, WeilMix.rowMap, fourG, hw]
  simp
  set μ : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hμ
  haveI : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  set G : (Fin r → F) → ℂ := fun x => (∫ b', f (A, b', x, l) * ψ (b' ⬝ᵥ c) ∂μ) * ψ (x ⬝ᵥ b) with hG
  set H : (Fin r → F) → (Fin r → F) → ℂ := fun x b' => f (A, b', x, l) * ψ (b' ⬝ᵥ c) * ψ (x ⬝ᵥ b) with hH
  have hHc : Continuous (Function.uncurry H) := by
    have h1 : Continuous (fun p : (Fin r → F) × (Fin r → F) => f (A, p.2, p.1, l)) :=
      hf.1.continuous.comp (by fun_prop)
    have h2 : Continuous (fun p : (Fin r → F) × (Fin r → F) => ψ (p.2 ⬝ᵥ c)) :=
      hψc.comp (continuous_snd.dotProduct continuous_const)
    have h3 : Continuous (fun p : (Fin r → F) × (Fin r → F) => ψ (p.1 ⬝ᵥ b)) :=
      hψc.comp (continuous_fst.dotProduct continuous_const)
    exact (h1.mul h2).mul h3
  have hHs : HasCompactSupport (Function.uncurry H) := by
    refine HasCompactSupport.intro ((hf.2.isCompact).image
      (show Continuous (fun Y : Gl r F => (Y.2.2.1, Y.2.1)) by fun_prop)) ?_
    intro p hp
    by_contra hne
    apply hp
    refine ⟨(A, p.2, p.1, l), subset_tsupport _ ?_, rfl⟩
    intro h0
    apply hne
    simp [Function.uncurry, H, h0]
  have hint : Integrable (Function.uncurry H) (μ.prod μ) := hHc.integrable_of_hasCompactSupport hHs
  calc _ = ∫ x, G (-x) ∂μ := by
        congr 1; funext x; simp only [G, neg_dotProduct, neg_neg]; rfl
    _ = ∫ x, G x ∂μ := integral_neg_eq_self G μ
    _ = ∫ x, ∫ b', H x b' ∂μ ∂μ := by
        congr 1; funext x; simp only [G, H]; rw [integral_mul_const]
    _ = ∫ b', ∫ x, H x b' ∂μ ∂μ := integral_integral_swap hint
    _ = _ := by
        congr 1; funext b'; congr 1; funext x
        simp only [H]
        rw [mul_assoc, ← AddChar.map_add_eq_mul, dotProduct_comm b' c, add_comm]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NegOneMemNormOfValuationEq
section
open ValuativeRel

namespace GlobalTheory

open GroundTheory.LocalField in

theorem neg_one_mem_norm_of_valuation_eq : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E], (∀ y : E, ∃ x : F, y ≤ᵥ algebraMap F E x ∧ algebraMap F E x ≤ᵥ y) → ∃ z : E, Algebra.norm F z = -1 := by
  intro F E _ _ _ _ _ _ _ _ _ _ _ hval
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨x, h1, h2⟩ := hval (ϖ : E)
  have hv : valuation E (ϖ : E) = valuation E (algebraMap F E x) :=
    le_antisymm ((Valuation.Compatible.vle_iff_le _ _).1 h1) ((Valuation.Compatible.vle_iff_le _ _).1 h2)
  have hord : ord (ϖ : E) = ord (algebraMap F E x) := by
    simp only [ord]
    rw [(normalizedValuation_eq_iff (K := E)).2 hv]
  rw [ord_uniformizer hϖ, ord_algebraMap] at hord
  have he : ramificationIndex F E = 1 := by
    have hd : ((ramificationIndex F E : ℕ) : ℤ) ∣ 1 := ⟨ord x, hord⟩
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd
  haveI : IsUnramified F E := (isUnramified_iff F E).2 he
  obtain ⟨w, hw⟩ := normIntegerUnits_surjective (K := F) (L := E) (-1)
  refine ⟨((w : 𝒪[E]) : E), ?_⟩
  have := congrArg (fun u : 𝒪[F]ˣ => ((u : 𝒪[F]) : F)) hw
  simp only [coe_normIntegerUnits_eq] at this
  rw [← coe_norm_integer]
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem _root_.GlobalTheory.Cyc.norm_natCast_prime_padicComplex (l : ℕ) [Fact l.Prime] :
    ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := by
  have h1 := PadicComplex.norm_extends l (algebraMap ℚ_[l] (PadicAlgCl l) l)
  rw [PadicAlgCl.norm_extends, Padic.norm_p, map_natCast] at h1
  rw [← h1]
  norm_cast

theorem _root_.GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot {K : Type*} [NormedField K]
    [IsUltrametricDist K]
    {n : ℕ} (hn : n ≠ 0) {ζ μ : K} (hζ : IsPrimitiveRoot ζ n) (hμ : μ ^ n = 1) :
    ‖μ - 1‖ ≤ ‖ζ - 1‖ := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  have hnorm : ‖ζ‖ = 1 := by
    have h := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hn).mp h
  clear hμ
  induction k with
  | zero => simp
  | succ k ih =>
    have : ζ ^ (k + 1) - 1 = ζ ^ k * (ζ - 1) + (ζ ^ k - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
    rw [norm_mul, norm_pow, hnorm, one_pow, one_mul]

theorem _root_.GlobalTheory.Cyc.norm_primitiveRoot_sub_one (l : ℕ) [hl : Fact l.Prime] (j : ℕ)
    (hj : 1 ≤ j) (ζ : PadicComplex l) (hζ : IsPrimitiveRoot ζ (l ^ j)) :
    ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  have hpos : 0 < l ^ j := pow_pos hl.out.pos j
  have hall : ∀ μ ∈ primitiveRoots (l ^ j) (PadicComplex l), ‖1 - μ‖ = ‖ζ - 1‖ := by
    intro μ hμ
    rw [mem_primitiveRoots hpos] at hμ
    rw [norm_sub_rev]
    exact le_antisymm
      (_root_.GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot hpos.ne' hζ hμ.pow_eq_one)
      (_root_.GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot hpos.ne' hμ hζ.pow_eq_one)
  have heval :=
    congrArg (Polynomial.eval 1) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Polynomial.eval_one_cyclotomic_prime_pow, Polynomial.eval_prod] at heval
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heval
  have hprod := congrArg norm heval
  rw [_root_.GlobalTheory.Cyc.norm_natCast_prime_padicComplex, norm_prod, Finset.prod_congr rfl hall, Finset.prod_const,
    hζ.card_primitiveRoots, Nat.totient_prime_pow hl.out (Nat.succ_pos k)] at hprod
  simp only [Nat.succ_sub_one, Nat.add_sub_cancel] at hprod ⊢
  have hN : l ^ k * (l - 1) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ hl.out.ne_zero) (Nat.sub_ne_zero_of_lt hl.out.one_lt)
  have hcast : ((l ^ k * (l - 1) : ℕ) : ℝ) = (l : ℝ) ^ k * ((l : ℝ) - 1) := by
    push_cast [Nat.cast_sub hl.out.one_le]
    ring
  rw [← Real.pow_rpow_inv_natCast (norm_nonneg (ζ - 1)) hN, ← hprod, hcast,
    Real.inv_rpow (Nat.cast_nonneg l), ← Real.rpow_neg (Nat.cast_nonneg l), neg_div, one_div]

end GlobalTheory.Cyc
end

