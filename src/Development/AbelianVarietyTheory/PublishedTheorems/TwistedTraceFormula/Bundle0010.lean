import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CharacterRegularityFiniteLength
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

def CharacterRegularityFiniteLength : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h : IsAdmRep ε π), HasFiniteLength ε π →
    ∃ Θ, IsGlobalChar μ (groupRep ε h.1) Θ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacterSUTrivialTwo
section
noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep repVia CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open GlobalTheory.DSSU (SUJ SUset IsParS IsHCS)
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.SUChar

variable {n : ℕ}

def suMat (ε : Fin n → Bool) : SUJ ε →* Matrix (Fin n) (Fin n) ℂ := (ujMat ε).comp (SUJ ε).subtype

theorem suMat_mem (ε : Fin n → Bool) (g : SUJ ε) : suMat ε g ∈ SUset ε := ⟨g.1.2, g.2⟩

def suRep {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
    {ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)} (h : IsURepOn (SUset ε) ρ) : SUJ ε →* (X →L[ℂ] X) :=
  repVia h (suMat ε) (suMat_mem ε)

def suTorusPt (ε : Fin n → Bool) (θ : Fin n → ℝ) (hθ : ∑ a, θ a = 0) : SUJ ε :=
  ⟨torusPt ε θ, by
    change (ujMat ε (torusPt ε θ)).det = 1
    rw [ujMat_torusPt, det_diagonal, ← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum, hθ]
    simp⟩

theorem suMat_suTorusPt (ε : Fin n → Bool) (θ : Fin n → ℝ) (hθ : ∑ a, θ a = 0) :
    suMat ε (suTorusPt ε θ hθ) = diagonal fun a => Complex.exp (θ a * Complex.I) := rfl

theorem isInducing_suMat (ε : Fin n → Bool) : Topology.IsInducing (GlobalTheory.Orb.matCoord (suMat ε)) :=
  (isInducing_matCoord (ε := ε)).comp Topology.IsInducing.subtypeVal

def chamberDenom (lam θ : Fin n → ℝ) : ℂ :=
  ∏ a, ∏ b ∈ Finset.univ.filter (fun b => lam b < lam a), (Complex.exp (((θ a - θ b) / 2 : ℝ) * Complex.I) -
    Complex.exp ((-((θ a - θ b) / 2) : ℝ) * Complex.I))

def chamberChar (ε : Fin n → Bool) (lam θ : Fin n → ℝ) : ℂ :=
  (-1) ^ halfDim ε * (∑ w ∈ compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * wtVal (lam ∘ w.symm) θ) / chamberDenom lam θ

theorem chamberDenom_of_strictAnti {lam : Fin n → ℝ} (h : StrictAnti lam) (θ : Fin n → ℝ) :
    chamberDenom lam θ = weylDenom θ := by
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr ?_ fun _ _ => rfl
  ext b
  simp [h.lt_iff_gt]

theorem chamberChar_of_strictAnti (ε : Fin n → Bool) {lam : Fin n → ℝ} (h : StrictAnti lam) (θ : Fin n → ℝ) :
    chamberChar ε lam θ = dsChar ε lam θ := by
  rw [chamberChar, chamberDenom_of_strictAnti h, dsChar]

end GlobalTheory.SUChar

namespace GlobalTheory.Published

open GlobalTheory.SUChar

def DiscreteSeriesCharacterSU : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (ε : Fin n → Bool) (μ : Measure (SUJ ε)) [μ.IsHaarMeasure] (lam : Fin n → ℝ), IsParS lam →
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h : IsHCS ε lam σ) (Θ : SUJ ε → ℂ),
      IsCharFn (suMat ε) μ (suRep h.1.2.2.1) Θ ∧
        ∀ (θ : Fin n → ℝ) (hθ : ∑ a, θ a = 0), IsRegSS (suMat ε (suTorusPt ε θ hθ)) →
          Θ (suTorusPt ε θ hθ) = chamberChar ε lam θ

def DiscreteSeriesCharacterOfParameter : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h : IsSqIntIrr ε σ),
      (∃ S : Submodule ℂ V, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S) ∧
      (∀ (ν : Fin n → ℝ) (S : Submodule ℂ V), IsKTypeOf ε σ ν S → ∃ c : Fin n → Fin n → ℕ,
        (∀ a b, c a b ≠ 0 → a < b) ∧ ν = Formalism.QuantumDeterminants.lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b) ∧
      ∃ Θ, IsCharFn (ujMat ε) μ (ujRep h.2.2.1) Θ ∧
        ∀ θ : Fin n → ℝ, IsRegSS (ujMat ε (torusPt ε θ)) → Θ (torusPt ε θ) = dsChar ε lam θ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace
open scoped ENNReal NNReal Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

def CuspDecaySobolev : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ N M : ℕ,
      ∃ (d : ℕ) (C : ℝ≥0), ∀ φ : GA D V → ℂ, IsAutFun V φ → (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) →
        φ ∈ SmFun θ V → (∀ k, growthSob θ V k N φ ≠ ∞) → IsCuspFun V φ →
          decaySize V M φ ≤ C * growthSob θ V d N φ

def UnitaryReduction : Prop :=
  ∀ (D : D7) (V : HSp D),
    (∃ A : ℕ, ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
      IntegrableOn (fun g => (quotHeight V g ^ A)⁻¹) 𝓕 μ) ∧
    ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) →
      ∃ S : Finset (GA D V), (∀ x ∈ S, x ∈ GfC V) ∧
        ∀ g, ∃ γ ∈ GQ V, ∃ x ∈ S, ∃ a ∈ GinfC V, ∃ k ∈ U, k ∈ GfC V ∧ g = γ * x * a * k

end GlobalTheory.Published

namespace GlobalTheory.Size

variable {D : D7} {θ : InfFam D} {V : HSp D} {φ : GA D V → ℂ}

theorem integrableOn_inv_quotHeight_pow (A : ℕ) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) : IntegrableOn (fun g => (quotHeight V g ^ A)⁻¹) 𝓕 μ := by
  refine Measure.integrableOn_of_bounded (M := 1)
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
    (((continuous_quotHeight V).pow A).inv₀ fun g => (pow_pos (quotHeight_pos V g) A).ne').aestronglyMeasurable
    (.of_forall fun g => ?_)
  rw [Real.norm_of_nonneg (inv_pos.2 (pow_pos (quotHeight_pos V g) A)).le]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_quotHeight V g))

theorem exists_finset_doubleCosets (V : HSp D) (U : Subgroup (GA D V)) (hU : IsOpen (U : Set (GA D V))) :
    ∃ S : Finset (GA D V), (∀ x ∈ S, x ∈ GfC V) ∧
      ∀ g, ∃ γ ∈ GQ V, ∃ x ∈ S, ∃ a ∈ GinfC V, ∃ k ∈ U, k ∈ GfC V ∧ g = γ * x * a * k := by
  classical
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain ⟨S, _, _, hS⟩ := GlobalTheory.SmoothForms.reduction hθ R U hU
  choose p hp q hq e using R.2.2.2.2.2.2.1
  refine ⟨S.image p, fun x hx => ?_, fun g => ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hp y
  · obtain ⟨γ, hγ, x, hx, a, ha, k, hk, hk', h, -⟩ := hS g
    refine ⟨γ⁻¹, inv_mem hγ, p x, Finset.mem_image_of_mem p hx, q x * a, mul_mem (hq x) ha, k, hk, hk', ?_⟩
    rw [mul_assoc γ⁻¹, mul_assoc γ⁻¹, ← mul_assoc (p x), ← e x, ← h, inv_mul_cancel_left]

theorem _root_.GlobalTheory.Published.unitaryReduction_holds : GlobalTheory.Published.UnitaryReduction := fun _ V =>
  ⟨⟨0, fun _ _ => integrableOn_inv_quotHeight_pow 0⟩, exists_finset_doubleCosets V⟩

theorem exists_growthSob_ne_top_of_isAutFunSm (hθ : IsInfFam θ) (h : IsAutFunSm θ V φ) :
    UnifModGrowth V θ φ ∧ ∃ N, ∀ d, growthSob θ V d N φ ≠ ∞ :=
  ⟨unifModGrowth_of_isAutFunSm hθ h, exists_growthSob_ne_top h.smooth (unifModGrowth_of_isAutFunSm hθ h)⟩

theorem growthSize_sum_le {T : (GA D V → ℂ) → GA D V → ℂ} (hT : LinOnSm θ V T) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    {f : ι → GA D V → ℂ} (hf : ∀ a, f a ∈ SmFun θ V) (N : ℕ) :
    growthSize V N (T (∑ a ∈ s, c a • f a)) ≤ ∑ a ∈ s, ‖c a‖ₑ * growthSize V N (T (f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hT.smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [Finset.sum_empty, Finset.sum_empty, this]
    exact ((growthSize_const (0 : ℂ)).trans enorm_zero).le
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hT.add _ (Submodule.smul_mem _ _ (hf a)) _
      (sum_mem fun b _ => Submodule.smul_mem _ _ (hf b)), hT.smul, ← growthSize_smul]
    exact growthSize_add_le.trans (add_le_add le_rfl ih)

theorem exists_growthSize_rWord_le (hθ : IsInfFam θ)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : IsLieWord V l) :
    ∃ c : ℝ≥0, ∀ φ ∈ SmFun θ V, ∀ (N d : ℕ) (l' : List (D.what₂.Tau × Fin V.rank × Fin V.rank)),
      l'.length + l.length ≤ d →
        growthSize V N (wordAct (glDer θ V) l' (rWord θ V l φ)) ≤ c * growthSob θ V d N φ := by
  induction l with
  | nil => exact ⟨1, fun φ _ N d l' hd => by
      rw [ENNReal.coe_one, one_mul]
      exact le_wordSum (p := growthSize V N) (l := l') hd φ⟩
  | cons p l ih =>
    have hl' : IsLieWord V l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨c, hc⟩ := ih hl'
    refine ⟨(∑ a : Fin V.rank × Fin V.rank, ‖p.2 a.1 a.2‖₊) * c, fun φ hs N d l' hd => ?_⟩
    have hm := (linOnSm_rWord hl').mem φ hs
    have e : rWord θ V (p :: l) φ = Rder θ V p.1 p.2 (rWord θ V l φ) := rfl
    rw [e, Rder_eq_sum_glDer hθ hm (hl p List.mem_cons_self)]
    refine (growthSize_sum_le (linOnSm_glWord l') _ _ (fun a => (linOnSm_RderC p.1 _).mem _ hm) N).trans ?_
    rw [ENNReal.coe_mul, ENNReal.coe_finset_sum, mul_assoc, Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl ?_
    have := hc φ hs N d (l' ++ [(p.1, a)])
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hd ⊢; omega)
    rwa [wordAct_append] at this

theorem cuspDecaySobolev_of_bound (hP : GlobalTheory.Published.CuspDecayBound) : GlobalTheory.Published.CuspDecaySobolev := by
  intro D θ hθ V U hU N M
  obtain ⟨L, C, hL, h⟩ := hP D θ hθ V U hU N M
  choose! c hc using fun l hl => exists_growthSize_rWord_le (V := V) hθ l hl
  refine ⟨L.sup List.length, C.toNNReal * ∑ l ∈ L, c l, fun φ ha hk hs hg hcu => ?_⟩
  lift growthSob θ V (L.sup List.length) N φ to ℝ≥0 using hg _ with s hs'
  have h1 := h φ ha hk hs (fun l hl => modGrowthExp_iff.2 (growthSize_rWord_ne_top hθ hs hg l hl)) hcu
    (fun l => (c l * s : ℝ≥0)) fun l hl => (growthSize_le_iff (NNReal.coe_nonneg _)).1 (by
      rw [ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul, hs']
      exact hc l (hL l hl) φ hs N _ [] (by simpa using Finset.le_sup (f := List.length) hl))
  rw [← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal]
  refine (decaySize_le_iff (NNReal.coe_nonneg _)).2 fun g => (h1 g).trans ?_
  rw [← NNReal.coe_sum, ← Finset.sum_mul, mul_assoc, NNReal.coe_mul C.toNNReal]
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (NNReal.coe_nonneg _)

theorem rapidDec_of_cuspDecaySobolev (hP : GlobalTheory.Published.CuspDecaySobolev) (hθ : IsInfFam θ) (ha : IsAutFun V φ)
    (hs : φ ∈ SmFun θ V) (hg : UnifModGrowth V θ φ) (hc : IsCuspFun V φ) : RapidDec V φ := by
  obtain ⟨U, hU, hk⟩ := ha.level
  obtain ⟨N, hN⟩ := exists_growthSob_ne_top hs hg
  refine rapidDec_iff_decaySize.2 ⟨ha.left, ha.cont, fun M => ?_⟩
  obtain ⟨d, C, h⟩ := hP D θ hθ V U hU N M
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (hN d)) (h φ ha hk hs hN hc)

theorem continuous_Rder_of_growth (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (hc : Continuous φ) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {A : ℕ}
    (hg : ModGrowthExp V A (Rder θ V τ X (Rder θ V τ X φ))) : Continuous (Rder θ V τ X φ) := by
  obtain ⟨B, hB⟩ := hg
  have hB0 := nonneg_of_growth hB
  obtain ⟨c, hc'⟩ := exists_height_le_of_isCompact V
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image (GlobalTheory.Mem.Lift.continuous_oneP hθ hX))
  have key : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ g, ‖Rder θ V τ X φ g - h⁻¹ • (φ (g * oneP θ V τ X h) - φ g)‖ ≤
      B * (height V g * c) ^ A * h := fun h h0 h1 g => by
    set q := h⁻¹ • (φ (g * oneP θ V τ X h) - φ g) with hq
    have d1 := GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder hs hX) g
    have d2 := GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder (Rder_mem hs hX) hX) g
    have := GlobalTheory.CuspDecay.mul_norm_deriv_le (f := fun t => φ (g * oneP θ V τ X t) - φ g - t • q)
      (f₁ := fun t => Rder θ V τ X φ (g * oneP θ V τ X t) - q)
      (fun t => by simpa using ((d1 t).sub_const (φ g)).fun_sub ((hasDerivAt_id t).smul_const q))
      (fun t => (d2 t).sub_const q) h0.le (B := B * (height V g * c) ^ A) fun t ht => (hB _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le ((height_mul_le V _ _).trans
          (mul_le_mul_of_nonneg_left (hc' _ ⟨t, ⟨ht.1, ht.2.trans h1⟩, rfl⟩) (height_pos V g).le)) A) hB0)
    rw [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one, hq, smul_inv_smul₀ h0.ne', sub_self, sub_self, zero_smul, sub_self,
      norm_zero, zero_add, zero_add, mul_comm _ h] at this
    exact le_of_mul_le_mul_left this h0
  refine continuous_of_locally_uniform_approx_of_continuousAt fun x u hu => ?_
  obtain ⟨ε, hε, hu⟩ := Metric.mem_uniformity_dist.1 hu
  have hb : Continuous fun g => B * (height V g * c) ^ A :=
    continuous_const.mul (((continuous_height V).mul continuous_const).pow A)
  obtain ⟨h, h0, h1, h2⟩ : ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ B * (height V x * c) ^ A * h < ε := by
    have : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h ≤ 1 ∧ B * (height V x * c) ^ A * h < ε :=
      eventually_mem_nhdsWithin.and (Filter.Eventually.filter_mono nhdsWithin_le_nhds
        ((eventually_le_nhds zero_lt_one).and
          ((continuous_const.mul continuous_id).continuousAt.eventually_lt continuousAt_const (by simpa using hε))))
    exact this.exists
  refine ⟨_, (isOpen_lt (hb.mul (continuous_const (y := h))) (continuous_const (y := ε))).mem_nhds h2,
    fun g => h⁻¹ • (φ (g * oneP θ V τ X h) - φ g),
    (((hc.comp (continuous_mul_const _)).sub hc).const_smul h⁻¹).continuousAt, fun y hy => hu ?_⟩
  rw [dist_eq_norm]
  exact (key h h0 h1 y).trans_lt hy

theorem continuous_rWord (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (hc : Continuous φ) (hg : UnifModGrowth V θ φ)
    {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)} (hl : IsLieWord V l) : Continuous (rWord θ V l φ) := by
  obtain ⟨A, hA⟩ := hg
  induction l with
  | nil => exact hc
  | cons p l ih =>
    have hl' : IsLieWord V l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    exact continuous_Rder_of_growth hθ ((linOnSm_rWord hl').mem φ hs) (ih hl') (hl p List.mem_cons_self)
      (hA (p :: p :: l) fun q hq => (List.mem_cons.1 hq).elim (fun e => e ▸ hl p List.mem_cons_self) (hl q))

theorem rWord_left {γ : GA D V} (h : ∀ g, φ (γ * g) = φ g)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) : ∀ g, rWord θ V l φ (γ * g) = rWord θ V l φ g := by
  induction l with
  | nil => exact h
  | cons p l ih =>
    intro g
    change Rder θ V p.1 p.2 (rWord θ V l φ) _ = Rder θ V p.1 p.2 (rWord θ V l φ) _
    simp only [Rder, mul_assoc, ih]

theorem rapidDecSm_of_unifModGrowth (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (ha : IsAutFun V φ)
    (hs : φ ∈ SmFun θ V) (hg : UnifModGrowth V θ φ) (hc : IsCuspFun V φ) : RapidDecSm θ V φ :=
  ⟨ha, hs, fun l hl => (rapidDec_iff_isRapidDecay hθ).2 ⟨fun γ hγ => rWord_left (ha.left γ hγ) l,
    continuous_rWord hθ hs ha.cont hg hl,
    GlobalTheory.CuspDecay.isRapidDecay_foldr_Rder hP hθ ha hs (hg.growth hθ) hc l hl⟩⟩

theorem rapidDecSm_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (h : IsAutFunSm θ V φ)
    (hc : IsCuspFun V φ) : RapidDecSm θ V φ :=
  rapidDecSm_of_unifModGrowth hP hθ h.toIsAutFun h.smooth (unifModGrowth_of_isAutFunSm hθ h) hc

end GlobalTheory.Size

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InducedAdmissibleFiniteLength
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

def InducedAdmissibleFiniteLength : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a),
    IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] [Nontrivial V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (mats (leviOne ε W)) σ → IsIrredOn (mats (leviOne ε W)) σ →
      ∀ (s : Fin a → ℂ) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
        (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (ι : indFun (ε := ε) ⊤ j W σ s →ₗ[ℂ] X),
        IsIndModel ⊤ (KG ε) (muK ε) _ ρ ι →
        IsAdmRep ε ρ ∧ HasFiniteLength ε ρ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InducedCharacterVanishing
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

def InducedCharacterVanishing : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (a : ℕ) (j : Fin a → ℕ) (W : Flag n a),
    IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] [Nontrivial V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (mats (leviOne ε W)) σ → IsIrredOn (mats (leviOne ε W)) σ →
      ∀ (s : Fin a → ℂ) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
        (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (ι : indFun (ε := ε) ⊤ j W σ s →ₗ[ℂ] X),
        IsIndModel ⊤ (KG ε) (muK ε) _ ρ ι →
        ∀ h : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ, ∃ Θ, IsCharFn (ujMat ε) μ (groupRep ε h) Θ ∧
          ∀ g, IsRegSS (ujMat ε g) → (∀ x, x * g * x⁻¹ ∉ flagM ε W) → Θ g = 0

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
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

def IrreducibleUnitaryAdmissible : Prop :=
  ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), GlobalTheory.LinRed.IsLinRed G →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn G σ → IsIrredOn G σ → GlobalTheory.LinRed.IsAdmOn G σ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteCoefficientsAnalytic
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

def KFiniteCoefficientsAnalytic : Prop :=
  ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), GlobalTheory.LinRed.IsLinRed G →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), GlobalTheory.LinRed.IsAdmOn G π →
      ∀ v w : H, GlobalTheory.LinRed.IsKFinOn G π v → GlobalTheory.LinRed.AnalyticOnGroup G fun g => ⟪w, π g v⟫_ℂ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteVectorsSmooth
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

def KFiniteVectorsSmooth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε π → IsGKSub ε π (kFinVec ε π)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.OppositeCellIntegration
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

def OppositeCellIntegration : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∀ ν' : Measure (UJ ε), IsHaarSub (flagN ε (opp ε W)) ν' → ∃ c : ℝ, 0 < c ∧
      ∀ φ ∈ indFun ⊤ j W (fun _ => (1 : ℂ →L[ℂ] ℂ)) (rho n j),
        Integrable φ ν' ∧ ∫ k : KG ε, φ k ∂muK ε = c * ∫ u, φ u ∂ν'

end GlobalTheory.Published

end
end

