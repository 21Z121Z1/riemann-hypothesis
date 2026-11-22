import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentationIff
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published
open GlobalTheory.Parabolic (isIrreducible_of_equiv)

namespace GlobalTheory.SegmentRepModel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def Concl {d : ℕ} (σ : Representation ℂ (GL (Fin d) k) V) (l : ℕ) : Prop :=
  ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
    S.toRepresentation.IsIrreducible ∧
    (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
      S'.toRepresentation.IsIrreducible → S' = S) ∧
    Nonempty ((jac (consecBlocks l d) S.toRepresentation).Equiv (piTensor (segTerm σ l)))

theorem segmentRepresentation_iff : SegmentRepresentation ↔
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (d l : ℕ), 0 < d → 0 < l → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ → Concl σ.ρ l := Iff.rfl

def jacCongr {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (φ : π.Equiv τ) : (jac e π).Equiv (jac e τ) :=
  equivOfBijective (jacMap e φ.toIntertwiningMap) (Function.bijective_iff_has_inverse.2
    ⟨jacMap e φ.symm.toIntertwiningMap,
      fun y => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact congrArg Submodule.Quotient.mk (φ.symm_apply_apply v),
      fun y => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact congrArg Submodule.Quotient.mk (φ.apply_symm_apply v)⟩)

theorem concl_of_isSocle {d l : ℕ} {σ : Representation ℂ (GL (Fin d) k) V}
    {τ : Representation ℂ (GL (Fin (l * d)) k) W}
    (h : IsSocle τ (multiProd (consecBlocks l d) (segTerm σ l)))
    (hj : Nonempty ((jac (consecBlocks l d) τ).Equiv (piTensor (segTerm σ l)))) : Concl σ l := by
  obtain ⟨hi, f, hf, hS⟩ := h
  have inc : ∀ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
      ∃ g : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ l)),
        Function.Injective g ∧ g.range = S := fun S =>
    ⟨⟨S.toSubmodule.subtype, fun _ => rfl⟩, Subtype.val_injective,
      Subrepresentation.toSubmodule_injective (Submodule.range_subtype _)⟩
  obtain ⟨g, hg, hr⟩ := inc f.range
  obtain ⟨φ⟩ := nonempty_equiv_of_range_eq f hf g hg hr.symm
  obtain ⟨ψ⟩ := hj
  refine ⟨f.range, isIrreducible_of_equiv φ hi, fun S' hS' => ?_, ⟨(jacCongr _ φ.symm).trans ψ⟩⟩
  obtain ⟨g', hg', hr'⟩ := inc S'
  exact hS _ (hr' ▸ isAtom_range hS' g' hg')

theorem concl_two {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) : Concl (detRep (Fin 1) χ) 2 := by
  classical
  have he : consecBlocks 2 1 = (ProjLine.pts : (Σ _ : Fin 2, Fin 1) ≃ Fin (2 * 1)) := by
    ext ⟨a, j⟩
    rw [consecBlocks_val, ProjLine.pts_apply]
    omega
  have hη : IsSmoothChar (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)) := hχ.mul (isSmoothChar_absPow _)
  obtain ⟨ψ⟩ := nonempty_jac_det_equiv (consecBlocks 2 1) χ
  refine concl_of_isSocle (τ := detRep (Fin (2 * 1)) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))) ?_ ⟨ψ⟩
  obtain ⟨X, _, _, π, f, ⟨φ⟩, hf, h0, h, -⟩ := ProjLine.exists_line hη
  let a : (ofChar (detLevi (consecBlocks 2 1) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)))).Equiv
      (jac (consecBlocks 2 1) (detRep (Fin (2 * 1)) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)))) :=
    .mk (Submodule.quotEquivOfEqBot _ (twKer_detRep _ _)).symm fun g => LinearMap.ext fun c => by
      simp only [LinearMap.comp_apply]
      rw [Model.jac_detRep, ofChar_apply]
      exact map_smul _ (_ : ℂ) c
  have b := parIndEquiv (consecBlocks 2 1) (a.trans ψ)
  have φ' : π.Equiv (parInd (consecBlocks 2 1)
      (ofChar (detLevi (consecBlocks 2 1) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))))) := by
    rw [he]; exact φ
  exact (ProjLine.isSocle_of_le (isIrreducible_ofChar _) f hf h0 h).of_equiv (.refl _) (φ'.trans b)

theorem single_block {d N : ℕ} (hN : N = d) (e : (Σ _ : Fin 1, Fin d) ≃ Fin N) (he : ∀ a i, (e ⟨a, i⟩ : ℕ) = i)
    {π : Representation ℂ (GL (Fin d) k) V} (hπ : IsSmooth π) (hi : π.IsIrreducible) :
    (multiProd e fun _ : Fin 1 => π).IsIrreducible ∧
      Nonempty ((jac e (multiProd e fun _ : Fin 1 => π)).Equiv (piTensor fun _ : Fin 1 => π)) := by
  subst hN
  have he' : ∀ a i, e ⟨a, i⟩ = i := fun a i => Fin.ext (he a i)
  obtain ⟨φ⟩ := nonempty_equiv_multiProd_one hπ e he'
  refine ⟨isIrreducible_of_equiv φ hi, ⟨(jacCongr e φ.symm).trans ?_⟩⟩
  have hU : twKer π (unipRad k e) 1 = ⊥ := by
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨u, v, rfl⟩
    have : (u : GL (Fin N) k) = 1 := by
      ext i j
      have := (mem_unipRad.1 u.2).2 0 i j
      rwa [he', he'] at this
    simp [this]
  let L := (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) 0).symm
  have hL : ∀ v, L v = PiTensorProduct.tprod ℂ fun _ => v := fun v => by
    rw [LinearEquiv.symm_apply_eq]
    simp
  refine .mk ((Submodule.quotEquivOfEqBot _ hU).trans L) fun g => Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  have hd : deltaHalf k (fun _ : Fin 1 => Fin N) g = 1 := by
    simp [deltaHalf_apply, modExp, Finset.filter_singleton]
  have hg : leviEmb k e g = g 0 := by
    ext i j
    have := leviEmb_apply_same k e g 0 i j
    rwa [he', he'] at this
  show L ((((deltaHalf k (fun _ : Fin 1 => Fin N) g)⁻¹ : ℂˣ) : ℂ) • π (leviEmb k e g) v) =
    piTensor (fun _ : Fin 1 => π) g (L v)
  rw [hd, hg, hL, hL, piTensor_tprod]
  congr 1
  funext a
  rw [Subsingleton.elim a 0]
  simp

theorem concl_one {d : ℕ} (σ : IrrRep (GL (Fin d) k)) : Concl σ.ρ 1 := by
  have h0 : segTerm σ.ρ 1 = fun _ => σ.ρ := funext fun a => by
    have : detChar (Fin d) (absPow k (((a : ℕ) : ℂ))) = 1 := by
      ext g; simp [Subsingleton.elim a 0]
    rw [segTerm, this, twist_one]
  obtain ⟨h1, h2⟩ := single_block (one_mul d) (consecBlocks 1 d)
    (fun a i => by rw [consecBlocks_val]; simp) σ.smooth σ.irr
  refine concl_of_isSocle (τ := multiProd (consecBlocks 1 d) fun _ : Fin 1 => σ.ρ) ?_ ?_
  · rw [h0]; exact isSocle_self h1
  · rw [h0]; exact h2

example {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsCuspidal (IrrRep.det (Fin 1) χ hχ).ρ ∧ Concl (IrrRep.det (Fin 1) χ hχ).ρ 2 :=
  ⟨isCuspidal_detRep_one hχ, concl_two hχ⟩

example (p : ℕ) [Fact p.Prime] : Concl (detRep (Fin 1) (1 : ℚ_[p]ˣ →* ℂˣ)) 2 := concl_two isSmoothChar_one

end GlobalTheory.SegmentRepModel

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
section
noncomputable section

open scoped TensorProduct ContDiff
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.Grow in

def CuspDecayBound : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ A N : ℕ,
      ∃ (L : Finset (List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ),
        (∀ l ∈ L, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧
        ∀ φ : GA D V → ℂ, IsAutFun V φ → (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) →
          (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
            (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
              ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) →
          (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
            ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ)) →
          IsCuspFun V φ →
          ∀ c : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) → ℝ,
            (∀ l ∈ L, ∀ g, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) g‖ ≤ c l * height V g ^ A) →
            ∀ g, ‖φ g‖ * quotHeight V g ^ N ≤ C * ∑ l ∈ L, c l

end GlobalTheory.Published

namespace GlobalTheory.Grow

open GlobalTheory.SmoothForms
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (IsUnifModerate IsSmoothInf)

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem quotHeight_comparison (hθ : IsInfFam θ) (V : HSp D) : ∃ C : ℝ, 0 < C ∧ ∀ g : GA D V,
    (GlobalTheory.CuspDecay.quotHeight θ V g : ℝ) ≤ C * quotHeight V g ∧
      quotHeight V g ≤ C * (GlobalTheory.CuspDecay.quotHeight θ V g : ℝ) := by
  obtain ⟨C, hC, h⟩ := height_comparison V hθ
  refine ⟨C * 2, by positivity, fun g => ⟨?_, ?_⟩⟩
  · obtain ⟨γ, hγ, h2⟩ := exists_height_le_two_mul_quotHeight V g
    rw [mul_assoc]
    exact (NNReal.coe_le_coe.2 (GlobalTheory.CuspDecay.quotHeight_le g hγ)).trans
      ((h _).1.trans (mul_le_mul_of_nonneg_left h2 hC.le))
  · obtain ⟨γ, hγ, h2⟩ := GlobalTheory.CuspDecay.exists_height_le (θ := θ) g
    rw [mul_assoc]
    exact (quotHeight_le V g hγ).trans ((h _).2.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast h2) hC.le))

theorem rapidDec_iff_isRapidDecay (hθ : IsInfFam θ) {φ : GA D V → ℂ} :
    RapidDec V φ ↔ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ Continuous φ ∧ GlobalTheory.CuspDecay.IsRapidDecay θ V φ := by
  obtain ⟨K, hK, h⟩ := quotHeight_comparison hθ V
  have key : ∀ {a b x C : ℝ} {N : ℕ}, 0 ≤ a → 0 ≤ x → a ≤ K * b → x * b ^ N ≤ C → x * a ^ N ≤ K ^ N * C :=
    fun {a b x C N} ha hx h1 h2 => (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha h1 N) hx).trans (by
      rw [mul_pow, mul_left_comm]; exact mul_le_mul_of_nonneg_left h2 (pow_pos hK N).le)
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun N => ⟨?_, ?_⟩
  · rintro ⟨C, hC⟩
    exact ⟨_, fun g => key (NNReal.coe_nonneg _) (norm_nonneg _) (h g).1 (hC g)⟩
  · rintro ⟨C, hC⟩
    exact ⟨_, fun g => key (quotHeight_pos V g).le (norm_nonneg _) (h g).2 (hC g)⟩

theorem unifModGrowth_of_isUnifModerate (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsUnifModerate θ V (expInf θ V) φ) : UnifModGrowth V θ φ := by
  obtain ⟨K, hK, hh⟩ := height_comparison V hθ
  obtain ⟨A, hA⟩ := h
  have key : ∀ ψ : GA D V → ℂ, (∃ C : ℝ, ∀ g, ‖ψ g‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^ A) →
      ModGrowthExp V A ψ := by
    rintro ψ ⟨C, hC⟩
    refine ⟨|C| * K ^ A, fun g => (hC g).trans ?_⟩
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hh g).1 A)
      (pow_nonneg (NNReal.coe_nonneg _) A) (abs_nonneg _)
  refine ⟨A, fun l hl => key _ ?_⟩
  obtain ⟨l', hl'⟩ := exists_sigma_list l hl
  rw [hl', foldr_Rder_eq ((GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V)]
  exact hA _

theorem unifModGrowth_of_isAutFunSm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) :
    UnifModGrowth V θ φ :=
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  unifModGrowth_of_isUnifModerate hθ ((growth_iff hθ R h.toIsAutFun ((smooth_iff R φ).1 h.smooth)).1 h.growth)

theorem cuspRapidDecay_of_bound (hP : GlobalTheory.Published.CuspDecayBound) : GlobalTheory.Published.CuspRapidDecay := by
  intro D θ hθ V e he φ ha hs hg hc
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain rfl := eq_expInf R he
  obtain ⟨A, hA⟩ := unifModGrowth_of_isUnifModerate hθ hg
  obtain ⟨U, hU, hφ⟩ := ha.level
  refine ((rapidDec_iff_isRapidDecay hθ).1 ⟨ha.left, ha.cont, fun N => ?_⟩).2.2
  obtain ⟨L, C, hL, h⟩ := hP D θ hθ V U hU A N
  choose! c hc' using hA
  exact ⟨_, h φ ha hφ ((smooth_iff R φ).2 hs) (fun l hl => ⟨c l, hc' l hl⟩) hc c fun l hl => hc' l (hL l hl)⟩

theorem rapidDec_of_unifModGrowth (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hg : UnifModGrowth V θ φ) (hc : IsCuspFun V φ) : RapidDec V φ :=
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hs' := (smooth_iff R φ).1 hs
  (rapidDec_iff_isRapidDecay hθ).2 ⟨ha.left, ha.cont,
    hP D θ hθ V _ (isExpFam_expInf R) φ ha hs' ((growth_iff hθ R ha hs').1 (hg.growth hθ)) hc⟩

theorem rapidDec_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : RapidDec V φ :=
  rapidDec_of_unifModGrowth hP hθ h.toIsAutFun h.smooth (unifModGrowth_of_isAutFunSm hθ h) hc

theorem RapidDec.integrableOn_fundamentalDomain {Φ : GA D V → ℂ} (h : RapidDec V Φ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) : IntegrableOn Φ 𝓕 μ :=
  h.integrableOn (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne

theorem RapidDec.integrableOn_mul_of_le {f Φ : GA D V → ℂ} (h : RapidDec V Φ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hm : AEStronglyMeasurable f (μ.restrict 𝓕)) {C : ℝ} {A : ℕ} (hf : ∀ g, ‖f g‖ ≤ C * quotHeight V g ^ A) :
    IntegrableOn (f * Φ) 𝓕 μ := by
  obtain ⟨B, hB⟩ := h.decay A
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  refine Integrable.of_bound (hm.mul h.continuous.aestronglyMeasurable) (|C| * B) (.of_forall fun g => ?_)
  have hq := (pow_pos (quotHeight_pos V g) A).le
  calc ‖(f * Φ) g‖ = ‖f g‖ * ‖Φ g‖ := norm_mul _ _
    _ ≤ |C| * quotHeight V g ^ A * ‖Φ g‖ :=
        mul_le_mul_of_nonneg_right ((hf g).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hq)) (norm_nonneg _)
    _ = |C| * (‖Φ g‖ * quotHeight V g ^ A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB g) (abs_nonneg C)

theorem RapidDec.integrableOn_modGrowth_mul {f Φ : GA D V → ℂ} (h : RapidDec V Φ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hf : ModGrowth V f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (hm : AEStronglyMeasurable f (μ.restrict 𝓕)) :
    IntegrableOn (f * Φ) 𝓕 μ := by
  obtain ⟨C, A, hC⟩ := hf
  exact h.integrableOn_mul_of_le hμ h𝓕 hm (norm_le_quotHeight_pow hl hC)

end GlobalTheory.Grow

end
end

