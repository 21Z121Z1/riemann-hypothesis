import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0038
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0063
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0182
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
import Development.WeilBound.CoreStatements.MeasureExistence.ExistsMeas
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.EqZeroOfFourierCoefficientsVanish
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.FourierComplete

open scoped Pointwise

section Gen

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem exists_descent (Λ : AddSubgroup V) (f : V → ℂ) (hf : Continuous f)
    (hp : ∀ x, ∀ l ∈ Λ, f (x + l) = f x) :
    ∃ h : C(V ⧸ Λ, ℂ), ∀ x, h (QuotientAddGroup.mk x) = f x := by
  let p : C(V, V ⧸ Λ) := ⟨QuotientAddGroup.mk, continuous_quotient_mk'⟩
  have hq : Topology.IsQuotientMap p := QuotientAddGroup.isQuotientMap_mk Λ
  have hfac : Function.FactorsThrough (⟨f, hf⟩ : C(V, ℂ)) p := by
    intro a b hab
    have h1 : -a + b ∈ Λ := QuotientAddGroup.eq.1 hab
    have h2 := hp a _ h1
    simpa using h2.symm
  refine ⟨hq.lift ⟨f, hf⟩ hfac, fun x => ?_⟩
  exact DFunLike.congr_fun (hq.lift_comp ⟨f, hf⟩ hfac) x

theorem compactSpace_quotient (Λ : AddSubgroup V) {K : Set V} (hK : IsCompact K)
    (hc : ∀ x, ∃ l ∈ Λ, x - l ∈ K) : CompactSpace (V ⧸ Λ) := by
  refine ⟨?_⟩
  have himg : (QuotientAddGroup.mk '' K : Set (V ⧸ Λ)) = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨l, hl, hx⟩ := hc x
    refine ⟨x - l, hx, ?_⟩
    rw [QuotientAddGroup.eq]
    have h1 : -(x - l) + x = l := by abel
    rwa [h1]
  rw [← himg]
  exact hK.image continuous_quotient_mk'

theorem mem_closure_span {X : Type*} [TopologicalSpace X] [CompactSpace X] {T : Type*} [AddCommGroup T]
    (c : T → C(X, ℂ)) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hstar : ∀ t, star (c t) = c (-t)) (hsep : ∀ x y, x ≠ y → ∃ t, c t x ≠ c t y) (f : C(X, ℂ)) :
    f ∈ closure ((Submodule.span ℂ (Set.range c) : Submodule ℂ C(X, ℂ)) : Set C(X, ℂ)) := by
  set S : Submodule ℂ C(X, ℂ) := Submodule.span ℂ (Set.range c) with hS
  have hcS : ∀ t, c t ∈ S := fun t => Submodule.subset_span ⟨t, rfl⟩
  have h1 : (1 : C(X, ℂ)) ∈ S := h0 ▸ hcS 0
  have hmul : ∀ x y, x ∈ S → y ∈ S → x * y ∈ S := by
    intro x y hx hy
    have hle : S * S ≤ S := by
      rw [hS, Submodule.span_mul_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
      show c s * c t ∈ _
      rw [← hadd]
      exact hcS _
    exact hle (Submodule.mul_mem_mul hx hy)
  have hst : ∀ x ∈ S, star x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h => obtain ⟨t, rfl⟩ := h; rw [hstar]; exact hcS _
    | zero => simp
    | add x y _ _ hx hy => rw [star_add]; exact S.add_mem hx hy
    | smul a x _ hx => rw [star_smul]; exact S.smul_mem _ hx
  let A : StarSubalgebra ℂ C(X, ℂ) :=
    { toSubalgebra := S.toSubalgebra h1 hmul, star_mem' := fun {a} ha => hst a ha }
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨t, ht⟩ := hsep x y hxy
    exact ⟨c t, ⟨c t, hcS t, rfl⟩, ht⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  have hf : f ∈ (A.topologicalClosure : Set C(X, ℂ)) := by
    rw [htop]
    trivial
  rwa [StarSubalgebra.topologicalClosure_coe] at hf

theorem eq_zero_of_coeffs_vanish [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (Λ : AddSubgroup V) [Countable Λ] (μ : Measure V) [μ.IsAddHaarMeasure] {D : Set V}
    (hD : IsAddFundamentalDomain Λ D μ) {K : Set V} (hK : IsCompact K)
    (hc : ∀ x, ∃ l ∈ Λ, x - l ∈ K) {T : Type*} [AddCommGroup T] (χ : T → V → ℂ)
    (hχc : ∀ t, Continuous (χ t)) (hχp : ∀ t x, ∀ l ∈ Λ, χ t (x + l) = χ t x)
    (h0 : ∀ x, χ 0 x = 1) (hadd : ∀ s t x, χ (s + t) x = χ s x * χ t x)
    (hconj : ∀ t x, star (χ t x) = χ (-t) x)
    (hsep : ∀ x y, (∀ t, χ t x = χ t y) → -x + y ∈ Λ)
    (g : V → ℂ) (hg : Continuous g) (hgp : ∀ x, ∀ l ∈ Λ, g (x + l) = g x)
    (hF : ∀ t, ∫ b in D, g b * χ (-t) b ∂μ = 0) (x : V) : g x = 0 := by
  haveI : CompactSpace (V ⧸ Λ) := compactSpace_quotient Λ hK hc
  choose c hcχ using fun t => exists_descent Λ (χ t) (hχc t) (hχp t)
  obtain ⟨gb, hgb⟩ := exists_descent Λ g hg hgp
  have hext : ∀ a b : C(V ⧸ Λ, ℂ),
      (∀ x : V, a (QuotientAddGroup.mk x) = b (QuotientAddGroup.mk x)) → a = b := by
    intro a b h
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact h x
  have hc0 : c 0 = 1 := hext _ _ fun x => by
    rw [hcχ, h0]; rfl
  have hcadd : ∀ s t, c (s + t) = c s * c t := fun s t => hext _ _ fun x => by
    rw [hcχ, hadd, ContinuousMap.mul_apply, hcχ, hcχ]
  have hcstar : ∀ t, star (c t) = c (-t) := fun t => hext _ _ fun x => by
    rw [ContinuousMap.star_apply, hcχ, hcχ, hconj]
  have hsepc : ∀ p q : V ⧸ Λ, p ≠ q → ∃ t, c t p ≠ c t q := by
    intro p q hpq
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
    by_contra hcon
    push Not at hcon
    apply hpq
    rw [QuotientAddGroup.eq]
    exact hsep a b fun t => by simpa [hcχ] using hcon t
  have hfin : μ D < ⊤ := Formalism.IndefR.Tow.fd_measure_lt_top hD hK (fun y => by
    obtain ⟨l, hl, hy⟩ := hc y
    refine ⟨-l, Λ.neg_mem hl, ?_⟩
    have h1 : -l + y = y - l := by abel
    rwa [h1])
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by simpa using hfin⟩
  let L : C(V ⧸ Λ, ℂ) → ℂ := fun s => ∫ b in D, g b * s (QuotientAddGroup.mk b) ∂μ
  have hbd : ∀ (s : C(V ⧸ Λ, ℂ)) (b : V), ‖g b * s (QuotientAddGroup.mk b)‖ ≤ ‖gb‖ * ‖s‖ := by
    intro s b
    rw [norm_mul, ← hgb b]
    exact mul_le_mul (gb.norm_coe_le_norm _) (s.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  have hint : ∀ s : C(V ⧸ Λ, ℂ),
      Integrable (fun b => g b * s (QuotientAddGroup.mk b)) (μ.restrict D) := by
    intro s
    have hcont : Continuous fun b => g b * s (QuotientAddGroup.mk b) :=
      hg.mul (s.continuous.comp continuous_quotient_mk')
    exact Integrable.of_bound hcont.aestronglyMeasurable (‖gb‖ * ‖s‖) (ae_of_all _ (hbd s))
  have hLc : Continuous L := by
    have hl : LipschitzWith (Real.toNNReal (‖gb‖ * (μ.restrict D).real Set.univ)) L := by
      refine LipschitzWith.of_dist_le' fun s s' => ?_
      rw [dist_eq_norm, dist_eq_norm]
      have h1 : L s - L s' = ∫ b in D, g b * (s - s') (QuotientAddGroup.mk b) ∂μ := by
        show (∫ b in D, _ ∂μ) - (∫ b in D, _ ∂μ) = _
        rw [← integral_sub (hint s) (hint s')]
        refine integral_congr_ae (ae_of_all _ fun b => ?_)
        simp [mul_sub]
      rw [h1]
      have h2 := norm_integral_le_of_norm_le_const (μ := μ.restrict D)
        (ae_of_all _ (hbd (s - s')))
      calc _ ≤ _ := h2
        _ = _ := by ring
    exact hl.continuous
  have hz : ∀ s ∈ Submodule.span ℂ (Set.range c), L s = 0 := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem s h =>
      obtain ⟨t, rfl⟩ := h
      have h1 := hF (-t)
      rw [neg_neg] at h1
      show ∫ b in D, g b * c t (QuotientAddGroup.mk b) ∂μ = 0
      simpa only [hcχ] using h1
    | zero => simp [L]
    | add s s' _ _ hs hs' =>
      have h1 : L (s + s') = L s + L s' := by
        show _ = (∫ b in D, _ ∂μ) + (∫ b in D, _ ∂μ)
        rw [← integral_add (hint s) (hint s')]
        refine integral_congr_ae (ae_of_all _ fun b => ?_)
        simp [mul_add]
      rw [h1, hs, hs', add_zero]
    | smul a s _ hs =>
      have h1 : L (a • s) = a * L s := by
        show _ = a * ∫ b in D, _ ∂μ
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun b => ?_)
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      rw [h1, hs, mul_zero]
  have hL0 : L (star gb) = 0 := by
    have hsub : ((Submodule.span ℂ (Set.range c) : Submodule ℂ C(V ⧸ Λ, ℂ)) : Set C(V ⧸ Λ, ℂ)) ⊆
        {s | L s = 0} := fun s hs => hz s hs
    exact closure_minimal hsub (isClosed_eq hLc continuous_const)
      (mem_closure_span c hc0 hcadd hcstar hsepc (star gb))
  have hpt : ∀ b, g b * (star gb) (QuotientAddGroup.mk b) = ((‖g b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    rw [ContinuousMap.star_apply, hgb]
    simpa using Complex.mul_conj' (g b)
  have hR : ∫ b in D, ‖g b‖ ^ 2 ∂μ = 0 := by
    have h1 : ((∫ b in D, ‖g b‖ ^ 2 ∂μ : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal, ← hL0]
      exact integral_congr_ae (ae_of_all _ fun b => (hpt b).symm)
    exact_mod_cast h1
  have hRint : Integrable (fun b => ‖g b‖ ^ 2) (μ.restrict D) := by
    have hcont : Continuous fun b => ‖g b‖ ^ 2 := hg.norm.pow 2
    refine Integrable.of_bound hcont.aestronglyMeasurable (‖gb‖ ^ 2) (ae_of_all _ fun b => ?_)
    rw [Real.norm_of_nonneg (by positivity), ← hgb b]
    exact pow_le_pow_left₀ (norm_nonneg _) (gb.norm_coe_le_norm _) 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun b => by positivity) hRint).1 hR
  let Z : Set V := {y | g y ≠ 0}
  have hZo : IsOpen Z := isOpen_ne_fun hg continuous_const
  have hZD : μ (Z ∩ D) = 0 := by
    rw [← Measure.restrict_apply hZo.measurableSet]
    refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hae)
    have hy' : g y ≠ 0 := hy
    simpa using hy'
  have hZinv : ∀ l : Λ, l +ᵥ Z = Z := by
    intro l
    ext y
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have h1 : g (-l +ᵥ y) = g y := by
      have h2 := hgp y (-(l : V)) (Λ.neg_mem l.2)
      rw [← h2, add_comm]
      rfl
    show g (-l +ᵥ y) ≠ 0 ↔ g y ≠ 0
    rw [h1]
  have hZ0 := hD.measure_zero_of_invariant Z hZinv hZD
  have hZe : Z = ∅ := (hZo.measure_eq_zero_iff μ).1 hZ0
  by_contra hx
  have hxZ : x ∈ Z := hx
  rw [hZe] at hxZ
  exact hxZ

end Gen

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

end GlobalTheory.CompanionTheory.FourierComplete
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp

open GlobalTheory.Cusp GlobalTheory.Mem.AutSpace

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}

variable (θ V) in

abbrev Mc : Submodule ℂ (GA D V → ℂ) := cuspForms θ V ⊥

theorem mem_Mc_iff {φ : GA D V → ℂ} : φ ∈ Mc θ V ↔ IsAutFunSm θ V φ ∧ IsCuspFun V φ := by
  refine ⟨fun h => (mem_cuspForms.1 h).1, fun h => mem_cuspForms.2 ⟨h, ?_⟩⟩
  refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨Submodule.span ℂ {φ}, inferInstance, fun k hk => ?_⟩
  rw [Subgroup.mem_bot.1 hk]
  exact Submodule.subset_span (by simp [funext_iff])

def der (hθ : IsInfFam θ) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Module.End ℂ (Mc θ V) where
  toFun φ := ⟨Rder θ V τ X φ.1, mem_Mc_iff.2
    ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX (mem_Mc_iff.1 φ.2).1,
      GlobalTheory.CuspLie.isCuspFun_Rder hθ hX (mem_Mc_iff.1 φ.2).1 (mem_Mc_iff.1 φ.2).2⟩⟩
  map_add' f g := Subtype.ext (Rder_add (mem_Mc_iff.1 f.2).1.smooth (mem_Mc_iff.1 g.2).1.smooth hX)
  map_smul' c f := Subtype.ext (Rder_smul c f.1 τ X)

@[simp] theorem der_coe (hθ : IsInfFam θ) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (φ : Mc θ V) : (der hθ τ hX φ : GA D V → ℂ) = Rder θ V τ X φ.1 := rfl

def io (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) : Mc θ V →ₗ[ℂ] L2cusp V μ :=
  cuspToL2 ⊥ μ (GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound) hθ

theorem io_injective (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) :
    Function.Injective (io (V := V) μ hθ) := cusp_form_toL2_injective _ hθ

def derInf (hθ : IsInfFam θ) (X : GlobalTheory.SmoothForms.LieN V) : Module.End ℂ (Mc θ V) :=
  ∑ τ, der hθ τ (X := (X τ).1) (X τ).2

def IsKLie {n : ℕ} (e : Fin n → Bool) (y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  yᴴ = -y ∧ y * Formalism.REAL.Jm e = Formalism.REAL.Jm e * y

end GlobalTheory.CompanionTheory.HCCusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev

variable {D : D7}

def leftSub (V : HSp D) {m : ℕ} (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (S : Finset (Fin m)) : Subgroup (GA D V) :=
  unip D.sp.cm.sig V.gram X S ⊔ (GQ V ⊓ levi D.sp.cm.sig V.gram X Y S)

def formsOn (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {m : ℕ}
    (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (S : Finset (Fin m)) (U : Subgroup (GA D V))
    (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) : Set (GA D V → ℂ) :=
  {φ | IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ ∧ (∀ u ∈ U, u ∈ GfC V → ∀ g, φ (g * u) = φ g) ∧
    (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) ∧ ∀ τ k, gelf θ V τ k φ = c τ k • φ}

section Sub

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {m : ℕ}
  {X Y : Matrix (Fin V.rank) (Fin m) D.host.E} {S : Finset (Fin m)} {U : Subgroup (GA D V)}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
  {ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)} {c : D.what₂.Tau → ℕ → ℂ}

theorem isSmModOn_add {Γ : Set (GA D V)} {f g : GA D V → ℂ} (hf : IsSmModOn D.sp.cm.sig V.gram Γ f)
    (hg : IsSmModOn D.sp.cm.sig V.gram Γ g) : IsSmModOn D.sp.cm.sig V.gram Γ (f + g) := by
  have sf : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram f := hf.smooth
  have sg : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram g := hg.smooth
  refine ⟨fun γ hγ x => ?_, ?_, hf.cont.add hg.cont, GlobalTheory.UAut.isSm_add sf sg, ?_⟩
  · simp only [Pi.add_apply, hf.left γ hγ x, hg.left γ hγ x]
  · obtain ⟨A, hA, eA⟩ := hf.level
    obtain ⟨B, hB, eB⟩ := hg.level
    refine ⟨A ⊓ B, hA.inter hB, fun k hk hk' x => ?_⟩
    simp only [Pi.add_apply, eA k hk.1 hk' x, eB k hk.2 hk' x]
  · obtain ⟨N, hN⟩ := hf.growth
    obtain ⟨M, hM⟩ := hg.growth
    refine ⟨max N M, fun l hl => ?_⟩
    obtain ⟨A, hA⟩ := hN l hl
    obtain ⟨B, hB⟩ := hM l hl
    refine ⟨max A 0 + max B 0, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ (GlobalTheory.AdelicU.height D.sp.cm.sig V.gram x : ℝ) := by
      exact_mod_cast GlobalTheory.AdelicU.one_le_height D.sp.cm.sig V.gram x
    have p1 := pow_le_pow_right₀ h1 (le_max_left N M)
    have p2 := pow_le_pow_right₀ h1 (le_max_right N M)
    have p0 : (0 : ℝ) ≤ (GlobalTheory.AdelicU.height D.sp.cm.sig V.gram x : ℝ) ^ N := by positivity
    have p0' : (0 : ℝ) ≤ (GlobalTheory.AdelicU.height D.sp.cm.sig V.gram x : ℝ) ^ M := by positivity
    rw [GlobalTheory.UAut.foldr_add hl sf sg, Pi.add_apply, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((hA x).trans ?_) ((hB x).trans ?_))
    · exact (mul_le_mul_of_nonneg_right (le_max_left A 0) p0).trans
        (mul_le_mul_of_nonneg_left p1 (le_max_right A 0))
    · exact (mul_le_mul_of_nonneg_right (le_max_left B 0) p0').trans
        (mul_le_mul_of_nonneg_left p2 (le_max_right B 0))

theorem isSmModOn_smul {Γ : Set (GA D V)} (a : ℂ) {f : GA D V → ℂ} (hf : IsSmModOn D.sp.cm.sig V.gram Γ f) :
    IsSmModOn D.sp.cm.sig V.gram Γ (a • f) := by
  have sf : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram f := hf.smooth
  refine ⟨fun γ hγ x => ?_, ?_, hf.cont.const_smul a, GlobalTheory.UAut.isSm_smul a sf, ?_⟩
  · simp only [Pi.smul_apply, hf.left γ hγ x]
  · obtain ⟨A, hA, eA⟩ := hf.level
    exact ⟨A, hA, fun k hk hk' x => by simp only [Pi.smul_apply, eA k hk hk' x]⟩
  · obtain ⟨N, hN⟩ := hf.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨A, hA⟩ := hN l hl
    refine ⟨‖a‖ * A, fun x => ?_⟩
    rw [GlobalTheory.UAut.foldr_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA x) (norm_nonneg _)

theorem formsOn_add (hθ : IsInfFam θ) {f g : GA D V → ℂ} (hf : f ∈ formsOn θ V X Y S U ε fr ρ c)
    (hg : g ∈ formsOn θ V X Y S U ε fr ρ c) : f + g ∈ formsOn θ V X Y S U ε fr ρ c := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  obtain ⟨g1, g2, g3, g4⟩ := hg
  refine ⟨isSmModOn_add f1 g1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩
  · simp only [Pi.add_apply, f2 u hu hu' x, g2 u hu hu' x]
  · exact (coeffSpan (ρ τ)).add_mem (f3 τ x) (g3 τ x)
  · rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).add f (GlobalTheory.SphSmooth.mem_smFun_of_isSm hθ f1.smooth) g
      (GlobalTheory.SphSmooth.mem_smFun_of_isSm hθ g1.smooth), f4, g4, smul_add]

theorem formsOn_smul (a : ℂ) {f : GA D V → ℂ} (hf : f ∈ formsOn θ V X Y S U ε fr ρ c) :
    a • f ∈ formsOn θ V X Y S U ε fr ρ c := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  refine ⟨isSmModOn_smul a f1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩
  · simp only [Pi.smul_apply, f2 u hu hu' x]
  · exact (coeffSpan (ρ τ)).smul_mem a (f3 τ x)
  · rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul, f4, smul_comm]

theorem zero_mem_formsOn : (0 : GA D V → ℂ) ∈ formsOn θ V X Y S U ε fr ρ c := by
  refine ⟨isSmModOn_const _ _ _ 0, fun _ _ _ _ => rfl, fun τ x => (coeffSpan (ρ τ)).zero_mem, fun τ k => ?_⟩
  have := (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul 0 0
  simpa using this

theorem const_mem_formsOn (a : ℂ) :
    (fun _ => a) ∈ formsOn θ V X Y S U ε fr (fun τ => Representation.trivial ℂ (Formalism.REAL.KG (ε τ)) ℂ) (fun _ _ => 0) :=
  have h := const_mem_forms (θ := θ) (V := V) U ε fr a
  ⟨isSmModOn_const _ _ _ a, h.2.1, h.2.2.1, h.2.2.2⟩

theorem mem_formsOn_of_mem_span (hθ : IsInfFam θ) {f : GA D V → ℂ}
    (hf : f ∈ Submodule.span ℂ (formsOn θ V X Y S U ε fr ρ c)) : f ∈ formsOn θ V X Y S U ε fr ρ c := by
  induction hf using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact zero_mem_formsOn
  | add x y _ _ hx hy => exact formsOn_add hθ hx hy
  | smul a x _ hx => exact formsOn_smul a hx

end Sub

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicBlockEmbeddingCompact
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Glob.MinParLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_block_of_triangular {n r s : ℕ} (X : Matrix (Fin n) (Fin r) E) (S : Finset (Fin r)) (hs : s ≤ r)
    {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular id) (e : M * adMat F X = adMat F X * B) :
    ∃ B' : Matrix (Fin s) (Fin s) (AF F ⊗[F] E),
      (B'.BlockTriangular fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) ∧
      M * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B' := by
  refine ⟨B.submatrix (Fin.castLE hs) (Fin.castLE hs), fun i j hij => ?_, Matrix.ext fun x j => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_notMem_of_card_lt_card hij
    have hk1 := Finset.mem_filter.1 hk
    have h2 : k.val < i.val := by simpa [Fin.lt_def] using hk1.2
    have h1 : j.val ≤ k.val := by
      by_contra hc
      exact hk' (Finset.mem_filter.2 ⟨hk1.1, Fin.lt_def.2 (by simpa using not_le.1 hc)⟩)
    exact hB (show Fin.castLE hs j < Fin.castLE hs i from Fin.lt_def.2 (by simp only [Fin.val_castLE]; omega))
  · have e1 := congrFun (congrFun e x) (Fin.castLE hs j)
    have l1 : (M * adMat F (X.submatrix id (Fin.castLE hs))) x j =
        (M * adMat F X) x (Fin.castLE hs j) := rfl
    rw [l1, e1, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs) _ _ (fun i hi => ?_) fun i => rfl
    have hi' : s ≤ i.val := by
      by_contra hc
      exact hi ⟨⟨i.val, not_le.1 hc⟩, rfl⟩
    have hz : B i (Fin.castLE hs j) = 0 :=
      hB (show Fin.castLE hs j < i by rw [Fin.lt_def]; simp only [Fin.val_castLE]; omega)
    rw [hz, mul_zero]

theorem minPar_eq_unip_mul_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)), ∀ p ∈ PositivityTheory.ThKR.minPar σ J X, ∃ u ∈ GlobalTheory.StdPar.unip σ J X S, ∃ l ∈ GlobalTheory.StdPar.levi σ J X Y S, p = u * l := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S p hp
  obtain ⟨s, hs, hS⟩ : ∃ s, ∃ hs : s ≤ r, ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k := by
    refine ⟨S.sup fun k => k.val + 1, Finset.sup_le fun k _ => k.2, fun i => ?_⟩
    rw [Finset.lt_sup_iff]
    exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S s hs hS
    (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) fun _ => rfl
  have hp' : p ∈ parFlag σ J (X.submatrix id (Fin.castLE hs))
      (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) := by
    obtain ⟨B, hB, e⟩ := hp
    obtain ⟨B', hB', e'⟩ := PositivityTheory.ThKR.inv_mem_minPar h hJ hW (show p ∈ PositivityTheory.ThKR.minPar σ J X from ⟨B, hB, e⟩)
    exact ⟨exists_block_of_triangular X S hs hB e, exists_block_of_triangular X S hs hB' e'⟩
  obtain ⟨u, hu', m, hm, e, -⟩ := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ s (X.submatrix id (Fin.castLE hs))
    (Y.submatrix id (Fin.castLE hs)) (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).1 p hp'
  exact ⟨u, hu ▸ hu', m, hl ▸ hm, e⟩

end GlobalTheory.CompanionTheory.Glob.MinParLevi
end
end

