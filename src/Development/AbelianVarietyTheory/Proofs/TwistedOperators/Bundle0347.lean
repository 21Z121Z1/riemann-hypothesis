import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0022
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0329

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMulEndomorphismIsotypicRep
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.IsoTrace

theorem intertwining_sum_apply {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
    {π : Representation ℂ G N} {ρ : Representation ℂ G X} {ι : Type} (t : Finset ι)
    (c : ι → ℂ) (φ : ι → π.IntertwiningMap ρ) (n : N) : (∑ j ∈ t, c j • φ j) n = ∑ j ∈ t, c j • φ j n := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => simp [Finset.sum_insert ha, ih]

theorem trace_mul_isotypic : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible → (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) → IsIsotypicAlg π ρ → ∀ H : X →ₗ[ℂ] X, (∀ g x, H (ρ g x) = ρ g (H x)) → (∃ s : Finset (π.IntertwiningMap ρ), LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) → ∃ c : ℂ, ∀ (A : N →ₗ[ℂ] N) (B : X →ₗ[ℂ] X), (∀ φ : π.IntertwiningMap ρ, B ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ A) → ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (H ∘ₗ B) (c * b) := by
  intro G _ N X _ _ _ _ π ρ hirr hschur hiso H hH ⟨s, hs⟩
  let S := Submodule.span ℂ (s : Set (π.IntertwiningMap ρ))
  haveI : FiniteDimensional ℂ S := FiniteDimensional.span_finset ℂ s
  let bS := Module.finBasis ℂ S
  let φ : Fin (Module.finrank ℂ S) → π.IntertwiningMap ρ := fun j => (bS j : π.IntertwiningMap ρ)
  have hli : LinearIndependent ℂ φ := bS.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hinj := GlobalTheory.T.injective_sum_of_linIndep_intertwiners G N X π ρ hirr hschur _ φ hli
  have hY : LinearMap.range H ≤ ⨆ j, LinearMap.range (φ j).toLinearMap := by
    refine hs.trans (iSup₂_le fun ψ hψ => ?_)
    have hψS : ψ ∈ S := Submodule.subset_span hψ
    have e : ψ = ∑ j, bS.repr ⟨ψ, hψS⟩ j • φ j := by
      have := congrArg Subtype.val (bS.sum_repr ⟨ψ, hψS⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rintro _ ⟨n, rfl⟩
    have hn : ψ n = ∑ j, bS.repr ⟨ψ, hψS⟩ j • φ j n := by
      rw [← intertwining_sum_apply, ← e]
    change ψ n ∈ _
    rw [hn]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem j ⟨n, rfl⟩)
  have hcoef : ∀ ψ : π.IntertwiningMap ρ, ∃ c : Fin (Module.finrank ℂ S) → ℂ,
      ∀ n, H (ψ n) = ∑ j, c j • φ j n := by
    intro ψ
    let Hψ : π.IntertwiningMap ρ := (H ∘ₗ ψ.toLinearMap).intertwiningMap_of_isIntertwiningMap π ρ
      (fun g v => by simp [ψ.isIntertwining, hH])
    have hr : LinearMap.range Hψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap := by
      rintro _ ⟨n, rfl⟩
      exact hY ⟨ψ n, rfl⟩
    exact GlobalTheory.T.exists_eq_sum_smul_of_range_le_iSup_range G N X π ρ hschur _ φ hinj Hψ hr
  choose hc hhc using fun j => hcoef (φ j)
  refine ⟨∑ j, hc j j, fun A B hB b hb => ?_⟩
  obtain ⟨hfin, htr⟩ := hb
  let R := LinearMap.range A
  let Φ' : (Fin (Module.finrank ℂ S) → R) →ₗ[ℂ] X :=
    ∑ j, (φ j).toLinearMap ∘ₗ R.subtype ∘ₗ LinearMap.proj j
  have hΦ' : ∀ w, Φ' w = ∑ j, φ j (w j : N) := by
    intro w
    simp [Φ', LinearMap.sum_apply]
  have hinj' : Function.Injective Φ' := by
    intro w w' e
    rw [hΦ', hΦ'] at e
    have := hinj e
    funext j
    exact Subtype.ext (congrFun this j)
  let Z := LinearMap.range Φ'
  have hBφ : ∀ (ψ : π.IntertwiningMap ρ) n, B (ψ n) = ψ (A n) := fun ψ n =>
    DFunLike.congr_fun (hB ψ) n
  have hrange : LinearMap.range (H ∘ₗ B) ≤ Z := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ ⨆ f : π.IntertwiningMap ρ, LinearMap.range f.toLinearMap := by
      have : x ∈ isoPartAlg π ρ := hiso ▸ Submodule.mem_top
      exact this
    refine Submodule.iSup_induction _ (motive := fun x => (H ∘ₗ B) x ∈ Z) hx ?_ ?_ ?_
    · rintro ψ _ ⟨n, rfl⟩
      obtain ⟨c, hc'⟩ := hcoef ψ
      refine ⟨fun j => c j • ⟨A n, LinearMap.mem_range_self A n⟩, ?_⟩
      rw [hΦ']
      simp only [LinearMap.comp_apply, Pi.smul_apply, SetLike.val_smul, map_smul]
      rw [show ψ.toLinearMap n = ψ n from rfl, hBφ, hc']
    · simp
    · intro x y hx hy
      simpa using Z.add_mem hx hy
  haveI : FiniteDimensional ℂ Z := LinearMap.finiteDimensional_range Φ'
  have hT1 := GlobalTheory.T.hasFiniteRankTraceOf_of_range_le_finiteDimensional X (H ∘ₗ B) Z hrange
  let e : (Fin (Module.finrank ℂ S) → R) ≃ₗ[ℂ] Z := LinearEquiv.ofInjective Φ' hinj'
  let A' : R →ₗ[ℂ] R := A.restrict (p := R) (q := R) fun v _ => LinearMap.mem_range_self A v
  let h : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ := Matrix.of fun k j => hc j k
  let M : (Fin (Module.finrank ℂ S) → R) →ₗ[ℂ] (Fin (Module.finrank ℂ S) → R) :=
    ∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ => R) k ∘ₗ A' ∘ₗ LinearMap.proj j)
  have hM : ∀ w k, (M w k : N) = ∑ j, hc j k • A (w j) := by
    intro w k
    simp [M, h, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply, A']
  have hconj : (H ∘ₗ B).restrict (p := Z) (q := Z) (fun x _ => hrange (LinearMap.mem_range_self _ x)) =
      e.conj M := by
    refine LinearMap.ext fun z => Subtype.ext ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    change H (B (Φ' w)) = Φ' (M w)
    rw [hΦ', hΦ', map_sum, map_sum]
    simp_rw [hBφ, hhc, hM, map_sum, map_smul]
    rw [Finset.sum_comm]
  have key : LinearMap.trace ℂ Z ((H ∘ₗ B).restrict (p := Z) (q := Z)
      fun x _ => hrange (LinearMap.mem_range_self _ x)) = (∑ j, hc j j) * b := by
    rw [hconj, LinearMap.trace_conj', GlobalTheory.T.trace_sum_single_comp_proj_eq R _ h A', ← htr]
    simp [h, Matrix.trace, A', R]
  rw [← key]
  exact hT1

end GlobalTheory.IsoTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransversalCoefficientDecayAtRealPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transversal_coefficient_decay_at_real_place : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c₁ lam q Cb : ℝ) (k : ℕ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B = gramAt D V τ → B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 →
  V.rank = k + 1 →
  (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ,
    Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ, ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
    lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < c₁ → 0 < lam → Cb ≤ Real.exp q →
  (∀ g ∈ Formalism.MainNotions.S.UJset (MP.ε τ),
    Integrable (fun h => ⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
      (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
      c₁ * Cb * Real.sqrt (∑ a, ‖g a (e none)‖ ^ 2) ^ (-(2 * (k : ℝ) + 7))) →
  ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)))
      (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖((lam * c₁ : ℝ) : ℂ)‖ := by
  first | exact @GlobalTheory.PackLoc.farClause | exact GlobalTheory.PackLoc.farClause | (intros; apply GlobalTheory.PackLoc.farClause <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncatedKernelOrbitSum
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.TruncKerConst

variable {D : D7} {V : HSp D}

theorem NA_eq_bot_of_k_eq_zero (𝔉 : IsoFlag V) (h : 𝔉.k = 0) : NA 𝔉 = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  have ht : 𝔉.X (Fin.last 𝔉.k) = ⊥ := by
    have e : (Fin.last 𝔉.k) = 0 := Fin.ext (by simp [h])
    rw [e, 𝔉.zero]
  have h2 := (IsoFlag.mem_unip.1 hg).2
  change g ∈ trivOn _ V _ (𝔉.X (Fin.last 𝔉.k)) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V (𝔉.X (Fin.last 𝔉.k))) at h2
  rw [ht, perp_bot, trivOn_bot_top] at h2
  exact h2

theorem parRat_eq_top_of_k_eq_zero (𝔉 : IsoFlag V) (h : 𝔉.k = 0) : 𝔉.parRat D.sp.cm = ⊤ := by
  refine eq_top_iff.2 fun γ _ => IsoFlag.mem_parRat.2 fun i x hx => ?_
  have hi : i = 0 := Fin.ext (by have := i.2; simp; omega)
  rw [hi, 𝔉.zero] at hx ⊢
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]

theorem integral_unipMeas_of_k_eq_zero (𝔉 : IsoFlag V) (h : 𝔉.k = 0) (φ : GA D V → ℂ) :
    ∫ n : NA 𝔉, φ n ∂unipMeas 𝔉 = φ 1 := by
  have hb := NA_eq_bot_of_k_eq_zero 𝔉 h
  have h1' : ∀ g ∈ NA 𝔉, g = 1 := fun g hg => Subgroup.mem_bot.1 (hb ▸ hg)
  haveI : Subsingleton (NA 𝔉) := ⟨fun a b => Subtype.ext ((h1' _ a.2).trans (h1' _ b.2).symm)⟩
  letI : Unique (NA 𝔉) := { default := 1, uniq := fun _ => Subsingleton.elim _ _ }
  have h1 : (Measure.haar : Measure (NA 𝔉)) univ = 1 := by
    rw [Measure.haar, ← (Classical.arbitrary (TopologicalSpace.PositiveCompacts (NA 𝔉))).nonempty.eq_univ]
    exact Measure.haarMeasure_self
  have h2 : quotMeasure (NQ 𝔉) Measure.haar univ = 1 := by
    rw [quotMeasure, Measure.map_apply GlobalTheory.AutomorphicL2Unitary.measurable_mk MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ,
      Set.Nonempty.eq_univ (s := GlobalTheory.AutomorphicL2Unitary.stdDom (NQ 𝔉)) ⟨_, GlobalTheory.AutomorphicL2Unitary.sec_mem (GlobalTheory.AutomorphicL2Unitary.mk (NQ 𝔉) 1)⟩, h1]
  rw [integral_unique, unipMeas, Measure.real, Measure.smul_apply, h2, h1]
  simp
  rfl

def conjEquiv (𝔬 : Set (GF V)) (h𝔬 : ∀ δ ∈ 𝔬, ∀ g, g * δ * g⁻¹ ∈ 𝔬) (g : GF V) : 𝔬 ≃ 𝔬 where
  toFun δ := ⟨g * δ * g⁻¹, h𝔬 _ δ.2 g⟩
  invFun δ := ⟨g⁻¹ * δ * g⁻¹⁻¹, h𝔬 _ δ.2 g⁻¹⟩
  left_inv δ := Subtype.ext (by simp [mul_assoc])
  right_inv δ := Subtype.ext (by simp [mul_assoc])

end GlobalTheory.TruncKerConst

open GlobalTheory.TruncKerConst in

theorem GlobalTheory.TruncKer.kT_eq_of_unipIntegralsVanish : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (K : Subgroup (GA D V)) (f : GA D V → ℂ), (∀ 𝔉 : IsoFlag V, 𝔉.Proper → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.UnipIntegralsVanish 𝔉 f) → ∀ 𝔬 : Set (GF V), (∀ δ ∈ 𝔬, ∀ g, g * δ * g⁻¹ ∈ 𝔬) → ∀ Tr x, kT Φ K 𝔬 f Tr x = ∑' δ : 𝔬, f (x⁻¹ * rat V δ * x) := by
  intro D V Φ K f hf 𝔬 h𝔬 Tr x
  classical
  rw [kT, Finset.sum_eq_single (∅ : Finset (Fin (wittIndex V)))]
  ·
    have hk : (Φ.stdFlag (∅ : Finset (Fin (wittIndex V)))).k = 0 := rfl
    haveI : Subsingleton (GlobalTheory.AutomorphicL2Unitary.Quot ((Φ.stdFlag ∅).parRat D.sp.cm)) := ⟨fun a b => by
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      exact Quotient.sound (QuotientGroup.rightRel_apply.2 (by rw [parRat_eq_top_of_k_eq_zero _ hk]; trivial))⟩
    set ξ₀ : GlobalTheory.AutomorphicL2Unitary.Quot ((Φ.stdFlag ∅).parRat D.sp.cm) := GlobalTheory.AutomorphicL2Unitary.mk _ 1
    rw [tsum_eq_single ξ₀ (fun b hb => absurd (Subsingleton.elim b ξ₀) hb)]
    have hτ : tauHat (stdPar (∅ : Finset (Fin (wittIndex V)))) ∅ (H0 Φ K (rat V ξ₀.out * x) - Tr) = 1 := by
      simp [tauHat, stdPar]
    rw [hτ, Finset.card_empty, pow_zero, one_mul, Complex.ofReal_one, one_mul, kerP]
    set g := ξ₀.out
    have hl : Φ.levi D.sp.cm (AF D.host.F) (stdPar (∅ : Finset (Fin (wittIndex V)))) = ⊤ := by
      simp [WittFrame.levi, stdPar]
    let e : 𝔬 ≃ {δ : GF V // δ ∈ 𝔬 ∧ rat V δ ∈ Φ.levi D.sp.cm (AF D.host.F) (stdPar (∅ : Finset (Fin (wittIndex V))))} :=
      (conjEquiv 𝔬 h𝔬 g).trans
        { toFun := fun δ => ⟨δ.1, δ.2, by rw [hl]; trivial⟩
          invFun := fun δ => ⟨δ.1, δ.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [← e.tsum_eq]
    refine tsum_congr fun δ => ?_
    refine (integral_unipMeas_of_k_eq_zero (φ := fun n => f (((rat V) g * x)⁻¹ * rat V (e δ).1 * n * ((rat V) g * x))) _ hk).trans ?_
    have hδ : ((e δ).1 : GF V) = g * δ.1 * g⁻¹ := rfl
    simp only [hδ, OneMemClass.coe_one, map_mul, map_inv, mul_inv_rev, mul_one]
    congr 1
    group
  ·
    intro J _ hJ
    have hp : (Φ.stdFlag J).Proper := by
      show 0 < J.card
      exact Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hJ)
    have h0 : ∀ y : GA D V, kerP Φ J 𝔬 f y y = 0 := fun y => by
      rw [kerP]
      refine (tsum_congr fun δ => ?_).trans tsum_zero
      rw [unipMeas, integral_smul_measure, ((hf _ hp) Measure.haar (y⁻¹ * rat V δ) y).2, smul_zero]
    simp [h0]
  · intro h; exact absurd (Finset.mem_univ _) h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationFamilyUnipotentInvariant
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab unipRad IsIsotropic diagH)
open scoped NNReal TensorProduct

noncomputable section

namespace GlobalTheory.TruncKer.RadInv

theorem iwAbs_mul_left_of_eq_one {G : Type} [Group G] {P : Subgroup G} {δ : P →* ℝ≥0} {K : Subgroup G}
    (h : ∀ p : P, (p : G) ∈ K → δ p = 1) (p : P) (hp : δ p = 1) (g : G) :
    Doubling.iwAbs δ K (p * g) = Doubling.iwAbs δ K g := by
  by_cases hg : ∃ p' : P, ∃ k ∈ K, g = p' * k
  · obtain ⟨p', k, hk, rfl⟩ := hg
    rw [← mul_assoc, ← Subgroup.coe_mul, Doubling.iwAbs_mul_of_triv h _ hk, Doubling.iwAbs_mul_of_triv h _ hk,
      map_mul, hp, one_mul]
  · have hg' : ¬ ∃ p' : P, ∃ k ∈ K, (p : G) * g = p' * k := by
      rintro ⟨p', k, hk, e⟩
      exact hg ⟨p⁻¹ * p', k, hk, by rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, ← e, inv_mul_cancel_left]⟩
    unfold Doubling.iwAbs
    rw [dif_neg hg, dif_neg hg']

theorem below_invSV {k : ℕ} (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) {a b : SV k} (h : Below a b) :
    Below (invSV π ε a) (invSV π ε b) := fun i hi => congrArg _ (h _ (right_ne_zero_of_mul hi))

theorem below_single_stdVec {k : ℕ} {i j : Fin k} (h : i ≤ j) : Below (Pi.single i 1) (stdVec j) := fun t ht => by
  by_cases e : t = i
  · subst e; simp [stdVec, h]
  · exact absurd (Pi.single_eq_of_ne e _) ht

variable {D : D7} {V : HSp D}

theorem sub_mono (Φ : WittFrame V) {a b : SV (wittIndex V)} (h : Below a b) : Φ.sub a ≤ Φ.sub b :=
  Submodule.span_mono (Set.union_subset_union
    (Set.image_mono fun i (hi : a i = 1) => show b i = 1 from (h i (by rw [hi]; decide)).trans hi)
    (Set.image_mono fun i (hi : a i = -1) => show b i = -1 from (h i (by rw [hi]; decide)).trans hi))

theorem sub_single_le (Φ : WittFrame V) (i : Fin (wittIndex V)) :
    Φ.sub (Pi.single i 1) ≤ Submodule.span D.host.E {Φ.e i} := by
  refine Submodule.span_le.2 (Set.union_subset ?_ ?_)
  · rintro _ ⟨t, ht, rfl⟩
    obtain rfl : t = i := by
      by_contra e
      simp [Pi.single_eq_of_ne e] at ht
    exact Submodule.mem_span_singleton_self _
  · rintro _ ⟨t, ht, rfl⟩
    exfalso
    by_cases e : t = i
    · subst e; simp at ht
    · simp [Pi.single_eq_of_ne e] at ht

theorem exists_ne_zero_mem_sub (Φ : WittFrame V) (π : Equiv.Perm (Fin (wittIndex V)))
    (ε : Fin (wittIndex V) → SignTypeˣ) (i : Fin (wittIndex V)) :
    ∃ y ∈ Φ.sub (invSV π ε (Pi.single i 1)), y ≠ 0 := by
  have hv : invSV π ε (Pi.single i 1) (π.symm i) = ε (π.symm i) := by simp [invSV]
  have h0 := Units.ne_zero (ε (π.symm i))
  generalize ((ε (π.symm i) : SignTypeˣ) : SignType) = s at hv h0
  cases s with
  | zero => exact absurd rfl h0
  | pos => exact ⟨Φ.e (π.symm i), Submodule.subset_span (Or.inl ⟨_, hv, rfl⟩), Φ.linearIndependent_e.ne_zero _⟩
  | neg =>
    refine ⟨Φ.f (π.symm i), Submodule.subset_span (Or.inr ⟨_, hv, rfl⟩), fun h => ?_⟩
    have := Φ.ef (π.symm i) (π.symm i)
    rw [if_pos rfl, h] at this
    simp [HSpace.hD] at this

theorem ratAct_inv_apply (γ : GF V) (x : V.V) : ratAct D.sp.cm V γ⁻¹ (ratAct D.sp.cm V γ x) = x := by
  have e : γ⁻¹.1.1 * γ.1.1 = 1 := congrArg (fun g : GF V => g.1.1) (inv_mul_cancel γ)
  rw [ratAct, ratAct, ← LinearMap.comp_apply, ← Matrix.toLin_mul, e, Matrix.toLin_one]
  rfl

theorem act_rat_mem {γ : GF V} {A B : Submodule D.host.E V.V} (h : ∀ x ∈ A, ratAct D.sp.cm V γ x ∈ B)
    {y : Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ extSub (F := D.host.F) V (AF D.host.F) A) :
    act D.sp.cm V (rat V γ) y ∈ extSub (F := D.host.F) V (AF D.host.F) B :=
  (Submodule.span_le (p := (extSub (F := D.host.F) V (AF D.host.F) B).comap
    (HA.mat (AF D.host.F) D.sp.cm.sig V.gram (rat V γ)).1.mulVecLin)).2 (by
      rintro _ ⟨x, hx, rfl⟩
      show act D.sp.cm V (diagH D.sp.cm.sig V.gram (AF D.host.F) γ) (coordR V (AF D.host.F) x) ∈
        extSub (F := D.host.F) V (AF D.host.F) B
      rw [act_diagH]
      exact coordR_mem V _ (h x hx)) hy

end GlobalTheory.TruncKer.RadInv
end

namespace GlobalTheory.TruncKer.RadInv

variable {D : D7} {V : HSp D}

theorem conj_mem_unipRad {γ : GF V} {A B : Submodule D.host.E V.V}
    (h1 : ∀ x ∈ A, ratAct D.sp.cm V γ x ∈ B) (h2 : ∀ x ∈ B, ratAct D.sp.cm V γ⁻¹ x ∈ A)
    {n : GA D V} (hn : n ∈ unipRad D.sp.cm V (AF D.host.F) A) :
    rat V γ * n * (rat V γ)⁻¹ ∈ unipRad D.sp.cm V (AF D.host.F) B := by
  have hi : (rat V γ)⁻¹ = rat V γ⁻¹ := (map_inv _ _).symm
  have hc : ∀ y, act D.sp.cm V (rat V γ) (act D.sp.cm V (rat V γ⁻¹) y) = y := fun y => by
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, ← map_mul, mul_inv_cancel, map_one, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one]
  have hc' : ∀ y, act D.sp.cm V (rat V γ⁻¹) (act D.sp.cm V (rat V γ) y) = y := fun y => by
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, ← map_mul, inv_mul_cancel, map_one, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [hi, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, hn.1 _ (act_rat_mem h2 hy), hc]
  · have hz : act D.sp.cm V (rat V γ⁻¹) y ∈ extSub (F := D.host.F) V (AF D.host.F) (perp V A) :=
      (mem_extSub_perp D.sp.cm V).2 fun x hx => by
        have := (hR_act D.sp.cm V (rat V γ⁻¹) (act D.sp.cm V (rat V γ) x) y).trans
          ((mem_extSub_perp D.sp.cm V).1 hy _ (act_rat_mem h1 hx))
        rwa [hc'] at this
    have := act_rat_mem h1 (hn.2 _ hz)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_sub, hc] at this
    rwa [hi, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul]

theorem absChi_eq_one_of_mem_unip (Φ : WittFrame V) (p : PA Φ.flag0)
    (hp : (p : GA D V) ∈ Φ.flag0.unip D.sp.cm (AF D.host.F)) (i : Fin (wittIndex V)) : absChi Φ i p = 1 := by
  have he : Φ.e i ∈ Φ.flag0.X i.succ := Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
  have h1 := Φ.coef_eq_zero D.sp.cm (AF D.host.F) i ((IsoFlag.mem_unip_iff.1 hp).1 i _ he)
  rw [map_sub, sub_eq_zero, WittFrame.coef_coordR, Φ.ef, if_pos rfl, map_one] at h1
  have h2 : Φ.chi D.sp.cm (AF D.host.F) i p = 1 := h1
  have h3 : (Φ.chi D.sp.cm (AF D.host.F) i).toHomUnits p = 1 := Units.ext h2
  simp only [absChi, MonoidHom.comp_apply, h3, map_one]

theorem ratAct_inv_e_mem (Φ : WittFrame V) {π : Equiv.Perm (Fin (wittIndex V))} {ε : Fin (wittIndex V) → SignTypeˣ}
    {w : GF V} (hw : Φ.IsWeylRep D.sp.cm π ε w) {i j : Fin (wittIndex V)} (hij : i ≤ j) :
    ratAct D.sp.cm V w⁻¹ (Φ.e i) ∈ Φ.sub (invSV π ε (stdVec j)) := by
  obtain ⟨y, hy, hy0⟩ := exists_ne_zero_mem_sub Φ π ε i
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (sub_single_le Φ i (hw _ y hy))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hy0 (by rw [← ratAct_inv_apply w y, ← hc, map_zero])
  have e : Φ.e i = ratAct D.sp.cm V w (c⁻¹ • y) := by
    rw [map_smul, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e, ratAct_inv_apply]
  exact sub_mono Φ (below_invSV π ε (below_single_stdVec hij)) (Submodule.smul_mem _ _ hy)

end GlobalTheory.TruncKer.RadInv

namespace GlobalTheory.TruncKer

open RadInv in

theorem yfam_unipRad_mul : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    ∀ Q, IsPar Q → ∀ u ∈ Q, ∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), ∀ n ∈ NA (IsoFlag.single hW), ∀ x Tr,
    Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (n * x) Tr Q = Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q := by
  intro D V Φ L a hg Q hQ u hu hW n hn x Tr
  obtain ⟨π, ε, w, hw, hsub, hY⟩ := exists_Yfam_eq (Φ := Φ) (K := levelAll D.sp.cm.sig V.gram L a) hQ
  rw [hY, hY]
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (hsub hu)
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
  have hX : IsIsotropic V (Φ.flag0.X j.succ) := Φ.flag0.isIsotropic (Fin.succ_ne_zero j)
  have h1 : ∀ y ∈ Φ.sub (invSV π ε (stdVec j)), ratAct D.sp.cm V w y ∈ Φ.flag0.X j.succ := fun y hy =>
    Φ.sub_stdVec j ▸ hw _ y hy
  have h2 : ∀ y ∈ Φ.flag0.X j.succ, ratAct D.sp.cm V w⁻¹ y ∈ Φ.sub (invSV π ε (stdVec j)) := by
    intro y hy
    refine (Submodule.span_le (p := (Φ.sub (invSV π ε (stdVec j))).comap (ratAct D.sp.cm V w⁻¹))).2 ?_ hy
    rintro _ ⟨i, hi, rfl⟩
    exact ratAct_inv_e_mem Φ hw (show i ≤ j from Nat.lt_succ_iff.1 hi)
  have hN : rat V w * n * (rat V w)⁻¹ ∈ (IsoFlag.single hX).unip D.sp.cm (AF D.host.F) := by
    rw [IsoFlag.unip_single]
    exact conj_mem_unipRad h1 h2 (by rw [← IsoFlag.unip_single]; exact hn)
  have hU := Φ.flag0.unip_single_le D.sp.cm (AF D.host.F) (Fin.succ_ne_zero j) hN
  let p : PA Φ.flag0 := ⟨_, Φ.flag0.unip_le_par _ _ hU⟩
  have hK := hg.isCompact
  have := Doubling.t2Space_adeleRing' (F := D.host.F)
  have e : rat V w * (n * x) = (p : GA D V) * (rat V w * x) := by simp [p, mul_assoc]
  have key : H0 Φ (levelAll D.sp.cm.sig V.gram L a) (rat V w * (n * x)) =
      H0 Φ (levelAll D.sp.cm.sig V.gram L a) (rat V w * x) := by
    simp only [H0, e]
    congr 2
    funext i
    rw [iwAbs_mul_left_of_eq_one (Doubling.triv_of_isCompact (Φ.flag0.isClosed_par _ _) (continuous_absChi i) hK) p
      (absChi_eq_one_of_mem_unip Φ p hU i)]
  simp only [Ys, key]

end GlobalTheory.TruncKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHaarCoordinateReversalPositiveMultipleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_haar_coordinate_reversal_positive_multiple : ∀ (m : ℕ) (ε : Fin m → Bool), ∃ lam : ℝ, 0 < lam ∧
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Matrix (Fin m) (Fin m) ℂ → E),
    (Integrable (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG ε) ↔
      Integrable (fun h : Formalism.REAL.UJ (fun a => ε a.rev) => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG (fun a => ε a.rev))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG ε) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG (fun a => ε a.rev)) := by
  first | exact @GlobalTheory.HaarRev.haar_rev | exact GlobalTheory.HaarRev.haar_rev | (intros; apply GlobalTheory.HaarRev.haar_rev <;> assumption)
end

