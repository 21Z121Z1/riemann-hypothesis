import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0127
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0145
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0147
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AbelianPartHeightLinear
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0146
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionSeventh
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem sameOrbit_fstPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (k₀ : K)
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun k => c (some k), fun k => hc _, ?_⟩
  funext p
  show z (v₀ k₀ p) = c (some p.1) * z' (v₀ k₀ p)
  rw [e]
  rfl

theorem sameOrbit_sndPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (k₀ : K)
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · by_cases hk : k = k₀
    · simpa [hk] using hc none
    · simpa [hk] using hc (some k)
  · funext p
    show z (v₁ k₀ p) = (if p.1 = k₀ then c none else c (some p.1)) * z' (v₁ k₀ p)
    rw [e]
    by_cases hk : p.1 = k₀
    · obtain ⟨k, m⟩ := p
      obtain rfl : k = k₀ := hk
      simp [v₁_self]
    · rw [if_neg hk, v₁_ne hk]

theorem null_w : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ l : Fin BM.q, IsNull RW.A {x | FA.pr (q 0 x) ∈ BM.O l ∧ (FA.pr (q 0 x) ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (fstPt k₀ (RW.lift x x)) p = 0 ∨ FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (sndPt k₀ (RW.lift x x)) p = 0)} := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hab hj hblk hca hcb RW q hq h0 h1 hinj l
  have hpr : HoloMap RW.A BM.Rb.A (FA.pr ∘ q 0) := Pr.holoMap_comp' (hq 0) FA.pr_holo
  have hdens := GlobalTheory.T.flag_adjacent_twisted_resolution_sixth K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hab hj hblk hca hcb RW q hq h0 h1 hinj l
  have hn0 := GlobalTheory.T.base_metric_pullback_family K ι Φ y Ψ N j M n BM (d + 2) RW.X RW.A RW.U
    (fun x y' => fstPt k₀ (RW.lift x y')) (FA.pr ∘ q 0) l hpr RW.isOpen_U RW.mem_U
    (fun x p => RW.holo x (v₀ k₀ p))
    (fun x y' hy => sameOrbit_fstPt k₀ (RW.compat x y' y' ⟨hy, RW.mem_U y'⟩))
    (fun x hx V hV hxV => by
      obtain ⟨x', hx', hb, hp⟩ := hdens x hx V hV hxV
      exact ⟨x', hx', hb, fun p => (hp p).1⟩)
  have hn1 := GlobalTheory.T.base_metric_pullback_family K ι Φ y Ψ N j M n BM (d + 2) RW.X RW.A RW.U
    (fun x y' => sndPt k₀ (RW.lift x y')) (FA.pr ∘ q 0) l hpr RW.isOpen_U RW.mem_U
    (fun x p => RW.holo x (v₁ k₀ p))
    (fun x y' hy => sameOrbit_sndPt k₀ (RW.compat x y' y' ⟨hy, RW.mem_U y'⟩))
    (fun x hx V hV hxV => by
      obtain ⟨x', hx', hb, hp⟩ := hdens x hx V hV hxV
      exact ⟨x', hx', hb, fun p => (hp p).2⟩)
  intro i
  refine measure_mono_null ?_ (measure_union_null (hn0 i) (hn1 i))
  rintro w ⟨hw, hw'⟩
  obtain ⟨hO, hs | ⟨p, hp | hp⟩⟩ := hw'
  · exact Or.inl ⟨hw, hO, Or.inl hs⟩
  · exact Or.inl ⟨hw, hO, Or.inr ⟨p, hp⟩⟩
  · exact Or.inr ⟨hw, hO, Or.inr ⟨p, hp⟩⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenusEqCardMulSignature
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim

theorem ringHom_injective {E : Type} [Field E] [NumberField E] (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  ext n
  simp [Ideal.mem_comap, RingHom.mem_ker]

theorem restrict_bijective (E : Type) [Field E] [NumberField E] :
    Function.Bijective (fun f : E →+* ℂ => f.comp (algebraMap (𝓞 E) E)) := by
  constructor
  · intro f f' h
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  · intro s
    refine ⟨IsFractionRing.lift (ringHom_injective s), ?_⟩
    ext a
    simp

theorem natCard_ringHom (E : Type) [Field E] [NumberField E] :
    Nat.card (𝓞 E →+* ℂ) = Module.finrank ℚ E := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (restrict_bijective E)), Nat.card_eq_fintype_card]
  exact NumberField.Embeddings.card E ℂ

def both {E Ψ : Type} [Field E] [NumberField E] (σ : Ψ → (𝓞 E →+* ℂ)) : Ψ ⊕ Ψ → (𝓞 E →+* ℂ) :=
  Sum.elim σ fun τ => (starRingEnd ℂ).comp (σ τ)

theorem conj_conj_comp {E : Type} [Field E] [NumberField E] (s : 𝓞 E →+* ℂ) :
    (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
  ext a
  simp

theorem both_bijective {E Ψ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)}
    (h : IsCMFam σ) : Function.Bijective (both σ) := by
  have hconj : Function.Injective fun s : 𝓞 E →+* ℂ => (starRingEnd ℂ).comp s := by
    intro s t hst
    have := congrArg (fun u : 𝓞 E →+* ℂ => (starRingEnd ℂ).comp u) hst
    simpa only [conj_conj_comp] using this
  have hcross : ∀ τ τ', σ τ ≠ (starRingEnd ℂ).comp (σ τ') := by
    intro τ τ' e
    exact ((h.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, e⟩
  constructor
  · rintro (τ | τ) (τ' | τ') e
    · exact congrArg Sum.inl (h.1 e)
    · exact absurd e (hcross τ τ')
    · exact absurd e.symm (hcross τ' τ)
    · exact congrArg Sum.inr (h.1 (hconj e))
  · intro s
    by_cases hs : ∃ τ, σ τ = s
    · obtain ⟨τ, rfl⟩ := hs
      exact ⟨Sum.inl τ, rfl⟩
    · have h' : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
        by_contra hn
        exact hs ((h.2 s).2 hn)
      obtain ⟨τ, e⟩ := h'
      refine ⟨Sum.inr τ, ?_⟩
      show (starRingEnd ℂ).comp (σ τ) = s
      rw [e, conj_conj_comp]

theorem card_sum_eq_finrank {E Ψ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)}
    (h : IsCMFam σ) : Fintype.card (Ψ ⊕ Ψ) = Module.finrank ℚ E := by
  rw [← natCard_ringHom E, ← Nat.card_congr (Equiv.ofBijective _ (both_bijective h)), Nat.card_eq_fintype_card]

theorem eigSp_le_eigenspace {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module ℂ V]
    (B : 𝓞 E →+* Module.End ℂ V) (s : 𝓞 E →+* ℂ) (θ : 𝓞 E) :
    eigSp B s ≤ Module.End.eigenspace (B θ) (s θ) := by
  intro x hx
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hx
  rw [Module.End.mem_eigenspace_iff]
  exact hx θ

theorem iSupIndep_eigSp {E V ι : Type} [Field E] [NumberField E] [AddCommGroup V] [Module ℂ V]
    (B : 𝓞 E →+* Module.End ℂ V) (σ : ι → (𝓞 E →+* ℂ)) (hσ : Function.Injective σ) :
    iSupIndep fun s => eigSp B (σ s) := by
  obtain ⟨θ, m, -, -, -, hgen⟩ := exists_integral_generator E
  have hagree : ∀ (τ : 𝓞 E →+* ℂ) (P : Polynomial ℤ), τ (Polynomial.aeval θ P) = Polynomial.aeval (τ θ) P := fun τ P =>
    (Polynomial.aeval_algHom_apply τ.toIntAlgHom θ P).symm
  have hinj : Function.Injective fun s => σ s θ := by
    intro s t hst
    apply hσ
    ext a
    obtain ⟨n, P, hn, hP⟩ := hgen a
    have h1 := hagree (σ s) P
    have h2 := hagree (σ t) P
    have hst' : σ s θ = σ t θ := hst
    rw [hst', ← h2, ← hP, map_mul, map_mul, map_intCast, map_intCast] at h1
    exact mul_left_cancel₀ (by exact_mod_cast hn) h1
  exact ((Module.End.eigenspaces_iSupIndep (B θ)).comp hinj).mono fun s => eigSp_le_eigenspace B (σ s) θ

theorem dim_eq_card_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g j j' : ℕ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → (∀ τ, Module.finrank ℂ (eigSp B (σ τ)) = j' ∧ Module.finrank ℂ (eigSp B ((starRingEnd ℂ).comp (σ τ))) = j) → g = Fintype.card Ψ * (j + j') := by
  intro E _ _ _ Ψ _ g j j' B σ hσ hdim
  classical
  have hb := both_bijective hσ
  have htop := iSup_eigSp_eq_top B (both σ) hb.1 (card_sum_eq_finrank hσ)
  have hind := iSupIndep_eigSp B (both σ) hb.1
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun s => eigSp B (both σ s)) hint).finrank_eq
  rw [Module.finrank_directSum, Module.finrank_fin_fun, Fintype.sum_sum_type] at e
  have h1 : ∀ τ, Module.finrank ℂ (eigSp B (both σ (Sum.inl τ))) = j' := fun τ => (hdim τ).1
  have h2 : ∀ τ, Module.finrank ℂ (eigSp B (both σ (Sum.inr τ))) = j := fun τ => (hdim τ).2
  simp only [h1, h2, Finset.sum_const, Finset.card_univ, smul_eq_mul] at e
  rw [← e]
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightBoundFullIntersectionSystemStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posU_of_full_intersection_system : PB.Inputs → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), IsFullIntersectionSystem II → S'.IsTied → (∀ B : ℕ, 4 * D.f + 2 ≤ B → NefOnFibres (mCoordIdeal D.y) (muTwDeg Hd B)) → PosU S' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.posU_of_nefOnFibres | exact GlobalTheory.CompanionTheory.Ar.Cusp.posU_of_nefOnFibres | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.posU_of_nefOnFibres <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionDifferenceTelescopingIntegralStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_difference_telescoping_integral : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (t t' : ℝ) (w : Fin (D + 1) → σ), 0 < t → t ≤ S.t₀ → 0 < t' → t' ≤ S.t₀ → Re.num II t w - Re.num II t' w = ∑ r : Fin (D + 1), mInt S.A (fun i => S.potT (w (r.succAbove i)) (if r.succAbove i < r then t else t')) (fun x => S.phT (w r) t x - S.phT (w r) t' x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.num_sub_num | exact GlobalTheory.CompanionTheory.Ar.PB.num_sub_num | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.num_sub_num <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeRationalEmbedding
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates

open scoped TensorProduct nonZeroDivisors

theorem exists_nat_eq_mul {E : Type} [Field E] [NumberField E] {a : 𝓞 E} (ha : a ≠ 0) :
    ∃ (k : ℕ) (b : 𝓞 E), k ≠ 0 ∧ (k : 𝓞 E) = b * a := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  refine ⟨Ideal.absNorm (Ideal.span {a}), b, ?_, hb.symm⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact ha

theorem exists_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ], ∃ N : ℕ, Module.finrank ℚ E * N = Module.finrank ℤ Λ ∧ ∃ e : Λ →+ (Fin N → E), Function.Injective e ∧ (∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) ∧ ∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v := by
  intro E _ _ _ Λ _ _ _ _
  let f : Λ →ₗ[𝓞 E] E ⊗[𝓞 E] Λ := TensorProduct.mk (𝓞 E) E Λ 1
  have hb : IsBaseChange E f := TensorProduct.isBaseChange _ _ _
  haveI h1 : IsLocalizedModule (𝓞 E)⁰ f := (isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E f).2 hb
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  haveI h2 : IsLocalizedModule (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) f :=
    (isLocalizedModule_iff_isBaseChange _ E f).2 hb
  haveI h3 : IsLocalizedModule ℤ⁰ (f.restrictScalars ℤ) := IsLocalizedModule.restrictScalars _ f
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Λ
  have hrank : Module.finrank ℚ E * Module.finrank E (E ⊗[𝓞 E] Λ) = Module.finrank ℤ Λ := by
    rw [← IsLocalizedModule.finrank_eq ℤ⁰ (f.restrictScalars ℤ) le_rfl,
      ← IsLocalization.finrank_eq ℚ ℤ⁰ le_rfl, Module.finrank_mul_finrank]
  have htors : ∀ x : Λ, f x = 0 → x = 0 := by
    intro x hx
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (𝓞 E)⁰ f).1 hx
    obtain ⟨k, b, hk, hkb⟩ := exists_nat_eq_mul (nonZeroDivisors.coe_ne_zero c)
    have hkx : (k : ℤ) • x = 0 := by
      rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), hkb, mul_smul]
      have : (c : 𝓞 E) • x = 0 := hc
      rw [this, smul_zero]
    exact (smul_eq_zero.1 hkx).resolve_left (by exact_mod_cast hk)
  let g := (Module.finBasis E (E ⊗[𝓞 E] Λ)).equivFun
  refine ⟨Module.finrank E (E ⊗[𝓞 E] Λ), hrank,
    AddMonoidHom.mk' (fun x => g (f x)) (fun x y => by simp only [map_add]), ?_, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => htors x ?_
    exact g.map_eq_zero_iff.1 hx
  · intro a x
    change g (f (a • x)) = (a : E) • g (f x)
    rw [map_smul, ← map_smul g]
    congr 1
  · intro v
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (𝓞 E)⁰ f (g.symm v)
    obtain ⟨k, b, hk, hkb⟩ := exists_nat_eq_mul (nonZeroDivisors.coe_ne_zero s)
    refine ⟨k, b • x, hk, ?_⟩
    change g (f (b • x)) = k • v
    have hs' : (s : 𝓞 E) • g.symm v = f x := hs
    rw [map_smul, ← hs', ← mul_smul, ← hkb, Nat.cast_smul_eq_nsmul, map_nsmul, LinearEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeStabilizerEquivAutomorphisms
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab

section Ext

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem exists_basis (e : Λ →+ V) (hspan : Submodule.span E (e.range : Set V) = ⊤) :
    ∃ (I : Type) (b : Module.Basis I E V) (xs : I → Λ), ∀ i, b i = e (xs i) := by
  obtain ⟨B, hB, hsp, hli⟩ := exists_linearIndependent E (e.range : Set V)
  have hx : ∀ i : B, ∃ x, e x = i.1 := fun i => AddMonoidHom.mem_range.1 (hB i.2)
  choose xs hxs using hx
  refine ⟨B, Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, hspan]), xs, fun i => ?_⟩
  rw [Module.Basis.mk_apply, hxs]

theorem exists_clear {I : Type} (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) (b : Module.Basis I E V) (xs : I → Λ)
    (hb : ∀ i, b i = e (xs i)) (x : Λ) :
    ∃ (d : 𝓞 E) (s : Finset I) (a : I → 𝓞 E), d ≠ 0 ∧ d • x = ∑ i ∈ s, a i • xs i := by
  classical
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E))
    (b.repr (e x)).support (fun i => b.repr (e x) i)
  have h2 : ∀ i ∈ (b.repr (e x)).support, ∃ a : 𝓞 E, (a : E) = (d : E) * b.repr (e x) i := by
    intro i hi
    obtain ⟨a, ha⟩ := hint i hi
    refine ⟨a, ?_⟩
    rw [show (a : E) = algebraMap (𝓞 E) E a from rfl, ha, Algebra.smul_def]
  choose! a ha using h2
  refine ⟨d, (b.repr (e x)).support, a, nonZeroDivisors.ne_zero hd, he ?_⟩
  rw [hs, map_sum]
  conv_lhs => rw [← b.linearCombination_repr (e x), Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hs, ← hb, ha i hi, smul_smul]

theorem exists_ext (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x)
    (hspan : Submodule.span E (e.range : Set V) = ⊤) (f : Λ →ₗ[𝓞 E] Λ) :
    ∃ Φ : V →ₗ[E] V, ∀ x, Φ (e x) = e (f x) := by
  obtain ⟨I, b, xs, hb⟩ := exists_basis e hspan
  refine ⟨b.constr E fun i => e (f (xs i)), fun x => ?_⟩
  obtain ⟨d, s, a, hd, hx⟩ := exists_clear e he hs b xs hb x
  have hdE : (d : E) ≠ 0 := by simpa using hd
  have h1 : (d : E) • (b.constr E fun i => e (f (xs i))) (e x) = (d : E) • e (f x) := by
    rw [← map_smul, ← hs, ← hs, ← map_smul, hx]
    simp only [map_sum, hs, map_smul, ← hb, Module.Basis.constr_basis]
  exact smul_right_injective _ hdE h1

theorem exists_extEquiv (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x)
    (hspan : Submodule.span E (e.range : Set V) = ⊤) (φ : Λ ≃ₗ[𝓞 E] Λ) :
    ∃ Φ : V ≃ₗ[E] V, ∀ x, Φ (e x) = e (φ x) := by
  obtain ⟨Φ₁, h₁⟩ := exists_ext e he hs hspan (φ : Λ →ₗ[𝓞 E] Λ)
  obtain ⟨Φ₂, h₂⟩ := exists_ext e he hs hspan (φ.symm : Λ →ₗ[𝓞 E] Λ)
  refine ⟨LinearEquiv.ofLinear Φ₁ Φ₂ ?_ ?_, fun x => h₁ x⟩
  · refine LinearMap.ext_on hspan ?_
    rintro _ ⟨x, rfl⟩
    simp [h₁, h₂]
  · refine LinearMap.ext_on hspan ?_
    rintro _ ⟨x, rfl⟩
    simp [h₁, h₂]

theorem exists_lat (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) (γ : V ≃ₗ[E] V)
    (h₁ : ∀ x, ∃ y, e y = γ (e x)) (h₂ : ∀ x, ∃ y, e y = γ.symm (e x)) :
    ∃ φ : Λ ≃ₗ[𝓞 E] Λ, ∀ x, e (φ x) = γ (e x) := by
  choose f hf using h₁
  choose k hk using h₂
  refine ⟨{ toFun := f, invFun := k, map_add' := fun x y => he ?_, map_smul' := fun a x => he ?_,
            left_inv := fun x => he ?_, right_inv := fun x => he ?_ }, hf⟩
  · simp [hf]
  · simp [hf, hs]
  · simp [hf, hk]
  · simp [hf, hk]

theorem eq_zero_of_trace {xi u : E} (hxi : xi ≠ 0)
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E (xi * ((a : E) * u)) = 0) : u = 0 := by
  by_contra hu
  obtain ⟨z, hz⟩ := Algebra.trace_surjective ℚ E 1
  have halg : IsAlgebraic ℤ (z / (xi * u)) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  have h1 := h (IsIntegralClosure.mk' (𝓞 E) _ hint)
  rw [show ((IsIntegralClosure.mk' (𝓞 E) _ hint : 𝓞 E) : E) = _ from
    IsIntegralClosure.algebraMap_mk' (𝓞 E) _ hint] at h1
  have h2 : xi * (m • (z / (xi * u)) * u) = (m : ℚ) • z := by
    rw [zsmul_eq_mul, Algebra.smul_def]
    simp only [eq_intCast, map_intCast]
    field_simp
  rw [h2, map_smul, hz] at h1
  simp at h1
  exact hm h1

end Ext

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ}
  {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ}

theorem xi_ne_zero (C : LatEmb F) : C.xi ≠ 0 := by
  have hΨ : ∃ τ : Ψ, True := by
    by_contra hn
    have hn' : ∀ τ : Ψ, False := fun τ => hn ⟨τ, trivial⟩
    let s : 𝓞 E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding.comp (algebraMap (𝓞 E) E)
    have h := (F.cm.2 s).2 (fun ⟨τ, _⟩ => hn' τ)
    exact hn' h.choose
  obtain ⟨τ, -⟩ := hΨ
  intro h0
  have h1 := C.xi_eq τ
  rw [h0, map_zero] at h1
  have he : C.eps τ ≠ 0 := by
    intro h
    have := C.eps_sq τ
    rw [h] at this
    norm_num at this
  have hc : C.c * C.eps τ ≠ 0 := mul_ne_zero C.c_pos.ne' he
  have : ((C.c * C.eps τ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  exact (mul_ne_zero Complex.I_ne_zero this) h1.symm

theorem sesq_eq (C : LatEmb F) (φ : autGrp (E := E) F.form) (x y : Λ) :
    C.h.toSesq (C.e (φ.1 y)) (C.e (φ.1 x)) = C.h.toSesq (C.e y) (C.e x) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_trace (xi_ne_zero C) fun a => ?_
  have h1 := C.form_eq (a • φ.1 x) (φ.1 y)
  have h2 := C.form_eq (a • x) y
  have h3 : F.form (a • φ.1 x) (φ.1 y) = F.form (a • x) y := by
    rw [← map_smul]
    exact φ.2 _ _
  rw [h3, h2, C.e_smul, C.e_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
  rw [mul_sub, mul_sub, map_sub, sub_eq_zero]
  exact h1.symm

theorem ext_unitary (C : LatEmb F) (φ : autGrp (E := E) F.form)
    (Φ : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (hΦ : ∀ x, Φ (C.e x) = C.e (φ.1 x)) :
    Φ ∈ C.h.unitaryGroup := by
  obtain ⟨I, b, xs, hb⟩ := exists_basis C.e C.integral.isLattice.span_eq_top
  intro v w
  have key : (C.h.toSesq.comp (Φ : (Fin (j + j') → E) →ₗ[E] (Fin (j + j') → E))).compl₂
      (Φ : (Fin (j + j') → E) →ₗ[E] (Fin (j + j') → E)) = C.h.toSesq := by
    refine LinearMap.ext_basis b b fun p q => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hb, hΦ]
    exact sesq_eq C φ _ _
  exact LinearMap.congr_fun₂ key v w

open scoped Pointwise in
theorem stab_apply_mem (C : LatEmb F) (γ : latticeStab C.h C.e.range) (x : Λ) :
    ∃ y, C.e y = ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) := by
  have hs : (γ : C.h.unitaryGroup) • C.e.range = C.e.range := MulAction.mem_stabilizer_iff.1 γ.2
  have h1 : (γ : C.h.unitaryGroup) • C.e x ∈ (γ : C.h.unitaryGroup) • C.e.range :=
    AddSubgroup.smul_mem_pointwise_smul _ _ _ ⟨x, rfl⟩
  rw [hs] at h1
  exact h1

theorem exists_of_stab (C : LatEmb F) (γ : latticeStab C.h C.e.range) :
    ∃ φ : autGrp (E := E) F.form, ∀ x, C.e (φ.1 x) =
      ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) := by
  obtain ⟨φ, hφ⟩ := exists_lat C.e C.e_inj C.e_smul
    ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E))
    (stab_apply_mem C γ) (stab_apply_mem C γ⁻¹)
  refine ⟨⟨φ, fun x y => ?_⟩, hφ⟩
  have hu := (γ : C.h.unitaryGroup).2 (C.e y) (C.e x)
  apply Int.cast_injective (α := ℚ)
  rw [C.form_eq, C.form_eq, hφ, hφ]
  exact congrArg (fun t => Algebra.trace ℚ E (C.xi * t)) hu

open scoped Pointwise in

theorem exists_of_aut (C : LatEmb F) (φ : autGrp (E := E) F.form) :
    ∃ γ : latticeStab C.h C.e.range, ∀ x,
      ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) = C.e (φ.1 x) := by
  obtain ⟨Φ, hΦ⟩ := exists_extEquiv C.e C.e_inj C.e_smul C.integral.isLattice.span_eq_top φ.1
  have hU := ext_unitary C φ Φ hΦ
  refine ⟨⟨⟨Φ, hU⟩, ?_⟩, hΦ⟩
  refine MulAction.mem_stabilizer_iff.2 ?_
  ext v
  change v ∈ Φ • C.e.range ↔ _
  rw [AddSubgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨φ.1 x, (hΦ x).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨C.e (φ.1.symm y), ⟨_, rfl⟩, ?_⟩
    change Φ (C.e (φ.1.symm y)) = _
    rw [hΦ, LinearEquiv.apply_symm_apply]

theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), ∃ α : latticeStab C.h C.e.range ≃* autGrp (E := E) F.form, ∀ γ x, C.e ((α γ).1 x) = ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C
  choose A hA using exists_of_stab C
  choose B hB using exists_of_aut C
  have hspan := C.integral.isLattice.span_eq_top
  refine ⟨{ toFun := A, invFun := B, left_inv := fun γ => ?_, right_inv := fun φ => ?_,
            map_mul' := fun a b => ?_ }, hA⟩
  · refine Subtype.ext (Subtype.ext (LinearEquiv.toLinearMap_injective
      (LinearMap.ext_on hspan ?_)))
    rintro _ ⟨x, rfl⟩
    simp only [LinearEquiv.coe_coe]
    rw [hB, hA]
  · exact Subtype.ext (LinearEquiv.ext fun x => C.e_inj (by rw [hA, hB]))
  · refine Subtype.ext (LinearEquiv.ext fun x => C.e_inj ?_)
    change C.e ((A (a * b)).1 x) = C.e ((A a).1 ((A b).1 x))
    rw [hA, hA, hA]
    rfl

end Main

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab
end
end

