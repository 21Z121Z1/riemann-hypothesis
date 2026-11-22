import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalOperatorScalarOnSphericalEigenspace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eig

theorem mem_of_fibres {X Q H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] {g : X → H} {a : H}
    (hg : HasSum g a) (π : X → Q) (L : Submodule ℂ H) (hL : IsClosed (L : Set H))
    (h : ∀ x₀, ∃ s : Finset X, (∀ x, π x = π x₀ ↔ x ∈ s) ∧ ∑ x ∈ s, g x ∈ L) : a ∈ L := by
  have h1 := hg.tsum_fiberwise π
  refine hL.mem_of_tendsto h1 (Filter.Eventually.of_forall fun s => L.sum_mem fun c _ => ?_)
  by_cases hc : ∃ x₀, π x₀ = c
  · obtain ⟨x₀, rfl⟩ := hc
    obtain ⟨s, hs, hm⟩ := h x₀
    have e : π ⁻¹' {π x₀} = (s : Set X) := Set.ext fun x => hs x
    rw [e, Finset.tsum_subtype' s g]
    exact hm
  · have e : π ⁻¹' {c} = ((∅ : Finset X) : Set X) := Set.ext fun x => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_empty, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hc ⟨x, hx⟩
    rw [e, Finset.tsum_subtype' ∅ g, Finset.sum_empty]
    exact L.zero_mem

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isFinIdem_fid (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : IsFinIdem D v (Eu.fid D v) := by
  have h : ∃ f, IsFinIdem D v f := by
    obtain ⟨ε, hε⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
    exact ⟨_, ε, hε, rfl⟩
  unfold Eu.fid
  rw [dif_pos h]
  exact h.choose_spec

theorem exists_primeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) :
    ∃ P e, P.under (𝓞 D.host.F) = v ∧ IsPrimeIdem P e f := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ.isPrime, hne⟩
  have hP : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQv.over.symm
  obtain ⟨e, f', h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  obtain ⟨ε', hε', rfl⟩ := hf
  rw [hP] at hε
  rw [GlobalTheory.IdemSupport.placeIdem_unique hε' hε]
  exact ⟨P, e, hP, h⟩

theorem primeIdem_of_under {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P.under (𝓞 D.host.F) = v) : ∃ e, IsPrimeIdem P e f := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f', h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  obtain ⟨ε', hε', rfl⟩ := hf
  rw [hP] at hε
  rw [GlobalTheory.IdemSupport.placeIdem_unique hε' hε]
  exact ⟨e, h⟩

variable {R : RealDat D A Ks} {i : Fin D.R.m}

theorem bop_spec (hTL : TransLaws R i) {γ : GA D (Wc D i)} (hγ : γ ∈ GfC (Wc D i)) (x y) :
    trPair R i γ x y = ⟪x, Eu.Bop R i γ y⟫_ℂ := by
  have hex := hTL.2.2.1 γ hγ
  unfold Eu.Bop
  rw [dif_pos hex]
  exact hex.choose_spec.2 x y

theorem bop_mul_lev (hLP : LevProd R i) (hTL : TransLaws R i) {γ k : GA D (Wc D i)} (hγ : γ ∈ GfC (Wc D i))
    (hk : k ∈ levW R i) : Eu.Bop R i (γ * k) = Eu.Bop R i γ := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [← bop_spec hTL hγ, ← bop_spec hTL (mul_mem hγ (hLP.1 hk))]
  have := hTL.2.2.2.1 γ hγ 1 (one_mem _) k hk x y
  rwa [one_mul] at this

theorem hecke_sum_good {F : Face D A} (hL : Laws R F) (hTL : TransLaws R i) {c} {y} (hy : y ∈ part R i ∅ c)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f)
    (hv : ∀ P ∈ R.Pg, P.under (𝓞 D.host.F) ≠ v) {α : GA D (Wc D i)} (hα : SuppF (Wc D i) f α)
    {C : Finset (GA D (Wc D i))} (hC : ∀ γ ∈ C, SuppF (Wc D i) f γ)
    (hCR : IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) :
    ∃ z : ℂ, ∑ δ ∈ C, Eu.Bop R i δ y = z • y := by
  obtain ⟨y', hy', hs⟩ := hTL.2.1 v f hf α hα C hC hCR y
  have e1 : ∑ δ ∈ C, Eu.Bop R i δ y = y' := by
    apply ext_inner_left ℂ
    intro x
    rw [← hTL.2.2.2.2.2 x y', hs 1 (one_mem _) x, inner_sum]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [one_mul, bop_spec hTL (hCR.1 δ hδ).1]
  obtain ⟨P, e, hPv, hP⟩ := exists_primeIdem hf
  obtain ⟨n, hβ⟩ := hL.lev.βW i
  obtain ⟨hJ, hχ, -⟩ := (GlobalTheory.LevSplit.lev_split (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ).2 P e f hP
    (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
    (by
      intro PP hPP
      have h1 : PP ∈ R.Pg := hPP.resolve_right (Finset.notMem_empty _)
      refine ⟨fun h => hv PP h1 (h ▸ hPv), fun h => hv PP h1 ?_⟩
      rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h, GlobalTheory.IdemSupport.under_cP] at hPv
      exact hPv)
  obtain ⟨-, ϖ, -, h1, h2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D P
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have he : e * e = e := GlobalTheory.IdemSupport.delta_idem hΦ (GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hP).1
  obtain ⟨d, hd, hD⟩ := GlobalTheory.SphLabelOps.exists_divAt (Wc D i) he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hP) h1 h2 α
  have hop : Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) ∅ P d C :=
    ⟨e, f, ϖ, α, fun w hw => absurd hw (Finset.notMem_empty w), hP, h1, h2, hd, hJ, hχ, hα, hD, hC, hCR⟩
  have hm := (Submodule.mem_comap.1 hy).2
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at hm
  have hk := hm P d C hop
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hk
  refine ⟨c P d, e1.trans ((hL.models.HW i (sg0 D A)).1 ?_)⟩
  rw [hy', hk, map_smul]
  rfl

theorem hecke_sum_mem {F : Face D A} (hL : Laws R F) {t : T} (hB : BadSupp R i t) (hLP : LevProd R i)
    (hTL : TransLaws R i) {μ 𝓕} (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) {c} {y} (hy : y ∈ part R i ∅ c)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f)
    {α : GA D (Wc D i)} (hα : SuppF (Wc D i) f α)
    {C : Finset (GA D (Wc D i))} (hC : ∀ γ ∈ C, SuppF (Wc D i) f γ)
    (hCR : IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) :
    coef R i t μ 𝓕 α • ∑ δ ∈ C, Eu.Bop R i δ y ∈ Submodule.span ℂ {y} := by
  by_cases hv : ∀ P ∈ R.Pg, P.under (𝓞 D.host.F) ≠ v
  · obtain ⟨z, hz⟩ := hecke_sum_good hL hTL hy hf hv hα hC hCR
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))
  · push_neg at hv
    obtain ⟨P, hP, hPv⟩ := hv
    obtain ⟨e, he⟩ := primeIdem_of_under hf hPv
    by_cases hk : α ∈ levW R i
    · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun δ hδ => ?_)
      obtain ⟨-, k₁, hk₁, k₂, hk₂, rfl⟩ := hCR.1 δ hδ
      have := bop_mul_lev hLP hTL (one_mem _) (mul_mem (mul_mem hk₁.1 hk) hk₂.1)
      rw [one_mul] at this
      rw [this, Eu.bop_one hTL]
      exact Submodule.mem_span_singleton_self y
    · rw [hB μ 𝓕 hμ P (Or.inl hP) e f he α hα hk, zero_smul]
      exact Submodule.zero_mem _

theorem mk_eq_iff {v : HeightOneSpectrum (𝓞 D.host.F)} (g : Eu.locSet R i v) (x : Eu.LX R i v) :
    (Quotient.mk _ g : Eu.LX R i v) = x ↔ g.1⁻¹ * Eu.rep x ∈ levW R i := by
  rw [← QuotientGroup.leftRel_apply]
  exact Quotient.mk_eq_iff_out

set_option maxHeartbeats 800000 in

theorem zop_eigen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, BadSupp R i t → LevFix R i t → LocSmall R i t → LevProd R i → TransLaws R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ c, ∀ y ∈ part R i ∅ c, ∀ v, ∃ z : ℂ, Eu.Zop R i t μ 𝓕 v y = z • y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hB hLF _ hLP hTL μ 𝓕 hμ hleft c y hy v
  suffices h : Eu.Zop R i t μ 𝓕 v y ∈ Submodule.span ℂ {y} by
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 h
    exact ⟨z, hz.symm⟩
  unfold Eu.Zop
  by_cases hs : Summable fun x : Eu.LX R i v => Eu.acoef R i t μ 𝓕 v x • Eu.Bop R i (Eu.rep x)
  swap
  · rw [tsum_eq_zero_of_not_summable hs]
    exact Submodule.zero_mem _
  have hf := isFinIdem_fid D v
  obtain ⟨P, e, -, hP⟩ := exists_primeIdem hf
  have h0 := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)).2.2.1 P e _ hP
  obtain ⟨S, hS⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)).1 _ h0.1 h0.2.1).1
  have hloc : ∀ g, g ∈ S → g ∈ Eu.locSet R i v := fun g hg => ⟨h0.2.2.1 g ((hS g).1 hg), (hS g).1 hg⟩
  have hrep : ∀ x : Eu.LX R i v, Eu.rep x ∈ S := fun x => (hS _).2 (Quotient.out x).2.2
  have hsum := (ContinuousLinearMap.apply ℂ _ y).hasSum hs.hasSum
  refine mem_of_fibres hsum (fun x => DoubleCoset.mk (levW R i ⊓ S) (levW R i ⊓ S) (Eu.rep x)) _
    (Submodule.closed_of_finiteDimensional _) fun x₀ => ?_
  have hα : SuppF (Wc D i) (Eu.fid D v) (Eu.rep x₀) := (hS _).1 (hrep x₀)
  obtain ⟨C, hC, hCR⟩ := hTL.1 v _ hf _ hα
  have hK : ∀ k, k ∈ {k | k ∈ levW R i ∧ SuppF (Wc D i) (Eu.fid D v) k} ↔ k ∈ levW R i ⊓ S := fun k =>
    and_congr_right fun _ => (hS k).symm
  obtain ⟨φ, hφ⟩ : ∃ φ : GA D (Wc D i) → Eu.LX R i v, ∀ δ ∈ C, ∀ x, φ δ = x ↔ δ⁻¹ * Eu.rep x ∈ levW R i ⊓ S := by
    have key : ∀ δ : GA D (Wc D i), ∃ x' : Eu.LX R i v, δ ∈ C → ∀ x, x' = x ↔ δ⁻¹ * Eu.rep x ∈ levW R i ⊓ S := by
      intro δ
      by_cases hδ : δ ∈ C
      · have h1 := (hS δ).2 (hC δ hδ)
        exact ⟨Quotient.mk _ ⟨δ, hloc δ h1⟩, fun _ x =>
          (mk_eq_iff ⟨δ, hloc δ h1⟩ x).trans ⟨fun h => ⟨h, S.mul_mem (S.inv_mem h1) (hrep x)⟩, fun h => h.1⟩⟩
      · exact ⟨Eu.lx0 R i v, fun h => absurd h hδ⟩
    choose φ hφ using key
    exact ⟨φ, hφ⟩
  have hdc : ∀ δ ∈ C, ∃ k₁ ∈ levW R i ⊓ S, ∃ k₂ ∈ levW R i ⊓ S, Eu.rep (φ δ) = k₁ * Eu.rep x₀ * k₂ := fun δ hδ => by
    obtain ⟨-, k₁, hk₁, k₂, hk₂, e1⟩ := hCR.1 δ hδ
    refine ⟨k₁, (hK _).1 hk₁, k₂ * (δ⁻¹ * Eu.rep (φ δ)), mul_mem ((hK _).1 hk₂) ((hφ δ hδ _).1 rfl), ?_⟩
    rw [← mul_assoc, ← e1, mul_inv_cancel_left]
  refine ⟨C.image φ, fun x => ?_, ?_⟩
  · rw [eq_comm, DoubleCoset.eq, Finset.mem_image]
    constructor
    · rintro ⟨k₁, hk₁, k₂, hk₂, e1⟩
      obtain ⟨δ, ⟨hδ, h1⟩, -⟩ := hCR.2 _ ⟨k₁, (hK _).2 hk₁, k₂, (hK _).2 hk₂, e1⟩
      exact ⟨δ, hδ, (hφ δ hδ x).2 ((hK _).1 h1)⟩
    · rintro ⟨δ, hδ, rfl⟩
      exact hdc δ hδ
  · rw [Finset.sum_image]
    · have := hecke_sum_mem hL hB hLP hTL hμ hy hf hα hC hCR
      rw [Finset.smul_sum] at this
      refine (congrArg (· ∈ Submodule.span ℂ {y}) (Finset.sum_congr rfl fun δ hδ => ?_)).mpr this
      obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := hdc δ hδ
      have e2 : Eu.acoef R i t μ 𝓕 v (φ δ) = coef R i t μ 𝓕 (Eu.rep x₀) := by
        unfold Eu.acoef
        rw [e1, Model.coef_mul_lev R i t hLF μ 𝓕 _ _ hk₂.1, hleft _ hk₁.1]
      have e3 : Eu.Bop R i (Eu.rep (φ δ)) = Eu.Bop R i δ := by
        rw [← bop_mul_lev hLP hTL (hCR.1 δ hδ).1 ((hφ δ hδ _).1 rfl).1, mul_inv_cancel_left]
      rw [ContinuousLinearMap.apply_apply, e2, e3, ContinuousLinearMap.smul_apply]
    · intro δ hδ δ' hδ' h
      obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := hdc δ hδ
      obtain ⟨δ₀, -, hu⟩ := hCR.2 _ ⟨k₁, (hK _).2 hk₁, k₂, (hK _).2 hk₂, e1⟩
      exact (hu δ ⟨hδ, (hK _).2 ((hφ δ hδ _).1 rfl)⟩).trans (hu δ' ⟨hδ', (hK _).2 ((hφ δ' hδ' _).1 h.symm)⟩).symm

end GlobalTheory.RawLift.Eig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicAverageEqCoeffSinglePlaceElementStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicAverage_eq_coeff_singlePlaceElement : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eR : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) →
    ∀ (i : Fin D.R.m) (kv0 : Σ k : Fin 2, D.nd.PlG k) (a : Fin D.R.r → kP (plg kv0).1) (b : Bool) (ε : ℤ) (y : G),
    haveI : Fact (D.host.g kv0.1).Prime := ⟨D.host.g_prime kv0.1⟩
    GlobalTheory.DownLift.mirC R i (plg kv0) a b ε y = (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then
      (GlobalTheory.MirAvg.mirEl ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) (plg kv0).1).comp
        (Units.map (iso kv0 : ZMod (D.host.g kv0.1) →* kP (plg kv0).1))))
        (fun j => (iso kv0).symm (a j)) b).coeff (eR y kv0) else 0) := by
  first | exact @GlobalTheory.MirAvg.mirC_eq_coeff_mirEl | exact GlobalTheory.MirAvg.mirC_eq_coeff_mirEl | (intros; apply GlobalTheory.MirAvg.mirC_eq_coeff_mirEl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicDetCharacterFunctionConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

namespace GlobalTheory.DownLift.GenFinite

section Lin
variable {n k : Type} [Fintype n] [DecidableEq n] [CommRing k]

theorem gl_mulVec_inv_mulVec (X : GL n k) (v : n → k) :
    (X : Matrix n n k) *ᵥ (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem gl_inv_mulVec_mulVec (X : GL n k) (v : n → k) :
    ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ ((X : Matrix n n k) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem gl_conj_mulVec (X g : GL n k) (v : n → k) :
    ((X * g * X⁻¹ : GL n k) : Matrix n n k) *ᵥ v =
      (X : Matrix n n k) *ᵥ ((g : Matrix n n k) *ᵥ (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ v)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul]

theorem conj_fix_hyperplane_iff (X g : GL n k) (a : n → k) :
    (∀ v, a ⬝ᵥ v = 0 → ((X * g * X⁻¹ : GL n k) : Matrix n n k) *ᵥ v = v) ↔
      ∀ w, (a ᵥ* (X : Matrix n n k)) ⬝ᵥ w = 0 → (g : Matrix n n k) *ᵥ w = w := by
  constructor
  · intro h w hw
    have h1 := h ((X : Matrix n n k) *ᵥ w) (by rw [Matrix.dotProduct_mulVec]; exact hw)
    rw [gl_conj_mulVec, gl_inv_mulVec_mulVec] at h1
    have h2 := congrArg (fun u => ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ u) h1
    simpa only [gl_inv_mulVec_mulVec] using h2
  · intro h v hv
    rw [gl_conj_mulVec, h _ (by rw [← Matrix.dotProduct_mulVec, gl_mulVec_inv_mulVec]; exact hv),
      gl_mulVec_inv_mulVec]

theorem conj_triv_mod_line_iff (X g : GL n k) (a : n → k) :
    (∀ v, ∃ c : k, ((X * g * X⁻¹ : GL n k) : Matrix n n k) *ᵥ v - v = c • a) ↔
      ∀ w, ∃ c : k, (g : Matrix n n k) *ᵥ w - w = c • (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ a) := by
  constructor
  · intro h w
    obtain ⟨c, h1⟩ := h ((X : Matrix n n k) *ᵥ w)
    rw [gl_conj_mulVec, gl_inv_mulVec_mulVec] at h1
    have h2 := congrArg (fun u => ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ u) h1
    exact ⟨c, by simpa only [Matrix.mulVec_sub, Matrix.mulVec_smul, gl_inv_mulVec_mulVec] using h2⟩
  · intro h v
    obtain ⟨c, h1⟩ := h (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ v)
    have h2 := congrArg (fun u => (X : Matrix n n k) *ᵥ u) h1
    refine ⟨c, ?_⟩
    rw [gl_conj_mulVec]
    simpa only [Matrix.mulVec_sub, Matrix.mulVec_smul, gl_mulVec_inv_mulVec] using h2

theorem vecMul_gl_ne_zero (X : GL n k) {a : n → k} (ha : a ≠ 0) : a ᵥ* (X : Matrix n n k) ≠ 0 := by
  intro h
  apply ha
  have h2 := congrArg (fun u => u ᵥ* ((X⁻¹ : GL n k) : Matrix n n k)) h
  simp only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one,
    Matrix.zero_vecMul] at h2
  exact h2

theorem gl_inv_mulVec_ne_zero (X : GL n k) {a : n → k} (ha : a ≠ 0) :
    ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ a ≠ 0 := by
  intro h
  apply ha
  rw [← gl_mulVec_inv_mulVec X a, h, Matrix.mulVec_zero]

theorem det_conj_gl (X g : GL n k) :
    Matrix.GeneralLinearGroup.det (X * g * X⁻¹) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

theorem ite_congr_of_iff {p q : Prop} {dp : Decidable p} {dq : Decidable q} {u v : ℂ} (h : p ↔ q) :
    @ite ℂ p dp u v = @ite ℂ q dq u v := if_congr h rfl rfl

end Lin

theorem mirC_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ) (x : G), ∃ a' : Fin D.R.r → kP PP.1, a' ≠ 0 ∧ ∀ g, mirC R i PP a tr ε (x * g * x⁻¹) = mirC R i PP a' tr ε g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i PP a ha tr ε x
  have he : ∀ g PP', R.eG (x * g * x⁻¹) PP' = R.eG x PP' * R.eG g PP' * (R.eG x PP')⁻¹ := by
    intro g PP'
    rw [map_mul, map_mul, map_inv]
    rfl
  have h1 : ∀ g, (∀ PP', PP' ≠ PP → R.eG (x * g * x⁻¹) PP' = 1) ↔ ∀ PP', PP' ≠ PP → R.eG g PP' = 1 := by
    intro g
    refine forall_congr' fun PP' => forall_congr' fun _ => ?_
    rw [he, conj_eq_one_iff]
  have h2 : ∀ g, Matrix.GeneralLinearGroup.det (R.eG (x * g * x⁻¹) PP) = Matrix.GeneralLinearGroup.det (R.eG g PP) := by
    intro g
    rw [he]
    exact det_conj_gl _ _
  cases tr
  · refine ⟨_, vecMul_gl_ne_zero (R.eG x PP) ha, fun g => ?_⟩
    have h3 := conj_fix_hyperplane_iff (R.eG x PP) (R.eG g PP) a
    rw [← he] at h3
    unfold mirC
    rw [h2]
    refine ite_congr_of_iff (and_congr (h1 g) ?_)
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    exact h3
  · refine ⟨_, gl_inv_mulVec_ne_zero (R.eG x PP) ha, fun g => ?_⟩
    have h3 := conj_triv_mod_line_iff (R.eG x PP) (R.eG g PP) a
    rw [← he] at h3
    unfold mirC
    rw [h2]
    refine ite_congr_of_iff (and_congr (h1 g) ?_)
    rw [if_pos rfl, if_pos rfl]
    exact h3

end GlobalTheory.DownLift.GenFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOneOfChrEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

open Formalism.L2.Host

variable {D : D7} {T N : Type}

theorem pow_apply' {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (x) : (χ ^ a).1 x = χ.1 x ^ a := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

theorem loc_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) : (χ ^ a).loc v x = χ.loc v x ^ a :=
  pow_apply' χ a _

theorem locK_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) : (χ ^ a).locK v x = χ.locK v x ^ a :=
  pow_apply' χ a _

theorem trivOn_pow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ : HChar E}
    (h : χ.TrivOn F) (a : ℕ) : (χ ^ a).TrivOn F := by
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · have h1 := h.1 v k
    simp only [HChar.resFin, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢
    simp only [locK_pow]
    rw [Finset.prod_pow, h1, one_pow]
  · have h1 := h.2 w k
    simp only [HChar.resInf, HChar.locInf, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢
    simp only [pow_apply']
    rw [Finset.prod_pow, h1, one_pow]

theorem unrAt_pow {E : Type} [Field E] [NumberField E] {χ : HChar E} {v} (h : χ.UnrAt v) (a : ℕ) : (χ ^ a).UnrAt v :=
  fun x hx => by rw [loc_pow, h x hx, one_pow]

theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) : ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · rw [MonoidHom.pow_apply, locK_pow, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

theorem pow_eq_one_of_chrEq {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) {n : ℕ} (hn : χ.OrderDvd n) :
    c ^ n = 1 := by
  have h1 := chrEq_pow h n
  rw [show χ ^ n = 1 from hn] at h1
  exact MonoidHom.ext fun x => GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x

theorem exists_pow_aut (τ : ℂ ≃+* ℂ) {n : ℕ} (hn : 0 < n) : ∃ a, a < n ∧ ∀ z : ℂ, z ^ n = 1 → τ z = z ^ a := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨a, ha, h⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ (Complex.exp (2 * Real.pi * Complex.I / n)))
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  refine ⟨a, ha, fun z hz => ?_⟩
  obtain ⟨b, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
  rw [map_pow, ← h, ← pow_mul, ← pow_mul, mul_comm a b]

theorem exists_conj_pow {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) : ∃ n : ℕ, ∀ τ : ℂ ≃+* ℂ, ∃ a, a < n ∧
    (∀ x, (((L.xi t ^ a) x : Circle) : ℂ) = τ ((L.xi t x : Circle) : ℂ)) ∧ ∃ b, (L.xiH t ^ a) ^ b = L.xiH t := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 : ∀ x, ((L.xi t x : Circle) : ℂ) ^ n = 1 := fun x => by
    have := DFunLike.congr_fun (pow_eq_one_of_chrEq (hL.xi t) ho) x
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    exact (map_pow Circle.coeHom _ _).symm.trans (congrArg _ this)
  have h2 : ∀ a x, (((L.xi t ^ a) x : Circle) : ℂ) = ((L.xi t x : Circle) : ℂ) ^ a := fun a x => by
    rw [MonoidHom.pow_apply]; exact map_pow Circle.coeHom _ _
  refine ⟨n, fun τ => ?_⟩
  obtain ⟨a, ha, h⟩ := exists_pow_aut τ hn
  obtain ⟨b, -, h'⟩ := exists_pow_aut τ.symm hn
  refine ⟨a, ha, fun x => by rw [h2, h _ (h1 x)], b, ?_⟩
  have e : (L.xi t ^ a) ^ b = L.xi t := MonoidHom.ext fun x => Circle.ext (by
    rw [← pow_mul, h2, pow_mul, ← h _ (h1 x), ← h' _ (by rw [← map_pow, h1, map_one]), RingEquiv.symm_apply_apply])
  exact GlobalTheory.ChrEqUnique.hchar_unique D (L.xi t) _ _ (e ▸ chrEq_pow (chrEq_pow (hL.xi t) a) b) (hL.xi t)

def SamePlaces (L : LevCh D T) (S : Set (ℂ ≃+* ℂ)) : Prop :=
  ∀ (t t' : T) (τ τ' : ℂ ≃+* ℂ), τ ∈ S → (τ' ∈ S ∨ τ' = RingEquiv.refl ℂ) →
    (∀ x, τ ((L.xi t x : Circle) : ℂ) = τ' ((L.xi t' x : Circle) : ℂ)) → L.Q t' = L.Q t

end GlobalTheory.ConjExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisInnerProductKernelIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rallis_inner_product_kernel_identity : ∀ D : D7, KerAbs D → SWPair D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ h, IntegrableOn (fun g => star (thetaKO om h g f₁) * φ₁ g) 𝓖 νW) ∧ IntegrableOn (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) 𝓗 νV ∧ ∫ h in 𝓗, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂νV = ((νV 𝓗).toReal : ℂ) * ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  first | exact @GlobalTheory.RawLift.rallis_kernel_step | exact GlobalTheory.RawLift.rallis_kernel_step | (intros; apply GlobalTheory.RawLift.rallis_kernel_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermStronglyMeasurableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_lagrangian_term_stronglyMeasurable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E, StronglyMeasurable (fun p : GA D W × GA D W => lagTerm μ 𝓕 C (om (1, p.1) f₁) (om (1, p.2) f₂)) := by
  first | exact @GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable | exact GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable | (intros; apply GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable <;> assumption)
end

