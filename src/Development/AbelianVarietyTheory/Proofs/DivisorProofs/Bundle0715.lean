import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0706
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0693
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqOneAddOfSq
section
set_option autoImplicit false

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer

theorem dpExp_eq_one_add_of_sq {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type}
    [CommRing C] {J : Ideal C} (δ : DividedPowers J) (ρ : Hol W →+* C) {x : C} (hx : x ∈ J)
    (hx2 : x * x = 0) : dpExp δ x = 1 + x := by
  have hv : ∀ n, 2 ≤ n → δ.dpow n x = 0 := by
    intro n hn
    have hu : IsUnit ((n.factorial : ℕ) : C) := by
      have h1 : IsUnit ((n.factorial : ℕ) : Hol W) := by
        rw [← map_natCast (algebraMap ℂ (Hol W))]
        exact (IsUnit.mk0 _ (by exact_mod_cast (Nat.factorial_ne_zero n))).map _
      simpa using h1.map ρ
    have hp : x ^ n = 0 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, sq, hx2, zero_mul]
    have := δ.factorial_mul_dpow_eq_pow hx (n := n)
    rw [hp] at this
    exact (hu.mul_right_eq_zero).1 this
  rw [dpExp_eq_sum_range_of_vanish δ x 2 hv]
  simp [Finset.sum_range_succ, δ.dpow_zero hx, δ.dpow_one hx]

theorem step_exp {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C]
    {J : Ideal C} {ρ ρ' : Hol W →+* C} (s : Step J ρ ρ') (e l : Hol W)
    (he : ∀ a, dw a e = dw a l * e) :
    ρ' l - ρ l ∈ J ∧ (ρ' l - ρ l) * (ρ' l - ρ l) = 0 ∧ ρ' e = ρ e * (1 + (ρ' l - ρ l)) := by
  obtain ⟨n, h1, h2, h3⟩ := s
  have hx : ρ' l - ρ l = ∑ a, ρ (dw a l) * n a := by rw [h3 l]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hx]; exact J.sum_mem fun a _ ↦ J.mul_mem_left _ (h1 a)
  · rw [hx, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
    rw [mul_mul_mul_comm, h2, mul_zero]
  · rw [hx, h3 e, mul_add, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [he, map_mul]; ring

theorem close_exp : ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C]
    (J : Ideal C) (δ : DividedPowers J), IsNilDP δ → ∀ (ρ₁ ρ₂ : Hol W →+* C) (e l : Hol W),
    (∀ a, dw a e = dw a l * e) → Close J ρ₁ ρ₂ → ρ₂ e = ρ₁ e * dpExp δ (ρ₂ l - ρ₁ l) := by
  intro I _ g W C _ J δ hδ ρ₁ ρ₂ e l he hc
  induction hc with
  | refl => rw [sub_self, dpExp_zero, mul_one]
  | @tail ρ ρ' hc' s ih =>
    obtain ⟨hxJ, hx2, hρ'⟩ := step_exp s e l he
    have hyJ : ρ l - ρ₁ l ∈ J := Close.sub_mem hc' l
    rw [show ρ' l - ρ₁ l = (ρ l - ρ₁ l) + (ρ' l - ρ l) by ring,
      hδ.dpExp_add_eq_mul hyJ hxJ, dpExp_eq_one_add_of_sq δ ρ₁ hxJ hx2, hρ', ih, mul_assoc]

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPairingChartPartialDerivativeModMaxStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_pairing_chart_partial_derivative_mod_max : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m → ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) → ∀ (ψ : G.A n →ₗ[O] O) (H : MvPowerSeries (Fin d ⊕ Fin d) O), LinearMap.mul' O O (TensorProduct.map ψ φ.ofConv (c.ev₂ n H)) - ψ (c.ev n (∑ i, u i • atZero (pderiv O (Sum.inr i) H))) ∈ m := by
  first | exact @GlobalTheory.PairingEv.pairing_ev₂_sub_mem | exact GlobalTheory.PairingEv.pairing_ev₂_sub_mem | (intros; apply GlobalTheory.PairingEv.pairing_ev₂_sub_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallInvariantDifferentialDvd
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem dvd_of_forall_omega_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ)
    (a : O) (b : G.A n),
    (∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit O φ = w.1 n → a ∣ φ b) →
      (∃ z, b = a • z) ∧ ∀ w : G.dual.omega, ∃ φ : CartierDual O (G.A n), dUnit O φ = w.1 n := by
  intro p O _ G n a b h
  have hall : ∀ φ : CartierDual O (G.A n), a ∣ φ b := fun φ => by
    obtain ⟨w, hw⟩ := G.dual.omegaLevel_surjective n (dUnit O φ)
    exact h w φ hw.symm
  exact ⟨GlobalTheory.T.exists_smul_eq_of_forall_dual_dvd O (G.A n) a b (fun φ => hall (WithConv.toConv φ)),
    fun w => AugCot.d_surjective _ (w.1 n)⟩

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DwComapLinear
section
open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem AnPer.dw_comap_linear : ∀ {I I' : Type} [Fintype I] [Fintype I'] {g g' : ℕ} {W : Opens (Tot I g)} {W' : Opens (Tot I' g')} (b : (I' → ℂ) → I → ℂ) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ p ∈ W', AnalyticAt ℂ b p.1) → ∀ (hΦ : AnalyticOnNhd ℂ (fun p : Tot I' g' ↦ ((b p.1, M p.2) : Tot I g)) W') (h : ∀ p ∈ W', ((b p.1, M p.2) : Tot I g) ∈ W) (a : Fin g') (f : Hol W), dw a (Hol.comap _ hΦ h f) = ∑ c, M (Pi.single a 1) c • Hol.comap _ hΦ h (dw c f) := by
  intro I I' _ _ g g' W W' b M hb hΦ h a f
  refine Hol.ext_fn fun p hp ↦ ?_
  have e : HasFDerivAt (fun p : Tot I' g' ↦ ((b p.1, M p.2) : Tot I g))
      (((fderiv ℂ b p.1).comp (ContinuousLinearMap.fst ℂ _ _)).prod
        ((LinearMap.toContinuousLinearMap M).comp (ContinuousLinearMap.snd ℂ _ _))) p :=
    ((hb p hp).differentiableAt.hasFDerivAt.comp p hasFDerivAt_fst).prodMk
      ((LinearMap.toContinuousLinearMap M).hasFDerivAt.comp p hasFDerivAt_snd)
  have hv : ((0 : I → ℂ), M (Pi.single a 1)) = ∑ c, M (Pi.single a 1) c • (((0 : I → ℂ), Pi.single c 1) : Tot I g) := by
    ext i
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  change (Hol.der _ (Hol.comap _ hΦ h f)).fn p = _
  rw [Hol.fn_der_comap _ _ _ _ f hp, e.fderiv]
  have e2 : (((fderiv ℂ b p.1).comp (ContinuousLinearMap.fst ℂ _ _)).prod
        ((LinearMap.toContinuousLinearMap M).comp (ContinuousLinearMap.snd ℂ _ _)))
        (((0 : I' → ℂ), Pi.single a 1) : Tot I' g') = ((0 : I → ℂ), M (Pi.single a 1)) := by
    simp
  rw [e2, hv, map_sum, ← Hol.ev_apply p hp, map_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, Hol.ev_apply p hp, Hol.fn_comap _ _ _ _ hp]
  change _ = _ * (Hol.der _ f).fn _
  rw [Hol.fn_der _ _ (h p hp)]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity : GlobalTheory.EtC.B1 := by
  first | (exact @GlobalTheory.EtC.pairingProperties) | (exact GlobalTheory.EtC.pairingProperties) | (intros; apply GlobalTheory.EtC.pairingProperties  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEnlargeByUniformiserRoots
section
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlarge

theorem etale_enlarge : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hFits ρ hρ hpt
  have htor := hFits.2.2.2.2.2.2
  obtain ⟨a, ha0, ha⟩ := GlobalTheory.T.exists_ne_zero_closureEtaleAt_alt q A EA QA DA actA hq hFits.2.2.1 htor
  obtain ⟨A₁, _, _, _, _, _, _, f, i₁, hf, hi₁, hloc₁, hcomp, hK⟩ :=
    GlobalTheory.T.exists_kummerEnlargement_rootsOfUniformisers T hT q hq hqT A i hFits.1 hFits.2.1 a ha0
  obtain ⟨EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, actA₁, hFits₁, ⟨ρ₁, hρ₁, hpt₁⟩, hEt, β, h, hβ, hh⟩ :=
    GlobalTheory.T.baseChange_integralClosure_etale_height_one T O hT P φ hφ hsh hP q hq hqT A i EA QA jA ψA DA actA hFits ρ hρ hpt a ha0 ha
      A₁ f i₁ hf hi₁ hloc₁ hcomp hK
  refine ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, i₁,
    EA₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₁, inferInstance, jA₁, ψA₁,
    DA₁, inferInstance, inferInstance, actA₁, hFits₁, ⟨ρ₁, hρ₁, ?_⟩, β, h, hβ, hh⟩
  exact (GlobalTheory.KeyOriginEnlarge.good_iff_etaleAt _ _ _ _).2
    ⟨GlobalTheory.T.integralClosureEtaleAt_of_height_le_one_purity q A₁ EA₁ QA₁ DA₁ actA₁ hFits₁.2.2.2.2.2.2 hEt, hpt₁⟩

end GlobalTheory.KeyOriginEnlarge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHolomorphicIffChartHolomorphic
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem holo_etale_iff_holo_chart : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ (Ω : Set Y) (u : Y → ℂ), IsOpen Ω → ((∀ e : OpenPartialHomeomorph U (V n), IsChart n (fun y : U => z y) e → DifferentiableOn ℂ ((fun y : U => u y) ∘ e.symm) (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω))) ↔ ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE Ω u hΩ
  have hloc := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  constructor
  · intro h i v hv
    obtain ⟨hvt, hvU, hvΩ⟩ := hv
    obtain ⟨e, hes, hez⟩ := hloc ⟨(A.chart i).symm v, hvU⟩
    have he : IsChart n (fun y : U => z y) e := fun w _ => by rw [hez]
    have hev : ∀ w : U, e w = z w := fun w => by rw [← hez]
    obtain ⟨W, hW, hWe⟩ := isOpen_induced_iff.1 e.open_source
    have hO : IsOpen (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω)) :=
      e.isOpen_inter_preimage_symm (hΩ.preimage continuous_subtype_val)
    have hmem : z ((A.chart i).symm v) ∈ e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω) := by
      have h1 := hev ⟨(A.chart i).symm v, hvU⟩
      simp only at h1
      rw [← h1]
      refine ⟨e.map_source hes, ?_⟩
      simp only [Set.mem_preimage]
      rw [e.left_inv hes]
      exact hvΩ
    have h1 : DifferentiableAt ℂ ((fun y : U => u y) ∘ e.symm) (z ((A.chart i).symm v)) :=
      (h e he _ hmem).differentiableAt (hO.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (z ∘ (A.chart i).symm) v :=
      (hE.holo i v ⟨hvt, hvU⟩).differentiableAt
        (((A.chart i).isOpen_inter_preimage_symm hE.isOpen).mem_nhds ⟨hvt, hvU⟩)
    have h3 := DifferentiableAt.comp v (g := (fun y : U => u y) ∘ e.symm)
      (f := z ∘ (A.chart i).symm) h1 h2
    refine (h3.congr_of_eventuallyEq ?_).differentiableWithinAt
    have hvW : (A.chart i).symm v ∈ W := by
      rw [← hWe] at hes
      exact hes
    filter_upwards [((A.chart i).isOpen_inter_preimage_symm (hE.isOpen.inter hW)).mem_nhds
      ⟨hvt, hvU, hvW⟩] with v' hv'
    have hs : (⟨(A.chart i).symm v', hv'.2.1⟩ : U) ∈ e.source := by
      rw [← hWe]
      exact hv'.2.2
    have h4 := hev ⟨(A.chart i).symm v', hv'.2.1⟩
    simp only at h4
    simp only [Function.comp]
    rw [← h4, e.left_inv hs]
  · intro h e he v hv
    obtain ⟨hvt, hvΩ⟩ := hv
    have hs := A.mem_pick (e.symm v : U)
    set i := A.pick (e.symm v : U)
    obtain ⟨hc, hev, -⟩ := GlobalTheory.T.contDiffAt_chart_inverse_of_etale n Y ι La A U z hE e he v hvt i hs
    have hmem : A.chart i (e.symm v : U) ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) := by
      refine ⟨(A.chart i).map_source hs, ?_⟩
      simp only [Set.mem_preimage]
      rw [(A.chart i).left_inv hs]
      exact ⟨(e.symm v).2, hvΩ⟩
    have h1 : DifferentiableAt ℂ (u ∘ (A.chart i).symm) (A.chart i (e.symm v : U)) :=
      (h i _ hmem).differentiableAt
        (((A.chart i).isOpen_inter_preimage_symm (hE.isOpen.inter hΩ)).mem_nhds hmem)
    have h3 := DifferentiableAt.comp v (g := u ∘ (A.chart i).symm)
      (f := fun v' => A.chart i (e.symm v' : U)) h1 (hc.differentiableAt (by simp))
    refine (h3.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hev] with v' hv'
    simp only [Function.comp]
    rw [(A.chart i).left_inv hv']

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfFilteredColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.PolyColim

variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0})

def polyDiag : J ⥤ CommRingCat.{0} where
  obj j := CommRingCat.of (Polynomial (D.obj j))
  map f := CommRingCat.ofHom (Polynomial.mapRingHom (D.map f).hom)
  map_id j := by
    refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    simp
  map_comp f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    simp [Polynomial.map_map]

def polyCocone (c : Cocone D) : Cocone (polyDiag D) where
  pt := CommRingCat.of (Polynomial c.pt)
  ι :=
    { app := fun j => CommRingCat.ofHom (Polynomial.mapRingHom (c.ι.app j).hom)
      naturality := fun i j f => by
        refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
        exact (Polynomial.map_map (D.map f).hom (c.ι.app j).hom (show Polynomial (D.obj i) from p)).trans
          (congrArg (fun g => Polynomial.map g (show Polynomial (D.obj i) from p))
            (by rw [← CommRingCat.hom_comp, c.w f])) }

variable {D} [IsFiltered J]

open CategoryTheory Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
private lemma exists_map_eq_zero_of_isColimit_lemma {c : Cocone D} (hc : IsColimit c) {j : J}
    (x : D.obj j) (h : (c.ι.app j).hom x = 0) : ∃ (k : J) (f : j ⟶ k), (D.map f).hom x = 0 := by
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc x 0 (by simpa using h)
  exact ⟨k, f, by simpa using hfg⟩

open CategoryTheory Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
theorem _root_.GlobalTheory.EtC.PolyColim.poly_exists_map_eq_zero {c : Cocone D} (hc : IsColimit c) {j : J}
    (p : Polynomial (D.obj j))
    (h : p.map (c.ι.app j).hom = 0) : ∃ (k : J) (f : j ⟶ k), p.map (D.map f).hom = 0 := by
  have key : ∀ s : Finset ℕ, ∃ (k : J) (f : j ⟶ k), ∀ n ∈ s, (D.map f).hom (p.coeff n) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨j, 𝟙 j, by simp⟩
    | insert a s _ ih =>
      obtain ⟨k, f, hf⟩ := ih
      have ha : (c.ι.app k).hom ((D.map f).hom (p.coeff a)) = 0 := by
        rw [← CommRingCat.comp_apply, c.w f, ← Polynomial.coeff_map, h, Polynomial.coeff_zero]
      obtain ⟨k', f', hf'⟩ := exists_map_eq_zero_of_isColimit_lemma hc _ ha
      refine ⟨k', f ≫ f', fun n hn => ?_⟩
      rw [D.map_comp, CommRingCat.comp_apply]
      rcases Finset.mem_insert.mp hn with rfl | hn
      · exact hf'
      · rw [hf n hn, map_zero]
  obtain ⟨k, f, hf⟩ := key p.support
  refine ⟨k, f, Polynomial.ext fun n => ?_⟩
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  by_cases hn : n ∈ p.support
  · exact hf n hn
  · rw [Polynomial.notMem_support_iff.mp hn, map_zero]

open CategoryTheory Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
private lemma exists_rep_of_isColimit_lemma_2 {c : Cocone D} (hc : IsColimit c) (x : c.pt) :
    ∃ (j : J) (y : D.obj j), (c.ι.app j).hom y = x := by
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep D hc x
  exact ⟨j, y, hy⟩

open CategoryTheory Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
theorem _root_.GlobalTheory.EtC.PolyColim.poly_exists_rep {c : Cocone D} (hc : IsColimit c)
    (p : Polynomial c.pt) :
    ∃ (j : J) (y : Polynomial (D.obj j)), y.map (c.ι.app j).hom = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨i, y, hy⟩ := hp
    obtain ⟨j, z, hz⟩ := hq
    refine ⟨IsFiltered.max i j, y.map (D.map (IsFiltered.leftToMax i j)).hom +
      z.map (D.map (IsFiltered.rightToMax i j)).hom, ?_⟩
    rw [Polynomial.map_add, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, c.w, c.w, hy, hz]
  | monomial n a =>
    obtain ⟨j, y, hy⟩ := exists_rep_of_isColimit_lemma_2 hc a
    exact ⟨j, Polynomial.monomial n y, by rw [Polynomial.map_monomial, hy]⟩

def polyCoconeIsColimit {c : Cocone D} (hc : IsColimit c) : IsColimit (polyCocone D c) := by
  haveI : ReflectsColimitsOfShape J (forget CommRingCat.{0}) := reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (polyCocone D c)) ?_ ?_)
  · intro x
    obtain ⟨j, y, hy⟩ := poly_exists_rep hc (show Polynomial c.pt from x)
    exact ⟨j, y, hy.symm⟩
  · intro i j xi xj h
    change Polynomial.map (c.ι.app i).hom xi = Polynomial.map (c.ι.app j).hom xj at h
    obtain ⟨k, f, hf⟩ := poly_exists_map_eq_zero hc (j := IsFiltered.max i j)
      ((show Polynomial (D.obj i) from xi).map (D.map (IsFiltered.leftToMax i j)).hom -
        (show Polynomial (D.obj j) from xj).map (D.map (IsFiltered.rightToMax i j)).hom) (by
        rw [Polynomial.map_sub, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
          ← CommRingCat.hom_comp, c.w, c.w, h, sub_self])
    refine ⟨k, IsFiltered.leftToMax i j ≫ f, IsFiltered.rightToMax i j ≫ f, ?_⟩
    change Polynomial.map (D.map (IsFiltered.leftToMax i j ≫ f)).hom xi =
      Polynomial.map (D.map (IsFiltered.rightToMax i j ≫ f)).hom xj
    rw [Polynomial.map_sub, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp, sub_eq_zero] at hf
    exact hf

end GlobalTheory.EtC.PolyColim

namespace GlobalTheory.EtC

theorem pull_spMap_comp (R : Type) [CommRing R] {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (F : Shv R) (n : ℤ) (x : H R (sp A) F n) :
    pull R (spMap (g.comp f)) F n x = pull R (spMap g) F n (pull R (spMap f) F n x) := by
  show pull R (sch.map _) F n x = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp, pull_comp]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show sch.map _ = sch.map _ ≫ sch.map _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem hInv_of_filtered_colimit : ∀ (q : ℕ) [NeZero q] (J : Type) [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ j, IsUnit (q : D.obj j)) →
    (∀ j, HInv q (D.obj j)) → HInv q c.pt := by
  intro q _ J _ _ D c hc hq hH i n
  have hB : B1 := pairingProperties
  let D' := PolyColim.polyDiag D
  let c' := PolyColim.polyCocone D c
  have hc' : IsColimit c' := PolyColim.polyCoconeIsColimit hc
  obtain ⟨j0⟩ : Nonempty J := IsFiltered.nonempty
  have hqc : IsUnit (q : c.pt) := by
    have := (hq j0).map (c.ι.app j0).hom
    rwa [map_natCast] at this
  have hqP : ∀ j, IsUnit (q : D'.obj j) := fun j => by
    have := (hq j).map (Polynomial.C : D.obj j →+* Polynomial (D.obj j))
    rwa [map_natCast] at this
  have hqc' : IsUnit (q : c'.pt) := by
    have := hqc.map (Polynomial.C : c.pt →+* Polynomial c.pt)
    rwa [map_natCast] at this
  have sq : ∀ j, (c'.ι.app j).hom.comp (Polynomial.C : D.obj j →+* Polynomial (D.obj j)) =
      (Polynomial.C : c.pt →+* Polynomial c.pt).comp (c.ι.app j).hom := fun j =>
    RingHom.ext fun a => by
      change Polynomial.map (c.ι.app j).hom (Polynomial.C a) = Polynomial.C ((c.ι.app j).hom a)
      exact Polynomial.map_C _
  have sqD : ∀ {j k : J} (f : j ⟶ k), (D'.map f).hom.comp (Polynomial.C : D.obj j →+* Polynomial (D.obj j)) =
      (Polynomial.C : D.obj k →+* Polynomial (D.obj k)).comp (D.map f).hom := @fun j k f =>
    RingHom.ext fun a => by
      change Polynomial.map (D.map f).hom (Polynomial.C a) = Polynomial.C ((D.map f).hom a)
      exact Polynomial.map_C _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, rfl⟩ := (hB q D c hc n i).1 x hqc
    have e1 : pull _ (spMap (c'.ι.app j).hom) _ _ (pull _ (spMap (Polynomial.C : D.obj j →+* Polynomial (D.obj j))) _ _ y) = 0 :=
      (pull_spMap_comp (ZMod q) Polynomial.C (c'.ι.app j).hom (tw q i) n y).symm.trans
        ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y) (sq j)).trans
          ((pull_spMap_comp (ZMod q) (c.ι.app j).hom Polynomial.C (tw q i) n y).trans hx))
    obtain ⟨k, f, hf⟩ := (hB q D' c' hc' n i).2 j _ (hqP j) e1
    have e2 : pull _ (spMap (Polynomial.C : D.obj k →+* Polynomial (D.obj k))) _ _ (pull _ (spMap (D.map f).hom) _ _ y) = 0 :=
      (pull_spMap_comp (ZMod q) (D.map f).hom Polynomial.C (tw q i) n y).symm.trans
        ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y) (sqD f).symm).trans
          ((pull_spMap_comp (ZMod q) Polynomial.C (D'.map f).hom (tw q i) n y).trans hf))
    have e3 := (hH k i n).1 (e2.trans (map_zero _).symm)
    rw [← c.w f, CommRingCat.hom_comp, spMap_comp', pull_comp, e3, map_zero]
  · intro x
    obtain ⟨j, y, rfl⟩ := (hB q D' c' hc' n i).1 x hqc'
    obtain ⟨y', rfl⟩ := (hH j i n).2 y
    refine ⟨pull _ (spMap (c.ι.app j).hom) _ _ y', ?_⟩
    exact (pull_spMap_comp (ZMod q) (c.ι.app j).hom Polynomial.C (tw q i) n y').symm.trans
      ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y') (sq j).symm).trans
        (pull_spMap_comp (ZMod q) Polynomial.C (c'.ι.app j).hom (tw q i) n y'))

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvResCounitCompatStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ev_res_counit_compat : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n, (∀ f, G.res n (c.ev (n + 1) f) = c.ev n f ∧ Coalgebra.counit (R := O) (c.ev n f) = constantCoeff f) ∧ ∀ s, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O (G.A n)) (Bialgebra.counitAlgHom O (G.A n)) (fun _ _ => Commute.all _ _) (c.ev₂ n s) = constantCoeff s := by
  first | exact @GlobalTheory.QLog.Chart.ev_res_counit | exact GlobalTheory.QLog.Chart.ev_res_counit | (intros; apply GlobalTheory.QLog.Chart.ev_res_counit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomAlgebraicClosureApplyEqPowStatement
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_algebraicClosure_apply_eq_pow' : ∀ (Ω : Type) [Field Ω] (K0 : Subfield Ω) (x : Ω), Transcendental K0 x → ∀ m : ℕ, 0 < m → ∃ τ : Ω →ₐ[K0] AlgebraicClosure Ω, τ x = algebraMap Ω (AlgebraicClosure Ω) x ^ m := by
  first | exact @GlobalTheory.exists_algHom_algebraicClosure_apply_eq_pow | exact GlobalTheory.exists_algHom_algebraicClosure_apply_eq_pow | (intros; apply GlobalTheory.exists_algHom_algebraicClosure_apply_eq_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCob1WittLiftModPStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cob1_witt_lift_mod_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c → ∀ w : Fin d → k, ∃ f ∈ intBy p k (Fin d) 1, RedV p (lin f) w ∧ ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < 2 → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w) := by
  first | exact @GlobalTheory.WittStart.start | exact GlobalTheory.WittStart.start | (intros; apply GlobalTheory.WittStart.start <;> assumption)
end

