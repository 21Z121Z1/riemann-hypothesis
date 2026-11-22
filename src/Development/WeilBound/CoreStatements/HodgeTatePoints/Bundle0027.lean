import Development.WeilBound.CoreStatements.HodgeTatePoints.GdDual
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0024

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GdChart
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

section SlopeTestRemainingChoices

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {C O : Type} [Field C] [CommRing O]
  [Algebra O C] {E : Type} [Field E] [NumberField E]

theorem map_mem_span (φ : A →+* O) (ψ : K →+* C)
    (h : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a)) {S : Set K} {S' : Set C}
    (hS : ∀ x ∈ S, ψ x ∈ S') {x : K} (hx : x ∈ Submodule.span A S) : ψ x ∈ Submodule.span O S' := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hS x hx)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, map_mul, h, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hx

theorem generatesDiff_map (φ : A →+* O) (ψ : K →+* C)
    (h : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a)) {σ : E →+* K} {d : A}
    (hd : GeneratesDiff σ d) : GeneratesDiff (ψ.comp σ) (φ d) := by
  unfold GeneratesDiff at hd ⊢
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, ← h]
    refine map_mem_span φ ψ h ?_ (hd.le (Submodule.mem_span_singleton_self _))
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine map_mem_span φ ψ h ?_ (hd.ge (Submodule.subset_span ⟨x, hx, rfl⟩))
    rintro _ rfl
    exact h d

theorem emb_mem [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A K] (σ : E →+* K) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A K).range :=
  IsIntegrallyClosed.isIntegral_iff.1
    ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)).tower_top)

variable {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Ω' : Type} [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']

theorem qgen_mem (σ : E →+* K) (l : Fin N) :
    eigProj D.ρΩ σ (D.h (Pi.single l 1)) ∈ D.omHT σ :=
  ⟨_, Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩), rfl⟩

theorem omHT_fg [IsNoetherianRing A] (σ : E →+* K) : (D.omHT σ).FG := by
  refine Submodule.FG.map _ (Submodule.FG.of_le D.om_lat.fg (sup_le ?_ ?_))
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩
    exact D.om.smul_mem _ hx

theorem tate_single {κ : O} (P : HTPoint C O c κ N V Ω') (l : Fin N) (a : 𝓞 E) :
    P.tate (Pi.single l a) = P.ρ a (P.t l) := by
  rw [HTPoint.tate, Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

variable [CharZero K] [CharZero C] {κ : O} {P : HTPoint C O c κ N V Ω'} {φ : A →+* O}
  {ι : D.om →ₛₗ[φ] Ω'}

theorem gen_at_point (hAK : Function.Injective (algebraMap A K))
    (hOC : Function.Injective (algebraMap O C)) (hφ : Function.Injective φ) (ψ : K →+* C)
    (h : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a)) (hred : D.ReducesTo φ P ι)
    {σ : E →+* K} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) {d : A}
    (hd : GeneratesDiff σ d) {π : O} (hπ : κ * π ∣ (p : O) ^ R) (J : D.omHT σ → Ω')
    (hJ : ∀ (z : D.omHT σ) (y : D.om), (y : Ω) = d • (z : Ω) → φ d • J z = ι y) (l : Fin N) :
    ∃ y ∈ P.omHT (ψ.comp σ), J ⟨_, qgen_mem D σ l⟩ =
      eigProj P.ρΩ (ψ.comp σ) (P.ht (P.t l)) + π • y := by
  obtain ⟨hd0, hdk, -⟩ := different_generator_dualInt A K E σ d hAK hσ hd
  choose u hu using hdk
  let y0 : D.om := ⟨D.h (Pi.single l 1), D.h_mem _⟩
  let y : D.om := ∑ k, u k • ⟨D.ρΩ (RingOfIntegers.basis E k) y0, D.om_stable _ _ y0.2⟩
  have h1 := hJ ⟨_, qgen_mem D σ l⟩ y (by
    simp only [y, eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
      Submodule.coe_sum, Submodule.coe_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul K (u k), hu, ← algebraMap_smul K d, smul_smul])
  have h2 : ι y = φ d • eigProj P.ρΩ (ψ.comp σ) (ι y0) := by
    simp only [y, eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, map_sum,
      LinearMap.map_smulₛₗ, hred.lin]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul C (φ (u k)), ← h, hu, ← algebraMap_smul C (φ d), smul_smul, map_mul, h]
    rfl
  have hd1 : algebraMap O C (φ d) ≠ 0 := by
    rw [← h]
    exact (map_ne_zero ψ).2 hd0
  have h3 : J ⟨_, qgen_mem D σ l⟩ = eigProj P.ρΩ (ψ.comp σ) (ι y0) := by
    rw [h2, ← algebraMap_smul C (φ d), ← algebraMap_smul C (φ d)] at h1
    exact smul_right_injective Ω' hd1 h1
  obtain ⟨y1, hy1, e1⟩ := hred.ht_eq (Pi.single l 1)
  obtain ⟨x1, hx1, e2⟩ := P.κ_mem y1 hy1
  obtain ⟨r, hr⟩ := hπ
  refine ⟨r • eigProj P.ρΩ (ψ.comp σ) (P.ht x1), Submodule.smul_mem _ _ (proj_ht_mem P _ hx1), ?_⟩
  rw [h3, e1, tate_single, map_one, Module.End.one_apply, map_add, e2, ← Nat.cast_smul_eq_nsmul O,
    Nat.cast_pow, hr, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, smul_smul, smul_smul]
  congr 2
  ring

theorem gram_at_point (hAK : Function.Injective (algebraMap A K)) (ψ : K →+* C)
    (h : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a)) (hred : D.ReducesTo φ P ι)
    {σ : E →+* K} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) {d : A}
    (hd : GeneratesDiff σ d) (l j : Fin N) :
    ∃ z : O, P.e (φ d • eigProj P.ρ (ψ.comp σ) (P.t l)) (P.t j) =
      ψ (D.gram σ d l j) + algebraMap O C ((p : O) ^ R * z) := by
  obtain ⟨-, hdk, -⟩ := different_generator_dualInt A K E σ d hAK hσ hd
  choose u hu using hdk
  choose z hz using hred.e_eq
  refine ⟨∑ k, φ (u k) * z (Pi.single l (RingOfIntegers.basis E k)) (Pi.single j 1), ?_⟩
  rw [← algebraMap_smul C (φ d)]
  simp only [eigProj, HTChart.gram, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, map_sum,
    map_smul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := hz (Pi.single l (RingOfIntegers.basis E k)) (Pi.single j 1)
  rw [tate_single, tate_single, map_one, Module.End.one_apply] at h1
  have h2 := congrArg ψ (hu k)
  rw [h, map_mul, h] at h2
  simp only [h1, smul_eq_mul, map_mul, map_add, map_natCast, h, h2, RingHom.comp_apply]
  ring

end SlopeTestRemainingChoices

theorem chart_comp_zero_of
    (hdiv : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω) (a b : A), M.FG → Module.Projective A M → x ∈ M → a ≠ 0 → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → a ∈ 𝔮 → b ∈ 𝔮) → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → b ∈ 𝔮 → ∃ s : A, s ∉ 𝔮 ∧ ∃ y ∈ M, s • x = a • y) → ∃ y ∈ M, x = a • y)
    (hdesc : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (𝔮 : Ideal A) (M : Type) [AddCommGroup M] [Module A M] (L : Submodule A M) (x : M), 𝔮.IsPrime → 𝔮.height = 1 → Function.Injective (algebraMap A O) → (∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (algebraMap A O a)) < 1) → (1 : O) ⊗ₜ[A] x ∈ Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ L)
    (hbc : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (κ' : O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[algebraMap A O] Ω') (hred : D.ReducesTo (algebraMap A O) P ι) (σ : E →+* K) (σ' : E →+* C) (d : A), (∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (algebraMap A O a') = σ' (a : E)) → GeneratesDiff σ d → κ' ∣ (p : O) ^ R → Module.Projective A (D.omHT σ) → ∃ j : O ⊗[A] (D.omHT σ) →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = P.omHT σ' ∧ (∀ (z : D.omHT σ) (y : D.om), (y : Ω) = d • (z : Ω) → algebraMap A O d • j (1 ⊗ₜ z) = ι y) ∧ Module.finrank A (D.omHT σ) = Module.finrank C (P.Ωsp σ')) :
    ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), κ * (p : A) ^ m ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → D.IsDualMap σ d m i → ∀ w, ∃ y ∈ D.omHT σ, D.q σ (i w) = ((p : A) ^ m) • y := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N hp Ω _ _ _ _ D κ σ d d' m i hκ hd hd' _ hP hP' htest hi w
  have hAK := IsFractionRing.injective A K
  have hq : D.q σ (i w) ∈ D.omHT σ :=
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (qgen_mem D σ l)
  refine hdiv A K Ω (D.omHT σ) _ ((p : A) ^ m) (p : A) (omHT_fg D σ) hP hq ?_
    (fun 𝔮 h𝔮 h => h𝔮.mem_of_pow_mem m h) fun 𝔮 h𝔮 hht hp𝔮 => ?_
  · refine pow_ne_zero _ fun h0 => hp.out.ne_zero ?_
    have := congrArg (algebraMap A K) h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  obtain ⟨C, O, _, _, _, _, _, v, φ, V, Ω', _, _, _, _, _, _, _, _, P, ι, hv, hφ, hcen, hred⟩ :=
    htest 𝔮 h𝔮 hht hp𝔮
  letI : Algebra A O := φ.toAlgebra
  have hOC := hv.hom_inj
  let ψ : K →+* C := IsFractionRing.lift (g := (algebraMap O C).comp φ) (hOC.comp hφ)
  have hψ : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a) := fun a => IsFractionRing.lift_algebraMap _ a
  have hκ' : φ κ * (p : O) ^ m ∣ (p : O) ^ R := by
    simpa using map_dvd φ hκ
  have hcomp : ∀ (τ : E →+* K) (a : 𝓞 E) (a' : A), algebraMap A K a' = τ (a : E) →
      algebraMap O C (algebraMap A O a') = (ψ.comp τ) (a : E) := fun τ a a' h => by
    rw [RingHom.comp_apply, ← h, hψ]
    rfl
  obtain ⟨j, hjinj, hjr, hj, -⟩ := hbc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred σ (ψ.comp σ) d
    (hcomp σ) hd (dvd_of_mul_right_dvd hκ') hP
  obtain ⟨j', hjinj', hjr', hj', -⟩ := hbc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred
    (σ.comp c.toRingHom) ((ψ.comp σ).comp c.toRingHom) d'
    (hcomp _) hd' (dvd_of_mul_right_dvd hκ') hP'
  choose y hy ey using gen_at_point D hAK hOC hφ ψ hψ hred (emb_mem σ) hd hκ' (fun z => j (1 ⊗ₜ z)) hj
  choose y' hy' ey' using gen_at_point D hAK hOC hφ ψ hψ hred (emb_mem _) hd' hκ'
    (fun z => j' (1 ⊗ₜ z)) hj'
  let eq' : (O ⊗[A] D.omHT (σ.comp c.toRingHom)) ≃ₗ[O] P.omHT ((ψ.comp σ).comp c.toRingHom) :=
    (LinearEquiv.ofInjective j' hjinj').trans (LinearEquiv.ofEq _ _ hjr')
  let wO : O ⊗[A] D.omHT (σ.comp c.toRingHom) →ₗ[O] O :=
    LinearMap.liftBaseChange O (Algebra.linearMap A O ∘ₗ w)
  let f : P.omHT ((ψ.comp σ).comp c.toRingHom) →ₗ[O] O := wO ∘ₗ eq'.symm.toLinearMap
  have hf : ∀ z, f (eq' (1 ⊗ₜ z)) = φ (w z) := fun z => by
    simp only [f, wO, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  obtain ⟨w', hw', ew'⟩ := exists_alt_bis hv hc P (ψ.comp σ) f
  have htT : ∀ l, P.t l ∈ P.T := fun l => by
    have h1 : P.t l = P.ρ 1 (P.t l) := by simp
    rw [h1, ← (RingOfIntegers.basis E).sum_repr 1, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    refine zsmul_mem ?_ _
    rw [P.free.2.2]
    exact Submodule.subset_span ⟨(l, k), rfl⟩
  obtain ⟨y1, hy1, e1⟩ := pt_comp_zero C v O hv E c hc (φ κ) N V Ω' P (ψ.comp σ) (φ d) ((p : O) ^ m)
    (fun l => φ (i w l)) w' (generatesDiff_map φ ψ hψ hd) hw' (fun l => by
      choose z hz using gram_at_point D hAK ψ hψ hred (emb_mem σ) hd
      obtain ⟨z1, hz1⟩ := hi w l ⟨_, qgen_mem D _ l⟩ rfl
      obtain ⟨r, hr⟩ := dvd_of_mul_left_dvd hκ'
      have h1 : eq' (1 ⊗ₜ ⟨_, qgen_mem D _ l⟩) = ⟨_, proj_ht_mem P _ (htT l)⟩ +
          ((p : O) ^ m) • ⟨y' l, hy' l⟩ := Subtype.ext (ey' l)
      have h2 := hf ⟨_, qgen_mem D _ l⟩
      rw [h1, map_add, map_smul] at h2
      have h3 := congrArg ψ hz1
      rw [hψ, map_add, map_mul, map_pow, map_natCast, ← h2, map_sum] at h3
      refine ⟨f ⟨y' l, hy' l⟩ + φ z1 + ∑ k, φ (i w k) * (r * z k l), ?_⟩
      simp only [hz, ew' _ (htT l), mul_add, Finset.sum_add_distrib, map_mul, hψ, hr] at h3 ⊢
      rw [h3]
      simp only [map_add, map_mul, map_sum, smul_eq_mul, Finset.mul_sum, add_assoc]
      congr 3
      refine Finset.sum_congr rfl fun k _ => ?_
      ring)
  have h2 : j (1 ⊗ₜ ⟨_, hq⟩) = ((p : O) ^ m) • (y1 + ∑ l, φ (i w l) • y l) := by
    have : (⟨_, hq⟩ : D.omHT σ) = ∑ l, i w l • ⟨_, qgen_mem D σ l⟩ := Subtype.ext (by
      simp [HTChart.q])
    rw [this, TensorProduct.tmul_sum, map_sum, smul_add, ← e1, Finset.smul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [TensorProduct.tmul_smul, ← algebraMap_smul O (i w l), map_smul, ey, smul_add, smul_comm]
    rfl
  have h3 : y1 + ∑ l, φ (i w l) • y l ∈ LinearMap.range j := by
    rw [hjr]
    exact Submodule.add_mem _ hy1 (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hy l))
  obtain ⟨t, ht⟩ := h3
  rw [← ht, ← map_smul] at h2
  have h4 := hjinj h2
  obtain ⟨s, hs, u, hu⟩ := hdesc A K C v O hv 𝔮 (D.omHT σ)
    (LinearMap.range (((p : A) ^ m) • LinearMap.id)) ⟨_, hq⟩ h𝔮 hht hφ hcen (by
      rw [h4]
      clear h4 h2 ht
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
      | tmul a b =>
        have : ((p : O) ^ m) • (a ⊗ₜ[A] b) = a • ((1 : O) ⊗ₜ[A] (((p : A) ^ m) • b)) := by
          rw [TensorProduct.tmul_smul, ← algebraMap_smul O ((p : A) ^ m), map_pow, map_natCast,
            smul_comm, TensorProduct.smul_tmul' a, smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨b, rfl⟩, rfl⟩))
  exact ⟨s, hs, u, u.2, (congrArg Subtype.val hu).symm⟩

end PositivityTheory.HtPt.Gd
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfLin
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Htat.QuotientDualMap

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (v : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt v ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (v.appTop.hom s) := by
  rfl

theorem valAt_spec_comp {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (φ : B →+* C)
    (v : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ v) ⊤ le_top s = φ (valAt v ⊤ le_top s) := by
  rw [valAt_top, valAt_top, Scheme.Hom.comp_appTop]
  exact congrArg (fun f => f.hom (v.appTop.hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem valAt_mul [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {B : Type} [CommRing B]
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (y z : Over.mk q ⟶ Γ.G) :
    valAt (B := B) (y * z).left ⊤ le_top s =
      valAt (B := B) y.left ⊤ le_top s * valAt (B := B) z.left ⊤ le_top s := by
  have h := (PositivityTheory.HtPt.Htat.ht_char_mul R T Γ χ s hs (Over.mk q)).1 y z
  rw [valAt_top, valAt_top, valAt_top, ← map_mul]
  exact congrArg _ h

theorem valAt_one [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {B : Type} [CommRing B]
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) :
    valAt (B := B) (1 : Over.mk q ⟶ Γ.G).left ⊤ le_top s = 1 := by
  have h := (PositivityTheory.HtPt.Htat.ht_char_mul R T Γ χ s hs (Over.mk q)).2
  rw [valAt_top]
  refine (congrArg _ h).trans ?_
  exact map_one _

theorem tors_one {Γ : QFGroup R T} {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i)
    (Y : Over (Spec (CommRingCat.of R))) :
    (1 : Y ⟶ Γ.G).left ≫ i = (1 : Over.mk (Y.hom ≫ x) ⟶ G).left := by
  let y₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk ((1 : Y ⟶ Γ.G).left ≫ i) (by
    show ((1 : Y ⟶ Γ.G).left ≫ i) ≫ G.hom = Y.hom ≫ x
    rw [Category.assoc, h.isOver, ← Category.assoc, Over.w])
  have h1 := h.mul Y 1 1 y₀ y₀ rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : y₀ * y₀ = y₀ * 1 := by
    rw [_root_.mul_one]
    exact Over.OverMorphism.ext h1
  have h3 : y₀ = 1 := mul_left_cancel h2
  exact congrArg (fun f => f.left) h3

section Tangent

variable {A : Type} [CommRing A] (π : R →+* A)

abbrev qMap : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap A (DualNumber A)).comp π))

abbrev dMap : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of (DualNumber R)) :=
  Spec.map (CommRingCat.ofHom (dualMap π))

theorem dMap_over : dMap π ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = qMap π := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul (c : R) :
    (epsMul (π c)).comp (dualMap π) = (dualMap π).comp (epsMul c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

theorem epsMul_algebraMap (c : A) : (epsMul c).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_dualMap : ((TrivSqZeroExt.fstHom A A A).toRingHom).comp (dualMap π) =
    π.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [dualMap]

theorem fst_q : ((TrivSqZeroExt.fstHom A A A).toRingHom).comp ((algebraMap A (DualNumber A)).comp π) = π := by
  refine RingHom.ext fun a => ?_
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  {L : Type} [AddCommGroup L] [Module R L]

def IsTan (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left) (M : LieModel G x L) (e : L)
    (v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left) : Prop :=
  v ≫ Γ.G.hom = qMap π ∧ v ≫ i = dMap π ≫ (M.pt e).left

variable {π} {N : ℕ} {Γ : QFGroup R T} {i : Γ.G.left ⟶ G.left} {M : LieModel G x L}

theorem fst_valAt [Finite T] (h : Γ.IsTorsionAlong G x N i) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {e : L}
    {v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left} (hv : IsTan π Γ i M e v) :
    (valAt v ⊤ le_top s).fst = 1 := by
  let r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom π)
  let p : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (DualNumber A)) :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom)
  have hpq : p ≫ qMap π = r := by
    simp only [p, r, qMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_q]
  let y : Over.mk r ⟶ Γ.G := Over.homMk (p ≫ v) (by
    show (p ≫ v) ≫ Γ.G.hom = r
    rw [Category.assoc, hv.1, hpq])
  have hy : y = 1 := by
    apply h.inj (Over.mk r)
    rw [tors_one h]
    have hp : p ≫ dMap π = r ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
      simp only [p, r, dMap]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, fst_dualMap]
    let w : Over.mk (r ≫ x) ⟶ Over.mk x := Over.homMk r rfl
    have h1 : (w ≫ (1 : Over.mk x ⟶ G)).left = r ≫ (1 : Over.mk x ⟶ G).left := rfl
    rw [comp_one] at h1
    show (p ≫ v) ≫ i = (1 : Over.mk (r ≫ x) ⟶ G).left
    rw [h1, Category.assoc, hv.2, ← Category.assoc, hp, Category.assoc]
    exact congrArg (r ≫ ·) (M.tan e)
  have h2 : valAt (p ≫ v) ⊤ le_top s = 1 := by
    have h3 := valAt_one Γ χ s hs r
    rw [← hy] at h3
    exact h3
  have h4 := valAt_spec_comp (TrivSqZeroExt.fstHom A A A).toRingHom v s
  exact h4.symm.trans h2

theorem isTan_add [Finite T] (h : Γ.IsTorsionAlong G x N i) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {e e' : L}
    {v v' : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left} (hv : IsTan π Γ i M e v)
    (hv' : IsTan π Γ i M e' v') :
    ∃ w, IsTan π Γ i M (e + e') w ∧ valAt w ⊤ le_top s = valAt v ⊤ le_top s * valAt v' ⊤ le_top s := by
  let y : Over.mk (qMap π) ⟶ Γ.G := Over.homMk v hv.1
  let z : Over.mk (qMap π) ⟶ Γ.G := Over.homMk v' hv'.1
  let ρ : Over.mk (qMap π ≫ x) ⟶ epsAt x := Over.homMk (dMap π) (by
    show dMap π ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x = qMap π ≫ x
    rw [← Category.assoc, dMap_over])
  have hm := h.mul (Over.mk (qMap π)) y z (ρ ≫ M.pt e) (ρ ≫ M.pt e') hv.2.symm hv'.2.symm
  rw [← comp_mul, ← M.add] at hm
  exact ⟨(y * z).left, ⟨Over.w (y * z), hm.symm⟩, valAt_mul Γ χ s hs (qMap π) y z⟩

theorem isTan_smul (c : R) {e : L} {v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left}
    (hv : IsTan π Γ i M e v) :
    IsTan π Γ i M (c • e) (Spec.map (CommRingCat.ofHom (epsMul (π c))) ≫ v) := by
  constructor
  · rw [Category.assoc, hv.1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, epsMul_algebraMap]
  · rw [Category.assoc, hv.2, M.smul, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, dualMap_epsMul]

end Tangent

theorem snd_epsMul {A : Type} [CommRing A] (c : A) (a : DualNumber A) :
    (epsMul c a).snd = c * a.snd := by
  simp [epsMul]

theorem fst_epsMul {A : Type} [CommRing A] (c : A) (a : DualNumber A) :
    (epsMul c a).fst = a.fst := by
  simp [epsMul]

theorem char_on_tangent_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) → ∃ l : L →ₗ[R] (R ⧸ Ideal.span {(N : R)}), ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l e) := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M χ s hs
  have hex : ∀ e : L, ∃ v, IsTan (Ideal.Quotient.mk (Ideal.span {(N : R)})) Γ i M e v ∧
      ∀ w, IsTan (Ideal.Quotient.mk (Ideal.span {(N : R)})) Γ i M e w → w = v :=
    fun e => GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i h L M e
  choose v hv hu using hex
  have hfst : ∀ e, (valAt (v e) ⊤ le_top s).fst = 1 := fun e => fst_valAt h χ s hs (hv e)
  refine ⟨{ toFun := fun e => (valAt (v e) ⊤ le_top s).snd, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro e e'
    obtain ⟨w, hw, hval⟩ := isTan_add h χ s hs (hv e) (hv e')
    rw [← hu _ w hw, hval, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [add_comm]
  · intro c e
    have h1 := hu _ _ (isTan_smul c (hv e))
    rw [← h1, valAt_spec_comp, snd_epsMul]
    simp [Algebra.smul_def]
  · intro e w hw
    rw [hu e w hw]
    ext
    · simp [hfst]
    · simp

end PositivityTheory.HtPt.Htat.QuotientDualMap

theorem PositivityTheory.HtPt.Htat.ht_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) → ∃ l : L →ₗ[R] (R ⧸ Ideal.span {(N : R)}), ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l e) :=
  @PositivityTheory.HtPt.Htat.QuotientDualMap.char_on_tangent_linear
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinMany
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinMany.JoinMany

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
  {A : Type} [Fintype A] {κa : A → Type} (w : ∀ a, κa a → Ω)

theorem inChart_prod_of_forall (p : Cpt ξ) (h : ∀ a, ∃ l, InChart ξ (w a) l p) :
    ∃ c, InChart ξ (fun c : (∀ a, κa a) => ∏ a, w a (c a)) c p := by
  choose c hc using h
  refine ⟨c, Finset.prod_ne_zero_iff.2 fun a _ => (hc a).1, fun c' => ?_⟩
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun a _ => (hc a).2 (c' a)

theorem inChart_of_inChart_prod [DecidableEq A] {p : Cpt ξ} {c : ∀ a, κa a}
    (h : InChart ξ (fun c : (∀ a, κa a) => ∏ a, w a (c a)) c p) (a : A) : InChart ξ (w a) (c a) p := by
  obtain ⟨h0, h1⟩ := h
  have hne : ∀ b, w b (c b) ≠ 0 := fun b => (Finset.prod_ne_zero_iff.1 h0) b (Finset.mem_univ b)
  refine ⟨hne a, fun l => ?_⟩
  have key : (∏ b, w b (Function.update c a l b)) / (∏ b, w b (c b)) = w a l / w a (c a) := by
    rw [← Finset.prod_div_distrib, Fintype.prod_eq_single a]
    · simp
    · intro b hb
      simp [Function.update_of_ne hb, div_self (hne b)]
  rw [← key]
  exact h1 _

end PositivityTheory.HtPt.Mb.LJoinMany.JoinMany

namespace PositivityTheory.HtPt.Mb.LJoinMany

theorem join_finitely_many : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω), (∀ a, ∃ l, w a l ≠ 0) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → IsoAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ Ω _ _ κ _ x M A _ κa _ w hw
  classical
  haveI := Fintype.ofFinite A
  have hW : ∃ l : (∀ a, κa a), (∏ a, w a (l a)) ≠ 0 := by
    choose c hc using hw
    exact ⟨c, Finset.prod_ne_zero_iff.2 fun a _ => hc a⟩
  have hcl : Subfield.closure (Set.range (RingHom.id Ω) ∪
      {z | ∃ l l' : (∀ a, κa a), z = (∏ a, w a (l a)) / ∏ a, w a (l' a)}) = ⊤ :=
    eq_top_iff.2 fun z _ => Subfield.subset_closure (Or.inl ⟨z, rfl⟩)
  obtain ⟨M', f, hf⟩ := PositivityTheory.HtPt.Mb.join_exists o Ω κ x M Ω (RingHom.id Ω) (∀ a, κa a)
    (fun c => ∏ a, w a (c a)) (fun _ => rfl) hW hcl
  refine ⟨κ × (∀ a, κa a), inferInstance, _, M', f, hf, ?_, ?_⟩
  · intro a p'
    obtain ⟨-, c, hc⟩ := PositivityTheory.HtPt.Mb.join_charts o Ω κ (∀ a, κa a) x Ω (RingHom.id Ω)
      (fun c => ∏ a, w a (c a)) M' (fun _ => rfl) p'
    exact ⟨c a, JoinMany.inChart_of_inChart_prod _ w hc a⟩
  · intro p hp
    exact PositivityTheory.HtPt.Mb.join_iso o Ω κ x M (∀ a, κa a) (fun c => ∏ a, w a (c a)) M' f hf p
      (JoinMany.inChart_prod_of_forall _ w p hp)

end PositivityTheory.HtPt.Mb.LJoinMany

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.join_many : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω), (∀ a, ∃ l, w a l ≠ 0) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → IsoAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LJoinMany.join_finitely_many
end

