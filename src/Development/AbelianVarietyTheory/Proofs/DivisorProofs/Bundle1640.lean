import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1612
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFreeFiniteBijectiveOfSmooth
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

open GlobalTheory.HodgeTateCompare in

theorem omega_free_finite_bijective_of_smooth {O : Type} [CommRing O] [IsLocalRing O]
    (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [Smooth G.hom] :
    Module.Free O (omega G) ∧ Module.Finite O (omega G) ∧
      Function.Bijective (fun (x : LieG G) => ((LinearMap.proj x : (LieG G → O) →ₗ[O] O) ∘ₗ
        (omega G).subtype : Module.Dual O (omega G))) := by
  obtain ⟨h₁, h₂⟩ := finite_projective_of_smooth (G := G)
  haveI : Module.Free O (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G) := Module.free_of_flat_of_isLocalRing
  refine ⟨.of_equiv (omegaEquiv G), .equiv (omegaEquiv G), ?_⟩
  refine (Function.Bijective.of_comp_iff _ (lieEquiv G).bijective).1 ?_
  refine (Function.Bijective.of_comp_iff' (omegaEquiv G).dualMap.bijective _).1 ?_
  convert Function.bijective_id
  funext w
  exact LinearMap.ext fun f => ev_apply f w

theorem Point.omega_free_finite_bijective : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), Module.Free O (omega P.Gt) ∧ Module.Finite O (omega P.Gt) ∧ Function.Bijective (fun (x : LieG P.Gt) => ((LinearMap.proj x : (LieG P.Gt → O) →ₗ[O] O) ∘ₗ (omega P.Gt).subtype : Module.Dual O (omega P.Gt))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  haveI := P.isLocalRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨P.D⟩).1
  exact omega_free_finite_bijective_of_smooth P.Gt

end GlobalTheory.HTLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointLinearFunctionalCm
section
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal

namespace GlobalTheory.TateLocFree

theorem exists_place_decomp : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C), ∃ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) ∧ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 ∧ ∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j) := by
  intro p _ C _ _ _ v O _ _ _ E _ _ _ P φ
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  obtain ⟨w, hw⟩ := GlobalTheory.exists_placeU_mem_emb p (𝓞 E) O (embO P.integers φ)
  obtain ⟨hdom, hpid, -⟩ := GlobalTheory.PlaceMono.place_monogenic p (𝓞 E) w
  let A := ℤ_[p] ⊗[ℤ] 𝓞 E
  let e : A := w.e
  let I : Ideal A := Ideal.span {1 - e}
  letI : Module A P.T := Module.compHom P.T (tensorAction P.actT).toRingHom
  have hsmul : ∀ (a : A) (t : P.T), a • t = tensorAction P.actT a t := fun _ _ => rfl
  haveI : IsScalarTower ℤ_[p] A P.T := ⟨fun c a t => by
    rw [hsmul, hsmul, map_smul]; rfl⟩
  let M : Submodule A P.T := LinearMap.range (LinearMap.lsmul A P.T e)
  have hee : e * e = e := w.idem
  have hfix : ∀ m ∈ M, e • m = m := by
    rintro _ ⟨t, rfl⟩
    change e • e • t = e • t
    rw [smul_smul, hee]
  have htor : Module.IsTorsionBySet A M I := by
    intro x a
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 a.2
    apply Subtype.ext
    rw [Submodule.coe_smul, ← hc, mul_smul, sub_smul, one_smul, hfix _ x.2, sub_self, smul_zero,
      Submodule.coe_zero]
  letI : Module (A ⧸ I) M := htor.module
  haveI : IsScalarTower A (A ⧸ I) M := htor.isScalarTower
  haveI : IsDomain (A ⧸ I) := hdom
  haveI : IsPrincipalIdealRing (A ⧸ I) := hpid
  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite ℤ_[p] A
  haveI : Module.Finite A P.T := Module.Finite.of_restrictScalars_finite ℤ_[p] A P.T
  haveI : Module.Finite (A ⧸ I) M := Module.Finite.of_restrictScalars_finite A (A ⧸ I) M
  haveI : Module.Finite ℤ_[p] (A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] I).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ_[p] I)
  haveI : Module.IsTorsionFree (A ⧸ I) M := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ_[p]) hr
      (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hc)
    have h1 : (algebraMap ℤ_[p] A c) • (m : P.T) = 0 := by
      have : (algebraMap ℤ_[p] (A ⧸ I) c) • m = 0 := by rw [← hs, mul_smul, h, smul_zero]
      have h2 : (((algebraMap ℤ_[p] (A ⧸ I) c) • m : M) : P.T) = 0 := by rw [this]; rfl
      exact h2
    rw [algebraMap_smul] at h1
    apply Subtype.ext
    exact (smul_eq_zero.1 h1).resolve_left hc0
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := A ⧸ I) (M := M)
  have hI : (I : Submodule A A) ≤ LinearMap.ker (LinearMap.mulLeft A e) := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
    linear_combination c * (1 - hee)
  let liftE : (A ⧸ I) →ₗ[A] A := Submodule.liftQ I (LinearMap.mulLeft A e) hI
  have hlift : ∀ (r : A ⧸ I) (m : M), liftE r • (m : P.T) = ((r • m : M) : P.T) := by
    intro r m
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
    have h1 : liftE (Ideal.Quotient.mk I x) = e * x := Submodule.liftQ_apply _ _ _
    rw [h1, mul_comm, mul_smul, hfix _ m.2]
    rfl
  let emap : P.T →ₗ[A] M := (LinearMap.lsmul A P.T e).rangeRestrict
  let L : Fin n → (P.T →ₗ[A] A) := fun j => liftE ∘ₗ ((b.coord j).restrictScalars A) ∘ₗ emap
  refine ⟨n, fun j => (b j : P.T), fun j => (L j).restrictScalars ℤ_[p], e, ?_, hw, ?_⟩
  · intro j a t
    have h1 : P.actT a t = (1 ⊗ₜ a : A) • t := by
      rw [hsmul, tensorAction_tmul, one_smul]
    rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, h1, map_smul, smul_eq_mul]
  · intro t
    have h0 : ((emap t : M) : P.T) = e • t := rfl
    rw [← hsmul, ← h0, ← b.sum_repr (emap t), Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hsmul, ← hlift]
    rfl
end GlobalTheory.TateLocFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointTraceDual
section
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EigGlue

section Alg

variable {O R ι : Type} [CommRing O] [Field R] [DecidableEq ι] {σ : ι → O →+* R}

theorem eq_smul_idem (h : IsSplitting σ) (i : ι) (z : R ⊗[ℤ] O)
    (hz : ∀ a, (1 ⊗ₜ a) * z = σ i a • z) : z = splitMap σ z i • idem h i := by
  apply h.1
  funext k
  rw [map_smul, splitMap_idem, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = i
  · subst hk; simp
  · rw [Pi.single_eq_of_ne hk, mul_zero]
    have hne : σ k ≠ σ i := fun e => hk (h.injective e)
    obtain ⟨a, ha⟩ : ∃ a, σ k a ≠ σ i a := by
      by_contra hc
      push Not at hc
      exact hne (RingHom.ext hc)
    have e := congrArg (fun t => splitMap σ t k) (hz a)
    simp only [map_mul, Pi.mul_apply, splitMap_tmul, one_mul, map_smul, Pi.smul_apply, smul_eq_mul] at e
    have : (σ k a - σ i a) * splitMap σ z k = 0 := by rw [sub_mul, e, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)

end Alg

section Act

variable {p : ℕ} [Fact p.Prime] (C : Type) [Field C] [Algebra ℤ_[p] C] {E : Type} [Field E]
  {T : Type} [AddCommGroup T] [Module ℤ_[p] T] (ρ : 𝓞 E →+* Module.End ℤ_[p] T)

def inclC : ℤ_[p] ⊗[ℤ] 𝓞 E →ₐ[ℤ_[p]] C ⊗[ℤ] 𝓞 E :=
  Algebra.TensorProduct.map (Algebra.ofId ℤ_[p] C) (AlgHom.id ℤ (𝓞 E))

theorem inclC_tmul (r : ℤ_[p]) (a : 𝓞 E) : inclC C (r ⊗ₜ a) = algebraMap ℤ_[p] C r ⊗ₜ a := by
  simp [inclC, Algebra.ofId_apply]

theorem tensorAction_inclC (z : ℤ_[p] ⊗[ℤ] 𝓞 E) (x : C ⊗[ℤ_[p]] T) :
    tensorAction (baseChangeAction C ρ) (inclC C z) x = (tensorAction ρ z).baseChange C x := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz, LinearMap.baseChange_add]
  | tmul r a =>
    have e : tensorAction ρ (r ⊗ₜ a) = r • ρ a := LinearMap.ext fun y => by
      rw [tensorAction_tmul, LinearMap.smul_apply]
    rw [inclC_tmul, tensorAction_tmul, e, LinearMap.baseChange_smul,
      LinearMap.smul_apply, algebraMap_smul, baseChangeAction_apply]

variable {m : ℕ} (ℓ : Fin m → (T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E))

def coordC (j : Fin m) : C ⊗[ℤ_[p]] T →ₗ[C] C ⊗[ℤ] 𝓞 E :=
  ((inclC C).toLinearMap ∘ₗ ℓ j).liftBaseChange C

theorem coordC_tmul (j : Fin m) (c : C) (t : T) : coordC C ℓ j (c ⊗ₜ t) = c • inclC C (ℓ j t) := by
  rw [coordC, LinearMap.liftBaseChange_tmul]
  rfl

variable {ρ ℓ}

theorem coordC_act (hℓ : ∀ j a t, ℓ j (ρ a t) = (1 ⊗ₜ a) * ℓ j t) (j : Fin m) (a : 𝓞 E)
    (x : C ⊗[ℤ_[p]] T) : coordC C ℓ j (baseChangeAction C ρ a x) = (1 ⊗ₜ a) * coordC C ℓ j x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | tmul c t =>
    rw [baseChangeAction_apply, LinearMap.baseChange_tmul, coordC_tmul, coordC_tmul, hℓ, map_mul,
      mul_smul_comm]
    congr 2
    simp [inclC]

theorem baseChange_eq_sum {u : Fin m → T} {e : ℤ_[p] ⊗[ℤ] 𝓞 E}
    (hE : ∀ t, tensorAction ρ e t = ∑ j, tensorAction ρ (ℓ j t) (u j)) (x : C ⊗[ℤ_[p]] T) :
    (tensorAction ρ e).baseChange C x =
      ∑ j, tensorAction (baseChangeAction C ρ) (coordC C ℓ j x) (1 ⊗ₜ u j) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_apply, Finset.sum_add_distrib]
  | tmul c t =>
    rw [LinearMap.baseChange_tmul, hE, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coordC_tmul, map_smul, LinearMap.smul_apply, tensorAction_inclC, LinearMap.baseChange_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end Act

section Point

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {E : Type} [Field E]

theorem splitMap_inclC (hv : v.Integers O) (φ : E →+* C) (e : ℤ_[p] ⊗[ℤ] 𝓞 E) :
    splitMap (fun ψ : E →+* C => (algebraMap O C).comp (embO hv ψ)) (inclC C e) φ =
      algebraMap O C (ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO hv φ) e) := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul r a =>
    rw [inclC_tmul, splitMap_tmul]
    simp [ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt, Algebra.ofId_apply, IsScalarTower.algebraMap_apply ℤ_[p] O C]

def intPart (O C E : Type) [CommRing O] [Field C] [Algebra O C] [Field E] :
    Submodule O (C ⊗[ℤ] 𝓞 E) :=
  Submodule.span O (Set.range fun a : 𝓞 E => (1 : C) ⊗ₜ[ℤ] a)

theorem inclC_mem_intPart (z : ℤ_[p] ⊗[ℤ] 𝓞 E) : inclC C z ∈ intPart O C E := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul r a =>
    rw [inclC_tmul, IsScalarTower.algebraMap_apply ℤ_[p] O C, ← mul_one (algebraMap O C _),
      ← Algebra.smul_def, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem exists_fin_of_mem_intPart {z : C ⊗[ℤ] 𝓞 E} (hz : z ∈ intPart O C E) :
    ∃ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E), z = ∑ k, algebraMap O C (r k) ⊗ₜ[ℤ] a k := by
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hz
  refine ⟨n, f, fun k => (g k).2.choose, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← (g k).2.choose_spec, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]

end Point

theorem mem_latTQuot_of_smul_mem_latT : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C) (d : C), d ≠ 0 → (∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then s else 0) → v s ≤ v d) → ∀ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) → ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 → (∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j)) → ∀ w : P.V, w ∈ P.eigV (embO P.integers φ) → d • w ∈ P.latT → w ∈ P.latTQuot (σ := fun ψ : E →+* C => embO P.integers ψ) (isSplitting_embO P.integers) φ := by
  intro p _ C _ _ _ v O _ _ _ _ _ E _ _ _ P φ d hd hδ m u ℓ e hℓ he hE w hw hdw
  let σf : (E →+* C) → 𝓞 E →+* C := fun ψ => (algebraMap O C).comp (embO P.integers ψ)
  have h : IsSplitting σf := isSplitting_embO P.integers
  have hyV : d • w ∈ eigenSub P.actV (σf φ) := Submodule.smul_mem _ d hw
  have hact : P.actV = baseChangeAction C P.actT := rfl

  have h1 : (tensorAction P.actT e).baseChange C (d • w) = d • w := by
    rw [← tensorAction_inclC, ← hact, tensorAction_of_mem (σ := σf) (i := φ) hyV,
      splitMap_inclC P.integers φ e, he, map_one, one_smul]

  have h2 : ∀ j, ∃ o : O, coordC C ℓ j (d • w) = (d * algebraMap O C o) • idem h φ := by
    intro j
    have hz : ∀ a, (1 ⊗ₜ a) * coordC C ℓ j (d • w) = σf φ a • coordC C ℓ j (d • w) := by
      intro a
      rw [← coordC_act C hℓ, ← hact, mem_eigenSub.1 hyV a, map_smul]
    have heq := eq_smul_idem h φ _ hz
    set s := splitMap σf (coordC C ℓ j (d • w)) φ with hs
    have hmem : coordC C ℓ j (d • w) ∈ intPart O C E := by
      obtain ⟨x, hx⟩ := hdw
      rw [← hx]
      clear hx
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
      | tmul c t =>
        rw [Point.inclT_tmul, coordC_tmul, algebraMap_smul]
        exact Submodule.smul_mem _ _ (inclC_mem_intPart _)
    obtain ⟨n, r, a, hra⟩ := exists_fin_of_mem_intPart hmem
    have hvs : v s ≤ v d := by
      refine hδ n r a s fun ψ => ?_
      have e1 : splitMap σf (coordC C ℓ j (d • w)) ψ = s * (Pi.single φ 1 : (E →+* C) → C) ψ := by
        conv_lhs => rw [heq]
        rw [map_smul, splitMap_idem, Pi.smul_apply, smul_eq_mul]
      have e2 : splitMap σf (coordC C ℓ j (d • w)) ψ =
          ∑ k, algebraMap O C (r k) * ψ (a k) := by
        rw [hra, map_sum, Finset.sum_apply]
        simp only [splitMap_tmul, σf, RingHom.comp_apply, algebraMap_embO]
      rw [← e2, e1]
      by_cases hψ : ψ = φ
      · subst hψ; simp
      · simp [hψ]
    have hvd : v (s * d⁻¹) ≤ 1 := by
      rw [map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ hvs zero_le
    obtain ⟨o, ho⟩ := P.integers.exists_of_le_one hvd
    refine ⟨o, ?_⟩
    rw [heq, ho, mul_comm s, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  choose o ho using h2

  have h3 : d • w = d • proj h P.actV φ (∑ j, o j • ((1 : C) ⊗ₜ[ℤ_[p]] u j)) := by
    conv_lhs => rw [← h1, baseChange_eq_sum C hE]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ho, ← hact, map_smul, LinearMap.smul_apply, ← proj, ← algebraMap_smul C (o j), map_smul,
      smul_smul]
  have hw' := smul_right_injective _ hd h3
  refine (mem_eigQuotLat _ _).2 ⟨_, Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (P.one_tmul_mem_latT _), hw'.symm⟩

end GlobalTheory.EigGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaUnfold

open GlobalTheory.WeilM
open scoped Classical

theorem continuous_infToMixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem adele_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem schA_continuous (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine (f.continuous.comp ?_).mul (hg.1.continuous.comp ?_)
    · exact continuous_pi fun i =>
        (continuous_infToMixed F).comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  | zero => exact continuous_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact continuous_const.mul h

def ratEquiv (F : Type) [Field F] [NumberField F] (κ : Type) : (κ → F) ≃ GlobalTheory.ThetaParseval.ratVec F κ :=
  Equiv.ofBijective
    (fun ξ => ⟨fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i), (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ξ, rfl⟩⟩)
    ⟨fun a b h => funext fun i => (haveI := adele_nontrivial F; (algebraMap F (AdeleRing (𝓞 F) F)).injective) (congrFun (congrArg Subtype.val h) i),
     fun y => by
      obtain ⟨ξ, hξ⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff y.1).1 y.2
      exact ⟨ξ, Subtype.ext hξ.symm⟩⟩

theorem unfold : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      ∫⁻ x in 𝓕₁, ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ μ hμ 𝓕₁ h𝓕 Φ hΦ
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  have hc := schA_continuous F hΦ
  haveI : Countable F := by
    have b := Module.finBasis ℚ F
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := Countable.of_equiv _ (ratEquiv F κ)
  have hm : ∀ c : κ → AF F, Measurable fun x : κ → AF F => ‖Φ (c + x)‖ₑ ^ 2 := fun c =>
    ((hc.comp (continuous_const.add continuous_id)).measurable.enorm).pow_const 2
  rw [lintegral_tsum fun ξ => (hm _).aemeasurable, h𝓕.lintegral_eq_tsum' (fun x => ‖Φ x‖ₑ ^ 2)]
  rw [← ((ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
  refine tsum_congr fun ξ => ?_
  simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
  rfl
end GlobalTheory.ThetaUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIsoCompatibleLocalLanglandsFour
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL GlobalTheory.TheRecTransport

namespace GlobalTheory.LawsTTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem eig_of_wdRel {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (H : WDRel φ y y') {σ : Weil h} {σ' : Weil h'}
    (hσ : WeilRel φ σ σ') : y.eig σ = y'.eig σ' := by
  obtain ⟨n, b, b', e1, e2, -, hb⟩ := H
  rw [← e1, ← e2, WD.eig, WD.eig, WD.charPol_mk, WD.charPol_mk, hb σ _ hσ]

end GlobalTheory.LawsTTransport

theorem GlobalTheory.LawsTTransport.lawsT_transport : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → (∀ x x', RepRel i x x' → (UpperTheory.Zero.LLC.Good x ↔ UpperTheory.Zero.LLC.Good x')) → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a'), (∀ (x : IrrGL (w'.adicCompletion E')) ω, HasCentralChar x.rep ω → ∀ σ, ‖((rc' x).eig σ).prod‖ = ‖(ω (a' σ) : ℂ)‖) ∧ (∀ x χ hχ, UpperTheory.Zero.LLC.Good x → rc' (x.tw χ hχ) = (rc' x).lpChar (rc' (.ofChar χ hχ))) ∧ (∀ (x : IrrGL (w'.adicCompletion E')) ω, UpperTheory.Zero.LLC.Good x → HasCentralChar x.rep ω → ∀ σ, ((rc' x).eig σ).prod = (ω (a' σ) : ℂ)) ∧ (∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w'.adicCompletion E'))), UpperTheory.Zero.LLC.Good (cls π) → Nonempty (π'.ρ.Equiv (contra π.ρ)) → rc' (cls π') = (rc' (cls π)).lpDual) ∧ (∀ x y, UpperTheory.Zero.LLC.Good y → rc' x = rc' y → x = y) := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ A w w' h h' j i P rc rc' hR hG a ha L a' ha'
  have h3 := P.cont
  have := charZero_compl w
  have := charZero_compl w'
  have hs : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i h3).1
  obtain ⟨T, hT, -⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero _ _ i h3
  obtain ⟨-, hch⟩ := GlobalTheory.T.transport_keeps_cuspidal_twists_characters _ _ i h3
  obtain ⟨S, hS, -, -, -, hSc, -⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i P
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i P
  have hart := GlobalTheory.T.localArtinMap_unique_transport_placeIso GlobalTheory.globalArtinReciprocity_holds GlobalTheory.Published.chevalleyUnits'
    E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i P a a' ha ha'
  have hRS : ∀ x x', RepRel i x x' → rc' x' = S (rc x) := fun x x' r => ((hS _ _).1 (hR x x' r)).symm
  have hrel : ∀ x', RepRel i (T.symm x') x' := fun x' => (hT _ _).2 (T.apply_symm_apply x')
  have hwd : ∀ y, WDRel (RingEquiv.refl Ω) y (S y) := fun y => (hS _ _).2 rfl
  have hσ : ∀ σ', WeilRel (RingEquiv.refl Ω) (c.symm σ') σ' := fun σ' => (hc _ _).2 (c.apply_symm_apply σ')
  have hv : ∀ (ω : (w'.adicCompletion E')ˣ →* ℂˣ) (z : (w.adicCompletion E)ˣ),
      (ω.comp (Units.map i.symm.symm.toRingHom.toMonoidHom)) z = ω (Units.map i.toRingHom.toMonoidHom z) :=
    fun ω z => rfl

  have heig : ∀ x' σ', (rc' x').eig σ' = (rc (T.symm x')).eig (c.symm σ') := fun x' σ' => by
    rw [hRS _ _ (hrel x')]
    exact (GlobalTheory.LawsTTransport.eig_of_wdRel (hwd _) (hσ σ')).symm
  have hcent : ∀ (x' : IrrGL (w'.adicCompletion E')) ω, HasCentralChar x'.rep ω →
      HasCentralChar (T.symm x').rep (ω.comp (Units.map i.symm.symm.toRingHom.toMonoidHom)) :=
    fun x' ω hω => central_transport i.symm (repRel_symm (hrel x')) hω
  refine ⟨fun x' ω hω σ' => ?_, fun x' χ hχ hg => ?_, fun x' ω hg hω σ' => ?_,
    fun n π π' hg ⟨u₀⟩ => ?_, fun x' y' hg e => ?_⟩
  · rw [heig, L.absCentral _ _ (hcent x' ω hω) (c.symm σ'), hart _ _ (hσ σ'), hv]
  · have hχ0 := isSmoothChar_comp i h3 hχ
    have htw : ∀ x x', RepRel i x x' → RepRel i (x.tw _ hχ0) (x'.tw χ hχ) := by
      rintro x x' ⟨n, π, π', e, rfl, rfl, he⟩
      exact repRel_tw i π π' e he _ hχ0 χ hχ (fun _ => rfl)
    rw [hRS _ _ (htw _ _ (hrel x')), L.twist _ _ _ ((hG _ _ (hrel x')).2 hg), hSc, ← hRS _ _ (hrel x'),
      ← hRS _ _ (hch _ hχ0 χ hχ (fun _ => rfl))]
  · rw [heig, L.central _ _ ((hG _ _ (hrel x')).2 hg) (hcent x' ω hω) (c.symm σ'), hart _ _ (hσ σ'), hv]
  · obtain ⟨π₀, e, h1, he⟩ := exists_of_repRel π (repRel_symm (hrel (cls π)))
    obtain ⟨π₀', u, h2, hu⟩ := exists_of_repRel π' (repRel_symm (hrel (cls π')))
    have r1 : RepRel i (cls π₀) (cls π) := h1 ▸ hrel (cls π)
    have r2 : RepRel i (cls π₀') (cls π') := h2 ▸ hrel (cls π')
    rw [hRS _ _ r2, hRS _ _ r1, ← equiv_lpDual P S hS,
      L.dual n π₀ π₀' ((hG _ _ r1).2 hg) (contra_transport i.symm hs h3 π π' π₀ π₀' e he u hu u₀)]
  · have e2 : rc (T.symm x') = rc (T.symm y') := by
      apply S.injective
      rw [← hRS _ _ (hrel x'), ← hRS _ _ (hrel y'), e]
    exact T.symm.injective (L.inj _ _ ((hG _ _ (hrel y')).2 hg) e2)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDensityExistsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_density_exists : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∃ w : AlgChart p σ 1 → CxPts p σ → ℝ, IsDens w ∧ ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, 0 < w c y := by
  first | exact @GlobalTheory.CurveDens.exists_isDens_pos | exact GlobalTheory.CurveDens.exists_isDens_pos | (intros; apply GlobalTheory.CurveDens.exists_isDens_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensionalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_degree_generic_ne_zero_equidimensional : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ), LocallyOfFiniteType p → LocallyOfFiniteType f → Surjective f → topologicalKrullDim M = n → topologicalKrullDim W = n → f.residueDegree (genericPoint M) ≠ 0 := by
  first | exact @GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero | exact GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero | (intros; apply GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero <;> assumption)
end

