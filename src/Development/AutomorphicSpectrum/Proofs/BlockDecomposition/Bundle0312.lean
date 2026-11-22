import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0296
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0270
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0267
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0306
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0287
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0006
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0033
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassConeParametrization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0294
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVanishingIdealSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0305
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalClosedSystem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.LocTors

theorem chartIn_map {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) {N M : Type} [AddCommGroup N]
    [Module Γ(X, V) N] [AddCommGroup M] [Module Γ(X, V) M] (g : N →ₗ[Γ(X, V)] M)
    {T : Submodule Γ(X, V) N} {T' : Submodule Γ(X, V) M} (hT : T.map g ≤ T') {x : N}
    (hx : ChartIn φ V T x) : ChartIn φ V T' (g x) := by
  intro U hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  obtain ⟨y, hy⟩ := hx U hU h
  let g' : T →ₗ[Γ(X, V)] T' := (g.comp T.subtype).codRestrict T' (fun t => hT ⟨t, t.2, rfl⟩)
  refine ⟨g'.rTensor Γ(Z, U) y, ?_⟩
  have hc : T'.subtype.comp g' = g.comp T.subtype := rfl
  change (T'.subtype.rTensor Γ(Z, U)) (g'.rTensor Γ(Z, U) y) = g x ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U))
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hc, LinearMap.rTensor_comp,
    LinearMap.comp_apply, hy, LinearMap.rTensor_tmul]

theorem eq_zero_of_mem_pow {B R M : Type} [CommRing B] [CommRing R] [IsNoetherianRing R]
    [Algebra B R] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    [Module.Finite R M] (I : Ideal B) (hjac : I.map (algebraMap B R) ≤ Ideal.jacobson ⊥) (m : M)
    (hm : ∀ n, m ∈ (I ^ (n + 1) • ⊤ : Submodule B M)) : m = 0 := by
  set IR : Ideal R := I.map (algebraMap B R)
  have key : ∀ n, m ∈ (IR ^ n • ⊤ : Submodule R M) := by
    intro n
    have h1 : (I ^ (n + 1) • ⊤ : Submodule B M) ≤ (IR ^ (n + 1) • ⊤ : Submodule R M).restrictScalars B := by
      rw [Submodule.smul_le]
      intro a ha u _
      rw [Submodule.restrictScalars_mem, algebraMap_smul R a u |>.symm]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      have h2 : algebraMap B R a ∈ (I ^ (n + 1)).map (algebraMap B R) := Ideal.mem_map_of_mem _ ha
      rwa [Ideal.map_pow] at h2
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) (h1 (hm n))
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) IR hjac
  have : m ∈ (⨅ n : ℕ, IR ^ n • (⊤ : Submodule R M)) := Submodule.mem_iInf _ |>.2 key
  rw [hK] at this
  exact (Submodule.mem_bot R).1 this

theorem adjKer_pow_smul_mem_secs {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] (J : X.IdealSheafData)
    {Z : Scheme.{0}} [Z.Over (Spec (.of A))] (ψ : Z ⟶ J.subscheme) (hψ : IsProper ψ)
    (hover : (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)))
    (W : J.subscheme.Opens) (hW : IsIso (ψ ∣_ W)) {E : X.Modules} (hE : IsCoherent E)
    {S : ℕ → Subobject E} (hS : ClosedSys I E S) (hK : ∀ e, Killed J (S e))
    (B : Subobject ((Scheme.Modules.pullback (ψ ≫ J.subschemeι)).obj E))
    (hB : ∀ e, B ⊔ powSub I _ (e + 1) = pullSys I (ψ ≫ J.subschemeι) E S e)
    (V : X.affineOpens) (f : Γ(X, V)) (hf : J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W)
    (x : Γ(E, V)) (hx : x ∈ secs (adjKer (ψ ≫ J.subschemeι) B) V) :
    ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V := by
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  haveI : Module.Finite Γ(X, V) Γ(E, V) := hE.2 V V.2
  haveI : E.IsQuasicoherent := hE.1
  set IB : Ideal Γ(X, V) := Ideal.map (toFunctions (A := A) (V : X.Opens)) I with hIB
  have hpow : ∀ n, Ideal.map (toFunctions (A := A) (V : X.Opens)) (I ^ n) = IB ^ n :=
    fun n => Ideal.map_pow _ _ _
  let T : ℕ → Submodule Γ(X, V) Γ(E, V) := fun n => secsSub (S n) V
  have hpowsecs : ∀ n, secs (powSub I E n) V =
      ((IB ^ n • ⊤ : Submodule Γ(X, V) Γ(E, V)) : Set Γ(E, V)) := by
    intro n
    rw [GlobalTheory.T.ideal_power_subobject_sections I E hE.1 n V V.2, hpow]
  have h1 : ∀ n, IB ^ (n + 1) • (⊤ : Submodule Γ(X, V) Γ(E, V)) ≤ T n := by
    intro n y hy
    have hy' : y ∈ secs (powSub I E (n + 1)) V := by rw [hpowsecs]; exact hy
    exact (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 (hS.pow_le n) V hy'
  have h2 : ∀ n, T n = T (n + 1) ⊔ IB ^ (n + 1) • (⊤ : Submodule Γ(X, V) Γ(E, V)) := by
    intro n
    have hq : (powSub I E (n + 1) : X.Modules).IsQuasicoherent := (closedSys_pow I E).qcoh n
    obtain ⟨_, hsum⟩ := GlobalTheory.T.quasicoherent_sup_sections hE.1 (S (n + 1)) (powSub I E (n + 1)) (hS.qcoh (n + 1)) hq
    ext y
    change y ∈ secs (S n) V ↔ _
    rw [hS.succ n, hsum V V.2, Submodule.mem_sup]
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine ⟨s, hs, t, ?_, rfl⟩
      have ht' : t ∈ ((IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(E, V)) : Set Γ(E, V)) := by
        rw [← hpowsecs]; exact ht
      exact ht'
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine ⟨s, hs, t, ?_, rfl⟩
      rw [hpowsecs]
      exact ht
  obtain ⟨R, firstRealIndex, secondRealIndex, iR3, M, familyMassRatio, familyMassSecondLine, iM3, iM4, iM5, μ, hjac, hspan, hiff⟩ :=
    GlobalTheory.T.complete_module_noetherian_realization IB T h1 h2
  have hJ : ∀ a ∈ J.ideal ⟨(V : X.Opens), V.2⟩, ∀ m : M, a • m = 0 := by
    intro a ha m
    have hm : m ∈ Submodule.span R (Set.range μ) := hspan ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun m _ => a • m = 0) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨e, rfl⟩
      apply eq_zero_of_mem_pow IB hjac
      intro n
      rw [← map_smul]
      exact (hiff n (a • e)).1 (hK n V a ha e)
    · exact smul_zero a
    · intro u v _ _ hu hv
      rw [smul_add, hu, hv, add_zero]
    · intro r u _ hu
      rw [smul_comm a r u, hu, smul_zero]
  have hIso : IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) :=
    GroundTheory.Arith.SchemeCoh.isIso_morphismRestrict_of_le ψ hf
  have hch := GlobalTheory.T.pushforward_system_affine_sections I (ψ ≫ J.subschemeι) hover hE hS B hB (V : X.Opens) V.2 x hx
  have hch' : ∀ n, ChartIn (ψ ≫ J.subschemeι) (V : X.Opens)
      (IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) (μ x) := by
    intro n
    refine chartIn_map _ _ μ ?_ (hch n)
    rintro _ ⟨e, he, rfl⟩
    exact (hiff n e).1 he
  obtain ⟨k, hk⟩ := GlobalTheory.T.jacobson_ideal_faithful_module J ψ hψ (V : X.Opens) V.2 IB hjac hJ f hIso (μ x) hch'
  refine ⟨k, fun n => ?_⟩
  have hμ : μ (f ^ k • x) ∈ (IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) := by
    rw [map_smul, hk]
    exact Submodule.zero_mem _
  exact (hiff n _).2 hμ

end GlobalTheory.CompanionTheory.GE.LocTors
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPullbackSystemQuasicoherent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Shift

theorem exists_lift_pow_smul {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : N →ₗ[R] M) :
    ∃ k : ℕ, ∀ (n : ℕ) (y : N), f y ∈ J ^ (n + k) • (⊤ : Submodule R M) →
      ∃ i ∈ J ^ n • (⊤ : Submodule R N), f i = f y := by
  obtain ⟨k, hk⟩ := J.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨k, fun n y hy => ?_⟩
  have h1 : f y ∈ J ^ (n + k) • (⊤ : Submodule R M) ⊓ LinearMap.range f := ⟨hy, y, rfl⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h1
  have h2 : J ^ n • (J ^ k • (⊤ : Submodule R M) ⊓ LinearMap.range f) ≤
      (J ^ n • (⊤ : Submodule R N)).map f := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right
  obtain ⟨i, hi, hfi⟩ := h2 h1
  exact ⟨i, hi, hfi⟩

theorem mem_secs_adjKer {X Z : Scheme.{0}} (φ : Z ⟶ X) {E : X.Modules}
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (V : X.Opens) (x : Γ(E, V))
    (hx : (adjMap φ B).app V x = 0) : x ∈ secs (adjKer φ B) V := by
  obtain ⟨k, hk⟩ := kernel_ι_app_exact (adjMap φ B) V x hx
  refine ⟨(kernelSubobjectIso (adjMap φ B)).inv.app V k, ?_⟩
  rw [← hk, ← kernelSubobject_arrow' (adjMap φ B)]
  rfl

theorem local_shift {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X)
    (hφ : IsProper φ) (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) {E : X.Modules}
    (hE : IsCoherent E) (S : ℕ → Subobject E)
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (hB : (B : Z.Modules).IsQuasicoherent)
    (hBS : ∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e)
    (hK : (adjKer φ B : X.Modules).IsQuasicoherent)
    (V : X.Opens) (hV : IsAffineOpen V) :
    ∃ c : ℕ, ∀ e, secs (S (e + c)) V ⊆ secs (adjKer φ B ⊔ powSub I E (e + 1)) V := by
  haveI := hE.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow (isCoherent_pullback φ hE)
  have hP := GlobalTheory.T.proper_pushforward_coherent φ hφ hG
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.pushforward_ideal_power_shift I φ hφ hc hG V hV
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI := hP.2 V hV
  let f : Γ(E, V) →ₗ[Γ(X, V)] Γ((Scheme.Modules.pushforward φ).obj (cokernel B.arrow), V) :=
    { toFun := (adjMap φ B).app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  let J : Ideal Γ(X, V) := Ideal.map (toFunctions (A := A) V) I
  have hJ : ∀ m, Ideal.map (toFunctions (A := A) V) (I ^ m) = J ^ m := fun m => Ideal.map_pow _ _ _
  obtain ⟨c₂, hc₂⟩ := exists_lift_pow_smul J f
  refine ⟨c₂ + c₁, fun e x hx => ?_⟩
  have h1 := GlobalTheory.T.cokernel_section_ideal_power I φ S B (e + (c₂ + c₁)) (hBS _) V x hx
  rw [show e + (c₂ + c₁) + 1 = (e + 1 + c₂) + c₁ by omega] at h1
  have h2 := hc₁ (e + 1 + c₂) _ h1
  rw [hJ] at h2
  obtain ⟨i, hi, hfi⟩ := hc₂ (e + 1) x h2
  have hker : x - i ∈ secs (adjKer φ B) V :=
    mem_secs_adjKer φ B V _ (by
      change f (x - i) = 0
      rw [map_sub, hfi, sub_self])
  have hpow : i ∈ secs (powSub I E (e + 1)) V := by
    rw [GlobalTheory.T.ideal_power_subobject_sections I E hE.1 (e + 1) V hV, hJ]
    exact hi
  have hsup := (GlobalTheory.T.quasicoherent_sup_sections hE.1 (adjKer φ B) (powSub I E (e + 1)) hK
    ((closedSys_pow I E).qcoh e)).2 V hV
  rw [hsup]
  exact ⟨x - i, hker, i, hpow, by abel⟩

theorem shift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] [CompactSpace X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)), (B : Z.Modules).IsQuasicoherent → (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∃ c : ℕ, ∀ e, S (e + c) ≤ adjKer φ B ⊔ powSub I E (e + 1) := by
  intro A _ _ I X Z _ _ _ _ φ hφ hc E hE S hS B hB hBS
  haveI := hE.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow (isCoherent_pullback φ hE)
  have hP := GlobalTheory.T.proper_pushforward_coherent φ hφ hG
  haveI := hP.1
  have hK : (adjKer φ B : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubobjectIso (adjMap φ B)).symm (isQuasicoherent_kernel _)
  have hloc : ∀ V : X.affineOpens, ∃ c : ℕ,
      ∀ e, secs (S (e + c)) (V : X.Opens) ⊆ secs (adjKer φ B ⊔ powSub I E (e + 1)) (V : X.Opens) :=
    fun V => local_shift I φ hφ hc hE S B hB hBS hK V V.2
  choose c hc' using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hx, -⟩ :=
        exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩)
  have anti : Antitone S :=
    antitone_nat_of_succ_le fun n => le_of_le_of_eq le_sup_left (hS.succ n).symm
  refine ⟨t.sup c, fun e => ?_⟩
  have hsupq := (GlobalTheory.T.quasicoherent_sup_sections hE.1 (adjKer φ B) (powSub I E (e + 1)) hK
    ((closedSys_pow I E).qcoh e)).1
  refine GlobalTheory.T.subobject_le_of_affine_cover (S (e + t.sup c)) _ (hS.qcoh _) hsupq (fun i : t => (i.1.1 : X.Opens))
    (fun i => i.1.2) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hxU⟩
  · intro i
    refine subset_trans ?_ (hc' i.1 e)
    exact (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 (anti (Nat.add_le_add_left (Finset.le_sup i.2) e)) i.1

end GlobalTheory.CompanionTheory.GE.Shift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionNormOneConjClosure
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.ConjStep

variable {F : Type} [Field F] [NumberField F] {d β : F}

theorem conj_mem_suppAt {T : Set (Pl F)} (c : (Q d β (AF F))ˣ) {g : Q d β (AF F)}
    (hg : g ∈ SuppAt d β T) :
    ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * g * (c : Q d β (AF F)) ∈ SuppAt d β T := by
  have hcc : ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * (c : Q d β (AF F)) = 1 := c.inv_mul
  refine ⟨?_, fun u hu => ?_⟩
  · rw [qn_mul, qn_mul, hg.1, mul_one, ← qn_mul, hcc, qn_one]
  · rw [map_mul, map_mul, hg.2 u hu, mul_one, ← map_mul, hcc, map_one]

theorem star_mem_suppAt {T : Set (Pl F)} {g : Q d β (AF F)} (hg : g ∈ SuppAt d β T) :
    star g ∈ SuppAt d β T := by
  have h1 : star g * g = 1 := by rw [star_mul_eq, hg.1, map_one]
  refine ⟨by rw [qn_star, hg.1], fun u hu => ?_⟩
  have h2 := congrArg (qmap (proj u)) h1
  rwa [map_mul, hg.2 u hu, mul_one, map_one] at h2

theorem conj_central {A : Type*} [Ring A] (c ci D Di Z Zi X : A) (hZ : Z * X = X * Z)
    (hZZ : Z * Zi = 1) : (c * D * Z) * X * (Zi * Di * ci) = c * (D * X * Di) * ci := by
  calc (c * D * Z) * X * (Zi * Di * ci) = c * D * (Z * X) * Zi * Di * ci := by
        simp only [mul_assoc]
    _ = c * D * X * (Z * Zi) * Di * ci := by rw [hZ]; simp only [mul_assoc]
    _ = c * (D * X * Di) * ci := by rw [hZZ]; simp only [mul_assoc, mul_one]

theorem conj_mem_SAQ {s : Pl F} {b : Q d β (AF F)} {y c : (Q d β (AF F))ˣ} {δ : (Q d β F)ˣ} {z : (AF F)ˣ}
    {x : Q d β F} (hx : qn x = 1) {h : Q d β (AF F)} (hh : h ∈ SuppAt d β {s})
    (hy : y = c * Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ *
      Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z)
    (e : (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) = b * h) :
    ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * b * (c : Q d β (AF F)) ∈ SAQ d β s := by
  set ci : Q d β (AF F) := ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) with hci
  have hcc : ci * (c : Q d β (AF F)) = 1 := c.inv_mul
  have hsh : h * star h = 1 := by rw [mul_star_eq, hh.1, map_one]
  let ρ : Q d β F := (δ : Q d β F) * x * ((δ⁻¹ : (Q d β F)ˣ) : Q d β F)
  have hρ : qn ρ = 1 := by
    have h1 : ((δ⁻¹ : (Q d β F)ˣ) : Q d β F) * (δ : Q d β F) = 1 := δ.inv_mul
    have h2 : qn ((δ⁻¹ : (Q d β F)ˣ) : Q d β F) * qn (δ : Q d β F) = 1 := by
      rw [← qn_mul, h1, qn_one]
    simp only [ρ, qn_mul, hx, mul_one]
    rw [mul_comm]; exact h2
  have hconj : (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) =
      (c : Q d β (AF F)) * rat ρ * ci := by
    subst hy
    have hZZ : algebraMap (AF F) (Q d β (AF F)) (z : AF F) *
        algebraMap (AF F) (Q d β (AF F)) ((z⁻¹ : (AF F)ˣ) : AF F) = 1 := by
      rw [← map_mul, z.mul_inv, map_one]
    have := conj_central (c : Q d β (AF F)) ci (rat (δ : Q d β F))
      (rat ((δ⁻¹ : (Q d β F)ˣ) : Q d β F)) (algebraMap (AF F) (Q d β (AF F)) (z : AF F))
      (algebraMap (AF F) (Q d β (AF F)) ((z⁻¹ : (AF F)ˣ) : AF F)) (rat x)
      (Algebra.commutes _ _) hZZ
    simp only [ρ, map_mul]
    rw [← this]
    simp [mul_inv_rev, hci, mul_assoc]
  have hb : b = (c : Q d β (AF F)) * rat ρ * ci * star h := by
    rw [← hconj, e, mul_assoc, hsh, mul_one]
  refine ⟨ρ, hρ, ci * star h * (c : Q d β (AF F)), conj_mem_suppAt c (star_mem_suppAt hh), ?_⟩
  rw [hb]
  calc ci * ((c : Q d β (AF F)) * rat ρ * ci * star h) * (c : Q d β (AF F))
      = (ci * (c : Q d β (AF F))) * rat ρ * (ci * star h * (c : Q d β (AF F))) := by
        simp only [mul_assoc]
    _ = rat ρ * (ci * star h * (c : Q d β (AF F))) := by rw [hcc, one_mul]

theorem exists_conj_mem_closure : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → w ≠ s →
  ∀ a ∈ SuppAt d β {w}, (qmap (proj w) a).re ^ 2 ≠ 1 →
    ∃ c : (Q d β (AF F))ˣ, ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) := by
  intro F _ _ d β hdiv s w hs hws a ha hre
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.T.quaternion_class_number_finite d β hdiv
  by_contra hne
  push_neg at hne
  let f : (Q d β (AF F))ˣ × Q d β (AF F) → Q d β (AF F) := fun p =>
    ((p.1⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * p.2 * (p.1 : Q d β (AF F))
  have hf : Continuous f :=
    ((Units.continuous_val.comp (continuous_inv.comp continuous_fst)).mul continuous_snd).mul
      (Units.continuous_val.comp continuous_fst)
  have hopen : IsOpen (f ⁻¹' (closure (SAQ d β s))ᶜ) := isClosed_closure.isOpen_compl.preimage hf
  have hsub : C ×ˢ ({a} : Set (Q d β (AF F))) ⊆ f ⁻¹' (closure (SAQ d β s))ᶜ := by
    rintro ⟨c, b⟩ ⟨-, hb⟩
    obtain rfl : b = a := hb
    exact hne c
  obtain ⟨u, v, -, hv, hCu, hav, huv⟩ := generalized_tube_lemma hC isCompact_singleton hopen hsub
  obtain ⟨b, hb, y, x, hx, h, hh, e⟩ :=
    GlobalTheory.T.quaternion_conjugate_approximation d β hdiv s w hs hws a ha hre v (hv.mem_nhds (hav rfl))
  obtain ⟨c, hc, δ, z, hy⟩ := hcov y
  exact huv (Set.mk_mem_prod (hCu hc) hb) (subset_closure (conj_mem_SAQ hx hh hy e))

end GlobalTheory.CompanionTheory.PlaneSA.ConjStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassParametrizationExists
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem exists_classParam_sup_eq_top : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
      ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
        ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤ := by
  intro F _ _ _ 𝔣 h𝔣 𝔞 h𝔞
  obtain ⟨ι, _, r, v, hdom⟩ := exists_coneDomain F 𝔣 h𝔣
  obtain ⟨𝔟, x₀, hb, hx0, hx1, hxp, hab⟩ := exists_complement h𝔣 h𝔞
  obtain ⟨N, w, hN, hw⟩ := exists_scaled (𝔪 := 𝔟 * 𝔣) (mul_ne_zero hb.1 h𝔣) r v
  have hd := hdom.scale hN (u := fun c i => (w c i : F)) (fun c i => (hw c i).2)
  obtain ⟨J, a, b, c, d, e⟩ := classParam_of_scaled hb.1 hx0 hx1 hxp hab hd
    (fun c i => (Ideal.mul_le_left : 𝔟 * 𝔣 ≤ 𝔟) (hw c i).1)
    (fun c i => (Ideal.mul_le_right : 𝔟 * 𝔣 ≤ 𝔣) (hw c i).1)
  exact ⟨𝔟, J, a, b, c, d, e, hb.2⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayRelAntitoneModulusAndPowMod
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.RayFacts

theorem rayRel_mono_powMod_anti (F : Type) [Field F] [NumberField F] :
    (∀ 𝔣 𝔣' I J : Ideal (𝓞 F), 𝔣' ≤ 𝔣 → RayRel F 𝔣' I J → RayRel F 𝔣 I J) ∧
    (∀ l n m : ℕ, n ≤ m → powMod F l m ≤ powMod F l n) := by
  refine ⟨?_, ?_⟩
  · rintro 𝔣 𝔣' I J hle ⟨a, b, ha, hb, ha1, hb1, hσ, h⟩
    exact ⟨a, b, ha, hb, hle ha1, hle hb1, hσ, h⟩
  · intro l n m hnm
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hnm)

end GlobalTheory.CompanionTheory.RayFacts
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpEpsilonRootIdempotentSumStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharp_epsilon_root_idempotent_sum : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (ρ : ℕ → ((base l).cont ℤ_[l]).A),
  (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) (ρ 0) - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) →
  (∀ m, ρ (m + 1) ^ l = ρ m) → ∀ m, ((base l).cont ℤ_[l]).sharp (ρ m) =
    ∑ c : ZMod (l ^ m), ((base l).cont ℤ_[l]).sharp (GlobalTheory.CompanionTheory.ContUniv.ind (base l) m c) *
      ((base l).cont ℤ_[l]).sharp (((base l).cont ℤ_[l]).s (ε.e m)) ^ c.val := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.sharp_roots_universal | exact GlobalTheory.CompanionTheory.ContUniv.sharp_roots_universal | (intros; apply GlobalTheory.CompanionTheory.ContUniv.sharp_roots_universal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVanishingIdealSystemStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_vanishing_ideal_system : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤
        vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ vanIdeal (i e ≫ thickι R I N e)) →
        f ∈ vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e, vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ≤ vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
        vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ⊔
          (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Family.vanIdeal_family | exact GlobalTheory.CompanionTheory.GE.Family.vanIdeal_family | (intros; apply GlobalTheory.CompanionTheory.GE.Family.vanIdeal_family <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRestrictionRepresentationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_restriction_representation : PositivityTheory.RgDs.K.RhoTorus := by
  first | exact @GlobalTheory.CompanionTheory.RgTorus.rhoTorus | exact GlobalTheory.CompanionTheory.RgTorus.rhoTorus | (intros; apply GlobalTheory.CompanionTheory.RgTorus.rhoTorus <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusWeightDecompositionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_weight_decomposition : PositivityTheory.RgDs.K.TorW := by
  first | exact @GlobalTheory.CompanionTheory.RgDsTor.torW | exact GlobalTheory.CompanionTheory.RgDsTor.torW | (intros; apply GlobalTheory.CompanionTheory.RgDsTor.torW <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferStatementStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transfer_statement : PositivityTheory.RgDs.K.Transfer := by
  first | exact @GlobalTheory.CompanionTheory.RgKeyTransfer.transfer | exact GlobalTheory.CompanionTheory.RgKeyTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.RgKeyTransfer.transfer <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittToAcrisIsDPMorphismStatement
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_to_acris_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ), IsDPMorphism (Wc.pd l r.k n) (B.DD true (base l) n) (Mid.wn r n) := by
  first | exact @GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism | exact GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism | (intros; apply GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism <;> assumption)
end

