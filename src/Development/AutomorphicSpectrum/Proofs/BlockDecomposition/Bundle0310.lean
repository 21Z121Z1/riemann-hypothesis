import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0054
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0270
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0306
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftSectionsNonvanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0305
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicFunctionFacts
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.RgMass

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2]
  simp

theorem hE_self_fixed (hcm : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by
  simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : σ ((σ : E →+* E) (x j)) = x j := sigma_sigma hcm _
  have h2 : (σ : E →+* E) (x i) = σ (x i) := rfl
  rw [h1, hJ.1 i j, h2]
  ring

theorem exists_len (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J)
    {X : Fin 1 → Fin 2 → E} (hX : X ≠ 0) : ∃ β : F, β ≠ 0 ∧ X ∈ sph σ J β := by
  have hT : ∀ a b, σ (gramE σ J X b a) = gramE σ J X a b := fun a b => by
    rw [Subsingleton.elim a b]
    exact hE_self_fixed hcm hJ _
  obtain ⟨β, e, h, -⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm _ hT
  refine ⟨β, h ?_, e⟩
  rw [Matrix.det_unique]
  intro h0
  exact hX (funext fun a => by rw [Subsingleton.elim a default]; exact hA _ h0)

theorem sph_unique {J : Matrix (Fin 2) (Fin 2) E} {X : Fin 1 → Fin 2 → E} {β β' : F} (h : X ∈ sph σ J β)
    (h' : X ∈ sph σ J β') : β = β' := by
  have e : (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) = fun _ _ => algebraMap F E β' := h.symm.trans h'
  exact (algebraMap F E).injective (congrFun (congrFun e 0) 0)

theorem ne_zero_of_mem_sph {J : Matrix (Fin 2) (Fin 2) E} {X : Fin 1 → Fin 2 → E} {β : F} (hβ : β ≠ 0)
    (h : X ∈ sph σ J β) : X ≠ 0 := by
  rintro rfl
  refine hβ (sph_unique h ?_)
  funext a c
  simp [gramE, hE, hform]

def sphEquiv (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J) :
    (Σ β : {β : F // β ≠ 0}, sph σ J β.1) ≃ {X : Fin 1 → Fin 2 → E | X ≠ 0} :=
  Equiv.ofBijective (fun p => ⟨p.2.1, ne_zero_of_mem_sph p.1.2 p.2.2⟩) (by
    constructor
    · rintro ⟨β, X⟩ ⟨β', X'⟩ h
      have hX : X.1 = X'.1 := congrArg Subtype.val h
      have hb : β = β' := Subtype.ext (sph_unique X.2 (hX ▸ X'.2))
      subst hb
      obtain rfl : X = X' := Subtype.ext hX
      rfl
    · rintro ⟨X, hX⟩
      obtain ⟨β, h0, hβ⟩ := exists_len hcm hJ hA hX
      exact ⟨⟨⟨β, h0⟩, ⟨X, hβ⟩⟩, rfl⟩)

theorem thetaMeas_ne (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) :
    thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0} =
      Measure.sum fun β : {β : F // β ≠ 0} => thetaMeas σ J μ 𝓕 (sph σ J β.1) := by
  ext s hs
  simp only [thetaMeas, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, ENNReal.tsum_mul_left]
  congr 1
  rw [← (sphEquiv hcm hJ hA).tsum_eq, ENNReal.tsum_sigma']
  rfl

end Alg

set_option maxHeartbeats 1000000 in

theorem cnt : TestEx → LSide → RSide → Cnt := by
  intro hTE hL hR F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm κ hκ
  obtain ⟨⟨θ, hθ⟩, -⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real F hcm.1
  obtain ⟨S, hS⟩ := hR F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ
  obtain ⟨φ, A, ht, hv0, hvT⟩ := hTE F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm S
  have hLt := hL F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ S φ A ht
  have hRt := hS S (Finset.Subset.refl _) φ A ht
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  obtain ⟨_, -, -, -, -, -, -, hBinf, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)
  have := hBinf 1 2
  obtain ⟨hφc, -, -, -, hAS, hAo⟩ := ht
  have hdil : ∀ ε : ℝ, Continuous (dil θ ε : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → _) := fun ε =>
    continuous_pi fun a => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have hloc : ∀ v, IsCompact (A v) ∧ MeasurableSet (A v) ∧
      ∀ s : HermR (Fv F v) σ 1, m v s (A v) < ⊤ := fun v => by
    have hRv := GlobalTheory.T.completion_is_local_ring F v
    have hRv' := hRv
    obtain ⟨_, _, _, _, -⟩ := hRv'
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
    have := hB 1 2
    obtain ⟨-, k1, k2⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b (lam v) (hlam v).1
    have hco : IsCompact (A v) ∧ IsOpen (A v) := by
      by_cases hv : v ∈ S
      · exact ⟨(hAS v hv).1, (hAS v hv).2.1⟩
      · rw [hAo v hv]
        exact (GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2).2.2.2.1 v
    refine ⟨hco.1, hco.2.measurableSet, fun s => ?_⟩
    have := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 2 J hJ (Fv F v) hRv 1 _ _ _ (k1 1 2) (k2 1) (hm v) s).1
    exact hco.1.measure_lt_top
  have hcof : ∀ᶠ v in cofinite, A v = latV b v :=
    S.finite_toSet.eventually_cofinite_notMem.mono fun v hv => hAo v (by simpa using hv)
  have key : ∀ ε : ℝ, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, ENNReal.ofReal (φ (dil θ ε (projInf X)))
        ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0}) =
      (κ : ℝ≥0∞) * ∑' β : {β : F // β ≠ 0},
        (∫⁻ X, ENNReal.ofReal (φ (dil θ ε X)) ∂(mi (hermScal (Ainf F) σ (algebraMap F _ β.1)))) *
          ENNReal.ofReal (∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β.1)) (A v)).toReal) := fun ε => by
    rw [thetaMeas_ne hcm hJ hAn, Measure.restrict_sum_of_countable, lintegral_sum_measure, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun β => ?_
    have hEu : IsEulerProd b (thetaMeas σ J μ 𝓕 (sph σ J β.1)) κ (mi (hermScal (Ainf F) σ (algebraMap F _ β.1)))
        (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β.1))) := hκ β.1 β.2
    obtain ⟨-, e⟩ := GlobalTheory.T.euler_product_measure_integral F E σ hcm d b 1 2 _ κ _ _ hEu (fun Y => ENNReal.ofReal (φ (dil θ ε Y))) A
      (hφc.comp (hdil ε)).measurable.ennreal_ofReal (fun v => (hloc v).2.1) (fun v => (hloc v).2.2 _) hcof
    rw [e, mul_assoc]
  simp only [key] at hLt
  have h1 := ENNReal.Tendsto.const_mul (a := (κ : ℝ≥0∞)) hRt (Or.inr ENNReal.coe_ne_top)
  have h2 : (vol b li lam S φ A) = (κ : ℝ≥0∞) * vol b li lam S φ A :=
    tendsto_nhds_unique hLt (h1.congr fun ε => mul_left_comm _ _ _)
  have h3 : (κ : ℝ≥0∞) = 1 := by
    have h4 : (κ : ℝ≥0∞) * vol b li lam S φ A = 1 * vol b li lam S φ A := by rw [one_mul]; exact h2.symm
    exact (ENNReal.mul_left_inj hv0 hvT).1 h4
  exact_mod_cast h3

end GlobalTheory.CompanionTheory.RgMass

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProductIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.NonPrime

variable {X : Scheme.{0}}

lemma secs_mk {E F : X.Modules} (f : F ⟶ E) [Mono f] (V : X.Opens) :
    secs (Subobject.mk f) V = Set.range (f.app V) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(Subobject.underlyingIso f).hom.app V t, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · rintro ⟨t, rfl⟩
    refine ⟨(Subobject.underlyingIso f).inv.app V t, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.underlyingIso_arrow]

lemma smul_mem_secs {E : X.Modules} (S : Subobject E) {V : X.Opens} (a : Γ(X, V)) {x : Γ(E, V)}
    (hx : x ∈ secs S V) : a • x ∈ secs S V := by
  obtain ⟨t, rfl⟩ := hx
  exact ⟨a • t, Scheme.Modules.Hom.app_smul S.arrow a t⟩

lemma add_mem_secs {E : X.Modules} (S : Subobject E) {V : X.Opens} {x y : Γ(E, V)}
    (hx : x ∈ secs S V) (hy : y ∈ secs S V) : x + y ∈ secs S V := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  exact ⟨s + t, map_add _ s t⟩

def idealSub (J : X.IdealSheafData) (E : X.Modules) : Subobject E :=
  Subobject.mk (kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app E))

lemma secs_idealSub (J : X.IdealSheafData) (E : X.Modules) [E.IsQuasicoherent]
    (U : X.affineOpens) :
    secs (idealSub J E) U = ((J.ideal U • ⊤ : Submodule Γ(X, U) Γ(E, U)) : Set Γ(E, U)) := by
  rw [idealSub, secs_mk, ← (GlobalTheory.surjective_and_ker_unit_subschemeι J E U).2,
    ← GlobalTheory.QCoh.range_kernel_ι_app]
  rfl

lemma isQuasicoherent_idealSub (J : X.IdealSheafData) {E : X.Modules} (hE : IsCoherent E) :
    ((idealSub J E : Subobject E) : X.Modules).IsQuasicoherent := by
  have := hE.1
  have := (isCoherent_pullback J.subschemeι hE).1
  have h₀ : ((𝟭 X.Modules).obj E).IsQuasicoherent := hE.1
  have h₁ : ((Scheme.Modules.pullback J.subschemeι ⋙ Scheme.Modules.pushforward J.subschemeι).obj
      E).IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom J.subschemeι
    ((Scheme.Modules.pullback J.subschemeι).obj E)
  have hk : (kernel ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app
      E)).IsQuasicoherent := GlobalTheory.QCoh.isQuasicoherent_kernel _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (kernel.ι
      ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app E))).symm hk

lemma propSupp_mono {A : Type} [CommRing A] [X.Over (Spec (.of A))] {E : X.Modules}
    {S S' : Subobject E} (h : S ≤ S') (hS : PropSupp A S) : PropSupp A S' := by
  obtain ⟨T, hT, hsupp⟩ := hS
  refine ⟨T, hT, ?_⟩
  have w : S.arrow ≫ cokernel.π S'.arrow = 0 := by
    rw [← Subobject.ofLE_arrow h, Category.assoc, cokernel.condition, comp_zero]
  have : Epi (cokernel.desc S.arrow (cokernel.π S'.arrow) w) :=
    epi_of_epi_fac (cokernel.π_desc S.arrow (cokernel.π S'.arrow) w)
  exact Scheme.Modules.SupportedIn.of_epi (cokernel.desc S.arrow (cokernel.π S'.arrow) w) hsupp

theorem statement_of_mul_mem : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))]
    (J J₁ J₂ : X.IdealSheafData),
    (∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U) →
    Statement I J₁ → Statement I J₂ → Statement I J := by
  intro A _ _ I X _ _ _ _ J J₁ J₂ hm h₁ h₂ E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hEq : E.IsQuasicoherent := hE.1
  set K : Subobject E := idealSub J₁ E with hKdef
  have hKq : (K : X.Modules).IsQuasicoherent := isQuasicoherent_idealSub J₁ hE
  have hS1 : ClosedSys I E (fun e => S e ⊔ K) :=
    { qcoh := fun e => (GlobalTheory.T.quasicoherent_sup_sections hEq _ _ (hS.qcoh e) hKq).1
      pow_le := fun e => (hS.pow_le e).trans le_sup_left
      succ := fun e => by
        conv_lhs => rw [hS.succ e]
        exact sup_right_comm _ _ _ }
  have hK1 : ∀ e, Killed J₁ (S e ⊔ K) := by
    intro e U a ha x
    have hax : a • x ∈ secs K U := by
      rw [hKdef, secs_idealSub]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    exact (GlobalTheory.T.subobject_le_iff_affine_sections K (S e ⊔ K)).1 le_sup_right U hax
  obtain ⟨B, hBq, hBP, hB⟩ := h₁ E hE _ hS1 hK1 (propSupp_mono le_sup_left hP)
  have hDq : ((B ⊔ K : Subobject E) : X.Modules).IsQuasicoherent :=
    (GlobalTheory.T.quasicoherent_sup_sections hEq _ _ hBq hKq).1
  have hDP : PropSupp A (B ⊔ K) := propSupp_mono le_sup_left hBP
  have hc : ∀ e, S (e + 0) ≤ (B ⊔ K) ⊔ powSub I E (e + 1) := fun e =>
    (le_sup_left : S e ≤ S e ⊔ K).trans ((hB e).symm.le.trans (sup_le_sup_right le_sup_left _))
  obtain ⟨c', hS', hP', halg⟩ := GlobalTheory.T.artin_rees_closed_system I hE hS hP (B ⊔ K) hDq 0 hc
  have hkill : ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J₂.ideal U →
      ∀ x ∈ secs (B ⊔ K) U, a • x ∈ secs (S n) U := by
    intro n U a ha x hx
    have hle : B ⊔ K ≤ S n ⊔ K :=
      sup_le ((le_sup_left : B ≤ B ⊔ powSub I E (n + 1)).trans (hB n).le) le_sup_right
    have hx' := (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 hle U hx
    rw [(GlobalTheory.T.quasicoherent_sup_sections hEq _ _ (hS.qcoh n) hKq).2 U U.2] at hx'
    obtain ⟨s, hs, k, hk, rfl⟩ := hx'
    rw [smul_add]
    refine add_mem_secs _ (smul_mem_secs _ a hs) ?_
    rw [hKdef, secs_idealSub] at hk
    refine Submodule.smul_induction_on (p := fun k => a • k ∈ secs (S n) U) hk
      (fun b hb y _ => ?_) (fun y z hy hz => ?_)
    · rw [smul_smul, mul_comm]
      exact hK n U _ (hm U b a hb ha) y
    · rw [smul_add]
      exact add_mem_secs _ hy hz
  exact halg (h₂ _ (GlobalTheory.T.coherent_subobject_coherent hE _ hDq) _ hS' (GlobalTheory.T.restricted_system_killed_by_ideal I J₂ _ S c' hkill) hP') hDP

end GlobalTheory.CompanionTheory.GE.NonPrime
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftProjectiveEmbeddingCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X X' : Scheme.{0}}

theorem pullLE_ofSec {M : LB X} (π : X' ⟶ X) (V : X.Opens) (V' : X'.Opens) (e : V' ≤ π ⁻¹ᵁ V)
    (s : LB.Sec M) :
    SecOn.pullLE M π V V' e (GlobalTheory.LB.ofSec s V) = GlobalTheory.LB.ofSec (secPull s π) V' := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [SecOn.coord_pullLE, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.appLE_resG]
  change _ = resG X' _ ((π.appLE _ _ (GlobalTheory.LB.pull_U_le π j)).hom (s.f (j PUnit.unit)))
  rw [GlobalTheory.LB.resG_appLE]

theorem secMaps_of_cover {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen)
    {κ : Type} (O : κ → X.Opens) (hO : ⨆ a, O a = ⊤) (s : LB.Sec A) (t : LB.Sec B)
    (h : ∀ a, SecOn.congr hA hB w hw (O a) (GlobalTheory.LB.ofSec s (O a)) = GlobalTheory.LB.ofSec t (O a)) :
    SecMaps w s t := by
  rintro ⟨p, q⟩
  refine ext_germ fun x hx => ?_
  obtain ⟨a, ha⟩ : ∃ a, x ∈ O a := by
    have hx' : x ∈ (⨆ a, O a) := by rw [hO]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx'
  have hp : O a ⊓ (B.U p ⊓ A.U q) ≤ O a ⊓ B.U p := inf_le_inf_left _ inf_le_left
  have hq : O a ⊓ (B.U p ⊓ A.U q) ≤ O a ⊓ A.U q := inf_le_inf_left _ inf_le_right
  have hh : O a ⊓ (B.U p ⊓ A.U q) ≤ B.U p ⊓ A.U q := inf_le_right
  have e := SecOn.coord_congr hA hB w hw (GlobalTheory.LB.ofSec s (O a)) p q hp hq hh
  rw [h a, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec] at e
  have hxW : x ∈ O a ⊓ (B.U p ⊓ A.U q) := ⟨ha, hx⟩
  change resG X hp (resG X _ (t.f p)) = resG X hh _ * resG X hq (resG X _ (s.f q)) at e
  rw [resG_resG, resG_resG] at e
  refine (germ_resG hh x hxW _).symm.trans ((congrArg _ ?_).trans (germ_resG hh x hxW _))
  rw [map_mul, resG_resG, resG_resG]
  exact e

section Tower

variable {R : Type} [CommRing R] (I : Ideal R)
  (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
  (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
  (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
  (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen)

include hL in

theorem congr_ofSec_of_redL (e : ℕ) (V : (Y (e + 1)).left.Opens) (V' : (Y e).left.Opens)
    (h : V' ≤ β e ⁻¹ᵁ V) (τ : LB.Sec (L (e + 1))) (σ : LB.Sec (L e))
    (hr : redL I Y β hβ L w hL e V V' h (SecOnR.of _ _ _ (GlobalTheory.LB.ofSec τ V)) =
      SecOnR.of _ _ _ (GlobalTheory.LB.ofSec σ V')) :
    SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e) (hL e).2 V'
      (GlobalTheory.LB.ofSec σ V') = GlobalTheory.LB.ofSec (secPull τ (β e)) V' := by
  have h1 := (LinearEquiv.symm_apply_eq _).1 hr
  rw [SecOnR.pull_of, SecOnR.linEquiv_of] at h1
  exact h1.symm.trans (pullLE_ofSec (β e) V V' h τ)

end Tower

theorem lift_of_cech_pairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (t : ℤ) (e : ℕ), (∀ (c : ∀ i j : Fin (m + 1), Tm I Y N D (d : ℤ) (e + 1) t {i, j}), (∀ i j, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i, j} (c i j) = 0) → (∀ i j k, resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ij i j k) (c i j) + resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_jk i j k) (c j k) = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i, Tm I Y N D (d : ℤ) (e + 1) t {i}, (∀ i, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i} (b i) = 0) ∧ ∀ i j, c i j = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i) - resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j)) → ∀ σ : LB.Sec (pw (N e) ((d : ℤ) * t)), ∃ σ' : LB.Sec (pw (N (e + 1)) ((d : ℤ) * t)), SecMaps (pullPow (v e) ((d : ℤ) * t)) σ (secPull σ' (β e)) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa t e hc σ
  have hLp : ∀ e, (pw (N e) ((d : ℤ) * t)).IsLB ∧ (pullPow (v e) ((d : ℤ) * t)).IsGen :=
    fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩

  have hres : ∀ (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (x : Tm I Y N D (d : ℤ) (e + 1) t S),
      red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e S'
          (resT I Y N D (d : ℤ) hDm (e + 1) t h x) =
        resT I Y N D (d : ℤ) hDm e t h
          (red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e S x) :=
    fun S S' h x => GlobalTheory.T.thickening_restriction_compatible_opens R I Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t)) hLp e (D (e + 1) S) (D (e + 1) S') (D e S) (D e S')
      (hDβ e S).ge (hDβ e S').ge (hDm (e + 1) S S' h) (hDm e S S' h) x
  have hrr : ∀ (e : ℕ) (S S' S'' : Finset (Fin (m + 1))) (h : S ⊆ S') (h' : S' ⊆ S'')
      (x : Tm I Y N D (d : ℤ) e t S),
      resT I Y N D (d : ℤ) hDm e t h' (resT I Y N D (d : ℤ) hDm e t h x) =
        resT I Y N D (d : ℤ) hDm e t (h.trans h') x :=
    fun e S S' S'' h h' x => SecOnR.restrict_restrict _ _ _ x

  let σS : ∀ S, Tm I Y N D (d : ℤ) e t S := fun S => SecOnR.of _ _ _ (GlobalTheory.LB.ofSec σ (D e S))
  have hσS : ∀ (S S' : Finset (Fin (m + 1))) (h : S ⊆ S'),
      resT I Y N D (d : ℤ) hDm e t h (σS S) = σS S' :=
    fun S S' h => SecOn.restrict_ofSec σ (hDm e S S' h)

  have hlift : ∀ i, ∃ b : Tm I Y N D (d : ℤ) (e + 1) t {i},
      red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i} b = σS {i} :=
    fun i => (GlobalTheory.T.thickening_affine_preimage R I Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t)) hLp e (D (e + 1) {i}) (D e {i}) (hDβ e {i})
      (hDa (e + 1) {i} (Finset.singleton_nonempty i))).1 (σS {i})
  choose b hb using hlift
  obtain ⟨b', hb'0, hb'c⟩ := hc
    (fun i j => resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i) -
      resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j))
    (fun i j => by
      rw [map_sub, hres, hres, hb, hb, hσS, hσS, sub_self])
    (fun i j k => by
      simp only [map_sub, hrr]
      abel)

  have hf : ∀ i j, resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i - b' i) =
      resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j - b' j) := fun i j => by
    rw [map_sub, map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.1 (hb'c i j)
  have hfr : ∀ i, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i}
      (b i - b' i) = σS {i} := fun i => by rw [map_sub, hb, hb'0, sub_zero]

  obtain ⟨τ, hτ, -⟩ := SecOnR.existsUnique_glue (toR I Y (e + 1)) (M := pw (N (e + 1)) ((d : ℤ) * t))
    (V := ⊤) (fun i => D (e + 1) {i}) (fun _ => le_top) (hDc (e + 1)).ge (fun i => b i - b' i)
    (fun i j => by
      have hij : D (e + 1) {i} ⊓ D (e + 1) {j} ≤ D (e + 1) {i, j} := by
        rw [show ({i, j} : Finset (Fin (m + 1))) = insert i {j} from rfl, hDi (e + 1) {j} i,
          inf_comm]
      have h1 := congrArg (SecOnR.restrict (toR I Y (e + 1)) (pw (N (e + 1)) ((d : ℤ) * t)) hij)
        (hf i j)
      exact (SecOnR.restrict_restrict _ _ _ _).symm.trans
        (h1.trans (SecOnR.restrict_restrict _ _ _ _)))
  let σ' : LB.Sec (pw (N (e + 1)) ((d : ℤ) * t)) := SecOnR.topEquiv _ _ τ
  have hτσ : τ = SecOnR.of _ _ _ (GlobalTheory.LB.ofSec σ' ⊤) :=
    ((SecOn.topEquiv (pw (N (e + 1)) ((d : ℤ) * t))).symm_apply_apply τ).symm
  refine ⟨σ', secMaps_of_cover (hLp e).1 (LB.isLB_pull (hLp (e + 1)).1 (β e)) _ (hLp e).2
    (fun i => D e {i}) (hDc e) σ (secPull σ' (β e)) fun i => ?_⟩
  refine congr_ofSec_of_redL I Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
    (fun e => pullPow (v e) ((d : ℤ) * t)) hLp e (D (e + 1) {i}) (D e {i}) (hDβ e {i}).ge σ' σ ?_
  have h2 : SecOnR.of (toR I Y (e + 1)) _ _ (GlobalTheory.LB.ofSec σ' (D (e + 1) {i})) = b i - b' i := by
    rw [← hτ i, hτσ]
    exact (SecOn.restrict_ofSec σ' le_top).symm
  rw [h2]
  exact hfr i

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftSectionsNonvanishingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_sections_nonvanishing : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (hc : ∀ e S, OperatorsCommute (ι := Fin (m + 1)) (R := R) (A := fun t => Tm I Y N D (d : ℤ) e t S) fun j t => mulT I Y N D (d : ℤ) e t S (sh e j S)), (∀ e S j t (a : Tm I Y N D (d : ℤ) e t S), S.Nonempty → resT I Y N D (d : ℤ) hDm e t (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e S) t a = 0) ∧ (∀ e S j t (b : Tm I Y N D (d : ℤ) e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : Tm I Y N D (d : ℤ) e t' S), GrSum.of (hc e (insert j S)) t' (resT I Y N D (d : ℤ) hDm e t' (Finset.subset_insert j S) a) = (MvPolynomial.X j : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e (insert j S)) t b) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.localisation_grSum | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.localisation_grSum | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.localisation_grSum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftVeryAmpleSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_very_ample_sections : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)), ∃ sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S), (∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) ∧ (∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) ∧ (∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_lifts_tower | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_lifts_tower | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_lifts_tower <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureLocalBall
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi.BallVol

theorem measure_translate_ballV : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (k : ℕ) (a : Fv F v), lam ((fun z => z - a) ⁻¹' ballV v k) = ENNReal.ofReal (((Ideal.absNorm v.asIdeal : ℝ) ^ k)⁻¹) := by
  intro F _ _ v lam hlam k a
  obtain ⟨hHaar, h1⟩ := hlam
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : ProperSpace (Fv F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : lam.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure lam
  have htr : (fun z => z - a) ⁻¹' ballV v k = (fun z => z + -a) ⁻¹' ballV v k := by
    simp only [sub_eq_add_neg]
  rw [htr, measure_preimage_add_right]
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  let ϖ : Fv F v := ((π : v.adicCompletion F) : Fv F v)
  have hvϖ : Valued.v ϖ = WithZero.exp (-1) := by
    rw [← hπ]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hvϖ
    exact WithZero.exp_ne_zero hvϖ.symm
  open Pointwise in
  have hball : ballV v k = (ϖ ^ k) • (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext z
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (pow_ne_zero k hϖ0)]
    simp only [ballV, Set.mem_ofPred_eq, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      smul_eq_mul, map_mul, map_inv₀, map_pow, hvϖ]
    have hk : (WithZero.exp (-1 : ℤ)) ^ k = WithZero.exp (-(k : ℤ)) := by
      rw [← WithZero.exp_nsmul]; simp
    rw [hk, inv_mul_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), mul_one]
  rw [hball]
  have hu : IsUnit (ϖ ^ k) := (pow_ne_zero k hϖ0).isUnit
  open Pointwise in
  have key := distribHaarChar_mul lam hu.unit (v.adicCompletionIntegers F : Set (Fv F v))
  rw [Units.smul_def, IsUnit.unit_spec, h1, mul_one] at key
  rw [← key]
  have hm := GlobalTheory.GaugeProdFormula.modu_finite F v (ϖ ^ k) (pow_ne_zero k hϖ0)
  rw [GlobalTheory.GaugeEx.modu, dif_pos hu] at hm
  have hn : ‖ϖ‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ := by
    rw [NumberField.FinitePlace.norm_def, HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π, hπ,
      WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    show (((Ideal.absNorm v.asIdeal : NNReal) ^ (-1 : ℤ) : NNReal) : ℝ) = _
    rw [zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]
  rw [norm_pow, hn, inv_pow] at hm
  rw [← hm, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.CompanionTheory.Equi.BallVol
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicFunctionFactsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_function_facts : PositivityTheory.RgDs.K.HolFacts := by
  first | exact @GlobalTheory.CompanionTheory.HolOm.holFacts | exact GlobalTheory.CompanionTheory.HolOm.holFacts | (intros; apply GlobalTheory.CompanionTheory.HolOm.holFacts <;> assumption)
end

