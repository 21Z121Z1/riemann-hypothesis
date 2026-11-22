import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Formalism.CharacterColumnKernels.StatementRho
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedOddDegreeQuadraticLocalExt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Formalism.GaloisCohomology.Statement

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualityClausesOfMulEquiv
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

noncomputable section

namespace GlobalTheory.CohTransport

section Res

variable {R : Type*} [CommRing R]
  {Γ Γ' : Type*} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
  {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
  (σ : Representation R Γ N) (σ' : Representation R Γ' N) (φ : Γ' →* Γ)
  (hσ : ∀ g n, σ' g n = σ (φ g) n)

def rh0 : H0 σ →ₗ[R] H0 σ' :=
  Submodule.inclusion fun m hm g => by
    show σ' g m = m
    rw [hσ]; exact hm (φ g)

@[simp] theorem rh0_coe (m : H0 σ) : ((rh0 σ σ' φ hσ m : H0 σ') : N) = m := rfl

variable (hφ : Continuous φ)

def rz1 : Z1 σ →ₗ[R] Z1 σ' where
  toFun f := ⟨f.1 ∘ φ, f.2.1.comp hφ, fun g h => by
    simp only [Function.comp_apply, map_mul, hσ]; exact f.2.2 _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rh1 : H1 σ →ₗ[R] H1 σ' :=
  Submodule.mapQ _ _ (rz1 σ σ' φ hσ hφ) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 σ _).1 hf
    refine (mem_coboundaries1 _ _).2 ⟨m, fun h => ?_⟩
    show f.1 (φ h) = σ' h m - m
    rw [hσ]; exact hm (φ h)

def rz2 : Z2 σ →ₗ[R] Z2 σ' where
  toFun f := ⟨fun p => f.1 (φ p.1, φ p.2), f.2.1.comp (hφ.prodMap hφ), fun g h k => by
    simp only [map_mul, hσ]; exact f.2.2 _ _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rh2 : H2 σ →ₗ[R] H2 σ' :=
  Submodule.mapQ _ _ (rz2 σ σ' φ hσ hφ) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem σ _).1 hf
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ φ, hc.comp hφ, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    have e := congrFun hcf (φ g, φ h)
    simp only [Submodule.coe_subtype] at e
    change _ = f.1 (φ g, φ h)
    rw [← e]
    simp [d1_apply, hσ, map_mul]

end Res

section Equiv

variable {R : Type*} [CommRing R]
  {Γ Γ' : Type*} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
  {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
  (σ : Representation R Γ N) (σ' : Representation R Γ' N) (e : Γ' ≃* Γ)
  (he : Continuous e) (he' : Continuous e.symm)

theorem symm_rel (hσ : ∀ g n, σ' g n = σ (e g) n) : ∀ g n, σ g n = σ' (e.symm g) n := fun g n => by
  rw [hσ, MulEquiv.apply_symm_apply]

def eq0 (hσ : ∀ g n, σ' g n = σ (e g) n) : H0 σ ≃ₗ[R] H0 σ' :=
  LinearEquiv.ofLinear (rh0 σ σ' e.toMonoidHom hσ)
    (rh0 σ' σ e.symm.toMonoidHom (symm_rel σ σ' e hσ)) (by ext; rfl) (by ext; rfl)

def eq1 (hσ : ∀ g n, σ' g n = σ (e g) n) : H1 σ ≃ₗ[R] H1 σ' :=
  LinearEquiv.ofLinear (rh1 σ σ' e.toMonoidHom hσ he)
    (rh1 σ' σ e.symm.toMonoidHom (symm_rel σ σ' e hσ) he')
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => by
        show f.1 (e.symm (e g)) = f.1 g
        rw [MulEquiv.symm_apply_apply])))
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => by
        show f.1 (e (e.symm g)) = f.1 g
        rw [MulEquiv.apply_symm_apply])))

def eq2 (hσ : ∀ g n, σ' g n = σ (e g) n) : H2 σ ≃ₗ[R] H2 σ' :=
  LinearEquiv.ofLinear (rh2 σ σ' e.toMonoidHom hσ he)
    (rh2 σ' σ e.symm.toMonoidHom (symm_rel σ σ' e hσ) he')
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => by
        show f.1 (e.symm (e p.1), e.symm (e p.2)) = f.1 p
        rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply])))
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => by
        show f.1 (e (e.symm p.1), e (e.symm p.2)) = f.1 p
        rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply])))

end Equiv

theorem bijective_of_conj {R : Type*} [CommRing R] {A B C A' B' C' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B'] [AddCommGroup C'] [Module R C']
    (b : A →ₗ[R] B →ₗ[R] C) (b' : A' →ₗ[R] B' →ₗ[R] C') (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B')
    (eC : C ≃ₗ[R] C') (h : ∀ a x, b' (eA a) (eB x) = eC (b a x)) (hb : Function.Bijective b') :
    Function.Bijective b := by
  have key : (⇑b' ∘ ⇑eA) = ⇑(LinearEquiv.arrowCongr eB eC) ∘ ⇑b := by
    funext a
    refine LinearMap.ext fun x => ?_
    simp only [Function.comp_apply, LinearEquiv.arrowCongr_apply]
    rw [← h, LinearEquiv.apply_symm_apply]
  have h2 : Function.Bijective (⇑(LinearEquiv.arrowCongr eB eC) ∘ ⇑b) := key ▸ hb.comp eA.bijective
  exact (LinearEquiv.bijective _).of_comp_iff' _ |>.1 h2

theorem dualityClauses_of_mulEquiv : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [DiscreteTopology R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (h : ContAction ρ) (h' : ContAction (ρ.comp e.toMonoidHom)), (Nonempty (H2 (charRep (χ.comp e.toMonoidHom)) ≃ₗ[R] R) ∧ Function.Bijective (cupH0H2TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)) ∧ Function.Bijective (cupH1H1TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _) (h'.comp' continuous_id)) ∧ Function.Bijective (cupH1H1TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _) (h'.comp' continuous_id)).flip ∧ Function.Bijective (cup20 (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _))) → (Nonempty (H2 (charRep χ) ≃ₗ[R] R) ∧ Function.Bijective (cupH0H2TwistedDual χ ρ (MonoidHom.id _)) ∧ Function.Bijective (cupH1H1TwistedDual χ ρ (MonoidHom.id _) (h.comp' continuous_id)) ∧ Function.Bijective (cupH1H1TwistedDual χ ρ (MonoidHom.id _) (h.comp' continuous_id)).flip ∧ Function.Bijective (cup20 χ ρ (MonoidHom.id _))) := by
  intro R _ _ _ Γ Γ' _ _ _ _ M _ _ _ _ _ e he he' χ ρ h h' H
  have hA : ∀ g m, ((ρ.comp e.toMonoidHom).comp (MonoidHom.id Γ')) g m =
      (ρ.comp (MonoidHom.id Γ)) (e g) m := fun _ _ => rfl
  have hB : ∀ g φ, ((twDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)).comp
      (MonoidHom.id Γ')) g φ = ((twDual χ ρ).comp (MonoidHom.id Γ)) (e g) φ := by
    intro g φ
    refine TDual.ext fun m => ?_
    simp [twDual_apply, map_inv]
  have hC : ∀ g x, ((charRep (χ.comp e.toMonoidHom)).comp (MonoidHom.id Γ')) g x =
      ((charRep χ).comp (MonoidHom.id Γ)) (e g) x := fun _ _ => rfl
  let E0A := eq0 _ _ e hA
  let E0B := eq0 _ _ e hB
  let FrameLocalData := eq1 _ _ e he he' hA
  let E1B := eq1 _ _ e he he' hB
  let E2A := eq2 _ _ e he he' hA
  let E2B := eq2 _ _ e he he' hB
  let E2C := eq2 _ _ e he he' hC
  have c02 : ∀ m y, cupH0H2TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)
      (E0A m) (E2B y) = E2C (cupH0H2TwistedDual χ ρ (MonoidHom.id _) m y) := by
    intro m y
    induction y using Submodule.Quotient.induction_on with
    | H f => rfl
  have c11 : ∀ y x, cupH1H1TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)
      (h'.comp' continuous_id) (E1B y) (FrameLocalData x) =
      E2C (cupH1H1TwistedDual χ ρ (MonoidHom.id _) (h.comp' continuous_id) y x) := by
    intro y x
    induction y using Submodule.Quotient.induction_on with
    | H f =>
      induction x using Submodule.Quotient.induction_on with
      | H f' => rfl
  have c20 : ∀ x m, cup20 (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)
      (E2A x) (E0B m) = E2C (cup20 χ ρ (MonoidHom.id _) x m) := by
    intro x m
    induction x using Submodule.Quotient.induction_on with
    | H f => rfl
  obtain ⟨⟨j⟩, b02, b11, b11', b20⟩ := H
  refine ⟨⟨(eq2 (charRep χ) (charRep (χ.comp e.toMonoidHom)) e he he' (fun _ _ => rfl)).trans j⟩,
    bijective_of_conj _ _ E0A E2B E2C c02 b02, bijective_of_conj _ _ E1B FrameLocalData E2C c11 b11,
    bijective_of_conj _ _ FrameLocalData E1B E2C (fun x y => by simp only [LinearMap.flip_apply]; exact c11 y x) b11',
    bijective_of_conj _ _ E2A E0B E2C c20 b20⟩

end GlobalTheory.CohTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBaseNearOfDecompositionFixedStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_near_of_decomposition_fixed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (z : Ω), (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r := by
  first | exact @GlobalTheory.exists_base_near_of_dec_fixed | exact GlobalTheory.exists_base_near_of_dec_fixed | (intros; apply GlobalTheory.exists_base_near_of_dec_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisTraceInvolutionDetUnitUnramifiedStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_trace_involution_det_unit_unramified : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → letI : Algebra K.E K'.E := φ.toAlgebra; ∃ w : Module.Basis (Fin d) K.E K'.E, (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det ≠ 0 ∧ val K.O (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = 0 := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit | exact GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit | (intros; apply GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactPreimageNormCentralizerHermitianStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_preimage_norm_centralizer_hermitian : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ M : Set (GL (Fin r) E), IsCompact M → ∃ S : Set (GL (Fin r) E), IsCompact S ∧ ∀ t : GL (Fin r) E, (t : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) E) → (∃ m ∈ M, (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = (m : Matrix (Fin r) (Fin r) E)) → ∃ s ∈ S, (s : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (s : Matrix (Fin r) (Fin r) E) ∧ (s : Matrix (Fin r) (Fin r) E) * star (s : Matrix (Fin r) (Fin r) E) = (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) := by
  first | exact @GlobalTheory.NormSec.normsec | exact GlobalTheory.NormSec.normsec | (intros; apply GlobalTheory.NormSec.normsec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivFractionRingQuotPiProdFinite
section
open ReciprocityTheory.Gal

namespace GlobalTheory.CofinGen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem exists_pow_smul_eq {M : Type} [AddCommGroup M] [Module O M]
    (hd : ∀ m : M, ∃ m', ϖ • m' = m) (n : ℕ) (m : M) : ∃ m', ϖ ^ n • m' = m := by
  induction n generalizing m with
  | zero => exact ⟨m, by simp⟩
  | succ n ih =>
    obtain ⟨m1, h1⟩ := ih m
    obtain ⟨m2, h2⟩ := hd m1
    exact ⟨m2, by rw [pow_succ, mul_smul, h2, h1]⟩

theorem baer_of_div (hϖ : Irreducible ϖ) {M : Type} [AddCommGroup M] [Module O M]
    (hd : ∀ m : M, ∃ m', ϖ • m' = m) : Module.Baer O M := by
  intro I g
  by_cases hI : I = ⊥
  · subst hI
    refine ⟨0, fun x hx => ?_⟩
    have : (⟨x, hx⟩ : (⊥ : Ideal O)) = 0 := Subtype.ext (by simpa using hx)
    rw [this]; simp
  · obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
    subst hn
    obtain ⟨m, hm⟩ := exists_pow_smul_eq hd n (g ⟨ϖ ^ n, Ideal.mem_span_singleton_self _⟩)
    refine ⟨LinearMap.toSpanSingleton O M m, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have : (⟨c * ϖ ^ n, hx⟩ : Ideal.span {ϖ ^ n}) =
        c • ⟨ϖ ^ n, Ideal.mem_span_singleton_self _⟩ := Subtype.ext rfl
    rw [this, map_smul, ← hm, LinearMap.toSpanSingleton_apply, mul_smul]

theorem KO_div (hϖ : Irreducible ϖ) (m : Formalism.NG.KO O) : ∃ m', ϖ • m' = m := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by
    simpa using hϖ.ne_zero
  refine ⟨Submodule.Quotient.mk ((algebraMap O (FractionRing O) ϖ)⁻¹ * x), ?_⟩
  rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

theorem exists_inj (hϖ : Irreducible ϖ) {M : Type} [AddCommGroup M] [Module O M]
    (hd : ∀ m : M, ∃ m', ϖ • m' = m) (y : M) (hy : y ≠ 0) (hy' : ϖ • y = 0) :
    ∃ i : Formalism.NG.KO O →ₗ[O] M, Function.Injective i ∧ y ∈ LinearMap.range i := by
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by
    simpa using hϖ.ne_zero
  set w : FractionRing O := (algebraMap O (FractionRing O) ϖ)⁻¹ with hw
  have hinj : Function.Injective (LinearMap.toSpanSingleton O (FractionRing O) w) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_eq_zero] at hc
    rcases hc with hc | hc
    · simpa using hc
    · exact absurd hc (inv_ne_zero h0)
  obtain ⟨h, hh⟩ := (baer_of_div hϖ hd).extension_property _ hinj
    (LinearMap.toSpanSingleton O M y)
  have hw1 : h w = y := by simpa using LinearMap.congr_fun hh 1
  have h1 : h 1 = 0 := by
    have : (1 : FractionRing O) = ϖ • w := by rw [Algebra.smul_def, hw, mul_inv_cancel₀ h0]
    rw [this, map_smul, hw1, hy']
  have hle : (1 : Submodule O (FractionRing O)) ≤ LinearMap.ker h := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hx
    rw [LinearMap.mem_ker, Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
  refine ⟨Submodule.liftQ _ h hle, ?_, ⟨Submodule.Quotient.mk w, by simpa using hw1⟩⟩
  rw [← LinearMap.ker_eq_bot]
  refine Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => ?_
  rw [LinearMap.mem_ker] at hx
  by_cases hx0 : x = 0
  · subst hx0; exact Submodule.zero_mem _
  rcases ValuationRing.isInteger_or_isInteger O x with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Submodule.mem_one.2 ⟨c, hc⟩
  · by_cases hu : IsUnit c
    · obtain ⟨d, hd'⟩ := hu.exists_right_inv
      refine Submodule.mem_one.2 ⟨d, ?_⟩
      have := congrArg (algebraMap O (FractionRing O)) hd'
      rw [map_mul, hc, map_one] at this
      field_simp at this
      exact this
    · exfalso
      have hm : c ∈ IsLocalRing.maximalIdeal O := hu
      rw [hϖ.maximalIdeal_eq] at hm
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hm
      have : w = d • x := by
        rw [map_mul] at hc
        rw [Algebra.smul_def, hw]
        field_simp at hc ⊢
        rw [← hc]
      apply hy
      rw [← hw1, this, map_smul, hx, smul_zero]

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem exists_socle {Y : Type} [AddCommGroup Y] [Module O Y]
    (hp : ∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) (T : Submodule O Y) (y : Y) (hy : y ∈ T) (h0 : y ≠ 0) :
    ∃ z ∈ T, z ≠ 0 ∧ ϖ • z = 0 := by
  obtain ⟨n, hn⟩ := hp y
  induction n generalizing y with
  | zero => exact absurd (by simpa using hn) h0
  | succ n ih =>
    by_cases h : ϖ • y = 0
    · exact ⟨y, hy, h0, h⟩
    · exact ih (ϖ • y) (T.smul_mem _ hy) h (by rw [← mul_smul, ← pow_succ, hn])

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem finite_fiber {Y : Type} [AddCommGroup Y] [Module O Y]
    (hf : {y : Y | ϖ • y = 0}.Finite) (y : Y) : {z : Y | ϖ • z = y}.Finite := by
  rcases Set.eq_empty_or_nonempty {z : Y | ϖ • z = y} with h | ⟨z, hz⟩
  · rw [h]; exact Set.finite_empty
  · refine (hf.image (fun t => z + t)).subset fun x hx => ⟨x - z, ?_, by simp⟩
    simp only [Set.mem_setOf_eq] at hz hx ⊢
    rw [smul_sub, hz, hx, sub_self]

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem finite_pow {Y : Type} [AddCommGroup Y] [Module O Y]
    (hf : {y : Y | ϖ • y = 0}.Finite) (n : ℕ) : {z : Y | ϖ ^ n • z = 0}.Finite := by
  induction n with
  | zero => exact (Set.finite_singleton 0).subset fun x hx => by simpa using hx
  | succ n ih =>
    refine (ih.biUnion fun y _ => finite_fiber hf y).subset fun x hx => ?_
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
    exact ⟨ϖ • x, by rw [← mul_smul, ← pow_succ, hx], rfl⟩

def pw (ϖ : O) (Y : Type) [AddCommGroup Y] [Module O Y] (n : ℕ) : Submodule O Y :=
  LinearMap.range (ϖ ^ n • LinearMap.id : Y →ₗ[O] Y)

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem mem_pw {Y : Type} [AddCommGroup Y] [Module O Y] {n : ℕ} {y : Y} :
    y ∈ pw ϖ Y n ↔ ∃ z, ϖ ^ n • z = y := Iff.rfl

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem pw_anti {Y : Type} [AddCommGroup Y] [Module O Y] {n m : ℕ} (h : n ≤ m) :
    pw ϖ Y m ≤ pw ϖ Y n := by
  intro y hy
  obtain ⟨z, rfl⟩ := mem_pw.1 hy
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact mem_pw.2 ⟨ϖ ^ k • z, by rw [pow_add, mul_smul]⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem exists_uniform {Y : Type} [AddCommGroup Y] [Module O Y] {S : Set Y} (hS : S.Finite) :
    ∃ N, ∀ y ∈ S, y ∈ pw ϖ Y N → y ∈ ⨅ n, pw ϖ Y n := by
  have h1 : ∀ y : Y, ∃ N, y ∈ pw ϖ Y N → y ∈ ⨅ n, pw ϖ Y n := by
    intro y
    by_cases h : y ∈ ⨅ n, pw ϖ Y n
    · exact ⟨0, fun _ => h⟩
    · rw [Submodule.mem_iInf, not_forall] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨n, fun h => absurd h hn⟩
  choose f hf using h1
  obtain ⟨N, hN⟩ := (hS.image f).bddAbove
  exact ⟨N, fun y hy h => hf y (pw_anti (hN ⟨y, hy, rfl⟩) h)⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem iInf_div {Y : Type} [AddCommGroup Y] [Module O Y]
    (hf : {y : Y | ϖ • y = 0}.Finite) (m : (⨅ n, pw ϖ Y n : Submodule O Y)) :
    ∃ m', ϖ • m' = m := by
  obtain ⟨N, hN⟩ := exists_uniform (ϖ := ϖ) (finite_fiber hf m.1)
  obtain ⟨z, hz⟩ := mem_pw.1 ((Submodule.mem_iInf _).1 m.2 (N + 1))
  have h1 : ϖ • ϖ ^ N • z = m.1 := by rw [← mul_smul, ← pow_succ', hz]
  exact ⟨⟨ϖ ^ N • z, hN _ h1 (mem_pw.2 ⟨z, rfl⟩)⟩, Subtype.ext h1⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem finite_of_iInf_bot {Y : Type} [AddCommGroup Y] [Module O Y]
    (hp : ∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) (hf : {y : Y | ϖ • y = 0}.Finite)
    (hb : (⨅ n, pw ϖ Y n : Submodule O Y) = ⊥) : Finite Y := by
  obtain ⟨N, hN⟩ := exists_uniform (ϖ := ϖ) hf
  have : ∀ y : Y, ϖ ^ N • y = 0 := by
    intro y
    by_contra h
    obtain ⟨z, hz, hz0, hz1⟩ := exists_socle hp (pw ϖ Y N) _ (mem_pw.2 ⟨y, rfl⟩) h
    have := hN z hz1 hz
    rw [hb] at this
    exact hz0 (by simpa using this)
  exact Set.finite_univ_iff.1 ((finite_pow hf N).subset fun y _ => this y)

theorem aux (hϖ : Irreducible ϖ) (k : ℕ) : ∀ {Y : Type} [AddCommGroup Y] [Module O Y],
    (∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) → {y : Y | ϖ • y = 0}.Finite →
    {y : Y | ϖ • y = 0}.ncard = k →
    ∃ (a : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Module O F), Finite F ∧
      Nonempty (Y ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Y _ _ hp hf hk
  by_cases hb : (⨅ n, pw ϖ Y n : Submodule O Y) = ⊥
  · exact ⟨0, Y, inferInstance, inferInstance, finite_of_iInf_bot hp hf hb,
      ⟨(LinearEquiv.uniqueProd).symm⟩⟩
  · obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hb
    obtain ⟨z, hz, hz0, hz1⟩ := exists_socle hp _ y hy hy0
    obtain ⟨i0, hi0, x, hx⟩ := exists_inj hϖ (iInf_div hf) ⟨z, hz⟩
      (fun h => hz0 (congrArg Subtype.val h)) (Subtype.ext hz1)
    set i : Formalism.NG.KO O →ₗ[O] Y := (Submodule.subtype _).comp i0 with hi
    have hinj : Function.Injective i := Subtype.val_injective.comp hi0
    have hxz : i x = z := congrArg Subtype.val hx
    obtain ⟨r, hr⟩ := (baer_of_div hϖ (KO_div hϖ)).extension_property i hinj LinearMap.id
    have hri : ∀ t, r (i t) = t := fun t => LinearMap.congr_fun hr t
    have hsub : Subtype.val '' {y : LinearMap.ker r | ϖ • y = 0} ⊂ {y : Y | ϖ • y = 0} := by
      refine ⟨?_, fun h => ?_⟩
      · rintro _ ⟨t, ht, rfl⟩
        exact congrArg Subtype.val ht
      · obtain ⟨t, -, ht⟩ := h hz1
        have h2 : r z = 0 := ht ▸ t.2
        rw [← hxz, hri] at h2
        exact hz0 (by rw [← hxz, h2, map_zero])
    have hf' : {y : LinearMap.ker r | ϖ • y = 0}.Finite :=
      (hf.subset hsub.1).of_finite_image Subtype.val_injective.injOn
    have hlt := Set.ncard_lt_ncard hsub hf
    rw [Set.ncard_image_of_injective _ Subtype.val_injective, hk] at hlt
    obtain ⟨a, F, _, _, hF, ⟨e⟩⟩ := ih _ hlt (Y := LinearMap.ker r)
      (fun t => (hp t.1).imp fun n hn => Subtype.ext hn) hf' rfl
    have hbij : Function.Bijective (i.coprod (LinearMap.ker r).subtype) := by
      constructor
      · rw [injective_iff_map_eq_zero]
        rintro ⟨s, t⟩ h
        have h1 : i s + t.1 = 0 := h
        have h2 := congrArg r h1
        rw [map_add, hri, t.2, add_zero, map_zero] at h2
        subst h2
        rw [map_zero, zero_add] at h1
        exact Prod.ext rfl (Subtype.ext h1)
      · intro y
        exact ⟨(r y, ⟨y - i (r y), by simp [hri]⟩), by simp⟩
    refine ⟨a + 1, F, inferInstance, inferInstance, hF, ⟨?_⟩⟩
    exact (LinearEquiv.ofBijective _ hbij).symm ≪≫ₗ (LinearEquiv.refl O _).prodCongr e ≪≫ₗ
      (LinearEquiv.prodAssoc O _ _ _).symm ≪≫ₗ
      (Fin.consLinearEquiv O fun _ : Fin (a + 1) => Formalism.NG.KO O).prodCongr (LinearEquiv.refl O F)

theorem exists_equiv_pi_prod_finite :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ {Y : Type} [AddCommGroup Y] [Module O Y], (∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) →
    Finite (LinearMap.ker (ϖ • LinearMap.id : Y →ₗ[O] Y)) →
    ∃ (a : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Module O F), Finite F ∧
      Nonempty (Y ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) := by
  intro O _ _ _ ϖ hϖ Y _ _ hp hf
  exact aux hϖ _ hp hf rfl

end GlobalTheory.CofinGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTraceUnramifiedQuadraticLocalExtStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_trace_unramifiedQuadraticLocalExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.O, ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  first | exact @GlobalTheory.UnitLemma.Unr.trace_int | exact GlobalTheory.UnitLemma.Unr.trace_int | (intros; apply GlobalTheory.UnitLemma.Unr.trace_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLtCommutatorMemOfNeTop
section
open GlobalTheory.BI GlobalTheory.BrauerZero

namespace GlobalTheory

theorem exists_lt_commutator_mem_of_ne_top {G : Type} [Group G] [Finite G] [Group.IsNilpotent G]
    (K : Subgroup G) (hK : K ≠ ⊤) :
    ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K := by
  have hlt : K < Subgroup.normalizer (K : Set G) :=
    Group.normalizerCondition_of_isNilpotent K (lt_top_iff_ne_top.mpr hK)
  obtain ⟨x, hxN, hxK⟩ := SetLike.exists_of_lt hlt
  have hconj : ∀ i : ℤ, ∀ k ∈ K, x ^ i * k * (x ^ i)⁻¹ ∈ K := fun i k hk =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hxN i) k).mp hk
  let A : Subgroup G :=
    { carrier := {g | ∃ k ∈ K, ∃ i : ℤ, g = k * x ^ i}
      one_mem' := ⟨1, K.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k, hk, i, rfl⟩ ⟨k', hk', j, rfl⟩
        exact ⟨k * (x ^ i * k' * (x ^ i)⁻¹), K.mul_mem hk (hconj i k' hk'), i + j, by
          rw [zpow_add]; group⟩
      inv_mem' := by
        rintro _ ⟨k, hk, i, rfl⟩
        exact ⟨x ^ (-i) * k⁻¹ * (x ^ (-i))⁻¹, hconj (-i) _ (K.inv_mem hk), -i, by group⟩ }
  have hKA : K ≤ A := fun k hk => (⟨k, hk, 0, by simp⟩ : ∃ k' ∈ K, ∃ i : ℤ, k = k' * x ^ i)
  have hxA : x ∈ A := (⟨1, K.one_mem, 1, by simp⟩ : ∃ k ∈ K, ∃ i : ℤ, x = k * x ^ i)
  refine ⟨A, SetLike.lt_iff_le_and_exists.mpr ⟨hKA, x, hxA, hxK⟩, ?_⟩
  rintro _ ⟨k, hk, i, rfl⟩ _ ⟨k', hk', j, rfl⟩
  have h : k * x ^ i * (k' * x ^ j) * (k * x ^ i)⁻¹ * (k' * x ^ j)⁻¹ =
      k * (x ^ i * k' * (x ^ i)⁻¹) * (x ^ j * k⁻¹ * (x ^ j)⁻¹) * k'⁻¹ := by group
  rw [h]
  exact K.mul_mem (K.mul_mem (K.mul_mem hk (hconj i k' hk')) (hconj j _ (K.inv_mem hk)))
    (K.inv_mem hk')

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedOddDegreeQuadraticLocalExtStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_odd_degree_quadratic_local_ext : ∀ (K : UQ) (d : ℕ), Odd d → ∃ (K' : UQ) (φ : K.E →+* K'.E), K'.q = K.q ^ d ∧ (∀ x, φ (K.c x) = K'.c (φ x)) ∧ (∀ x, val K'.O (φ x) = val K.O x) ∧ (K.Odd → K'.Odd) ∧ @Module.finrank K.E K'.E _ _ (φ.toAlgebra).toModule = d ∧ ∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ := by
  first | exact @GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext | exact GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext | (intros; apply GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsZmodPowCoboundaryOfRationalCoboundaryStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zmod_pow_coboundary_of_rational_coboundary' : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (ε : Γ → ℤ_[l]) (O L : Type) [CommRing O] [Algebra ℤ_[l] O] [Field L] [TopologicalSpace L] [IsTopologicalRing L] (ι : O →+* L), Function.Injective ι → IsOpen (Set.range ι) → (l : L) ≠ 0 → (∀ x : L, ∃ n : ℕ, (l : L) ^ n * x ∈ Set.range ι) → ∀ (β : O →+ ZMod (l ^ 1)) (z : Γ → Γ → O) (f : Γ → L), Continuous f → (∀ g h, ι (z g h) = ι (algebraMap ℤ_[l] O (ε g)) * f h - f (g * h) + f g) → ∃ (n : ℕ) (a : Γ → ZMod (l ^ (n + 1))), Continuous a ∧ ∀ g h, PadicInt.toZModPow (n + 1) (ε g) * a h - a (g * h) + a g = ((l ^ n * (β (z g h)).val : ℕ) : ZMod (l ^ (n + 1))) := by
  first | exact @GlobalTheory.exists_zmod_pow_coboundary_of_rational_coboundary | exact GlobalTheory.exists_zmod_pow_coboundary_of_rational_coboundary | (intros; apply GlobalTheory.exists_zmod_pow_coboundary_of_rational_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FewRootsSmallDiscStatement
section
open Polynomial
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_roots_closedBall_le_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ) (W : ℂ_[l]), M ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ‖W‖ ≤ 1 → Multiset.card ((∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).roots.filter fun z => ‖z - W‖ ≤ ρ) ≤ l ^ M := by
  first | exact @GlobalTheory.few_roots_small_disc | exact GlobalTheory.few_roots_small_disc | (intros; apply GlobalTheory.few_roots_small_disc <;> assumption)
end

