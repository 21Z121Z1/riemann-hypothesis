import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0090
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFieldIdealsPrincipal
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.Capit

def clMap {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : ClassGroup A →* ClassGroup B :=
  letI := ψ.toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hψ
  ClassGroup.extendedHom A B

theorem clMap_mk0_eq_one_iff {A B : Type} [CommRing A] [IsDedekindDomain A] [CommRing B]
    [IsDedekindDomain B] (ψ : A →+* B) (hψ : Function.Injective ψ) (I : (Ideal A)⁰) :
    clMap ψ hψ (ClassGroup.mk0 I) = 1 ↔ (I.1.map ψ).IsPrincipal := by
  letI := ψ.toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hψ
  change ClassGroup.extendedHom A B (ClassGroup.mk0 I) = 1 ↔ _
  rw [ClassGroup.extendedHom_mk0]
  exact ClassGroup.mk0_eq_one_iff (ClassGroup.extendedIdeal A B I).2

theorem coeSubmodule_pow {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (I : Ideal R) (k : ℕ) :
    IsLocalization.coeSubmodule K (I ^ k) = IsLocalization.coeSubmodule K I ^ k := by
  induction k with
  | zero => simp [IsLocalization.coeSubmodule_top]
  | succ k ih => rw [pow_succ, pow_succ, IsLocalization.coeSubmodule_mul, ih]

variable {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ)

def intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) : 𝓞 E →+* 𝓞 F :=
  RingOfIntegers.mapRingHom (φ.codRestrict F h)

theorem coe_intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) (a : 𝓞 E) :
    ((intMap φ F h a : F) : ℂ) = φ (a : E) := rfl

theorem intMap_injective (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) :
    Function.Injective (intMap φ F h) := by
  intro a b hab
  have h1 : φ (a : E) = φ (b : E) := by rw [← coe_intMap φ F h, ← coe_intMap φ F h, hab]
  exact RingOfIntegers.ext (φ.injective h1)

def intIncl {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) : 𝓞 F →+* 𝓞 K :=
  RingOfIntegers.mapRingHom (IntermediateField.inclusion hFK).toRingHom

theorem map_intMap {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) (h : ∀ x, φ x ∈ F) (I : Ideal (𝓞 E)) :
    I.map (intMap φ K fun x => hFK (h x)) = (I.map (intMap φ F h)).map (intIncl hFK) := by
  rw [Ideal.map_map]; rfl

theorem isPrincipal_mono {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) (h : ∀ x, φ x ∈ F) (I : Ideal (𝓞 E))
    (hI : (I.map (intMap φ F h)).IsPrincipal) : (I.map (intMap φ K fun x => hFK (h x))).IsPrincipal := by
  obtain ⟨y, hy⟩ := hI
  rw [map_intMap φ hFK h, hy]
  exact ⟨intIncl hFK y, by simp [Ideal.map_span]⟩

theorem sz_mono' {F : IntermediateField ℚ ℂ} {a b a' b' : ℝ} (h : Sz F a b) (ha : a ≤ a') (hb : b ≤ b') :
    Sz F a' b' := by
  obtain ⟨i, h1, h2⟩ := h
  exact ⟨i, h1.trans ha, h2.trans hb⟩

theorem step (F : IntermediateField ℚ ℂ) (a b : ℝ) (hF : Sz F a b) (h : ∀ x, φ x ∈ F) (k : ℕ) (hk : 0 < k)
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hp : ((I ^ k).map (intMap φ F h)).IsPrincipal) :
    ∃ (K : IntermediateField ℚ ℂ) (hFK : F ≤ K), Sz K (a + Real.log k) (b + Real.log k) ∧
      (I.map (intMap φ K fun x => hFK (h x))).IsPrincipal := by
  obtain ⟨y, hy⟩ := hp
  have hy' : (I ^ k).map (intMap φ F h) = Ideal.span {y} := hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero, Ideal.map_eq_bot_iff_of_injective (intMap_injective φ F h)] at hy'
    exact pow_ne_zero k hI hy'
  have hyF : (y : F) ≠ 0 := fun h0 => hy0 (RingOfIntegers.ext h0)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((y : F) : ℂ) hk
  have hS := GlobalTheory.T.field_size_adjoin_kth_root F a b k (y : F) (IsLocalization.coeSubmodule F (I.map (intMap φ F h))) z hF hk hyF
    (by rw [← coeSubmodule_pow, ← Ideal.map_pow, hy', IsLocalization.coeSubmodule_span_singleton]) hz
  have hzK : z ∈ F ⊔ ℚ⟮z⟯ := (le_sup_right : ℚ⟮z⟯ ≤ F ⊔ ℚ⟮z⟯) (IntermediateField.mem_adjoin_simple_self ℚ z)
  have hFK : F ≤ F ⊔ ℚ⟮z⟯ := le_sup_left
  generalize F ⊔ ℚ⟮z⟯ = K at hS hzK hFK
  refine ⟨K, hFK, hS, ?_⟩
  haveI := finiteDimensional_of_sz hS
  haveI : NumberField K := NumberField.mk
  rw [← IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hz
    exact hyF (by exact_mod_cast hz.symm)
  refine ⟨⟨z, hzK⟩, GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ ⟨z, hzK⟩ k hk
    (fun h0 => hz0 (congrArg Subtype.val h0)) ?_ ?_⟩
  · exact (IsLocalization.coeSubmodule_fg K (RingOfIntegers.coe_injective) _).mpr (IsNoetherian.noetherian _)
  · rw [← coeSubmodule_pow, ← Ideal.map_pow, map_intMap φ hFK h, hy', Ideal.map_span, Set.image_singleton,
      IsLocalization.coeSubmodule_span_singleton]
    congr 2
    apply Subtype.ext
    exact hz.symm

theorem induct (n : ℕ) : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (a b : ℝ) (h : ∀ x, φ x ∈ F), Sz F a b →
    (clMap (intMap φ F h) (intMap_injective φ F h)).ker.index = n →
    ∃ (K : IntermediateField ℚ ℂ) (hFK : F ≤ K), Sz K (a + Real.log n) (b + Real.log n) ∧
      ∀ I : (Ideal (𝓞 E))⁰, (I.1.map (intMap φ K fun x => hFK (h x))).IsPrincipal := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F _ a b h hF hn
  by_cases hall : ∀ I : (Ideal (𝓞 E))⁰, (I.1.map (intMap φ F h)).IsPrincipal
  · have := Real.log_natCast_nonneg n
    exact ⟨F, le_rfl, sz_mono' hF (by linarith) (by linarith), hall⟩
  push Not at hall
  obtain ⟨I, hI⟩ := hall
  set f := clMap (intMap φ F h) (intMap_injective φ F h) with hf
  have hne : f (ClassGroup.mk0 I) ≠ 1 := fun h1 => hI ((clMap_mk0_eq_one_iff _ _ I).mp h1)
  set k := orderOf (f (ClassGroup.mk0 I)) with hk
  have hk0 : 0 < k := orderOf_pos _
  have hk1 : k ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.mp h1)
  have hpow : f (ClassGroup.mk0 (I ^ k)) = 1 := by rw [map_pow, map_pow, pow_orderOf_eq_one]
  obtain ⟨K, hFK, hK, hIK⟩ := step φ F a b hF h k hk0 I.1 (nonZeroDivisors.coe_ne_zero I)
    ((clMap_mk0_eq_one_iff _ _ (I ^ k)).mp hpow)
  haveI := finiteDimensional_of_sz hK
  haveI : NumberField K := NumberField.mk
  set g := clMap (intMap φ K fun x => hFK (h x)) (intMap_injective φ K _) with hg
  have hle : f.ker ≤ g.ker := by
    intro c hc
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective c
    exact (clMap_mk0_eq_one_iff _ _ J).mpr (isPrincipal_mono φ hFK h _ ((clMap_mk0_eq_one_iff _ _ J).mp hc))
  have hmem : ClassGroup.mk0 I ∈ g.ker := (clMap_mk0_eq_one_iff _ _ I).mpr hIK
  have hmul := Subgroup.relIndex_mul_index hle
  rw [Subgroup.relIndex_ker, hn] at hmul
  have hkr : k ≤ Nat.card (g.ker.map f) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_map_of_mem f hmem))
  have hm0 : 0 < g.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hkm : k * g.ker.index ≤ n := hmul ▸ Nat.mul_le_mul_right _ hkr
  have hlt : g.ker.index < n := by
    have : 2 ≤ k := by omega
    nlinarith
  obtain ⟨L, hKL, hL, hall⟩ := ih _ hlt K _ _ _ hK rfl
  have hlog : Real.log k + Real.log g.ker.index ≤ Real.log n := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hkm)
  exact ⟨L, hFK.trans hKL, sz_mono' hL (by linarith) (by linarith), hall⟩

end GlobalTheory.FieldSize.Capit

namespace GlobalTheory.FieldSize

open Capit in

theorem exists_sz_capitulation : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (F : IntermediateField ℚ ℂ) (a b : ℝ), Sz F a b → (∀ x, φ x ∈ F) → ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧ Sz F' (a + Real.log (classNumber E)) (b + Real.log (classNumber E)) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], F' ≤ K → ∀ 𝔞 : Ideal (𝓞 E), ∃ β : K, Submodule.span (𝓞 K) {β} = Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = φ (a : E)} := by
  intro E _ _ φ F a b hF h
  haveI := finiteDimensional_of_sz hF
  haveI : NumberField F := NumberField.mk
  obtain ⟨L, hFL, hL, hall⟩ := induct φ _ F a b h hF rfl
  set m := (clMap (intMap φ F h) (intMap_injective φ F h)).ker.index with hm
  have hm0 : 0 < m := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hmh : m ≤ classNumber E := by
    rw [classNumber, ← Nat.card_eq_fintype_card]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
  have hlog : Real.log m ≤ Real.log (classNumber E) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hmh)
  refine ⟨L, hFL, sz_mono' hL (by linarith) (by linarith), fun K _ hLK 𝔞 => ?_⟩
  have hK : ∀ x, φ x ∈ K := fun x => hLK (hFL (h x))
  have hp : (𝔞.map (intMap φ K hK)).IsPrincipal := by
    by_cases h0 : 𝔞 = ⊥
    · rw [h0, Ideal.map_bot]; infer_instance
    · exact isPrincipal_mono φ hLK _ _ (hall ⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h0⟩)
  obtain ⟨y, hy⟩ := hp
  refine ⟨(y : K), ?_⟩
  have h1 := congrArg (IsLocalization.coeSubmodule K) hy
  rw [Ideal.submodule_span_eq, IsLocalization.coeSubmodule_span_singleton, Ideal.map,
    IsLocalization.coeSubmodule_span] at h1
  refine h1.symm.trans ?_
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨_, ⟨a, ha, rfl⟩, Subtype.ext hx.symm⟩

end GlobalTheory.FieldSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponentsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_point_unitary_with_components : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V : HSp D) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → ∃ k ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = g τ := by
  first | exact @GlobalTheory.FockCompare.LiftUnitary.lift_unitary | exact GlobalTheory.FockCompare.LiftUnitary.lift_unitary | (intros; apply GlobalTheory.FockCompare.LiftUnitary.lift_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubmoduleThetaFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_submodule_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D), ∃ M : Submodule ℂ (WA V W → ℂ), ∀ f, f ∈ M ↔ IsThetaFun ψ V W f := by
  first | exact @GlobalTheory.FockCompare.exists_thetaSubmodule | exact GlobalTheory.FockCompare.exists_thetaSubmodule | (intros; apply GlobalTheory.FockCompare.exists_thetaSubmodule <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeSupAddStatement
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_size_sup_add : ∀ (F F' : IntermediateField ℚ ℂ) (a b a' b' : ℝ), Sz F a b → Sz F' a' b' → Sz (F ⊔ F') (a + a') (b + b') := by
  first | exact @GlobalTheory.FieldSize.sz_sup | exact GlobalTheory.FieldSize.sz_sup | (intros; apply GlobalTheory.FieldSize.sz_sup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FrameBasisMatrixOrthogonalPropertiesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_basis_matrix_orthogonal_properties : ∀ (D : D7) (V : HSp D), (∀ Q : Matrix (Fin V.rank) (Fin V.rank) D.host.E, IsUnit Q.det → ∃ b : Module.Basis (Fin V.rank) D.host.E V.V, Q = V.frame.toMatrix b) ∧ ∀ b : Module.Basis (Fin V.rank) D.host.E V.V, IsUnit (V.frame.toMatrix b).det ∧ (∀ i j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (V.frame.toMatrix b) * V.gram * V.frame.toMatrix b) i j = V.hT (b i) (b j)) ∧ ((∀ i j, i ≠ j → V.hT (b i) (b j) = 0) → ∀ τ : D.what₂.Tau, (∀ i, (tauE D τ (V.hT (b i) (b i))).re ≠ 0) ∧ ((V.frame.toMatrix b).map (tauE D τ))ᴴ * gramAt D V τ * (V.frame.toMatrix b).map (tauE D τ) = Matrix.diagonal (fun i => (((tauE D τ (V.hT (b i) (b i))).re : ℝ) : ℂ)) ∧ ∀ s : Module.End D.host.E V.V, (∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i) → thAt V τ s * (V.frame.toMatrix b).map (tauE D τ) = (V.frame.toMatrix b).map (tauE D τ) * Matrix.diagonal (fun i => if 0 < (tauE D τ (V.hT (b i) (b i))).re then (1 : ℂ) else -1)) := by
  first | exact @GlobalTheory.FockBasisMatrix.basis_matrix | exact GlobalTheory.FockBasisMatrix.basis_matrix | (intros; apply GlobalTheory.FockBasisMatrix.basis_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeCommutatorRelationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDerivative_commutator_relation : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → ∀ u v : R, hD ι π om u (hD ι π om v f) - hD ι π om v (hD ι π om u f) = (-(2 * Real.pi * Complex.I) * (om u v : ℝ)) • f := by
  first | exact @GlobalTheory.FockCompare.heisenberg_derivative_commutator | exact GlobalTheory.FockCompare.heisenberg_derivative_commutator | (intros; apply GlobalTheory.FockCompare.heisenberg_derivative_commutator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeQuasiInvariantAndLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDerivative_quasiInvariant_and_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ), ((∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) → ∀ γ w, dRho ψ V W L f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * dRho ψ V W L f w) ∧ ∀ u : WA V W, (∀ t, symplH V W u (L t) = 0 ∧ symplH V W (L t) u = 0) → Heisenberg₂ ψ V W u f = f → Heisenberg₂ ψ V W u (dRho ψ V W L f) = dRho ψ V W L f := by
  first | exact @GlobalTheory.FockCompare.dRho_quasi_and_level | exact GlobalTheory.FockCompare.dRho_quasi_and_level | (intros; apply GlobalTheory.FockCompare.dRho_quasi_and_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDirectionalDerivFormulaAndSmoothStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDirectionalDeriv_formula_and_smooth : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → ∀ (f : G → ℂ), Sm ι f → ∀ u : R, (∀ w, hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) ∧ Sm ι (hD ι π om u f) := by
  first | exact @GlobalTheory.FockCompare.hD_formula_smooth | exact GlobalTheory.FockCompare.hD_formula_smooth | (intros; apply GlobalTheory.FockCompare.hD_formula_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HermitianMajorantIsCartanInvolutionAndCommuteIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMajorant_isCartanInvolution_and_commute_iff : ∀ (n p q : ℕ), p + q = n → ∀ (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (G t : Matrix (Fin n) (Fin n) ℂ), G.det ≠ 0 → Aᴴ * Formalism.UG.Jpq p q * A = G → Formalism.UG.Jpq p q * A = A * t → IsCart G t ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, (∃ b : Mat p q, IsKC b ∧ b * A = A * g) ↔ Commute g t := by
  first | exact @GlobalTheory.FockCompare.CartanRel.cartan_rel | exact GlobalTheory.FockCompare.CartanRel.cartan_rel | (intros; apply GlobalTheory.FockCompare.CartanRel.cartan_rel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKilledByOperatorProductsSuccCreationApplyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKilledByOperatorProducts_succ_creation_apply : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a : I → Module.End ℂ M) (c : Module.End ℂ M), (∀ i, ∃ β : ℂ, a i * c - c * a i = β • (1 : Module.End ℂ M)) → ∀ (N : ℕ) (m : M), Killed a N m → Killed a (N + 1) (c m) := by
  first | exact @GlobalTheory.FockCompare.WeylCreate.killed_create | exact GlobalTheory.FockCompare.WeylCreate.killed_create | (intros; apply GlobalTheory.FockCompare.WeylCreate.killed_create <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.JpqMulMonomialEqMulSignDiagonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.Jpq_mul_monomial_eq_mul_sign_diagonal : ∀ (n p q : ℕ), p + q = n → ∀ (M : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (d : Fin n → ℝ), (∀ i, d i ≠ 0) → Mᴴ * Formalism.UG.Jpq p q * M = Matrix.diagonal (fun i => (d i : ℂ)) → (∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) → Formalism.UG.Jpq p q * M = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  first | exact @GlobalTheory.MonomialSign.Jpq_mul_eq | exact GlobalTheory.MonomialSign.Jpq_mul_eq | (intros; apply GlobalTheory.MonomialSign.Jpq_mul_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemOfIsKilledByOperatorProductsVacuumCreationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_isKilledByOperatorProducts_vacuum_creation : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a c : I → Module.End ℂ M) (n : ℕ) (e : Fin n → I) (lam : ℂ), lam ≠ 0 → (∀ i, a i * (∑ k, c (e k) * a (e k)) = ((∑ k, c (e k) * a (e k)) + lam • (1 : Module.End ℂ M)) * a i) → ∀ P : Submodule ℂ M, (∀ m, (∀ i, a i m = 0) → m ∈ P) → (∀ i, ∀ m ∈ P, c i m ∈ P) → ∀ (N : ℕ) (m : M), Killed a N m → m ∈ P := by
  first | exact @GlobalTheory.FockCompare.WeylInduct.mem_of_killed | exact GlobalTheory.FockCompare.WeylInduct.mem_of_killed | (intros; apply GlobalTheory.FockCompare.WeylInduct.mem_of_killed <;> assumption)
end

