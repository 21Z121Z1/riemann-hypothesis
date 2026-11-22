import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepBasisCharpoly
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneTmulOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepBasisCharpolyStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_basis_charpoly : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] (h d : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]), ∃ (N : ℕ) (y : Fin N → Fin h → ℤ_[p]), h = N * d ∧ Submodule.span ℤ_[p] (Set.range fun ij : Fin N × Fin d => ρ (b ij.2) *ᵥ y ij.1) = ⊤ ∧ ∀ a : Λ, (ρ a).charpoly = (LinearMap.mulLeft ℤ_[p] a).charpoly ^ N := by
  first | exact @GlobalTheory.DetInv.rep_free_charpoly | exact GlobalTheory.DetInv.rep_free_charpoly | (intros; apply GlobalTheory.DetInv.rep_free_charpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueFieldTiltStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_field_tilt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (r : PreTilt O p →+* k), Function.Surjective r := by
  first | exact @GlobalTheory.TiltResidue.preTilt_onto_algClosed_residue | exact GlobalTheory.TiltResidue.preTilt_onto_algClosed_residue | (intros; apply GlobalTheory.TiltResidue.preTilt_onto_algClosed_residue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondOrderNbhd
section
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem step_single {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C}
    {ρ₁ ρ₂ : Hol W →+* C} (a : Fin g) (e : C) (he : e ∈ J) (h2 : e * e = 0)
    (h : ∀ x, ρ₂ x = ρ₁ x + ρ₁ (dw a x) * e) : Step J ρ₁ ρ₂ := by
  refine ⟨Pi.single a e, fun c ↦ ?_, fun c d ↦ ?_, fun x ↦ ?_⟩
  · by_cases hc : c = a
    · subst hc; simpa using he
    · simp [hc]
  · by_cases hc : c = a
    · by_cases hd : d = a
      · subst hc; subst hd; simpa using h2
      · simp [hd]
    · simp [hc]
  · rw [h, Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [hc]
    · simp

theorem exists_second_order_nbhd : ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (K : Charts F) (k : K.K) (a b : Fin g), ∃ (T : K.Obj) (φ₀ φ₁ φ₂ φ₃ : K.triv k ⟶ T) (e₁ e₂ : T.C), φ₀.deg = 0 ∧ φ₁.deg = 0 ∧ φ₂.deg = 0 ∧ φ₃.deg = 0 ∧ e₁ ∈ T.J ∧ e₂ ∈ T.J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x : Hol (K.W k), φ₁.φ x = φ₀.φ x + φ₀.φ (dw a x) * e₁) ∧ (∀ x : Hol (K.W k), φ₂.φ x = φ₀.φ x + φ₀.φ (dw b x) * e₂) ∧ (∀ x : Hol (K.W k), φ₃.φ x = φ₁.φ x + φ₁.φ (dw b x) * e₂) ∧ (∀ x : Hol (K.W k), φ₃.φ x = φ₂.φ x + φ₂.φ (dw a x) * e₁) ∧ ∀ x : Hol (K.W k), φ₀.φ x * e₁ * e₂ = 0 → x = 0 := by
  intro I _ g Λ _ F K k a b
  obtain ⟨C, _, J, φ₀, φ₁, φ₂, φ₃, e₁, e₂, hJ, h1, h2, h11, h22, H1, H2, H3, H4, H5⟩ :=
    GlobalTheory.T.exists_secondOrderNbhd_commuting_derivations (Hol (K.W k)) (dw a) (dw b) (GlobalTheory.T.fibreCoordinatePartialDerivation_comm I g (K.W k) a b)
  let T : K.Obj :=
    { k := k, C := C, alg := (φ₀.comp (K.cst k)).toAlgebra, J := J, nil := hJ, ρ := φ₀, ρ_cst := fun _ ↦ rfl }
  have hs : T.ρ.comp (sh (K.le_refl k)) = φ₀ := RingHom.ext fun f ↦ congrArg φ₀ (sh_refl _ f)
  have c0 : Close T.J (T.ρ.comp (sh (K.le_refl k))) φ₀ := by rw [hs]; exact Relation.ReflTransGen.refl
  have c1 : Close T.J (T.ρ.comp (sh (K.le_refl k))) φ₁ := Relation.ReflTransGen.tail c0 (step_single a e₁ h1 h11 H1)
  have c2 : Close T.J (T.ρ.comp (sh (K.le_refl k))) φ₂ := Relation.ReflTransGen.tail c0 (step_single b e₂ h2 h22 H2)
  have c3 : Close T.J (T.ρ.comp (sh (K.le_refl k))) φ₃ := Relation.ReflTransGen.tail c1 (step_single b e₂ h2 h22 H3)
  have a1 : ∀ f, φ₁ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H1, dw_cst]; simp
  have a2 : ∀ f, φ₂ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H2, dw_cst]; simp
  have a3 : ∀ f, φ₃ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H3, dw_cst, a1]; simp
  exact ⟨T, fromTriv T (K.le_refl k) φ₀ (fun _ ↦ rfl) c0, fromTriv T (K.le_refl k) φ₁ a1 c1,
    fromTriv T (K.le_refl k) φ₂ a2 c2, fromTriv T (K.le_refl k) φ₃ a3 c3, e₁, e₂, rfl, rfl, rfl, rfl,
    h1, h2, h11, h22, H1, H2, H3, H4, H5⟩

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointOfGeometricallyDomainStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separable_point_of_geometrically_domain : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  first | exact @GlobalTheory.SepPoint.exists_sepPoint | exact GlobalTheory.SepPoint.exists_sepPoint | (intros; apply GlobalTheory.SepPoint.exists_sepPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroExtendLocalizationAwayPowStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqZero_extend_localizationAway_pow : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FinitePresentation R' A] (J : Ideal S), J ^ 2 = ⊥ → ∀ (g : S) (φ : A →ₐ[R'] S)
    (ψ : A →ₐ[R'] Localization.Away g),
    (∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈ J.map (algebraMap S (Localization.Away g))) →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N * (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  first | exact @GlobalTheory.SecGlue.exists_sqZero_extend_pow | exact GlobalTheory.SecGlue.exists_sqZero_extend_pow | (intros; apply GlobalTheory.SecGlue.exists_sqZero_extend_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisationOfHenselian
section
open IsLocalRing

namespace GlobalTheory

open StrictHensOfHens

theorem exists_strictHenselisation_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (Ω : Type) [Field Ω] [Algebra (ResidueField R) Ω] [IsSepClosure (ResidueField R) Ω], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), IsSepClosed (ResidueField S) ∧ Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] Ω) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R _ _ Ω _ _ _
  have hflat : Module.Flat R (SH R Ω) := by
    refine GlobalTheory.T.flat_of_forall_finset_subset_flat_submodule R (SH R Ω) fun s => ?_
    obtain ⟨E, hE⟩ := exists_ofA_finset s
    let e := AlgEquiv.ofInjective (ofA R Ω E) (ofA_injective E)
    haveI : Module.Flat R (Lift R Ω E) := Algebra.Smooth.flat _ _
    refine ⟨Subalgebra.toSubmodule (ofA R Ω E).range, fun x hx => ?_,
      Module.Flat.of_linearEquiv e.symm.toLinearEquiv⟩
    obtain ⟨a, rfl⟩ := hE x hx
    exact ⟨a, rfl⟩
  refine ⟨SH R Ω, inferInstance, inferInstance, inferInstance, inferInstance,
    isSepClosed_residueField, hflat, map_maximalIdeal, ⟨resAlgEquiv⟩, Idx R Ω, inferInstance,
    inferInstance, inferInstance, fun E => (ofA R Ω E).range, ?_, ?_, fun E => ?_⟩
  · intro E F h x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨trans R Ω E F h a, ofA_trans h a⟩
  · intro s
    obtain ⟨E, a, rfl⟩ := exists_ofA s
    exact ⟨E, a, rfl⟩
  · refine ⟨Lift R Ω E, inferInstance, inferInstance, inferInstance, maximalIdeal _, inferInstance, ⟨?_⟩⟩
    have hu : (maximalIdeal (Lift R Ω E)).primeCompl ≤ IsUnit.submonoid (Lift R Ω E) :=
      fun x hx => by simpa [IsUnit.mem_submonoid_iff, mem_maximalIdeal, mem_nonunits_iff] using hx
    exact ((IsLocalization.atUnits (Lift R Ω E) (maximalIdeal (Lift R Ω E)).primeCompl
      (S := Localization.AtPrime (maximalIdeal (Lift R Ω E))) hu).restrictScalars R).symm.trans
      (AlgEquiv.ofInjective (ofA R Ω E) (ofA_injective E))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaProjectionStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_projection : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (σ : Λ →+* O) (f : RL p O Λ →+* O) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), IsTheta σ f → ∃ π, IsProj C e f π := by
  first | exact @GlobalTheory.DetInv.proj_exists | exact GlobalTheory.DetInv.proj_exists | (intros; apply GlobalTheory.DetInv.proj_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformizerSeparableReductionStatement
section
open scoped TensorProduct nonZeroDivisors
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_separable_reduction : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O],
    ∃ (e : ℕ) (π a : O) (u : Oˣ) (h : ℤ_[l][X]), 0 < e ∧ (l : O) = π ^ e * u ∧ h.Monic ∧
      aeval a h ∈ Ideal.span {π} ∧ e * h.natDegree = Module.finrank ℤ_[l] O ∧
      ∀ (κ : Type) [Field κ] [CharP κ l] (ψ : ℤ_[l] →+* κ), (h.map ψ).Separable ∧
        (LinearMap.charpoly (LinearMap.mulLeft ℤ_[l] a)).map ψ = (h.map ψ) ^ e := by
  first | exact @GlobalTheory.UnramifiedGenerator.exists_ramification_and_generator | exact GlobalTheory.UnramifiedGenerator.exists_ramification_and_generator | (intros; apply GlobalTheory.UnramifiedGenerator.exists_ramification_and_generator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDescentCocycleDescendedSubmoduleEq
section
open TensorProduct GlobalTheory.EtC

namespace GlobalTheory.PicCech

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

theorem exists_sum_of_mem_mul {M N : Submodule A B} {z : B} (hz : z ∈ M * N) :
    ∃ (ι : Type) (_ : Fintype ι) (x y : ι → B), (∀ i, x i ∈ M) ∧ (∀ i, y i ∈ N) ∧ ∑ i, x i * y i = z := by
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem m hm n hn => exact ⟨Unit, inferInstance, fun _ => m, fun _ => n, fun _ => hm, fun _ => hn, by simp⟩
  | add a _ b _ ha hb =>
    obtain ⟨ι, _, x, y, hx, hy, hs⟩ := ha
    obtain ⟨κ, _, x', y', hx', hy', hs'⟩ := hb
    refine ⟨ι ⊕ κ, inferInstance, Sum.elim x x', Sum.elim y y', ?_, ?_, ?_⟩
    · rintro (i | i) <;> simp [hx, hx']
    · rintro (i | i) <;> simp [hy, hy']
    · rw [Fintype.sum_sum_type]; simp [hs, hs']

theorem tmul_eq_one_tmul {c : B} (hc : c ∈ (1 : Submodule A B)) (q : B) :
    c ⊗ₜ[A] q = (1 : B) ⊗ₜ[A] (c * q) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hc
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

theorem tmul_eq_tmul_one {c : B} (hc : c ∈ (1 : Submodule A B)) (p : B) :
    p ⊗ₜ[A] c = (p * c) ⊗ₜ[A] (1 : B) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hc
  rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

theorem sum_tmul_mul_one_tmul {ι : Type} [Fintype ι] (x y : ι → B) (hs : ∑ i, x i * y i = 1) {b : B}
    (hb : ∀ i, y i * b ∈ (1 : Submodule A B)) :
    (∑ i, x i ⊗ₜ[A] y i) * ((1 : B) ⊗ₜ[A] b) = b ⊗ₜ[A] (1 : B) := by
  rw [Finset.sum_mul]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [Finset.sum_congr rfl (fun i _ => tmul_eq_tmul_one (hb i) (x i)), ← TensorProduct.sum_tmul]
  congr 1
  simp_rw [← mul_assoc]; rw [← Finset.sum_mul, hs, one_mul]

theorem sum_tmul_mul_sum_tmul {ι : Type} [Fintype ι] (x y : ι → B) (hs : ∑ i, x i * y i = 1)
    (hxy : ∀ i j, x i * y j ∈ (1 : Submodule A B)) :
    (∑ i, x i ⊗ₜ[A] y i) * (∑ j, y j ⊗ₜ[A] x j) = 1 := by
  rw [Finset.sum_mul_sum]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => tmul_eq_one_tmul (hxy i j) (y i * x j)))]
  simp_rw [← TensorProduct.tmul_sum]
  rw [Algebra.TensorProduct.one_def]
  congr 1
  calc ∑ i, ∑ j, x i * y j * (y i * x j) = (∑ i, x i * y i) * (∑ j, x j * y j) := by
        rw [Finset.sum_mul_sum]; exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = 1 := by rw [hs, one_mul]

theorem cocycle_sum {ι : Type} [Fintype ι] (x y : ι → B) (hs : ∑ i, x i * y i = 1)
    (hyx : ∀ i j, y i * x j ∈ (1 : Submodule A B)) :
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (∑ i, x i ⊗ₜ[A] y i) =
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) (∑ i, x i ⊗ₜ[A] y i) *
      (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) (∑ i, x i ⊗ₜ[A] y i) := by
  simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeLeft_apply]
  rw [Finset.sum_mul_sum]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    congrArg (fun t => x i ⊗ₜ[A] t) (tmul_eq_one_tmul (hyx i j) (y j))))]
  simp_rw [← TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum, hs, mul_one]

theorem exists_unitCocycle_descMod_eq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], descMod A B 1 ≤ 1 →
    ∀ I : (Submodule A B)ˣ, ∃ u : (B ⊗[A] B)ˣ, UCoc A B u ∧ descMod A B u = (I : Submodule A B) := by
  intro A B _ _ _ h1 I
  have hone : (1 : B) ∈ (I : Submodule A B) * ↑I⁻¹ := by
    rw [I.mul_inv]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  obtain ⟨ι, _, x, y, hx, hy, hs⟩ := exists_sum_of_mem_mul hone
  have hxy : ∀ i j, x i * y j ∈ (1 : Submodule A B) := fun i j => by
    rw [← I.mul_inv]; exact Submodule.mul_mem_mul (hx i) (hy j)
  have hyx : ∀ i j, y i * x j ∈ (1 : Submodule A B) := fun i j => by
    rw [← I.inv_mul]; exact Submodule.mul_mem_mul (hy i) (hx j)
  have hs' : ∑ i, y i * x i = 1 := by simp_rw [mul_comm (y _)]; exact hs
  have huv := sum_tmul_mul_sum_tmul x y hs hxy
  let u : (B ⊗[A] B)ˣ := ⟨∑ i, x i ⊗ₜ[A] y i, ∑ j, y j ⊗ₜ[A] x j, huv, by rw [mul_comm]; exact huv⟩
  refine ⟨u, cocycle_sum x y hs hyx, le_antisymm ?_ ?_⟩
  · intro b hb
    have hb' : (∑ i, x i ⊗ₜ[A] y i) * ((1 : B) ⊗ₜ[A] b) = b ⊗ₜ[A] (1 : B) := hb
    have key : ∀ i, b * y i ∈ (1 : Submodule A B) := by
      intro i
      apply h1
      show ((1 : (B ⊗[A] B)ˣ) : B ⊗[A] B) * ((1 : B) ⊗ₜ[A] (b * y i)) = (b * y i) ⊗ₜ[A] (1 : B)
      have hv := sum_tmul_mul_one_tmul y x hs' (b := y i) (fun j => hxy j i)
      calc ((1 : (B ⊗[A] B)ˣ) : B ⊗[A] B) * ((1 : B) ⊗ₜ[A] (b * y i))
          = ((∑ i, x i ⊗ₜ[A] y i) * ((1 : B) ⊗ₜ[A] b)) * ((∑ j, y j ⊗ₜ[A] x j) * ((1 : B) ⊗ₜ[A] y i)) := by
            rw [mul_mul_mul_comm, huv, Algebra.TensorProduct.tmul_mul_tmul, Units.val_one, one_mul, one_mul, one_mul]
        _ = (b * y i) ⊗ₜ[A] (1 : B) := by rw [hb', hv, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hb2 : b = ∑ i, (b * y i) * x i := by
      simp_rw [mul_assoc, ← Finset.mul_sum, hs', mul_one]
    rw [hb2]
    exact Submodule.sum_mem _ fun i _ => by simpa using Submodule.mul_mem_mul (key i) (hx i)
  · intro b hb
    exact sum_tmul_mul_one_tmul x y hs (fun i => by rw [← I.inv_mul]; exact Submodule.mul_mem_mul (hy i) hb)

end GlobalTheory.PicCech
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivEqMulVecOfSchrodingerAnnihilatedStatement
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fderiv_eq_mulVec_of_schrodinger_annihilated : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 → ∀ f : Sch l, (∀ j : l, dRho (s *ᵥ Pi.single (.inl j) 1) f = I • dRho (s *ᵥ Pi.single (.inr j) 1) f) → ∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * ((-(Q * P⁻¹))ᵀ *ᵥ fun i => (x i : ℂ)) a * f x := by
  first | exact @GlobalTheory.RealWeil.fderiv_eq_of_annihilated | exact GlobalTheory.RealWeil.fderiv_eq_of_annihilated | (intros; apply GlobalTheory.RealWeil.fderiv_eq_of_annihilated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandPushoutAffineFlatAndPushouts
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.SchlessingerAffine

theorem nilKer {A B C D : CommRingCat.{0}} (e : A ≅ B) (g : B ⟶ C) (e' : C ≅ D)
    (h : IsNilpotent (RingHom.ker g.hom)) : IsNilpotent (RingHom.ker (e.hom ≫ g ≫ e'.hom).hom) := by
  have hk : RingHom.ker (e.hom ≫ g ≫ e'.hom).hom = Ideal.map e.inv.hom (RingHom.ker g.hom) := by
    ext x
    have hinj : Function.Injective e'.hom.hom := e'.commRingCatIsoToRingEquiv.injective
    constructor
    · intro hx
      rw [RingHom.mem_ker] at hx
      have hx' : g.hom (e.hom.hom x) = 0 := by
        apply hinj; simpa using hx
      have : x = e.inv.hom (e.hom.hom x) := by
        change x = (e.hom ≫ e.inv).hom x; simp
      rw [this]; exact Ideal.mem_map_of_mem _ hx'
    · intro hx
      rw [RingHom.mem_ker]
      have hle : Ideal.map e.inv.hom (RingHom.ker g.hom) ≤ RingHom.ker (e.hom ≫ g ≫ e'.hom).hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro z hz
        simp only [Ideal.mem_comap, RingHom.mem_ker] at hz ⊢
        change (e'.hom.hom (g.hom ((e.inv ≫ e.hom).hom z))) = 0
        simp [hz]
      exact hle hx
  rw [hk]
  exact h.map (Ideal.mapHom e.inv.hom)

theorem appTop_eq (R S : CommRingCat.{0}) (f : R ⟶ S) :
    (Spec.map f).appTop = (Scheme.ΓSpecIso R).hom ≫ f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality]; simp

theorem inv_comp_appTop (R S : CommRingCat.{0}) (f : R ⟶ S) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop = f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [appTop_eq]; simp

theorem surjTop {R S : CommRingCat.{0}} (f : R ⟶ S) (h : Function.Surjective f) :
    Function.Surjective (Spec.map f).appTop := by
  rw [appTop_eq]
  have h1 := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.surjective
  have h2 := (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv.surjective
  exact (h2.comp h).comp h1

theorem nilTop {R S : CommRingCat.{0}} (f : R ⟶ S) (h : IsNilpotent (RingHom.ker f.hom)) :
    IsNilpotent (RingHom.ker (Spec.map f).appTop.hom) := by
  rw [appTop_eq]
  exact nilKer (Scheme.ΓSpecIso R) f (Scheme.ΓSpecIso S).symm h

theorem pushout_of_eq (X X' S S' : Scheme.{0}) (f : X' ⟶ X) (g : X' ⟶ S') (p : X ⟶ S) (q : S' ⟶ S)
    (h : IsPullback f g p q) [IsAffine S] [IsAffine S'] (W : X.Opens) (hW : IsAffineOpen W)
    (O : X'.Opens) (hO : f ⁻¹ᵁ W = O) :
    IsPushout (p.appLE ⊤ W (fun _ _ => trivial)) q.appTop (f.appLE W O hO.ge)
      (g.appLE ⊤ O (fun _ _ => trivial)) := by
  subst hO
  have := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine X X' S S' f g p q h
    inferInstance inferInstance W hW
  rwa [Scheme.Hom.app_eq_appLE] at this

end GlobalTheory.SchlessingerAffine

open GlobalTheory.SchlessingerAffine in

theorem GlobalTheory.SchlessingerAffine.flat_and_pushouts : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → ∀ V : Y.Opens, IsAffineOpen V → (y.appLE ⊤ V (fun _ _ => trivial)).hom.Flat ∧ IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) (Spec.map f₁).appTop (j₁.app V) (p₁.appLE ⊤ (j₁ ⁻¹ᵁ V) (fun _ _ => trivial)) ∧ IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) (Spec.map f₂).appTop (j₂.app V) (p₂.appLE ⊤ (j₂ ⁻¹ᵁ V) (fun _ _ => trivial)) := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hF₁ hF₂ Y j₁ j₂ hw
    hj₁ hj₂ hV y hy₁ hy₂ V hVa
  have hU₁ : IsAffineOpen (j₁ ⁻¹ᵁ V) := hVa.preimage j₁
  have hU₂ : IsAffineOpen (j₂ ⁻¹ᵁ V) := hVa.preimage j₂
  have hPT : IsPullback (Spec.map f₁).appTop (Spec.map f₂).appTop (Spec.map g₁).appTop
      (Spec.map g₂).appTop :=
    IsPullback.of_iso hP (Scheme.ΓSpecIso P).symm (Scheme.ΓSpecIso R₁).symm
      (Scheme.ΓSpecIso R₂).symm (Scheme.ΓSpecIso R₀).symm
      (inv_comp_appTop _ _ f₁).symm (inv_comp_appTop _ _ f₂).symm
      (inv_comp_appTop _ _ g₁).symm (inv_comp_appTop _ _ g₂).symm
  have q₁ := pushout_of_eq Y₁ Y₀ (Spec R₁) (Spec R₀) i₁ p₀ p₁ (Spec.map g₁) h₁ (j₁ ⁻¹ᵁ V) hU₁
    ((i₁ ≫ j₁) ⁻¹ᵁ V) rfl
  have q₂ := pushout_of_eq Y₂ Y₀ (Spec R₂) (Spec R₀) i₂ p₀ p₂ (Spec.map g₂) h₂ (j₂ ⁻¹ᵁ V) hU₂
    ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; rfl)
  have c₁ : y.appLE ⊤ V (fun _ _ => trivial) ≫ j₁.app V =
      (Spec.map f₁).appTop ≫ p₁.appLE ⊤ (j₁ ⁻¹ᵁ V) (fun _ _ => trivial) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE j₁ y _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE p₁ (Spec.map f₁) _ _ _ _ _).symm
    simp only [hy₁]
  have c₂ : y.appLE ⊤ V (fun _ _ => trivial) ≫ j₂.app V =
      (Spec.map f₂).appTop ≫ p₂.appLE ⊤ (j₂ ⁻¹ᵁ V) (fun _ _ => trivial) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE j₂ y _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE p₂ (Spec.map f₂) _ _ _ _ _).symm
    simp only [hy₂]
  exact GlobalTheory.T.schlessinger_flat_fibreProduct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPT (surjTop g₁ hs₁) (surjTop g₂ hs₂)
    (nilTop g₁ hn₁) (nilTop g₂ hn₂) q₁ q₂
    (p₁.flat_appLE (isAffineOpen_top _) hU₁ le_top) (p₂.flat_appLE (isAffineOpen_top _) hU₂ le_top)
    (hV V) c₁ c₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCosinePushforwardUniform
section
open MeasureTheory
open scoped ComplexOrder ENNReal

set_option autoImplicit false

namespace GlobalTheory.FibCos

theorem lintegral_indicator_cos_mul_fs (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (J : Set ℝ)
    (hJ : MeasurableSet J) :
    ∫⁻ x : ℂ, J.indicator (fun _ => (1 : ENNReal)) (cos G x) * ENNReal.ofReal (fs G x) =
      volume (J ∩ Set.Icc (0 : ℝ) 1) := by
  set β : ℂ := G 1 0 / G 0 0
  set c : ℂ := (Real.sqrt G.det.re / (G 0 0).re : ℂ)
  have hdet : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  have ha : 0 < (G 0 0).re := (Complex.pos_iff.1 (hG.diag_pos (i := 0))).1
  have hc : c ≠ 0 := by
    simp only [c]
    exact_mod_cast (div_pos (Real.sqrt_pos.2 hdet) ha).ne'
  set g : ℝ → ℝ≥0∞ := J.indicator (fun _ => (1 : ENNReal))
  have hg : Measurable g := measurable_one.indicator hJ
  set H : ℂ → ℝ≥0∞ := fun y => g (1 / (1 + ‖y‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖y‖ ^ 2) ^ 2))
  have hH : Measurable H := by
    simp only [H]
    fun_prop
  have hnull : volume {x : ℂ | 1 + β * x = 0} = 0 := by
    apply Set.Subsingleton.measure_zero
    intro u hu v hv
    simp only [Set.mem_setOf_eq] at hu hv
    have hb : β ≠ 0 := by rintro hb; simp [hb] at hu
    have : β * u = β * v := by linear_combination hu - hv
    exact mul_left_cancel₀ hb this
  have hae : (fun x : ℂ => g (cos G x) * ENNReal.ofReal (fs G x)) =ᵐ[volume]
      fun x => ENNReal.ofReal (‖c / (1 + β * x) ^ 2‖ ^ 2) * H (c * x / (1 + β * x)) := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) hnull
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hne
    apply hx
    obtain ⟨h1, h2⟩ := GlobalTheory.T.fibre_cosine_explicit_formula G hG x hne
    simp only [H]
    rw [h1, h2, ENNReal.ofReal_mul (by positivity)]
    ring
  rw [lintegral_congr_ae hae, GlobalTheory.T.mobius_change_of_variables β c hc H hH, GlobalTheory.T.stereographic_measure_change g hg,
    lintegral_indicator_const hJ, one_mul, Measure.restrict_apply hJ]
  exact measure_congr (Filter.EventuallyEq.inter (Filter.EventuallyEq.refl _ _) Ioo_ae_eq_Icc)

end GlobalTheory.FibCos
end

