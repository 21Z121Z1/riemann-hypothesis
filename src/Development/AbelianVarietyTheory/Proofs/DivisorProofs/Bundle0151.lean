import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeKernelOfSplitCentralOneParamStatement
section
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteCovolume_kernel_of_split_central_oneParam : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H Γ Λ : Subgroup G) (s : G → ℝ) (c : ℝ → G), Continuous s → (∀ g h, s (g * h) = s g + s h) → Continuous c → (∀ x y, c (x + y) = c x * c y) → (∀ t g, c t * g = g * c t) → (∀ t, s (c t) = t) → (∀ g, g ∈ H ↔ s g = 0) → Γ ≤ H → Λ = Γ ⊔ Subgroup.zpowers (c 1) → DiscreteTopology Λ → (∀ (ν : Measure G) (D : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ D ν → ν D ≠ ⊤) → ∀ (π : Measure H) (D : Set H), π.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf H) D π → π D ≠ ⊤ := by
  first | exact @GlobalTheory.finiteCovolume_kernel | exact GlobalTheory.finiteCovolume_kernel | (intros; apply GlobalTheory.finiteCovolume_kernel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAdjoinStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_adjoin_apply_of_annihilating : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (c : ℕ → Module.End ℂ V) (g : ℂ → Module.End ℂ V), (∀ u, g u = ∑ i ∈ Finset.range (n + 1), u ^ i • c i) → (∀ u u', Commute (g u) (g u')) → ∀ (w : V) (P : ℂ → Polynomial ℂ), (∀ u, P u ≠ 0) → (∀ u, Polynomial.aeval (g u) (P u) w = 0) → FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w}) := by
  first | exact @GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin | exact GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin | (intros; apply GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAlgebraOrbitOfAnnihilatedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_algebra_orbit_of_annihilated : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V)) (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) → (∀ t ∈ T, p t ≠ 0) → ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ≤ ∏ t ∈ T, (p t).natDegree := by
  first | exact @GlobalTheory.killed_span_adjoin_finrank_le | exact GlobalTheory.killed_span_adjoin_finrank_le | (intros; apply GlobalTheory.killed_span_adjoin_finrank_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleSurjectiveProj
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.Et.TrivTors

noncomputable section

namespace GlobalTheory.Et.TrivTors

def sigmaFinSuccIso (V : Scheme.{0}) (k : ℕ) :
    (∐ fun _ : Fin (k + 1) => V) ≅ V ⨿ (∐ fun _ : Fin k => V) where
  hom := Sigma.desc (Fin.cases coprod.inl fun i => Sigma.ι (fun _ : Fin k => V) i ≫ coprod.inr)
  inv := coprod.desc (Sigma.ι (fun _ : Fin (k + 1) => V) 0)
    (Sigma.desc fun i => Sigma.ι (fun _ : Fin (k + 1) => V) i.succ)
  hom_inv_id := by
    ext i
    induction i using Fin.cases
    · simp only [Fin.cases_zero, Sigma.ι_desc_assoc]
      exact coprod.inl_desc _ _
    · simp only [Fin.cases_succ, Sigma.ι_desc_assoc, Category.assoc, Category.comp_id]
      erw [coprod.inr_desc, Sigma.ι_desc]
  inv_hom_id := by
    apply coprod.hom_ext
    · erw [coprod.inl_desc_assoc, Sigma.ι_desc]
      simp
    · erw [coprod.inr_desc_assoc]
      ext i
      simp

theorem sigmaFinSuccIso_hom_desc (V : Scheme.{0}) (k : ℕ) :
    (sigmaFinSuccIso V k).hom ≫ coprod.desc (𝟙 V) (Sigma.desc fun _ : Fin k => 𝟙 V) =
      Sigma.desc fun _ : Fin (k + 1) => 𝟙 V := by
  ext i
  induction i using Fin.cases
  · simp only [sigmaFinSuccIso, Sigma.ι_desc_assoc, Fin.cases_zero, Sigma.ι_desc]
    exact coprod.inl_desc _ _
  · simp only [sigmaFinSuccIso, Sigma.ι_desc_assoc, Fin.cases_succ, Sigma.ι_desc, Category.assoc]
    erw [coprod.inr_desc, Sigma.ι_desc]

theorem isFinite_sigmaDesc_fin (V : Scheme.{0}) : ∀ k : ℕ, IsFinite (Sigma.desc fun _ : Fin k => 𝟙 V)
  | 0 => by
    have : IsEmpty (∐ fun _ : Fin 0 => V : Scheme.{0}) := by
      refine ⟨fun x => ?_⟩
      obtain ⟨i, _, _⟩ := (sigmaOpenCover fun _ : Fin 0 => V).exists_eq x
      exact i.elim0
    infer_instance
  | k + 1 => by
    have := isFinite_sigmaDesc_fin V k
    rw [← sigmaFinSuccIso_hom_desc]
    infer_instance

theorem proj_finite_etale_surjective :
    ∀ (n : ℕ), n ≠ 0 → ∀ (V : Scheme.{0}), IsFinite (proj n V) ∧ Etale (proj n V) ∧ Surjective (proj n V) := by
  intro n hn V
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨isFinite_sigmaDesc_fin V (m + 1), ?_, ?_⟩
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
  · refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_forall fun v => ?_)
    exact Set.mem_iUnion.2 ⟨0, v, rfl⟩

end GlobalTheory.Et.TrivTors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreAndEqOfSpecializesOfIsFiniteStatement
section
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fibre_and_eq_of_specializes_of_isFinite' : ∀ (Y Y' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ y : Y, {a : Y' | k a = y}.Finite ∧ ∀ a b : Y', k a = y → k b = y → a ⤳ b → a = b := by
  first | exact @GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite | exact GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite | (intros; apply GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatSurjectiveClosedSubschemeOfOpenCoverStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_surjective_closedSubscheme_of_openCover : ∀ (X T₀ : Scheme.{0}) (p : X ⟶ T₀) (ι : Type) (V : ι → T₀.Opens), iSup V = ⊤ → ∀ (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X) (q : ∀ i, Xi i ⟶ (V i).toScheme), (∀ i, IsPullback (m i) (q i) p (V i).ι) → ∀ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), (∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) → (∀ i, IsFinite (a i ≫ q i) ∧ Flat (a i ≫ q i) ∧ Surjective (a i ≫ q i)) → IsFinite (b ≫ p) ∧ Flat (b ≫ p) ∧ Surjective (b ≫ p) := by
  first | exact @GlobalTheory.finite_flat_surjective_of_openCover | exact GlobalTheory.finite_flat_surjective_of_openCover | (intros; apply GlobalTheory.finite_flat_surjective_of_openCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaloisFractionRingOfIsFractionRingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_galois_fractionRing_fixing : ∀ (A K L : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra A L], (∀ a : A, algebraMap A L a = algebraMap K L (algebraMap A K a)) → ∃ (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L), FiniteDimensional (FractionRing A) L ∧ IsGalois (FractionRing A) L ∧ ∀ (σ : L ≃ₐ[FractionRing A] L) (x : K), σ (algebraMap K L x) = algebraMap K L x := by
  first | exact @GlobalTheory.finiteGalois_fractionRing_of_isFractionRing | exact GlobalTheory.finiteGalois_fractionRing_of_isFractionRing | (intros; apply GlobalTheory.finiteGalois_fractionRing_of_isFractionRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInjectiveRingHomIsLocalHomAndExtend
section
open IsLocalRing

namespace GlobalTheory

theorem finite_injective_localHom_and_extend (V R K : Type) [CommRing V] [IsDomain V] [IsLocalRing V]
    [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [IsAlgClosed K] (ρ : V →+* R) :
    Function.Injective ρ → ρ.Finite → IsLocalHom ρ ∧ ∀ ev : V →+* K, ∃ ev₁ : R →+* K, ev₁.comp ρ = ev := by
  first
  | exact @_root_.GlobalTheory.ValuationExtensionExistence.main
  | exact _root_.GlobalTheory.ValuationExtensionExistence.main
  | (apply _root_.GlobalTheory.ValuationExtensionExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationExtensionExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationExtensionExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationExtensionExistence.main ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegralClosureOfFormallyUnramified
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.AbhFin

theorem finite_integralClosure_of_formallyUnramified (R K C : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing C] [Algebra K C] [Algebra R C] [IsScalarTower R K C] [FiniteDimensional K C]
    [Algebra.FormallyUnramified K C] : Module.Finite R (integralClosure R C) := by
  classical
  haveI : IsArtinianRing C := IsArtinianRing.of_finite K C
  haveI : IsReduced C := Algebra.FormallyUnramified.isReduced_of_field K C
  haveI := Fintype.ofFinite (MaximalSpectrum C)
  haveI : ∀ m : MaximalSpectrum C, Module.Finite R (integralClosure R (C ⧸ m.asIdeal)) := fun m => by
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    haveI : Algebra.FormallyUnramified K (C ⧸ m.asIdeal) :=
      Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K m.asIdeal) Ideal.Quotient.mk_surjective
    haveI : Algebra.IsSeparable K (C ⧸ m.asIdeal) := Algebra.FormallyUnramified.isSeparable K _
    exact IsIntegralClosure.finite R K (C ⧸ m.asIdeal) _
  let red : ∀ m : MaximalSpectrum C, integralClosure R C →ₗ[R] integralClosure R (C ⧸ m.asIdeal) := fun m =>
    (((Ideal.Quotient.mkₐ R m.asIdeal).comp (integralClosure R C).val).codRestrict
      (integralClosure R (C ⧸ m.asIdeal))
      (fun a => (show IsIntegral R (a : C) from a.2).map (Ideal.Quotient.mkₐ R m.asIdeal))).toLinearMap
  refine Module.Finite.of_injective (LinearMap.pi red) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  apply Subtype.ext
  apply (IsArtinianRing.equivPi C).injective
  show _ = IsArtinianRing.equivPi C 0
  rw [map_zero]
  funext m
  exact congrArg Subtype.val (congrFun ha m)

theorem main : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : R) (e : ℕ), Irreducible π → IsUnit (e : R) → ∀ [IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R))] [IsDiscreteValuationRing (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R))], Module.Finite (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) (integralClosure (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) (TensorProduct R (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) L)) := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ _ π e hπ he _ _
  classical
  set f : R[X] := X ^ e - C π with hf
  set g : K[X] := X ^ e - C (algebraMap R K π) with hg
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have hfm : f.Monic := monic_X_pow_sub_C _ he0
  have hgm : g.Monic := monic_X_pow_sub_C _ he0
  have hπK : IsUnit (algebraMap R K π) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)).isUnit
  haveI : Algebra.Etale K (AdjoinRoot g) :=
    GlobalTheory.etale_adjoinRoot_X_pow_sub_C K e _ (by simpa using he.map (algebraMap R K)) hπK
  haveI : Module.Finite K (AdjoinRoot g) := (AdjoinRoot.powerBasis' hgm).finite
  haveI : Module.Finite R (AdjoinRoot f) := (AdjoinRoot.powerBasis' hfm).finite
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  let C' := L ⊗[K] AdjoinRoot g
  haveI : Algebra.FormallyUnramified L C' := inferInstance
  haveI : Algebra.FormallyUnramified K C' := Algebra.FormallyUnramified.comp K L C'
  haveI : FiniteDimensional K C' := inferInstance
  haveI : IsScalarTower R K C' := inferInstance
  have hfinC : Module.Finite R (integralClosure R C') :=
    finite_integralClosure_of_formallyUnramified R K C'

  have hroot : aeval (AdjoinRoot.root g) f = 0 := by
    have h := AdjoinRoot.eval₂_root g
    rw [hg, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
    rw [hf, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero, h]
    exact (IsScalarTower.algebraMap_apply R K (AdjoinRoot g) π).symm
  let φ : AdjoinRoot f →ₐ[R] AdjoinRoot g := AdjoinRoot.liftAlgHom f (Algebra.ofId R (AdjoinRoot g)) (AdjoinRoot.root g) hroot
  let ψ : L ⊗[R] AdjoinRoot f →ₐ[L] C' :=
    Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (S := L))
      (((Algebra.TensorProduct.includeRight : AdjoinRoot g →ₐ[K] C').restrictScalars R).comp φ)
      (fun _ _ => Commute.all _ _)
  let bR := Algebra.TensorProduct.basis L (AdjoinRoot.powerBasis' hfm).basis
  let bK := Algebra.TensorProduct.basis L (AdjoinRoot.powerBasis' hgm).basis
  have hdeg : f.natDegree = g.natDegree := by
    rw [hf, hg, natDegree_X_pow_sub_C, natDegree_X_pow_sub_C]
  have hψb : ∀ i, ψ (bR i) = bK (Fin.cast hdeg i) := by
    intro i
    have hφ : φ (AdjoinRoot.root f) = AdjoinRoot.root g := AdjoinRoot.liftAlgHom_root _ _ _ _
    simp only [bR, bK, Algebra.TensorProduct.basis_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen, ψ,
      Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeft_apply, map_pow,
      hφ, Fin.val_cast, Fin.coe_cast]
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
    rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hli := bK.linearIndependent.comp (Fin.cast hdeg) (Fin.cast_injective hdeg)
    rw [← bR.sum_repr x, map_sum] at hx
    simp only [map_smul, hψb] at hx
    have h0 : ∀ i, bR.repr x i = 0 := Fintype.linearIndependent_iff.1 hli _ hx
    rw [← bR.sum_repr x]
    simp [h0]
  let Φ : AdjoinRoot f ⊗[R] L →ₐ[R] C' :=
    (ψ.restrictScalars R).comp (Algebra.TensorProduct.comm R (AdjoinRoot f) L).toAlgHom
  have hΦ : Function.Injective Φ := hinj.comp (Algebra.TensorProduct.comm R (AdjoinRoot f) L).injective
  let M := integralClosure (AdjoinRoot f) (AdjoinRoot f ⊗[R] L)
  let lin : M →ₗ[R] integralClosure R C' :=
    { toFun := fun x => ⟨Φ (x : AdjoinRoot f ⊗[R] L), (isIntegral_trans (R := R) (A := AdjoinRoot f) _ x.2).map Φ⟩
      map_add' := fun x y => Subtype.ext (map_add Φ (x : AdjoinRoot f ⊗[R] L) y)
      map_smul' := fun r x => Subtype.ext (map_smul Φ r (x : AdjoinRoot f ⊗[R] L)) }
  have hlin : Function.Injective lin := fun x y h =>
    Subtype.ext (hΦ (congrArg Subtype.val h))
  haveI : Module.Finite R M := Module.Finite.of_injective lin hlin
  exact Module.Finite.of_restrictScalars_finite R (AdjoinRoot f) M

end GlobalTheory.AbhFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteJointEigensystemsStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_joint_eigenvalues_of_commute : ∀ (K : Type) [Field K] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K), (∀ i j, Commute (A i) (A j)) → Set.Finite {χ : ι → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, A i *ᵥ c = χ i • c} := by
  first | exact @GlobalTheory.finite_joint_eigensystems | exact GlobalTheory.finite_joint_eigensystems | (intros; apply GlobalTheory.finite_joint_eigensystems <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMaximalContaining
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_maximal_containing : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B), f ≠ 0 → {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite := by
  first | (exact @GlobalTheory.finite_maximal_ideals_containing') | (exact GlobalTheory.finite_maximal_ideals_containing') | (intros; apply GlobalTheory.finite_maximal_ideals_containing' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicRootsBddMulIsIntegralStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_monic_of_roots_bdd_of_mul_isIntegral : ∀ (F : Type) [Field F] [NumberField F] (n N : ℕ) (B : ℝ), 0 < N →
    {P : Polynomial F | P.Monic ∧ P.natDegree = n ∧ ∀ φ : F →+* ℂ, ∀ w ∈ (P.map φ).roots,
      ‖w‖ ≤ B ∧ IsIntegral ℤ ((N : ℂ) * w)}.Finite := by
  first | (exact @GlobalTheory.finite_monic_roots_bdd_mul_isIntegral) | (exact GlobalTheory.finite_monic_roots_bdd_mul_isIntegral) | (intros; apply GlobalTheory.finite_monic_roots_bdd_mul_isIntegral <;> assumption)
end

