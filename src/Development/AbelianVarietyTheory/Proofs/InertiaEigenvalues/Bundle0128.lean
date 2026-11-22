import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0071
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0047
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0112
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0126
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsKMulOfEtaleSplittingStatement
section
open GlobalTheory.JR MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absK_mul_of_etale_splitting : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K), A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by
  first | exact @GlobalTheory.JR.EtProdAbs.absK_prod | exact GlobalTheory.JR.EtProdAbs.absK_prod | (intros; apply GlobalTheory.JR.EtProdAbs.absK_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddValNormUnramifiedInvolutionFieldExtEqMulStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addVal_norm_unramifiedInvolutionFieldExt_eq_mul : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = d * val K'.O y := by
  first | exact @GlobalTheory.UnitLemma.Unr.NormVal.normval | exact GlobalTheory.UnitLemma.Unr.NormVal.normval | (intros; apply GlobalTheory.UnitLemma.Unr.NormVal.normval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaAllOrders
section
open GlobalTheory.PMonE

namespace GlobalTheory

theorem PMonE.generalLemma_allOrders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact GlobalTheory.T.additiveSystem_surjectivity_and_count_order_zero
  · exact ⟨GlobalTheory.T.additiveSystemIntegralSurjectivity_of_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.1, GlobalTheory.T.additiveSystemIntegralSolutionCount_of_order_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapDetRestrict
section
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

noncomputable section

namespace GlobalTheory.LatIndexDet

theorem val_algebraMap (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type)
    [Field E] [Algebra O E] [IsFractionRing O E] {d : O} (hd : d ≠ 0) :
    val O (algebraMap O E d) = ((IsDiscreteValuationRing.addVal O d).toNat : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).intValuation ϖ = WithZero.exp (-1 : ℤ) :=
    (IsDiscreteValuationRing.maximalIdeal O).intValuation_singleton hϖ.ne_zero hϖ.maximalIdeal_eq
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).intValuation (u : O) = 1 := by
    refine le_antisymm ((IsDiscreteValuationRing.maximalIdeal O).intValuation_le_one _) (not_lt.1 fun h => ?_)
    have := ((IsDiscreteValuationRing.maximalIdeal O).intValuation_lt_one_iff_mem _).1 h
    exact (IsLocalRing.mem_maximalIdeal _).1 this u.isUnit
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n]
  simp only [val, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, map_mul, map_pow, h1, h2,
    one_mul, ← WithZero.exp_nsmul, WithZero.log_exp, ENat.toNat_coe]
  simp

end GlobalTheory.LatIndexDet

namespace GlobalTheory.LatIndexDet

variable (O : Type) [CommRing O] [IsDomain O] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E]
  {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]

include E in

theorem isTorsionFree_lat (N : Submodule O V) : Module.IsTorsionFree O N := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
  by_cases hr : r = 0
  · exact Or.inl hr
  · refine Or.inr (Subtype.ext ?_)
    have h' : r • (x : V) = 0 := congrArg Subtype.val h
    rw [← algebraMap_smul E r (x : V)] at h'
    have hr' : algebraMap O E r ≠ 0 := fun h0 => hr (IsFractionRing.injective O E (by rw [h0, map_zero]))
    exact (smul_eq_zero.1 h').resolve_left hr'

theorem algebraMap_det_restrict (N : Submodule O V) [Module.Free O N] [Module.Finite O N]
    (hspan : Submodule.span E (N : Set V) = ⊤) (T : V →ₗ[E] V) (hT : ∀ x ∈ N, T x ∈ N) :
    algebraMap O E (LinearMap.det ((T.restrictScalars O).restrict hT)) = LinearMap.det T := by
  classical
  let b := Module.Free.chooseBasis O N
  let bV : Module.Free.ChooseBasisIndex O N → V := fun i => (b i : V)
  have hliO : LinearIndependent O bV :=
    b.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hli : LinearIndependent E bV := (LinearIndependent.iff_fractionRing O E).1 hliO
  have hNle : (N : Set V) ⊆ Submodule.span E (Set.range bV) := by
    intro x hx
    have hx'' : x = ∑ i, b.repr ⟨x, hx⟩ i • bV i := by
      have h0 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h0
      simp only [Submodule.coe_smul] at h0
      exact h0.symm
    rw [hx'']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul E]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span E (Set.range bV) := by
    rw [← hspan]; exact Submodule.span_le.2 hNle
  let BE := Module.Basis.mk hli hsp
  let T' := (T.restrictScalars O).restrict hT
  have hmat : LinearMap.toMatrix BE BE T = (LinearMap.toMatrix b b T').map (algebraMap O E) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have h1 : T (BE j) = ∑ k, algebraMap O E (b.repr (T' (b j)) k) • BE k := by
      have h2 : T' (b j) = ∑ k, b.repr (T' (b j)) k • b k := (b.sum_repr _).symm
      have h3 := congrArg Subtype.val h2
      simp only [Module.Basis.mk_apply, BE, bV]
      rw [show T (b j : V) = ((T' (b j) : N) : V) from rfl]
      conv_lhs => rw [h3]
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, algebraMap_smul]
    rw [h1, BE.repr_sum_self]
  rw [← LinearMap.det_toMatrix BE, hmat, ← LinearMap.det_toMatrix b T', RingHom.map_det]
  rfl

end GlobalTheory.LatIndexDet

namespace GlobalTheory.LatIndexDet

theorem card_quot_eq_pow_val : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (V : Type) [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [FiniteDimensional E V] (N : Submodule O V), N.FG → Submodule.span E (N : Set V) = ⊤ → ∀ T : V →ₗ[E] V, LinearMap.det T ≠ 0 → (∀ x ∈ N, T x ∈ N) → (Nat.card (↥N ⧸ (N.map (T.restrictScalars O)).comap N.subtype) : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (LinearMap.det T) := by
  intro O _ _ _ _ E _ _ _ V _ _ _ _ _ N hfg hspan T hdet hT
  haveI := isTorsionFree_lat O E N
  haveI : Module.Finite O N := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O N := Module.free_of_finite_type_torsion_free'
  let T' : N →ₗ[O] N := (T.restrictScalars O).restrict hT
  have hdetT : algebraMap O E (LinearMap.det T') = LinearMap.det T := algebraMap_det_restrict O E N hspan T hT
  have hdet' : LinearMap.det T' ≠ 0 := fun h => hdet (by rw [← hdetT, h, map_zero])
  have hrange : (N.map (T.restrictScalars O)).comap N.subtype = LinearMap.range T' := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
    · rintro ⟨⟨y, hy⟩, hyx⟩
      exact ⟨y, hy, congrArg Subtype.val hyx⟩
  rw [hrange, GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det T' hdet', ← hdetT, val_algebraMap O E hdet']
  push_cast
  rw [zpow_natCast]

end GlobalTheory.LatIndexDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticesIdempotentPositionBoundedStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_lattices_idempotent_position_bounded : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ N : ℕ, ∃ C : ℕ, ∀ p : ι → ℤ, {M : Submodule K.O B.A | Pos B a e N M p}.Finite ∧ {M : Submodule K.O B.A | Pos B a e N M p}.ncard ≤ C := by
  first | exact @GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le | exact GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le | (intros; apply GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardResidueFieldAdjoinUnitaryProdStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_residueField_adjoin_unitary_prod : ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)), ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  first | exact @GlobalTheory.UnitLemma.ResDeg.card_residueField_prod | exact GlobalTheory.UnitLemma.ResDeg.card_residueField_prod | (intros; apply GlobalTheory.UnitLemma.ResDeg.card_residueField_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallBoundsUltrametricStatement
section
open Polynomial
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_roots_closedBall_bounds_ultrametric : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ) (d : ℕ), 0 < ρ → f.coeff d ≠ 0 → ((∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff d‖ * ρ ^ d) → d ≤ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ((∀ j, d < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff d‖ * ρ ^ d) → Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) ≤ d) := by
  first | exact @GlobalTheory.card_roots_le_radius_bounds | exact GlobalTheory.card_roots_le_radius_bounds | (intros; apply GlobalTheory.card_roots_le_radius_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOverExtIntegralReductionPow
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem charpoly_overExt_integral_reduction : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))), B.P.Separable → IsIntegral K.O B.g → ∀ s : K'.O, @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ → ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B ψ hψ hσ).P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree := by
  intro K K' d φ hU B ψ hψ hσ hO hl hsep hint s hres
  set S := Algebra.adjoin K.O ({B.g} : Set B.A) with hSdef
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  haveI : IsScalarTower K'.O K'.E B.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite K'.E B.A := (overExt φ B ψ hψ hσ).fd
  let f0 : K'.O →+* S := (ψ.comp (algebraMap K'.O K'.E)).codRestrict S hO
  letI : Algebra K'.O S := f0.toAlgebra
  let ι : S →ₐ[K'.O] B.A := { S.val.toRingHom with commutes' := fun _ => rfl }
  have hinj : Function.Injective ι := Subtype.val_injective
  haveI : Module.Finite K.O S := Algebra.finite_adjoin_simple_of_isIntegral hint
  haveI : Module.Finite K'.O S := by
    obtain ⟨T, hT⟩ := (inferInstance : Module.Finite K.O S).fg_top
    refine ⟨⟨T, eq_top_iff.2 fun y hy0 => ?_⟩⟩
    clear hy0
    have hy : y ∈ Submodule.span K.O (T : Set S) := hT ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul a x _ hx =>
      obtain ⟨y', hy'⟩ := GlobalTheory.T.unramifiedInvolutionExt_maps_integers_to_integers K K' d φ hU a
      have h : a • x = y' • x := by
        apply Subtype.ext
        rw [Algebra.smul_def, Algebra.smul_def, MulMemClass.coe_mul, MulMemClass.coe_mul]
        change algebraMap K.O B.A a * (x : B.A) = ψ (algebraMap K'.O K'.E y') * (x : B.A)
        rw [hy', hψ, ← IsScalarTower.algebraMap_apply]
      rw [h]; exact Submodule.smul_mem _ _ hx
  have hspan : Submodule.span K'.E (Set.range ι) = ⊤ := by
    refine eq_top_iff.2 fun y hy0 => ?_
    clear hy0
    have hy : y ∈ Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) := GlobalTheory.T.span_pow_generator_eq_top_of_charpoly_separable K B hsep ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨⟨B.g ^ i, pow_mem (Algebra.self_mem_adjoin_singleton K.O B.g) i⟩, rfl⟩
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      have h : e • x = (φ e) • x := by
        rw [Algebra.smul_def, Algebra.smul_def, ← hψ e]; rfl
      rw [h]; exact Submodule.smul_mem _ _ hx
  haveI : IsLocalRing S := hl
  obtain ⟨n, b, hb⟩ := GlobalTheory.T.charpoly_mulLeft_eq_map_of_span_range_eq K'.O K'.E B.A S ι hinj hspan
  let x0 : S := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩
  refine ⟨(LinearMap.toMatrix b b (LinearMap.mulLeft K'.O x0)).charpoly, (hb x0).symm, ?_⟩
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, ← Matrix.charpoly_map]
  set t : S := x0 - algebraMap K'.O S s with ht
  have htm : t ∈ IsLocalRing.maximalIdeal S := by
    rw [ht, ← Ideal.Quotient.eq]; exact hres
  have hsplit : LinearMap.toMatrix b b (LinearMap.mulLeft K'.O x0) =
      LinearMap.toMatrix b b (LinearMap.mulLeft K'.O t) + Matrix.scalar (Fin n) s := by
    have : LinearMap.mulLeft K'.O x0 = LinearMap.mulLeft K'.O t + s • LinearMap.id := by
      ext y; simp [ht, Algebra.smul_def, sub_mul]
    rw [this, map_add, map_smul, LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal]; rfl
  rw [hsplit, Matrix.map_add _ (map_add _)]
  have hsc : (Matrix.scalar (Fin n) s).map (IsLocalRing.residue K'.O) = Matrix.scalar (Fin n) (IsLocalRing.residue K'.O s) := by
    ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply]; split_ifs <;> simp
  rw [hsc]
  exact GlobalTheory.T.charpoly_nilpotent_add_scalar' _ n _ _ (GlobalTheory.T.isNilpotent_residue_toMatrix_mulLeft' K'.O S n b t htm)

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionUniqueUpToIso
section
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem isCplAt_unique : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (φ' : R →+* S'), IsCplAt q φ → IsCplAt q φ' → ∃ e : S ≃+* S', (e : S →+* S').comp φ = φ' := by
  intro R S S' _ _ _ _ _ q _ φ φ' h h'
  haveI := h.complete
  haveI := h'.complete
  obtain ⟨θ, ⟨hθl, hθ⟩, -⟩ := GlobalTheory.T.completion_universal_local_hom R S S' q φ φ' h h'.comap_eq
  obtain ⟨η, ⟨hηl, hη⟩, -⟩ := GlobalTheory.T.completion_universal_local_hom R S' S q φ' φ h' h.comap_eq
  have u := (GlobalTheory.T.completion_universal_local_hom R S S q φ φ h h.comap_eq).unique
    (y₁ := η.comp θ) (y₂ := RingHom.id S)
    ⟨RingHom.isLocalHom_comp η θ, by rw [RingHom.comp_assoc, hθ, hη]⟩
    ⟨inferInstance, RingHom.id_comp φ⟩
  have u' := (GlobalTheory.T.completion_universal_local_hom R S' S' q φ' φ' h' h'.comap_eq).unique
    (y₁ := θ.comp η) (y₂ := RingHom.id S')
    ⟨RingHom.isLocalHom_comp θ η, by rw [RingHom.comp_assoc, hη, hθ]⟩
    ⟨inferInstance, RingHom.id_comp φ'⟩
  exact ⟨RingEquiv.ofRingHom θ η u' u, hθ⟩

end GlobalTheory.Pat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlacesOfSamePrimeBelowStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_valuationSubring_of_same_below : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A B : ValuationSubring Ω), (∀ x ∈ K, IsIntegral ℤ x → (A.valuation x < 1 ↔ B.valuation x < 1)) → ∃ ρ : G E Ω, (∀ x ∈ K, ρ x = x) ∧ ρ • A = B := by
  first | exact @GlobalTheory.conj_places_of_same_prime_below | exact GlobalTheory.conj_places_of_same_prime_below | (intros; apply GlobalTheory.conj_places_of_same_prime_below <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem eventually_apply_eq {l : ℕ} [Fact l.Prime] (x : Om l) (g₀ : GQ l) :
    ∀ᶠ g : GQ l in nhds g₀, g x = g₀ x := by
  have hS := stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x
  have hc : Continuous fun g : GQ l => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hmem : (fun g : GQ l => g₀⁻¹ * g) g₀ ∈ (MulAction.stabilizer (GQ l) x : Set (GQ l)) := by
    simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hS.mem_nhds hmem)] with g hg
  have hg' : (g₀⁻¹ * g) x = x := hg
  have := congrArg g₀ hg'
  simpa [AlgEquiv.mul_apply] using this

theorem IsActC.continuous_orbit (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (h : IsActC act) (y : PadicComplex l) :
    Continuous (fun g => act g y) := by
  obtain ⟨hext, hiso⟩ := h
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, hx⟩ : ∃ x : Om l, dist y (x : PadicComplex l) < ε / 2 :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt y (half_pos hε)
  filter_upwards [eventually_apply_eq x g₀] with g hg
  have h1 : act g y - act g₀ y = act g (y - x) - act g₀ (y - x) := by
    rw [map_sub, map_sub, hext g x, hext g₀ x, hg]
    ring
  rw [dist_eq_norm, h1]
  calc ‖act g (y - x) - act g₀ (y - x)‖ ≤ ‖act g (y - x)‖ + ‖act g₀ (y - x)‖ := norm_sub_le _ _
    _ = 2 * ‖y - x‖ := by rw [hiso, hiso]; ring
    _ < ε := by rw [← dist_eq_norm]; linarith

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordInjectiveRangeMem
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

noncomputable section

namespace GlobalTheory.WachTie

theorem coord_injective_range_mem : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → IsCrys PD T.ρ → Function.Injective (coord W R jE T (fun k => (b k : W.DD T))) ∧ LinearMap.range (coord W R jE T (fun k => (b k : W.DD T))) = DDinv W T ∧ ∀ x, coord W R jE T (fun k => (b k : W.DD T)) x ∈ W.NΔ T ↔ ∀ i, x i ∈ R.N0 r := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    hF hE hb hc
  obtain ⟨-, hFr, -⟩ := hF
  obtain ⟨hext, hinj, hEr, -⟩ := hE
  let c : Module.Basis (Fin r) W.EE (W.DD T) := (W.N_base T hc).basis b
  have hcb : ∀ k, c k = (b k : W.DD T) := fun k => IsBaseChange.basis_apply b (W.N_base T hc) k
  have huniq : ∀ y y' : Fin r → W.EE,
      ∑ k, y k • (b k : W.DD T) = ∑ k, y' k • (b k : W.DD T) → y = y' := by
    intro y y' h
    apply c.equivFun.symm.injective
    simp only [Module.Basis.equivFun_symm_apply, hcb]
    exact h
  have hex : ∀ m : W.DD T, ∃ y : Fin r → W.EE, ∑ k, y k • (b k : W.DD T) = m := by
    intro m
    refine ⟨c.repr m, ?_⟩
    simp only [← hcb]
    exact c.sum_repr m
  have hγ : ∀ δ ∈ W.DelF, ∀ y : Fin r → W.EE, W.γD T δ (∑ k, y k • (b k : W.DD T)) =
      ∑ k, W.γE δ (y k) • (b k : W.DD T) := by
    intro δ hδ y
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [W.γD_smul, (hb k).2 δ hδ]
  have hinv : ∀ x, ∀ δ ∈ W.DelF, W.γD T δ (coord W R jE T (fun k => (b k : W.DD T)) x) =
      coord W R jE T (fun k => (b k : W.DD T)) x := by
    intro x δ hδ
    rw [coord_apply, hγ δ hδ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hEr _).1 ⟨_, rfl⟩ δ hδ]
  refine ⟨?_, ?_, ?_⟩
  · intro x x' h
    have := huniq _ _ h
    funext i k
    exact congrFun (hinj (congrFun this k)) i
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact hinv x
    · intro m hm
      obtain ⟨y, rfl⟩ := hex m
      have hy : ∀ k, ∃ x, jE x = y k := fun k => (hEr _).2 fun δ hδ =>
        congrFun (huniq _ _ ((hγ δ hδ y).symm.trans (hm δ hδ))) k
      choose x hx using hy
      refine ⟨fun i k => x k i, ?_⟩
      rw [coord_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hx k]
  · intro x
    constructor
    · rintro ⟨hN, -⟩
      set a := b.repr ⟨_, hN⟩ with ha
      have h1 : ∑ k, algebraMap (LetA O n) W.EE (a k) • (b k : W.DD T) =
          ∑ k, jE (fun i => x i k) • (b k : W.DD T) := by
        have := congrArg (W.N T).subtype (b.sum_repr ⟨_, hN⟩)
        rw [map_sum] at this
        simp only [algebraMap_smul]
        exact this
      have h2 := huniq _ _ h1
      intro i k _
      have h3 : algebraMap (LetA O n) W.EE (a k) = jE (fun i => x i k) := congrFun h2 k
      have h4 : ∀ i', ∃ a', j a' = a k i' := fun i' => (hFr _).2 fun δ hδ => by
        have h5 := (hEr _).1 ⟨_, h3.symm⟩ δ hδ
        rw [W.γE_ext] at h5
        exact congrFun (W.EE_inj h5) i'
      choose a' ha' using h4
      have h6 : jE (fun i => R.ι (a' i)) = jE (fun i => x i k) := by
        rw [hext, ← h3]
        congr 1
        funext i'
        exact ha' i'
      exact ⟨a' i, congrFun (hinj h6) i⟩
    · intro hx
      refine ⟨?_, hinv x⟩
      rw [coord_apply]
      refine Submodule.sum_mem _ fun k _ => ?_
      have h4 : ∀ i, ∃ a', R.ι a' = x i k := fun i => hx i k (Set.mem_univ _)
      choose a' ha' using h4
      have : (fun i => x i k) = fun i => R.ι (a' i) := funext fun i => (ha' i).symm
      rw [this, hext, algebraMap_smul]
      exact (W.N T).smul_mem _ (b k).2

end GlobalTheory.WachTie
end
end

