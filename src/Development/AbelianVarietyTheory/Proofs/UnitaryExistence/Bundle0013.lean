import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionLatticeSeparatedComplete
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DvdOfForallSubMulMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionLatticeSeparatedCompleteStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCompletion_lattice_separated_complete : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → (∀ z : Fin n → RA F E, (∀ N : ℕ, 0 < N → ∃ w ∈ (hat F (L : Set (Fin n → E))), z = N • w) → z = 0) ∧ ∀ x : ℕ → (Fin n → RA F E), (∀ N, x N ∈ (hat F (L : Set (Fin n → E)))) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ (hat F (L : Set (Fin n → E))), x (N * m) = x N + N • w) → ∃ z ∈ (hat F (L : Set (Fin n → E))), ∀ N : ℕ, 0 < N → ∃ w ∈ (hat F (L : Set (Fin n → E))), z = x N + N • w := by
  first | exact @GlobalTheory.AdLat.Complete.hat_separated_complete | exact GlobalTheory.AdLat.Complete.hat_separated_complete | (intros; apply GlobalTheory.AdLat.Complete.hat_separated_complete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring
section
open IsLocalRing MvPowerSeries

namespace GlobalTheory.CohenStructure

theorem isDomain_mvPowerSeries (R : Type) [CommRing R] [IsDomain R] (n : ℕ) :
    IsDomain (MvPowerSeries (Fin n) R) :=
  NoZeroDivisors.to_isDomain _

theorem isIntegrallyClosed_mvPowerSeries (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
    have := isDomain_mvPowerSeries R n
    have := GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries (MvPowerSeries (Fin n) R)
    exact IsIntegrallyClosed.of_equiv (finSuccEquiv R n).toRingEquiv.symm

theorem isAdicComplete_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) [h : IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal B) B := by
  rw [← map_ringEquiv_maximalIdeal e, IsAdicComplete.congr_ringEquiv]
  exact h

theorem isAdicComplete_mvPowerSeries (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact isAdicComplete_of_ringEquiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
    have := ReciprocityTheory.P1.isAdicComplete_ps (R := MvPowerSeries (Fin n) R)
    exact isAdicComplete_of_ringEquiv (finSuccEquiv R n).toRingEquiv.symm

theorem finite_quotient_of_pow_le {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (h : ∀ s : S, ∃ a : A, s - algebraMap A S a ∈ I) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  have key : ∀ N : ℕ, ∃ F : Submodule A S, F.FG ∧ F ⊔ (I ^ N).restrictScalars A = ⊤ := by
    intro N
    induction N with
    | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
    | succ N ih =>
      obtain ⟨F, hF, hF'⟩ := ih
      obtain ⟨G, hG⟩ : (I ^ N).FG := IsNoetherian.noetherian _
      refine ⟨F ⊔ Submodule.span A (G : Set S), hF.sup (Submodule.fg_span G.finite_toSet), ?_⟩
      rw [eq_top_iff, ← hF', sup_assoc]
      refine sup_le_sup_left (fun x hx => ?_) _
      have hx' : x ∈ Submodule.span S (G : Set S) := hG.ge hx
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hx'
      refine sum_mem fun y hy => ?_
      obtain ⟨a, ha⟩ := h (c y)
      have : c y • y = a • y + y * (c y - algebraMap A S a) := by
        rw [Algebra.smul_def a, smul_eq_mul]; ring
      rw [this]
      refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span hy)) ?_
      rw [pow_succ]
      exact Ideal.mul_mem_mul (hG.le (Ideal.subset_span hy)) ha
  obtain ⟨F, hF, hF'⟩ := key N
  have : Module.Finite A F := Module.Finite.iff_fg.2 hF
  refine Module.Finite.of_surjective ((Ideal.Quotient.mkₐ A J).toLinearMap ∘ₗ F.subtype) fun s => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hF'.ge (Submodule.mem_top (x := s)))
  exact ⟨⟨y, hy⟩, Ideal.Quotient.eq.2 (by simpa using hN hz)⟩

theorem injective_of_ringKrullDim_eq {A S : Type} [CommRing A] [IsDomain A] [CommRing S]
    [Algebra A S] [Module.Finite A S] {n : ℕ} (hA : ringKrullDim A = n) (hS : ringKrullDim S = n) :
    Function.Injective (algebraMap A S) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  have h1 := ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := A) (⊥ : Ideal S)
  have h2 := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.mk ((⊥ : Ideal S).comap (algebraMap A S))) Ideal.Quotient.mk_surjective
    (mem_nonZeroDivisors_of_ne_zero hr0) (Ideal.Quotient.eq_zero_iff_mem.2 hr)
  rw [← h1, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot S), hA, hS] at h2
  norm_cast at h2
  omega

theorem exists_finite_injective_of_isAdicComplete :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S] (p : ℕ), p.Prime →
      (p : S) ∈ maximalIdeal S → IsNoetherianRing S → IsAdicComplete (maximalIdeal S) S →
      ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (i : A →+* S),
        Function.Injective i ∧ i.Finite ∧ IsNoetherianRing A ∧ IsIntegrallyClosed A ∧
          IsAdicComplete (maximalIdeal A) A := by
  intro S _ _ _ _ p hp h0 hn hc
  have hp0 : (p : S) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.PBasis.exists_pBasis (ResidueField S) p hp
    (by rw [← map_natCast (residue S), residue_eq_zero_iff]; exact h0)
  obtain ⟨Λ, h1, h2, h3⟩ := CoeffSubring.exists_coeffSubring hp hp0 h0 hB hB'
  obtain ⟨_, hm, hΛ⟩ := GlobalTheory.isDVR_of_closed_subring_principal S Λ p (by simpa using hp0) (by simpa using h0) hc h1 h2 h3
  obtain ⟨n, x, hx, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S p hp0 h0
  let A := MvPowerSeries (Fin n) Λ
  let φ : A →ₐ[Λ] S := mvEvalAdic Λ (maximalIdeal S) x hx
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := isDomain_mvPowerSeries Λ n
  have hA := isAdicComplete_mvPowerSeries Λ n
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => by simpa [φ] using hx j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hm, Ideal.mem_span_singleton] at h5
    obtain ⟨c, hc⟩ := h5
    have h6 : algebraMap Λ S (constantCoeff g) ∈ maximalIdeal S := by
      rw [hc, map_mul, map_natCast]
      exact Ideal.mul_mem_right _ _ h0
    have h7 := add_mem h4 h6
    rwa [sub_add_cancel] at h7
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rintro _ (rfl | ⟨i, rfl⟩)
    · rw [← map_natCast (algebraMap A S)]
      refine Ideal.mem_map_of_mem _ (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 ?_)
      rw [map_natCast, hm]
      exact Ideal.mem_span_singleton_self _
    · rw [← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]
      exact Ideal.mem_map_of_mem (algebraMap A S)
        (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, ha, h⟩ := h1 s
    refine ⟨C ⟨a, ha⟩, ?_⟩
    rwa [show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  refine ⟨A, inferInstance, inferInstance, inferInstance, algebraMap A S,
    injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin, inferInstance,
    isIntegrallyClosed_mvPowerSeries Λ n, hA⟩
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
    Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]
  norm_cast

end GlobalTheory.CohenStructure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGrpObjOfFlatClosed
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

theorem exists_grpObj_of_mono {H G : C} [GrpObj G] (j : H ⟶ G) [Mono j]
    (o : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (n : H ⟶ H) (ho : o ≫ j = η[G])
    (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[G]) (hn : n ≫ j = j ≫ GrpObj.inv) :
    ∃ _ : GrpObj H, IsMonHom j := by
  letI M : MonObj H :=
    { one := o
      mul := m
      one_mul := by
        rw [← cancel_mono j, Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, ho,
          Category.id_comp, tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono j, Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, ho,
          Category.id_comp, MonoidalCategory.tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono j]
        simp only [Category.assoc, hm]
        rw [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          tensorHom_comp_tensorHom_assoc, hm, Category.id_comp]
        have h1 : ((j ⊗ₘ j) ≫ μ[G] ⊗ₘ j) = ((j ⊗ₘ j) ⊗ₘ j) ≫ μ[G] ▷ G := by
          rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
        have h2 : (j ⊗ₘ (j ⊗ₘ j) ≫ μ[G]) = (j ⊗ₘ (j ⊗ₘ j)) ≫ G ◁ μ[G] := by
          rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
        rw [h1, h2, Category.assoc, Category.assoc, MonObj.mul_assoc, associator_naturality_assoc] }
  refine ⟨{ inv := n, left_inv := ?_, right_inv := ?_ }, ⟨ho, hm⟩⟩
  · rw [← cancel_mono j]
    change (lift n (𝟙 H) ≫ m) ≫ j = (toUnit H ≫ o) ≫ j
    rw [Category.assoc, hm, lift_map_assoc, hn, Category.assoc, ho, Category.id_comp]
    have := j ≫= GrpObj.left_inv G
    rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc] at this
    exact this
  · rw [← cancel_mono j]
    change (lift (𝟙 H) n ≫ m) ≫ j = (toUnit H ≫ o) ≫ j
    rw [Category.assoc, hm, lift_map_assoc, hn, Category.assoc, ho, Category.id_comp]
    have := j ≫= GrpObj.right_inv G
    rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc] at this
    exact this

theorem isMonHom_of_comp_mono {A B D : C} [MonObj A] [MonObj B] [MonObj D] (e : A ⟶ B) (i : B ⟶ D)
    [Mono i] [IsMonHom i] [h : IsMonHom (e ≫ i)] : IsMonHom e := by
  constructor
  · rw [← cancel_mono i, Category.assoc, h.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono i, Category.assoc, h.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

theorem isCommMonObj_of_mono [BraidedCategory C] {H G : C} [MonObj H] [MonObj G] (j : H ⟶ G)
    [Mono j] [IsMonHom j] [IsCommMonObj G] : IsCommMonObj H := by
  constructor
  rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]

end

theorem exists_grpObj_of_flat_closed {S S' : Scheme.{0}} (f : S' ⟶ S)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] (P Ga : Over S) [GrpObj P] (io : Ga ⟶ P)
    (Z : Over S') [GrpObj Z] (i : Z ⟶ (Over.pullback f).obj P) (e : (Over.pullback f).obj Ga ≅ Z)
    [IsClosedImmersion io.left] [Flat Ga.hom] [hi : IsMonHom i]
    (h : e.hom ≫ i = (Over.pullback f).map io) :
    ∃ _ : GrpObj Ga, IsMonHom io ∧ IsMonHom e.hom ∧ (IsCommMonObj P → IsCommMonObj Ga) := by
  have h1 : Flat (𝟙_ (Over S)).hom := inferInstanceAs (Flat (𝟙 S))
  have h2 : Flat (Ga ⊗ Ga).hom := inferInstanceAs (Flat (pullback.fst Ga.hom Ga.hom ≫ Ga.hom))
  have hm : Mono io := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono io.left))
  have hm' : Mono ((Over.pullback f).map io) := inferInstance
  have h' : e.inv ≫ (Over.pullback f).map io = i := by rw [← h, e.inv_hom_id_assoc]
  have hmi : Mono i := by rw [← h']; infer_instance
  obtain ⟨o, ⟨ho, -⟩, -⟩ := existsUnique_lift_of_flat f io η[P]
    (Functor.OplaxMonoidal.η (Over.pullback f) ≫ η[Z] ≫ e.inv) (by
      rw [Category.assoc, Category.assoc, h', hi.one_hom, Functor.obj.η_def,
        Functor.Monoidal.η_ε_assoc])
  obtain ⟨m, ⟨hm, -⟩, -⟩ := existsUnique_lift_of_flat f io ((io ⊗ₘ io) ≫ μ[P])
    (Functor.OplaxMonoidal.δ (Over.pullback f) Ga Ga ≫ (e.hom ⊗ₘ e.hom) ≫ μ[Z] ≫ e.inv) (by
      simp only [Category.assoc]
      rw [h', hi.mul_hom, tensorHom_comp_tensorHom_assoc, h, Functor.obj.μ_def,
        Functor.LaxMonoidal.μ_natural_assoc, Functor.Monoidal.δ_μ_assoc, Functor.map_comp])
  obtain ⟨n, ⟨hn, -⟩, -⟩ := existsUnique_lift_of_flat f io (io ≫ GrpObj.inv)
    (e.hom ≫ GrpObj.inv ≫ e.inv) (by
      simp only [Category.assoc]
      rw [h', GrpObj.inv_hom, ← Category.assoc, h, Functor.obj.ι_def, Functor.map_comp])
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono io o m n ho hm hn
  refine ⟨G, hG, ?_, fun _ => isCommMonObj_of_mono io⟩
  have : IsMonHom (e.hom ≫ i) := by rw [h]; infer_instance
  exact isMonHom_of_comp_mono e.hom i

theorem flat_closure_subgroup :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (P Ga : Over (Sp T)) [GrpObj P] (io : Ga ⟶ P) (Z : Over (Sp K)) [GrpObj Z] (i : Z ⟶ (Over.pullback (spMap (algebraMap T K))).obj P) (e : (Over.pullback (spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left → Flat Ga.hom → IsMonHom i → e.hom ≫ i = (Over.pullback (spMap (algebraMap T K))).map io → ∃ _ : GrpObj Ga, IsMonHom io ∧ IsMonHom e.hom ∧ (IsCommMonObj P → IsCommMonObj Ga) := by
  intro T K _ _ _ _ _ _ P Ga _ io Z _ i e _ _ _ h
  have := schemeTheoreticallyDominant_fractionField T K
  exact exists_grpObj_of_flat_closed _ P Ga io Z i e h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteOfIsClosedSplitTorusOfPowEqOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

namespace GlobalTheory

theorem adjunction_homEquiv_symm_mul {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [R.Monoidal] {Y : C} {M : D} [MonObj M] (a b : Y ⟶ R.obj M) :
    (adj.homEquiv Y M).symm (a * b) = (adj.homEquiv Y M).symm a * (adj.homEquiv Y M).symm b := by
  rw [Hom.mul_def, Hom.mul_def, Functor.obj.μ_def, ← Category.assoc,
    adj.homEquiv_naturality_right_symm]
  congr 1
  ext
  · rw [← adj.homEquiv_naturality_right_symm]; simp
  · rw [← adj.homEquiv_naturality_right_symm]; simp

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra

noncomputable def splitTorusPoint (t : Multiplicative X →* kˣ) :
    𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X :=
  Over.homMk (Spec.map (CommRingCat.ofHom (torusEval t).toRingHom) ≫ (torusIso k X).hom) (by
    erw [Category.assoc, torusIso_hom_hom, ← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp]
    have : (torusEval t).toRingHom.comp (algebraMap k (AddMonoidAlgebra k X)) = RingHom.id k :=
      (torusEval t).comp_algebraMap
    rw [this]
    exact Spec.map_id _)

theorem splitTorusPoint_left (t : Multiplicative X →* kˣ) :
    (splitTorusPoint t).left =
      Spec.map (CommRingCat.ofHom (torusEval t).toRingHom) ≫ (torusIso k X).hom := rfl

theorem splitTorusPoint_bijective :
    Function.Bijective (splitTorusPoint : (Multiplicative X →* kˣ) → _) := by
  constructor
  · intro s t h
    have h1 := congrArg (·.left) h
    simp only [splitTorusPoint_left] at h1
    have h2 := Spec.map_injective ((cancel_mono _).1 h1)
    exact torusEval_bijective.1 (AlgHom.coe_ringHom_injective (congrArg (·.hom) h2))
  · intro x
    let g : Spec (.of k) ⟶ Spec (.of (AddMonoidAlgebra k X)) := x.left ≫ (torusIso k X).inv
    have hg : CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k X)) ≫ Spec.preimage g = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, ← torusIso_hom_hom, Spec.map_id]
      simp only [g]
      erw [Category.assoc, Iso.inv_hom_id_assoc]
      exact Over.w x
    obtain ⟨t, ht⟩ := torusEval_bijective.2 ⟨(Spec.preimage g).hom, fun r => congr($hg r)⟩
    refine ⟨t, Over.OverMorphism.ext ?_⟩
    rw [splitTorusPoint_left, ht]
    change Spec.map (Spec.preimage g) ≫ _ = _
    rw [Spec.map_preimage]
    simp only [g]
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

noncomputable def splitTorusDown (x : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    (Spec (.of k)).asOver (Spec ZU) ⟶ splitTorusAff ZU X :=
  (Over.homMk (𝟙 (Sp k)) (specULiftZIsTerminal.hom_ext _ _) :
    (Spec (.of k)).asOver (Spec ZU) ⟶ (Over.map (toZ (Sp k))).obj (𝟙_ (Over (Sp k)))) ≫
    ((Over.mapPullbackAdj (toZ (Sp k))).homEquiv _ _).symm x

theorem splitTorusDown_left (x : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    (splitTorusDown x).left = x.left ≫ torusFst (Sp k) X := by
  simp [splitTorusDown, Adjunction.homEquiv_symm_apply, torusFst]
  rfl

theorem splitTorusDown_mul (x y : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    splitTorusDown (x * y) = splitTorusDown x * splitTorusDown y := by
  unfold splitTorusDown
  rw [← comp_mul]
  exact congrArg _ (adjunction_homEquiv_symm_mul (Over.mapPullbackAdj _) x y)

theorem splitTorusDown_injective :
    Function.Injective (splitTorusDown : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) → _) := by
  intro x y h
  have h1 := congrArg (·.left) h
  simp only [splitTorusDown_left] at h1
  exact Over.OverMorphism.ext (pullback.hom_ext h1 ((Over.w x).trans (Over.w y).symm))

noncomputable def torusEvalInt (t : Multiplicative X →* kˣ) :
    AddMonoidAlgebra ZU.{0} X →ₐ[ZU.{0}] k :=
  AddMonoidAlgebra.lift _ k X ((Units.coeHom k).comp t)

theorem splitTorusDown_point (t : Multiplicative X →* kˣ) :
    splitTorusDown (splitTorusPoint t) = Spec.mapMulEquiv (WithConv.toConv (torusEvalInt t)) := by
  refine Over.OverMorphism.ext ?_
  rw [splitTorusDown_left, splitTorusPoint_left]
  erw [Category.assoc, torusIso_hom_fst, ← Spec.map_comp]
  change _ = Spec.map (CommRingCat.ofHom (torusEvalInt t).toRingHom)
  rw [← CommRingCat.ofHom_comp]
  congr 2
  refine ringHom_ext_ZU fun y => ?_
  simp [torusEvalInt]

theorem torusEvalInt_mul (s t : Multiplicative X →* kˣ) :
    WithConv.toConv (torusEvalInt (s * t)) =
      WithConv.toConv (torusEvalInt s) * WithConv.toConv (torusEvalInt t) := by
  apply WithConv.ofConv_injective
  apply AlgHom.coe_ringHom_injective
  refine ringHom_ext_ZU fun y => ?_
  simp [torusEvalInt, AlgHom.convMul_def]

theorem splitTorusPoint_mul (s t : Multiplicative X →* kˣ) :
    splitTorusPoint (s * t) = splitTorusPoint s * splitTorusPoint t := by
  apply splitTorusDown_injective
  rw [splitTorusDown_mul, splitTorusDown_point, splitTorusDown_point, splitTorusDown_point,
    torusEvalInt_mul, map_mul]

variable (k X) in

noncomputable def splitTorusPointEquiv :
    (Multiplicative X →* kˣ) ≃* (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :=
  { Equiv.ofBijective _ splitTorusPoint_bijective with map_mul' := splitTorusPoint_mul }

theorem range_splitTorusPoint_left (t : Multiplicative X →* kˣ) :
    Set.range (splitTorusPoint t).left = {(torusIso k X).hom (torusPrime t)} := by
  have h : ∀ p, (splitTorusPoint t).left p = (torusIso k X).hom (torusPrime t) := fun p => by
    have hp : p = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [hp]
    rfl
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact h p
  · rintro rfl
    exact ⟨_, h (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)⟩

theorem finite_of_isClosed_splitTorus_of_pow_eq_one :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X] (n : ℕ), n.Prime → (n : k) ≠ 0 →
      ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X))
        (Z : Set (splitTorus (Sp k) X).left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) →
        (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by
  intro k _ _ X _ _ _ n hp hn C Z hZ hC htors
  haveI : NeZero (n : k) := ⟨hn⟩
  let e := splitTorusPointEquiv k X
  have hcl : @IsClosed _ (torusZariski k X)
      (C.comap e.toMonoidHom : Set (Multiplicative X →* kˣ)) := by
    refine isClosed_induced_iff.2 ⟨(torusIso k X).hom ⁻¹' Z,
      hZ.preimage (torusIso k X).hom.continuous, ?_⟩
    ext t
    change _ ↔ splitTorusPoint t ∈ C
    rw [hC, range_splitTorusPoint_left, Set.singleton_subset_iff]
    rfl
  have h := finite_of_isClosed_torusZariski_of_pow_eq_one hp.two_le hcl fun s hs h1 =>
    e.injective (by rw [map_one]; exact htors _ hs (by rw [← map_pow, h1, map_one]))
  have e' : C.comap e.toMonoidHom ≃ C := e.toEquiv.subtypeEquiv fun _ => Iff.rfl
  exact e'.finite_iff.1 h.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isOpenImmersion_spMap_of_isDiscreteValuationRing (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] :
    IsOpenImmersion (spMap (algebraMap T K)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have : IsLocalization.Away π K := by
    refine IsLocalization.Away.mk π (IsUnit.mk0 _ (by simpa using hπ.ne_zero)) (fun s => ?_)
      (fun a b hab => ⟨0, by simpa using IsFractionRing.injective T K hab⟩)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T) s
    obtain ⟨n, v, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    refine ⟨n, a * (v⁻¹ : Tˣ), ?_⟩
    have h1 : algebraMap T K π ≠ 0 := by simpa using hπ.ne_zero
    have h2 : algebraMap T K v ≠ 0 := by simp
    simp only [map_mul, map_pow, map_units_inv]
    field_simp
  exact IsOpenImmersion.of_isLocalization π

theorem isIntegral_of_flat_of_isIntegral_genericFibre (T K : Type) [CommRing T] [IsDomain T]
    [Field K] [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [IsIntegral (pullback f (spMap (algebraMap T K)))] : IsIntegral X := by
  have := isDominant_spMap_of_isFractionRing T K
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  let g := pullback.fst f (spMap (algebraMap T K))
  have : IsReduced X := IsSchemeTheoreticallyDominant.isReduced g
  have : IsDominant g := inferInstance
  have h : IsIrreducible (closure (Set.range g)) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image g g.continuous.continuousOn).closure
  rw [g.denseRange.closure_range] at h
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr h
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem isIso_of_quasiFinite_of_isIso_genericFibre_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (Ga G : Over (Sp T)) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      Flat Ga.hom → IsSeparated p.left → LocallyOfFiniteType p.left → QuasiCompact p.left →
      LocallyQuasiFinite p.left → Smooth G.hom → GeometricallyConnected G.hom →
      IsIso ((Over.pullback (spMap (algebraMap T K))).map p) → IsIso p := by
  intro T K _ _ _ _ _ _ Ga G _ _ p _ _ _ _ _ _ _ _ _
  let t := spMap (algebraMap T K)
  have : IsOpenImmersion t := isOpenImmersion_spMap_of_isDiscreteValuationRing T K
  have hc : ConnectedSpace ((Over.pullback t).obj G).left :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback G.hom t)
  obtain ⟨hG, hN⟩ := isIntegral_and_isNormalScheme_of_smooth_dvr T K G ‹_› hc
  let q : pullback Ga.hom t ⟶ pullback G.hom t := ((Over.pullback t).map p).left
  have : IsIso q := inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback t).map p)))
  have e : q ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left := pullback.lift_fst _ _ _
  have : ConnectedSpace ↥(pullback G.hom t) := hc
  have : IsIntegral (pullback G.hom t) := isIntegral_of_isOpenImmersion (pullback.fst G.hom t)
  have : Nonempty ↥(pullback Ga.hom t) := ⟨inv q (Classical.arbitrary _)⟩
  have : IsIntegral (pullback Ga.hom t) := isIntegral_of_isOpenImmersion q
  have : IsIntegral Ga.left := isIntegral_of_flat_of_isIntegral_genericFibre T K Ga.hom
  let j := pullback.fst Ga.hom t
  have : IsOpenImmersion (j.opensRange.ι ≫ p.left) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc, ← e]
    infer_instance
  have : IsOpenImmersion p.left :=
    isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict p.left (fun y ↦ (hN y).2)
      j.opensRange ⟨⟨j (Classical.arbitrary _), _, rfl⟩⟩
  exact isIso_of_isOpenImmersion_of_geometricallyConnected _ Ga G p ‹_› ‹_› inferInstance ‹_›

end GlobalTheory
end

