import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumOrbitsCountingPrincipleFiniteFibres
section
open Polynomial

namespace GlobalTheory.OrbitCounting

theorem stabilizer_smul_eq {G X : Type} [CommGroup G] [MulAction G X] (g : G) (x : X) :
    MulAction.stabilizer G (g • x) = MulAction.stabilizer G x := by
  ext h
  simp only [MulAction.mem_stabilizer_iff]
  rw [← mul_smul, mul_comm, mul_smul, smul_left_cancel_iff]

theorem ncard_fibre_inter_orbit {G X Y : Type} [CommGroup G] [MulAction G X] [MulAction G Y]
    (π : X → Y) (hπ : ∀ (g : G) (x : X), π (g • x) = g • π x) (x0 : X) :
    {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0}.ncard =
      (MulAction.stabilizer G x0).relIndex (MulAction.stabilizer G (π x0)) := by
  have hset : {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0} =
      MulAction.orbit (MulAction.stabilizer G (π x0)) x0 := by
    ext x; constructor
    · rintro ⟨hx, g, rfl⟩
      refine ⟨⟨g, ?_⟩, rfl⟩
      rw [MulAction.mem_stabilizer_iff, ← hπ]; exact hx
    · rintro ⟨⟨g, hg⟩, rfl⟩
      refine ⟨?_, ⟨g, rfl⟩⟩
      show π (g • x0) = π x0
      rw [hπ]; exact hg
  rw [hset, Subgroup.relIndex, ← MulAction.index_stabilizer]
  congr 1

theorem counting_principle : ∀ (G X Y : Type) [CommGroup G] [MulAction G X] [MulAction G Y] (Gc : Subgroup G) (π : X → Y), (∀ (g : G) (x : X), π (g • x) = g • π x) → (∀ y, (π ⁻¹' {y}).Finite) → (∀ y : Y, MulAction.stabilizer G y ≤ Gc ∧ (MulAction.stabilizer G y).relIndex Gc ≠ 0) → Finite (MulAction.orbitRel.Quotient G Y) → ∀ w : Y → ℚ, (∀ (g : G) (y : Y), w (g • y) = w y) → ∑ᶠ o : MulAction.orbitRel.Quotient G X, w (π (Quotient.out o)) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) = ∑ᶠ o : MulAction.orbitRel.Quotient G Y, w (Quotient.out o) * ((π ⁻¹' {(Quotient.out o)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) := by
  intro G X Y _ _ _ Gc π hπ hfin hstab hY w hw
  classical
  have hmem : ∀ a b : X, a ∈ MulAction.orbit G b → π a ∈ MulAction.orbit G (π b) := by
    rintro a b ⟨g, rfl⟩; exact ⟨g, (hπ g b).symm⟩
  let q : MulAction.orbitRel.Quotient G X → MulAction.orbitRel.Quotient G Y :=
    Quotient.map π (fun a b h => MulAction.orbitRel_apply.2 (hmem a b (MulAction.orbitRel_apply.1 h)))
  have hq : ∀ x : X, q (Quotient.mk _ x) = Quotient.mk _ (π x) := fun x => rfl

  have hrep : ∀ (oX : MulAction.orbitRel.Quotient G X) (y : Y), q oX = Quotient.mk _ y →
      ∃ x0, π x0 = y ∧ Quotient.mk _ x0 = oX := by
    intro oX y h
    have h1 : q oX = Quotient.mk _ (π (Quotient.out oX)) := by
      rw [← hq, Quotient.out_eq]
    rw [h1] at h
    have h2 : y ∈ MulAction.orbit G (π (Quotient.out oX)) :=
      MulAction.orbitRel_apply.1 (Quotient.exact h.symm)
    obtain ⟨g, hg⟩ := h2
    refine ⟨g • Quotient.out oX, by rw [hπ]; exact hg, ?_⟩
    rw [← Quotient.out_eq oX]
    exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, by rw [Quotient.out_eq]⟩)

  let F : X → ℚ := fun x => w (π x) * ((MulAction.stabilizer G x).relIndex Gc : ℚ)
  let H : Y → ℚ := fun y => w y * ((π ⁻¹' {y}).ncard : ℚ) * ((MulAction.stabilizer G y).relIndex Gc : ℚ)
  have hF : ∀ x x' : X, x' ∈ MulAction.orbit G x → F x' = F x := by
    rintro x x' ⟨g, rfl⟩
    simp only [F, hπ, hw, stabilizer_smul_eq]

  haveI : ∀ oY : MulAction.orbitRel.Quotient G Y, Finite ↥(π ⁻¹' {Quotient.out oY}) :=
    fun oY => (hfin _).to_subtype
  haveI hXf : Finite (MulAction.orbitRel.Quotient G X) := by
    refine Finite.of_surjective
      (fun p : (Σ oY : MulAction.orbitRel.Quotient G Y, ↥(π ⁻¹' {Quotient.out oY})) =>
        (Quotient.mk _ (p.2 : X) : MulAction.orbitRel.Quotient G X)) ?_
    intro oX
    obtain ⟨x0, hx0, hx0'⟩ := hrep oX (Quotient.out (q oX)) (Quotient.out_eq _).symm
    exact ⟨⟨q oX, ⟨x0, hx0⟩⟩, hx0'⟩
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient G Y)
  have hL : ∀ oX : MulAction.orbitRel.Quotient G X,
      w (π (Quotient.out oX)) * ((MulAction.stabilizer G (Quotient.out oX)).relIndex Gc : ℚ) = F (Quotient.out oX) := fun _ => rfl
  have hR : ∀ oY : MulAction.orbitRel.Quotient G Y,
      w (Quotient.out oY) * ((π ⁻¹' {(Quotient.out oY)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out oY)).relIndex Gc : ℚ) = H (Quotient.out oY) := fun _ => rfl
  simp only [hL, hR]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_fiberwise Finset.univ q]
  refine Finset.sum_congr rfl (fun oY _ => ?_)
  set y := Quotient.out oY with hy
  have hyo : Quotient.mk _ y = oY := Quotient.out_eq oY
  set S := (hfin y).toFinset with hS
  have hcard : (π ⁻¹' {y}).ncard = S.card := Set.ncard_eq_toFinset_card _ (hfin y)
  have hmaps : (S : Set X).MapsTo (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X))
      (Finset.univ.filter (fun oX => q oX = oY) : Finset _) := by
    intro x hx
    simp only [hS, Set.Finite.coe_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [hq, hx, hyo]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  show _ = w y * ((π ⁻¹' {y}).ncard : ℚ) * ((MulAction.stabilizer G y).relIndex Gc : ℚ)
  rw [hcard, hsum]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun oX hoX => ?_)
  have hqo : q oX = Quotient.mk _ y := by
    rw [hyo]; simpa using hoX
  obtain ⟨x0, hx0, hx0'⟩ := hrep oX y hqo
  have hout : Quotient.out oX ∈ MulAction.orbit G x0 := by
    apply MulAction.orbitRel_apply.1
    apply Quotient.exact
    rw [Quotient.out_eq, hx0']
  rw [hF x0 _ hout]
  have hfilt : ((S.filter (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X) = oX) : Finset X) : Set X)
      = {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0} := by
    ext x
    simp only [hS, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_setOf_eq, hx0]
    rw [← hx0']
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, MulAction.orbitRel_apply.1 (Quotient.exact h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Quotient.sound (MulAction.orbitRel_apply.2 h2)⟩
  rw [← Set.ncard_coe_finset, hfilt, ncard_fibre_inter_orbit π hπ x0]
  have hle1 : MulAction.stabilizer G x0 ≤ MulAction.stabilizer G (π x0) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← hπ, hg]
  rw [hx0] at hle1
  have hle2 : MulAction.stabilizer G y ≤ Gc := (hstab y).1
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  simp only [F, hx0]
  rw [← hmul]
  push_cast
  ring

end GlobalTheory.OrbitCounting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionalIdealExistsIntNotMemOfCountEqZero
section
open IsDedekindDomain

namespace GlobalTheory

theorem fractionalIdeal_exists_int_not_mem_of_count_eq_zero
    {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (I : FractionalIdeal (nonZeroDivisors R) K) :
    I ≠ 0 → FractionalIdeal.count K v I = 0 → ∃ s : R, s ∉ v.asIdeal ∧ algebraMap R K s ∈ I := by
  intro hI hc
  classical
  obtain ⟨a, J, ha, haJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ : J ≠ 0 := by
    rintro rfl
    apply hI
    rw [haJ]
    simp
  have hv : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  rw [FractionalIdeal.count_well_defined K v hI haJ, sub_eq_zero, Nat.cast_inj] at hc
  set n := (Associates.mk v.asIdeal).count (Associates.mk J).factors with hn
  have hJne : Associates.mk J ≠ 0 := Associates.mk_ne_zero.mpr hJ
  have haspan : Ideal.span {a} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ha
  have haNe : Associates.mk (Ideal.span {a}) ≠ 0 := Associates.mk_ne_zero.mpr haspan
  have hdJ : v.asIdeal ^ n ∣ J := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le hJne hv).mpr le_rfl
  have hda : v.asIdeal ^ n ∣ Ideal.span {a} := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le haNe hv).mpr hc.le
  obtain ⟨J1, hJ1⟩ := hdJ
  have hnot : ¬ v.asIdeal ∣ J1 := by
    intro h
    have h2 : v.asIdeal ^ (n + 1) ∣ J := by
      rw [hJ1, pow_succ]
      exact mul_dvd_mul_left _ h
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le hJne hv] at h2
    omega
  rw [Ideal.dvd_iff_le, SetLike.not_le_iff_exists] at hnot
  obtain ⟨s, hsJ1, hsv⟩ := hnot
  refine ⟨s, hsv, ?_⟩
  have hsa : s * a ∈ J := by
    rw [hJ1, mul_comm s a]
    exact Ideal.mul_mem_mul (Ideal.dvd_iff_le.mp hda (Ideal.mem_span_singleton_self a)) hsJ1
  rw [haJ, FractionalIdeal.mem_singleton_mul]
  refine ⟨algebraMap R K (s * a), FractionalIdeal.mem_coeIdeal_of_mem _ hsa, ?_⟩
  have ha' : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
  rw [map_mul]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameTranslateLatticeCosetSubset
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
namespace GlobalTheory.ParahoricTranslate

theorem isUnit_det_one_add_nonunit_smul {O : Type} [CommRing O] [IsLocalRing O] {r : ℕ} (ϖ : O)
    (hϖ : ¬ IsUnit ϖ) (Z : Matrix (Fin r) (Fin r) O) :
    IsUnit (1 + ϖ • Z).det := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro h
  set f := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
  have h0 : f (1 + ϖ • Z).det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
  have hf : f ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hϖ))
  have h1 : f.mapMatrix (1 + ϖ • Z) = 1 := by
    rw [map_add, map_one]
    ext i j
    simp [hf]
  rw [RingHom.map_det, h1, Matrix.det_one] at h0
  exact one_ne_zero h0

theorem toRows_left_mul_matrix_eq {K : Type} [CommRing K] {r t : ℕ}
    (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : Matrix (Fin r) (Fin r) K) :
    Matrix.toRows₁ (x * g) = Matrix.toRows₁ x * g := by
  ext i j; simp [Matrix.toRows₁, Matrix.mul_apply]

theorem translate_lattice_coset_subset : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g g' : GL (Fin r) K) (z z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → x * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K) → ∀ (y : Matrix (Fin r ⊕ Fin t) (Fin r) K) (w : Matrix (Fin r ⊕ Fin t) (Fin r) O), y * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w).map (algebraMap O K) → ∃ w' : Matrix (Fin r ⊕ Fin t) (Fin r) O, y * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w').map (algebraMap O K) := by
  intro O K _ _ _ _ _ _ _ r t ϖ hirr x g g' z z' hx hx' y w hy
  set φ := algebraMap O K
  set e := Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)
  set Z := Matrix.toRows₁ z
  set Z' := Matrix.toRows₁ z'
  set P : Matrix (Fin r) (Fin r) O := 1 + ϖ • Z
  set P' : Matrix (Fin r) (Fin r) O := 1 + ϖ • Z'
  set A := Matrix.toRows₁ x
  have hP : IsUnit P.det := isUnit_det_one_add_nonunit_smul ϖ hirr.not_isUnit Z
  have hA : A * (g : Matrix (Fin r) (Fin r) K) = φ.mapMatrix P := by
    have := congrArg Matrix.toRows₁ hx
    rw [toRows_left_mul_matrix_eq] at this
    rw [this, RingHom.mapMatrix_apply]
    show (Matrix.toRows₁ (e + ϖ • z)).map φ = (1 + ϖ • Z).map φ
    congr 1
  have hA' : A * (g' : Matrix (Fin r) (Fin r) K) = φ.mapMatrix P' := by
    have := congrArg Matrix.toRows₁ hx'
    rw [toRows_left_mul_matrix_eq] at this
    rw [this, RingHom.mapMatrix_apply]
    show (Matrix.toRows₁ (e + ϖ • z')).map φ = (1 + ϖ • Z').map φ
    congr 1
  have hPK : IsUnit (φ.mapMatrix P).det := by
    rw [← RingHom.map_det]; exact hP.map φ
  have hAu : IsUnit A.det := by
    rw [← hA, Matrix.det_mul] at hPK
    exact isUnit_of_mul_isUnit_left hPK
  set c : Matrix (Fin r) (Fin r) O := P⁻¹ * P'
  have hgc : (g' : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K) * φ.mapMatrix c := by
    have h2 : A * (g' : Matrix (Fin r) (Fin r) K) = A * ((g : Matrix (Fin r) (Fin r) K) * φ.mapMatrix c) := by
      rw [hA', ← Matrix.mul_assoc, hA, map_mul, ← Matrix.mul_assoc, ← map_mul,
        Matrix.mul_nonsing_inv _ hP, map_one, Matrix.one_mul]
    have h3 := congrArg (fun M => A⁻¹ * M) h2
    simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hAu] using h3
  refine ⟨Matrix.fromRows (P⁻¹ * (Z' - Z)) (0 : Matrix (Fin t) (Fin r) O) + w * c, ?_⟩
  have hc : c = 1 + ϖ • (P⁻¹ * (Z' - Z)) := by
    have : P' = P + ϖ • (Z' - Z) := by
      simp only [P, P', smul_sub]; abel
    simp only [c, this, Matrix.mul_add, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hP]
  have key : (e + ϖ • w) * c = e + ϖ • (Matrix.fromRows (P⁻¹ * (Z' - Z)) (0 : Matrix (Fin t) (Fin r) O) + w * c) := by
    rw [Matrix.add_mul, Matrix.smul_mul]
    have he : e * c = Matrix.fromRows c (0 : Matrix (Fin t) (Fin r) O) := by
      simp [e, Matrix.fromRows_mul]
    rw [he]
    nth_rewrite 1 [hc]
    ext (i | i) j <;> simp [e, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, smul_add, add_assoc]
  rw [hgc, ← Matrix.mul_assoc, hy, RingHom.mapMatrix_apply, ← Matrix.map_mul, key]

end GlobalTheory.ParahoricTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeModuleAdicCompleteSeparated
section
namespace GlobalTheory

theorem freeModule_adicComplete_separated : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → (∀ a : R, (∀ n : ℕ, ∃ b : R, a = ϖ ^ n * b) → a = 0) → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M], (∀ x : ℕ → M, ∃ y : M, ∀ n : ℕ, ∃ z : M, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) ∧ (∀ m : M, (∀ n : ℕ, ∃ z : M, m = ϖ ^ n • z) → m = 0) := by
  intro R _ ϖ hc hs M _ _ _ _
  classical
  let b := Module.Free.chooseBasis R M
  haveI : Fintype (Module.Free.ChooseBasisIndex R M) := Module.Free.ChooseBasisIndex.fintype R M
  constructor
  · intro x
    choose a ha using fun i => hc (fun j => b.equivFun (x j) i)
    refine ⟨b.equivFun.symm a, fun n => ?_⟩
    choose c hc' using fun i => ha i n
    refine ⟨b.equivFun.symm c, ?_⟩
    apply b.equivFun.injective
    funext i
    simp only [map_sub, map_sum, map_smul, LinearEquiv.apply_symm_apply, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hc' i
  · intro m hm
    apply b.equivFun.injective
    funext i
    show b.equivFun m i = b.equivFun 0 i
    rw [map_zero]
    show b.equivFun m i = 0
    apply hs
    intro n
    obtain ⟨z, hz⟩ := hm n
    refine ⟨b.equivFun z i, ?_⟩
    rw [hz, map_smul]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeOfXRegularQuotientTorsionFreeScalarTower
section
namespace GlobalTheory

open PowerSeries

theorem free_of_X_regular_quotient_torsionFree_scalarTower (O M : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup M] [Module (PowerSeries O) M]
    [Module.Finite (PowerSeries O) M] [Module O M] [IsScalarTower O (PowerSeries O) M]
    (hX : ∀ x : M, (PowerSeries.X : PowerSeries O) • x = 0 → x = 0)
    (hT : ∀ (c : O) (x : M), c ≠ 0 →
      (∃ y : M, (PowerSeries.C c : PowerSeries O) • x = (PowerSeries.X : PowerSeries O) • y) →
      ∃ y : M, x = (PowerSeries.X : PowerSeries O) • y) :
    Module.Free (PowerSeries O) M := by
  classical
  set p : Submodule (PowerSeries O) M :=
    Ideal.span {(PowerSeries.X : PowerSeries O)} • (⊤ : Submodule (PowerSeries O) M) with hp
  have memp : ∀ m : M, m ∈ p ↔ ∃ y : M, m = (PowerSeries.X : PowerSeries O) • y := by
    intro m
    rw [hp, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, hy⟩
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, Submodule.mem_top, hy.symm⟩
  have hsmul : ∀ (c : O) (m : M), c • m = (PowerSeries.C c : PowerSeries O) • m := by
    intro c m
    rw [← IsScalarTower.algebraMap_smul (PowerSeries O) c m, PowerSeries.algebraMap_apply]
    simp

  have hdec : ∀ r : PowerSeries O, ∃ s : PowerSeries O,
      r = PowerSeries.C (PowerSeries.constantCoeff r) + PowerSeries.X * s := by
    intro r
    obtain ⟨s, hs⟩ : (PowerSeries.X : PowerSeries O) ∣
        r - PowerSeries.C (PowerSeries.constantCoeff r) := by
      rw [PowerSeries.X_dvd_iff]
      simp
    exact ⟨s, by rw [← hs]; ring⟩

  have hN : ∀ (r : PowerSeries O) (y : M ⧸ p), r • y = (PowerSeries.constantCoeff r) • y := by
    intro r y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective p y
    obtain ⟨s, hs⟩ := hdec r
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, memp]
    have e1 : r • m = (PowerSeries.C (PowerSeries.constantCoeff r) : PowerSeries O) • m
        + (PowerSeries.X : PowerSeries O) • (s • m) := by
      conv_lhs => rw [hs]
      rw [add_smul, mul_smul]
    refine ⟨s • m, ?_⟩
    rw [e1, hsmul]
    abel
  have hfin : Module.Finite O (M ⧸ p) := by
    obtain ⟨T, hT'⟩ := Module.finite_def.mp
      (inferInstance : Module.Finite (PowerSeries O) (M ⧸ p))
    refine ⟨⟨T, ?_⟩⟩
    rw [eq_top_iff]
    rintro y -
    have hy : y ∈ Submodule.span (PowerSeries O) (T : Set (M ⧸ p)) := by
      rw [hT']
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r x _ hx =>
      rw [hN]
      exact Submodule.smul_mem _ _ hx
  have htf : Module.IsTorsionFree O (M ⧸ p) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c y hcy => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective p y
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, memp, hsmul c m] at hcy
      rw [Submodule.Quotient.mk_eq_zero, memp]
      exact hT c m hc hcy
  let b := Module.Free.chooseBasis O (M ⧸ p)
  choose e he using fun i => Submodule.Quotient.mk_surjective p (b i)
  have hspan : (⊤ : Submodule (PowerSeries O) M) ≤ Submodule.span (PowerSeries O) (Set.range e) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {PowerSeries.X})
      (Module.finite_def.mp inferInstance) ?_ ?_
    · rw [Ideal.span_le]
      rintro _ rfl
      change PowerSeries.X ∈ Ideal.jacobson (⊥ : Ideal (PowerSeries O))
      rw [Ideal.mem_jacobson_bot]
      intro y
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp
    · intro m _
      set c := b.repr (Submodule.Quotient.mk m)
      have h2 : m - ∑ i, c i • e i ∈ p := by
        rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply p (∑ i, c i • e i), map_sum]
        simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, he]
        exact (b.sum_repr _).symm
      rw [Submodule.mem_sup]
      refine ⟨∑ i, c i • e i, ?_, m - ∑ i, c i • e i, h2, by abel⟩
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent (PowerSeries O) e := by
    rw [Fintype.linearIndependent_iff]

    have key : ∀ k : ℕ, ∀ g : Module.Free.ChooseBasisIndex O (M ⧸ p) → PowerSeries O,
        ∑ i, g i • e i = 0 → ∀ i, (PowerSeries.X : PowerSeries O) ^ k ∣ g i := by
      intro k
      induction k with
      | zero =>
        intro g _ i
        simp
      | succ k ih =>
        intro g hg i
        choose s hs using fun j => hdec (g j)
        have hc : ∀ j, PowerSeries.constantCoeff (g j) = 0 := by
          have h0 : ∑ j, (PowerSeries.constantCoeff (g j)) • b j = 0 := by
            have h1 := congrArg p.mkQ hg
            simp only [map_sum, map_smul, Submodule.mkQ_apply, he, hN, map_zero] at h1
            exact h1
          exact (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h0
        have hgX : ∀ j, g j = PowerSeries.X * s j := by
          intro j
          rw [hs j, hc j]
          simp
        have hg' : (PowerSeries.X : PowerSeries O) • ∑ j, s j • e j = 0 := by
          rw [Finset.smul_sum, ← hg]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hgX j, mul_smul]
        obtain ⟨t, ht⟩ := ih s (hX _ hg') i
        exact ⟨t, by rw [hgX i, ht]; ring⟩
    intro g hg i
    ext n
    have h := PowerSeries.X_pow_dvd_iff.mp (key (n + 1) g hg i) n (Nat.lt_succ_self n)
    simpa using h
  exact Module.Free.of_basis (Module.Basis.mk hli hspan)

theorem free_of_X_regular_of_quotient_torsionFree (O M : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup M] [Module (PowerSeries O) M]
    [Module.Finite (PowerSeries O) M]
    (hX : ∀ x : M, (PowerSeries.X : PowerSeries O) • x = 0 → x = 0)
    (hT : ∀ (c : O) (x : M), c ≠ 0 →
      (∃ y : M, (PowerSeries.C c : PowerSeries O) • x = (PowerSeries.X : PowerSeries O) • y) →
      ∃ y : M, x = (PowerSeries.X : PowerSeries O) • y) :
    Module.Free (PowerSeries O) M := by
  let _ : Module O M := Module.compHom M (algebraMap O (PowerSeries O))
  have : IsScalarTower O (PowerSeries O) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact free_of_X_regular_quotient_torsionFree_scalarTower O M hX hT

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GhostComponentInjectiveOfNoTorsion
section
open scoped NNReal

namespace GlobalTheory

theorem WittVector.ghostComponent_injective_of_noTorsion :
    ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) →
      ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by
  intro l _ A _ hA x y h
  have hpow : ∀ (k : ℕ) (a : A), ((l : ℕ) : A) ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      apply hA
      apply ih
      rw [← mul_assoc, ← pow_succ]
      exact ha
  apply _root_.WittVector.ext
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := h n
    rw [_root_.WittVector.ghostComponent_apply, _root_.WittVector.ghostComponent_apply,
      wittPolynomial_eq_sum_C_mul_X_pow] at hn
    simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      eq_intCast, Int.cast_natCast, map_natCast] at hn
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hn
    have hs : ∑ i ∈ Finset.range n, ((l : ℕ) : A) ^ i * x.coeff i ^ l ^ (n - i) =
        ∑ i ∈ Finset.range n, ((l : ℕ) : A) ^ i * y.coeff i ^ l ^ (n - i) :=
      Finset.sum_congr rfl (fun i hi => by rw [ih i (Finset.mem_range.1 hi)])
    rw [hs, add_left_cancel_iff, Nat.sub_self, pow_zero, pow_one, pow_one] at hn
    apply sub_eq_zero.1
    apply hpow n
    rw [mul_sub, hn, sub_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisTer
section
namespace GlobalTheory.SingleStatement

theorem main : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {ι : Type} (s : Finset ι) (g : ι → ℂ_[p]) {r : ℝ},
    (0 : ℝ) ≤ r → (∀ k ∈ s, ‖g k‖ ≤ r) → ‖∑ k ∈ s, g k‖ ≤ r := by
  intro p _ ι s g r hr hg
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ‖g a‖ ≤ r := hg a (Finset.mem_insert_self a s)
    have h2 : ‖∑ k ∈ s, g k‖ ≤ r := ih (fun k hk => hg k (Finset.mem_insert_of_mem hk))
    exact (PadicComplex.isNonarchimedean p (g a) (∑ k ∈ s, g k)).trans (max_le h1 h2)

end GlobalTheory.SingleStatement
end

