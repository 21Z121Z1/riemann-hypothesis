import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0010
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelLatticeBaseChange
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AdicCompleteAlgebraLiftingUniqueStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adic_complete_algebra_lifting_unique : ∀ (R A B : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Module.Finite R A] (I : Ideal R) [IsAdicComplete I R] (f : ∀ e : ℕ, B →ₐ[R] A ⧸ (I ^ (e + 1)).map (algebraMap R A)), (∀ e (b : B) (a : A), Ideal.Quotient.mk _ a = f (e + 1) b → Ideal.Quotient.mk _ a = f e b) → ∃! g : B →ₐ[R] A, ∀ e b, Ideal.Quotient.mk _ (g b) = f e b := by
  first | exact @GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique | exact GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique | (intros; apply GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField
open scoped nonZeroDivisors

section

variable (E : Type) [Field E] [NumberField E]

theorem mem_dual_one_iff_span_dualInt (y : E) :
    y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      y ∈ Submodule.span ℤ (Set.range (dualInt E)) := by
  classical
  have h := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 E) E) (integralBasis E) (by
    ext x
    rw [Submodule.restrictScalars_mem, mem_span_integralBasis, Submodule.mem_one]
    rfl)
  have h2 : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one]
  rw [h2, ← Submodule.restrictScalars_mem ℤ, h]
  have : (⇑(integralBasis E).traceDual) = dualInt E := by
    funext k
    unfold dualInt Module.Basis.traceDual
    congr!
  rw [this]

theorem different_mul_dual_one :
    ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀
    (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E)))]

theorem exists_different_mul_dualInt (x : 𝓞 E) (hx : x ∈ differentIdeal ℤ (𝓞 E))
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∃ z : 𝓞 E, (z : E) = (x : E) * dualInt E k := by
  have h1 : dualInt E k ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
    (mem_dual_one_iff_span_dualInt E _).2 (Submodule.subset_span ⟨k, rfl⟩)
  have h2 : (x : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :=
    FractionalIdeal.mem_coeIdeal_of_mem _ hx
  have h3 := FractionalIdeal.mul_mem_mul h2 h1
  rw [different_mul_dual_one, FractionalIdeal.mem_one_iff] at h3
  exact h3

end

theorem different_generator_dualInt :
    ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (E : Type) [Field E]
      [NumberField E] (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) →
      (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) →
      Submodule.span A {algebraMap A K d} =
        Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} →
      algebraMap A K d ≠ 0 ∧
        (∀ k, algebraMap A K d * σ (dualInt E k) ∈ (algebraMap A K).range) ∧
        ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A,
          ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
  intro A K _ _ _ _ E _ _ σ d _ hσ hd
  have key : ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A,
      ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
    set M : Submodule A K :=
      Submodule.span A (Set.range fun k => algebraMap A K d * σ (dualInt E k)) with hM
    have hy : ∀ y ∈ Submodule.span ℤ (Set.range (dualInt E)), algebraMap A K d * σ y ∈ M := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, mul_add]; exact M.add_mem ha hb
      | smul n a _ ha =>
        rw [map_zsmul, mul_smul_comm]
        exact zsmul_mem ha n
    have h1 : (1 : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [different_mul_dual_one]
      exact FractionalIdeal.one_mem_one _
    have h2 : σ 1 ∈ M := by
      refine FractionalIdeal.mul_induction_on (C := fun z => σ z ∈ M) h1 ?_ ?_
      · intro x hx y hy'
        obtain ⟨x, hx0, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
        have hx' : σ (x : E) ∈ Submodule.span A {algebraMap A K d} := by
          rw [hd]; exact Submodule.subset_span ⟨x, hx0, rfl⟩
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hx'
        change σ ((x : E) * y) ∈ M
        rw [map_mul, ← ha, smul_mul_assoc]
        exact M.smul_mem a (hy y ((mem_dual_one_iff_span_dualInt E y).1 hy'))
      · intro x y hx hy
        rw [map_add]; exact M.add_mem hx hy
    rw [map_one, hM, Submodule.mem_span_range_iff_exists_fun] at h2
    obtain ⟨u, hu⟩ := h2
    exact ⟨u, by simpa only [Algebra.smul_def] using hu⟩
  refine ⟨?_, ?_, key⟩
  · intro h0
    obtain ⟨u, hu⟩ := key
    simp [h0] at hu
  · intro k
    have hy : ∀ y ∈ Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)},
        y * σ (dualInt E k) ∈ (algebraMap A K).range := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        obtain ⟨z, hz⟩ := exists_different_mul_dualInt E x hx k
        rw [← map_mul, ← hz]
        exact hσ z
      | zero => simp
      | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
      | smul n a _ ha =>
        rw [smul_mul_assoc, Algebra.smul_def]
        exact mul_mem ⟨n, rfl⟩ ha
    exact hy _ (hd ▸ Submodule.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualFamilyIsBasis
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg

theorem linearIndependent_span_of_dual_unit :
    ∀ (V : Type) [CommRing V] (L : Type) [AddCommGroup L] [Module V L] (n : ℕ)
      (b : Module.Basis (Fin n) V L) (u : Fin n → L) (f : Fin n → (L →ₗ[V] V)) (N : V),
      IsUnit N → (∀ i j, f j (u i) = if i = j then N else 0) →
      LinearIndependent V u ∧ Submodule.span V (Set.range u) = ⊤ := by
  intro V _ L _ _ n b u f N hN hf
  classical

  let U : Matrix (Fin n) (Fin n) V := Matrix.of fun i k => b.repr (u i) k
  let F : Matrix (Fin n) (Fin n) V := Matrix.of fun k j => f j (b k)
  have hUF : U * F = N • (1 : Matrix (Fin n) (Fin n) V) := by
    ext i j
    have h1 : f j (u i) = ∑ k, b.repr (u i) k * f j (b k) := by
      calc f j (u i) = f j (∑ k, b.repr (u i) k • b k) := by rw [b.sum_repr]
        _ = ∑ k, b.repr (u i) k * f j (b k) := by
          simp only [map_sum, map_smul, smul_eq_mul]
    simp only [Matrix.mul_apply, U, F, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [← h1, hf]
    split_ifs <;> simp
  have hdet : IsUnit U.det := by
    have h2 : U.det * F.det = N ^ n := by
      rw [← Matrix.det_mul, hUF, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact isUnit_of_mul_isUnit_left (h2 ▸ hN.pow n)
  have hb : b.toMatrix u = U.transpose := by
    ext k i
    simp [Module.Basis.toMatrix_apply, U]
  have hdet' : IsUnit (b.toMatrix u).det := by
    rw [hb, Matrix.det_transpose]; exact hdet
  have hdet2 : IsUnit (b.det u) := by
    rw [Module.Basis.det_apply]; exact hdet'
  exact (Module.Basis.is_basis_iff_det b).mpr hdet2

end GlobalTheory.CompanionTheory.CommAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeCoordinateGeneratorStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_coordinate_generator : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (n : ℕ) (L : AddSubgroup (Fin n → Ω)), LocFree R n L → (∀ i, Summand L (annSub Ω n i)) → ∀ (i : Fin n) (u : Ω), u ≠ 0 → (∀ c, c ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i) ↔ ∃ a ∈ R, c = a * u) → ∀ t : Ω, (∃ v ∈ dotDual R L, (∀ j, i < j → v j = 0) ∧ v i = t) ↔ ∃ a ∈ R, t = a * u⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HhGraded.main | exact GlobalTheory.CompanionTheory.Ar.Num.HhGraded.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HhGraded.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNeg
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegDual

open GlobalTheory.CompanionTheory.Ar.Crv Module

variable {K : Type} [Field K] (C : ACurve K)
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

theorem isLatOf_dual (L : C.I → AddSubgroup V) (B : V →ₗ[K] V' →ₗ[K] K) (i : C.I) {n : ℕ}
    (b : Basis (Fin n) K V) (b' : Basis (Fin n) K V')
    (hb : ∀ y q, b'.repr y q = B (b q) y) (h : IsLatOf C i b (L i)) :
    IsLatOf C i b' (dualLat C L B i) := by
  intro y
  change (∀ x ∈ L i, C.v i (B x y) ≤ 1) ↔ _
  constructor
  · intro hy q
    rw [hb]
    refine hy _ ((h _).2 fun p => ?_)
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  · intro hy x hx
    have hx' := (h x).1 hx
    rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
    refine (C.v i).map_sum_le fun q _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, ← hb]
    exact mul_le_one' (hx' q) (hy q)

theorem dual_symm (B : V →ₗ[K] V' →ₗ[K] K) {n : ℕ}
    (b : Basis (Fin n) K V) (b' : Basis (Fin n) K V')
    (hb : ∀ y q, b'.repr y q = B (b q) y) (x : V) (q : Fin n) :
    b.repr x q = B.flip (b' q) x := by
  have : b.coord q = B.flip (b' q) := by
    refine b.ext fun p => ?_
    rw [LinearMap.flip_apply, ← hb, Basis.coord_apply, Basis.repr_self, Basis.repr_self,
      Finsupp.single_apply, Finsupp.single_apply]
    simp [eq_comm]
  rw [← this, Basis.coord_apply]

theorem exists_dual [FiniteDimensional K V] [FiniteDimensional K V'] (B : V →ₗ[K] V' →ₗ[K] K)
    (hB : Function.Bijective B) {n : ℕ} (b : Basis (Fin n) K V) :
    ∃ b' : Basis (Fin n) K V', ∀ y q, b'.repr y q = B (b q) y := by
  have hf : Function.Bijective B.flip := (LinearMap.flip_bijective_iff₁).2 hB
  refine ⟨b.dualBasis.map (LinearEquiv.ofBijective B.flip hf).symm, fun y q => ?_⟩
  simp

theorem det_dual (B : V →ₗ[K] V' →ₗ[K] K) {n : ℕ}
    (b₀ b : Basis (Fin n) K V) (b₀' b' : Basis (Fin n) K V')
    (h₀ : ∀ y q, b₀'.repr y q = B (b₀ q) y) (hb : ∀ y q, b'.repr y q = B (b q) y) :
    b₀'.det b' = (b₀.det b)⁻¹ := by
  have h1 : b₀'.toMatrix b' = (b.toMatrix b₀).transpose := by
    ext p q
    rw [Matrix.transpose_apply, Basis.toMatrix_apply, Basis.toMatrix_apply, h₀,
      dual_symm B b b' hb, LinearMap.flip_apply]
  have h2 : (b.toMatrix b₀).det * (b₀.toMatrix b).det = 1 := by
    rw [← Matrix.det_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  rw [Basis.det_apply, Basis.det_apply, h1, Matrix.det_transpose]
  exact eq_inv_of_mul_eq_one_left h2

theorem isLatOf_reindex (i : C.I) {n m : ℕ} (b : Basis (Fin n) K V) (e : Fin n ≃ Fin m)
    (L : AddSubgroup V) (h : IsLatOf C i b L) : IsLatOf C i (b.reindex e) L := by
  intro x
  rw [h x]
  simp only [Basis.repr_reindex_apply]
  exact ⟨fun H q => H _, fun H q => by simpa using H (e q)⟩

theorem deg_dual : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (L : C.I → AddSubgroup V) (B : V →ₗ[K] V' →ₗ[K] K), IsBun C L → Function.Bijective B →
    IsBun C (dualLat C L B) ∧ deg C (dualLat C L B) = - deg C L ∧
      dualLat C (dualLat C L B) B.flip = L := by
  intro K _ C V _ _ _ V' _ _ _ L B hL hB
  obtain ⟨hloc, b₀, hfin⟩ := id hL
  choose b hb using hloc
  choose d hd using fun c : Basis (Fin (finrank K V)) K V => exists_dual B hB c
  have hrk : finrank K V = finrank K V' := by
    rw [finrank_eq_card_basis (d b₀), Fintype.card_fin]
  have hd' : ∀ i, IsLatOf C i (d (b i)) (dualLat C L B i) := fun i =>
    isLatOf_dual C L B i (b i) _ (hd _) (hb i)
  have hbun : IsBun C (dualLat C L B) := by
    refine ⟨fun i => ⟨_, isLatOf_reindex C i _ (finCongr hrk) _ (hd' i)⟩,
      (d b₀).reindex (finCongr hrk), hfin.subset fun i hi h => hi ?_⟩
    exact isLatOf_reindex C i _ _ _ (isLatOf_dual C L B i b₀ _ (hd _) h)
  refine ⟨hbun, ?_, ?_⟩
  · rw [(GlobalTheory.T.bundle_degree_eq_sum_valuations K C V' _ _ (d b₀) (fun i => d (b i)) hbun hd').2,
      (GlobalTheory.T.bundle_degree_eq_sum_valuations K C V _ _ b₀ b hL hb).2, ← finsum_neg_distrib]
    refine finsum_congr fun i => ?_
    rw [det_dual B b₀ (b i) _ _ (hd _) (hd _), map_inv₀, WithZero.log_inv, mul_neg]
  · funext i
    ext x
    rw [hb i x]
    exact isLatOf_dual C _ B.flip i (d (b i)) (b i) (dual_symm B _ _ (hd _)) (hd' i) x

end GlobalTheory.CompanionTheory.Ar.Crv.DegDual
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsDiffGenerator
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

theorem diffGen_v_le_one {C : Type} [Field C] (v : Valuation C NNReal)
    {E : Type} [Field E] [NumberField E] (σ : E →+* C) (a : 𝓞 E) : v (σ (a : E)) ≤ 1 := by
  have h1 : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have h2 : IsIntegral v.integer (σ (a : E)) := h1.tower_top
  exact (Valuation.integer.integers v).mem_of_integral h2

theorem diffGen_exists_max {C : Type} [Field C] (v : Valuation C NNReal)
    {E : Type} [Field E] [NumberField E] (σ : E →+* C) (D : Ideal (𝓞 E)) :
    ∃ x₀ ∈ D, ∀ x ∈ D, v (σ ((x : 𝓞 E) : E)) ≤ v (σ ((x₀ : 𝓞 E) : E)) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian D : D.FG)
  rcases s.eq_empty_or_nonempty with h | h
  · refine ⟨0, D.zero_mem, fun x hx => ?_⟩
    rw [← hs, h, Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hx
    simp [hx]
  · obtain ⟨x₀, hx₀s, hmax⟩ := s.exists_max_image (fun g : 𝓞 E => v (σ (g : E))) h
    refine ⟨x₀, ?_, fun x hx => ?_⟩
    · rw [← hs]
      exact Submodule.subset_span hx₀s
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hmax y hy
    | zero => simp
    | add y z _ _ hy hz =>
      calc v (σ ((y + z : 𝓞 E) : E)) = v (σ (y : E) + σ (z : E)) := by simp
        _ ≤ max (v (σ (y : E))) (v (σ (z : E))) := v.map_add _ _
        _ ≤ _ := max_le hy hz
    | smul r y _ hy =>
      calc v (σ ((r • y : 𝓞 E) : E)) = v (σ (r : E)) * v (σ (y : E)) := by simp [smul_eq_mul]
        _ ≤ 1 * v (σ (x₀ : E)) := mul_le_mul' (diffGen_v_le_one v σ r) hy
        _ = _ := one_mul _

theorem exists_diff_generator (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (hv : v.Integers O) [CharZero C] (E : Type) [Field E] [NumberField E]
    (σ : E →+* C) :
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O C).range) ∧
      ∃ d : O, algebraMap O C d ≠ 0 ∧ v (algebraMap O C d) = diffAbs v σ ∧
        Submodule.span O {algebraMap O C d} =
          Submodule.span O {y : C | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} := by
  have hint : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O C).range := by
    intro a
    have h1 : IsIntegral ℤ (σ (a : E)) := (a.isIntegral_coe).map σ.toIntAlgHom
    have h3 : σ (a : E) ∈ v.integer := hv.mem_of_integral (h1.tower_top (A := O))
    exact RingHom.mem_range.2 (hv.exists_of_le_one ((Valuation.mem_integer_iff v _).1 h3))
  refine ⟨hint, ?_⟩
  obtain ⟨x₀, hx₀, hmax⟩ := diffGen_exists_max v σ (differentIdeal ℤ (𝓞 E))
  obtain ⟨d, hd⟩ := RingHom.mem_range.1 (hint x₀)
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hσz : σ (z : E) ≠ 0 := (map_ne_zero σ).2 (by simpa using hz0)
  have hx0ne : σ (x₀ : E) ≠ 0 := by
    intro h
    have hle := hmax z hz
    rw [h, map_zero] at hle
    exact (v.ne_zero_iff.2 hσz) (le_antisymm hle zero_le)
  refine ⟨d, by rw [hd]; exact hx0ne, ?_, ?_⟩
  · rw [hd, diffAbs]
    apply le_antisymm
    · exact le_ciSup (f := fun x : differentIdeal ℤ (𝓞 E) => v (σ ((x : 𝓞 E) : E)))
        ⟨v (σ (x₀ : E)), by rintro _ ⟨x, rfl⟩; exact hmax x x.2⟩ ⟨x₀, hx₀⟩
    · exact ciSup_le fun x => hmax x x.2
  · rw [hd]
    apply le_antisymm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨x₀, hx₀, rfl⟩
    · rw [Submodule.span_le]
      rintro y ⟨x, hx, rfl⟩
      have hle : v (σ (x : E) / σ (x₀ : E)) ≤ 1 := by
        rw [map_div₀]
        exact div_le_one_of_le₀ (hmax x hx) zero_le
      obtain ⟨c, hc⟩ := hv.exists_of_le_one hle
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      rw [Algebra.smul_def, hc, div_mul_cancel₀ _ hx0ne]

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHenselianFlatOverPrimeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_henselian_flat_over_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : HenselianLocalRing R') (_ : Algebra R R'), IsIntegrallyClosed R' ∧ Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime | exact GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime | (intros; apply GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FgInfRestrictScalarsOfIntegers
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem fg_inf_restrictScalars_of_integers (C : Type) [Field C] (v : Valuation C NNReal) (O : Type)
    [CommRing O] [Algebra O C] (hv : v.Integers O) (V : Type) [AddCommGroup V] [Module C V]
    [Module O V] [IsScalarTower O C V] (L : Submodule O V) (U : Submodule C V) (hL : L.FG) :
    (L ⊓ U.restrictScalars O).FG := by
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := hinj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  let f : L →ₗ[O] (V ⧸ U) := (U.mkQ.restrictScalars O).comp L.subtype
  haveI : Module.Finite O L := Module.Finite.iff_fg.2 hL
  haveI : Module.Finite O (LinearMap.range f) := inferInstance
  haveI : Module.Flat O (LinearMap.range f) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro ⟨x, hx⟩ ⟨⟨a, ha⟩, h⟩
    have h1 : a • x = 0 := congrArg Subtype.val h
    have ha0 : algebraMap O C a ≠ 0 := by
      intro h0
      exact nonZeroDivisors.ne_zero ha (hinj (by simpa using h0))
    rw [← algebraMap_smul C a x] at h1
    have : x = 0 := (smul_eq_zero.1 h1).resolve_left ha0
    simp [this]
  haveI : Module.Free O (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict LinearMap.id
    f.surjective_rangeRestrict
  let p : L →ₗ[O] V := L.subtype.comp (LinearMap.id - s.comp f.rangeRestrict)
  have key : L ⊓ U.restrictScalars O = LinearMap.range p := by
    apply le_antisymm
    · rintro x ⟨hxL, hxU⟩
      refine ⟨⟨x, hxL⟩, ?_⟩
      have : f.rangeRestrict ⟨x, hxL⟩ = 0 := by
        apply Subtype.ext
        change U.mkQ x = 0
        exact (Submodule.Quotient.mk_eq_zero U).2 hxU
      simp [p, this]
    · rintro _ ⟨y, rfl⟩
      refine ⟨(y - s (f.rangeRestrict y)).2, ?_⟩
      have h2 : f.rangeRestrict (s (f.rangeRestrict y)) = f.rangeRestrict y :=
        LinearMap.congr_fun hs _
      have h3 : f (y - s (f.rangeRestrict y)) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact (congrArg Subtype.val h2).symm
      exact (Submodule.Quotient.mk_eq_zero U).1 h3
  rw [key]
  exact Module.Finite.iff_fg.1 inferInstance

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussSumValuationTeichmullerStatement
section
open scoped Matrix TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_sum_valuation_teichmuller : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → Fintype.card F ≠ 2 → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → ∀ ψ : AddChar F C, ψ ≠ 1 → v (∑ a, algebraMap R C (σ⁻¹ a) * ψ a) ^ (p - 1) = v (p : C) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.gauss_value | exact GlobalTheory.CompanionTheory.Ar.GR.gauss_value | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.gauss_value <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelGraphBaseChangeHolds
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem kernel_graph_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (∀ i, (D.bc RC).kk τ i = spanOver RC (bcMap Ω C _ '' D.kk τ i)) ∧ ∀ i, (D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (Prod.map (algebraMap Ω C) (bcMap Ω C _) '' D.stepGraph τ (χ τ) i) :=
  @PositivityTheory.Xgn.kernel_lattice_base_change

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelRankBoundNormValuationStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_free_basis_of_kernel_rank_le_norm_valuation : ∀ (E : Type) [Field E] [NumberField E] (k W : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (r : ℕ) (ρ : 𝓞 E →+* Module.End k W), (∀ a : 𝓞 E, (ρ a).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r) → (∀ a : 𝓞 E, a ≠ 0 → Module.finrank k (LinearMap.ker (ρ a)) ≤ r * padicValNat p (Algebra.norm ℤ a).natAbs) → ∃ x : Fin r → W, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lemF_algebra | exact GlobalTheory.CompanionTheory.Ar.Flat.lemF_algebra | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lemF_algebra <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeQuotient
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.GraphRestrict

theorem main : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] {Z Zc : Type} [AddCommGroup Z] [Module Ω Z] [AddCommGroup Zc] [Module C Zc] [Module Ω Zc] [IsScalarTower Ω C Zc] (b : V →ₗ[Ω] Vc) (b' : Z →ₗ[Ω] Zc), IsBaseChange C b → IsBaseChange C b' → ∀ (Δ : AddSubgroup (V × Z)) (H : AddSubgroup V) (N : ℕ), (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → LocFree R N (Δ.map (AddMonoidHom.fst V Z)) → H ≤ Δ.map (AddMonoidHom.fst V Z) → (∀ a ∈ R, ∀ v ∈ H, a • v ∈ H) → spanOver RC (Prod.map b b' '' Δ) ⊓ (spanOver RC (b '' H)).prod ⊤ = spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) ∧ (spanOver RC (Prod.map b b' '' Δ)).comap (AddMonoidHom.inr Vc Zc) = spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)) :=
  @PositivityTheory.Xgn.t_graph_restrict_bc

end GlobalTheory.CompanionTheory.Ar.GraphRestrict
end

