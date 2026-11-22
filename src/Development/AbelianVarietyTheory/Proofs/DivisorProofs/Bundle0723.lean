import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationCoeffEqZeroOfDegreeLtStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDerivation_coeff_eq_zero_of_degree_lt : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R) (r : ℕ), (∀ α : Fin d →₀ ℕ, α.degree < r + 1 → coeff α F = 0) → ∀ α : Fin d →₀ ℕ, α.degree < r → coeff α (invDer μ u F) = 0 := by
  first | exact @GlobalTheory.invDer_coeff_eq_zero_of_degree_lt | exact GlobalTheory.invDer_coeff_eq_zero_of_degree_lt | (intros; apply GlobalTheory.invDer_coeff_eq_zero_of_degree_lt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCast
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.FinProjComplete

theorem mem_span_pow_smul_top_iff (p : ℕ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (x : M) :
    x ∈ (Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R M) ↔ ∃ m : M, x = (p ^ n : ℕ) • m := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨m, -, rfl⟩
    exact ⟨m, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, Submodule.mem_top, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩

theorem smodEq_iff (p : ℕ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (x y : M) :
    x ≡ y [SMOD ((Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R M))] ↔
      ∃ m : M, x - y = (p ^ n : ℕ) • m := by
  rw [SModEq.sub_mem, mem_span_pow_smul_top_iff]

end GlobalTheory.FinProjComplete

open GlobalTheory.FinProjComplete in
theorem GlobalTheory.FinProjComplete.isAdicComplete_span_natCast : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  intro p O A _ _ _ _ _ hO
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' O A
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π (LinearMap.id) hπ
  have hπs : ∀ a, π (s a) = a := fun a => by simpa using LinearMap.congr_fun hs a
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hc : ∀ i, s x i = 0 := by
      intro i
      apply hO.toIsHausdorff.haus'
      intro n
      obtain ⟨m, hm⟩ := (smodEq_iff p n x 0).1 (hx n)
      rw [smodEq_iff]
      refine ⟨s m i, ?_⟩
      rw [sub_zero] at hm ⊢
      rw [hm, map_nsmul, Pi.smul_apply]
    have : s x = 0 := funext hc
    rw [← hπs x, this, map_zero]
  · intro f hf
    have hcoord : ∀ i, ∃ L : O, ∀ n, s (f n) i ≡ L [SMOD ((Ideal.span {(p : O)}) ^ n • (⊤ : Submodule O O))] := by
      intro i
      apply hO.toIsPrecomplete.prec'
      intro m n hmn
      obtain ⟨c, hc⟩ := (smodEq_iff p m (f m) (f n)).1 (hf hmn)
      rw [smodEq_iff]
      refine ⟨s c i, ?_⟩
      rw [← Pi.sub_apply, ← map_sub, hc, map_nsmul, Pi.smul_apply]
    choose L hL using hcoord
    refine ⟨π L, fun n => ?_⟩
    have hd : ∀ i, ∃ c : O, s (f n) i - L i = (p ^ n : ℕ) • c := fun i => (smodEq_iff p n _ _).1 (hL i n)
    choose c hc using hd
    rw [smodEq_iff]
    refine ⟨π c, ?_⟩
    have hv : s (f n) - L = (p ^ n : ℕ) • c := funext fun i => by simpa using hc i
    rw [← map_nsmul, ← hv, map_sub, hπs]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCrystallineChernOnAnalyticThickenings
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isChern_real : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X) (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ z : SecondDeRham s, IsChern (dp0 B) s M z → ∃ (i : K.Obj → M.ι) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) ∧ (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) ∧ (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ ((show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) ∧ r.coef.pull2 z = GlobalTheory.CatCoh.H2.mk K.Oc ℓ := by
  intro I _ g Λ _ F B _ X s σ K r M j hj z hz
  obtain ⟨i₀, hi₀, u₀, ℓ₀, h1, h2, h3⟩ := hz
  let G : K.Obj ⥤ (IsSmall (dp0 B) s M.U).FullSubcategory :=
    ObjectProperty.lift _ r.functor fun T ↦ ⟨j T.k, fun p _ ↦ hj T.k (Set.mem_univ _)⟩
  let n : GlobalTheory.CatCoh.CoefMap σ ((IsSmall (dp0 B) s M.U).ι ⋙ O (dp0 B) s) K.Oc :=
    { G := G
      α := fun T ↦ RingHom.id T.C
      naturality := fun _ _ ↦ rfl
      smul := fun T b c ↦ r.coef.smul T b c }
  refine ⟨fun T ↦ i₀ (G.obj T), fun T T' φ ↦ u₀ _ _ (G.map φ), n.pullbackTwoCocycle ℓ₀, fun T ↦ hi₀ (G.obj T),
    fun T T' φ _ ↦ h1 _ _ (G.map φ), fun T T' T'' φ ψ ↦ ?_, ?_⟩
  · have h := h2 _ _ _ (G.map φ) (G.map ψ)
    rw [← G.map_comp] at h
    exact h
  · rw [← n.pullCohomologyTwo_class, ← h3]
    obtain ⟨z, rfl⟩ := GlobalTheory.CatCoh.H2.mk_surjective _ z
    rfl

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormalGroupLawHomFormalGroupLawNatMultiple
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.NMulHom

theorem isHom_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ n, IsHom μ μ (nmul μ n) :=
  GlobalTheory.NMulEndo.isHom_nmul

end GlobalTheory.NMulHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomNmulOfIsLawStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHom_nmul_of_isLaw : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ k : ℕ, IsHom μ μ (nmul μ k) := by
  first | exact @GlobalTheory.NMulEndo.isHom_nmul | exact GlobalTheory.NMulEndo.isHom_nmul | (intros; apply GlobalTheory.NMulEndo.isHom_nmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionNonrealMultiplier
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.LatTorsVal

theorem exists_tors {L : PeriodPair} {c : ℂ} {τ : ℍ} (hτ : IsTauOf L c τ) (M : ℕ) [NeZero M] (P : ℂ)
    (hP : (M : ℂ) * P ∈ L.lattice) :
    ∃ x : Fin 2 → ZMod M, P - c * tors M τ x ∈ L.lattice ∧ (P ∉ L.lattice → x ≠ 0) := by
  have hom := GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf L c τ hτ
  have tm := GlobalTheory.WpFam.TorsMem.main M τ
  have hc : c ≠ 0 := hτ.1
  have hPz : P = c * (P / c) := by field_simp
  have hMz : (M : ℂ) * (P / c) ∈ (tauPair τ).lattice := by
    rw [← hom.1]
    have : c * ((M : ℂ) * (P / c)) = (M : ℂ) * P := by rw [hPz]; field_simp
    rw [this]; exact hP
  obtain ⟨x, hx⟩ := tm.2.2.2.2 (P / c) hMz
  refine ⟨x, ?_, ?_⟩
  · have := (hom.1 _).2 hx
    rwa [mul_sub, ← hPz] at this
  · rintro hPL rfl
    apply hPL
    have h0 := (tm.2.2.1 0).2 rfl
    have : P / c ∈ (tauPair τ).lattice := by
      have := add_mem hx h0
      simpa using this
    rw [hPz]; exact (hom.1 _).2 this

theorem wp_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (M : ℕ) (P : ℂ) (x : Fin 2 → ZMod M)
    (h : P - c * tors M τ x ∈ L.lattice) :
    L.weierstrassP P = L.weierstrassP (c * tors M τ x) ∧
      L.derivWeierstrassP P = L.derivWeierstrassP (c * tors M τ x) := by
  have e : P = c * tors M τ x + ((⟨P - c * tors M τ x, h⟩ : L.lattice) : ℂ) := by simp
  constructor
  · rw [e, L.weierstrassP_add_coe]
  · rw [e, L.derivWeierstrassP_add_coe]

theorem main : ∀ (L : PeriodPair) (β Ω : ℂ) (M : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → 0 < M → (∀ P, (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (12 * (M : ℂ) ^ 2 * L.weierstrassP P / Ω ^ 2) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * L.derivWeierstrassP P / Ω ^ 3)) ∧ ∀ P Q, P ∉ L.lattice → Q ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → (M : ℂ) * Q ∈ L.lattice → IsIntegral ℤ ((M : ℂ) ^ 2 * (L.weierstrassP P - L.weierstrassP Q) / Ω ^ 2) := by
  intro L β Ω M hβ hβi hΩ hM
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hj := GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication L c τ β hτ hβ hβi
  have hω := (GlobalTheory.QFam.jT_eq_and_pow_twelve_eq_DD L c τ hτ).2 Ω hΩ
  have st := (GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau L c Ω τ hτ).2 M
  refine ⟨fun P hP => ?_, fun P Q hP hQ hMP hMQ => ?_⟩
  · obtain ⟨x, hx, -⟩ := exists_tors hτ M P hP
    obtain ⟨e1, e2⟩ := wp_eq M P x hx
    have hv := GlobalTheory.T.isIntegral_weierstrassP_torsion_integral_j M τ _ hj hω x
    rw [e1, e2, mul_div_assoc, mul_div_assoc, ← (st x).1, ← (st x).2, ← mul_div_assoc, ← mul_div_assoc]
    exact hv
  · obtain ⟨x, hx, hx0⟩ := exists_tors hτ M P hMP
    obtain ⟨y, hy, hy0⟩ := exists_tors hτ M Q hMQ
    have hv := GlobalTheory.T.isIntegral_weierstrassP_torsion_difference M τ _ hj hω x y (hx0 hP) (hy0 hQ)
    rw [(wp_eq M P x hx).1, (wp_eq M Q y hy).1, mul_div_assoc, sub_div, ← (st x).1, ← (st y).1, ← sub_div,
      ← mul_div_assoc]
    exact hv

end GlobalTheory.WpFam.LatTorsVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNarrowRayClassLFunctionMulPrimeWideIndicator
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory

theorem isRayL_mul_prime_wideInd {F : Type} [Field F] [NumberField F] (𝔪 𝔭 : Ideal (𝓞 F)) (hmax : 𝔭.IsMaximal) (hp : 𝔭 ≠ ⊥)
    (hpm : 𝔭 ⊔ 𝔪 = ⊤) (C : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ) (hZ : IsRayL 𝔪 (wideInd C) Z)
    (hZ' : IsRayL 𝔪 (wideInd (C * (cls 𝔭)⁻¹)) Z') :
    IsRayL (𝔪 * 𝔭) (wideInd C) (fun s => Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
  have hN : ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hp)
  refine ⟨?_, ?_⟩
  · refine hZ.1.sub (DifferentiableOn.mul (fun s _ => ?_) hZ'.1)
    exact ((differentiableAt_id.neg).const_cpow (Or.inl hN)).differentiableWithinAt
  intro s hs
  classical
  set S : Set (Ideal (𝓞 F)) := {I | CoprimeTo F 𝔪 I} with hSdef
  set A : Set (Ideal (𝓞 F)) := {I | CoprimeTo F (𝔪 * 𝔭) I} with hAdef
  set B : Set (Ideal (𝓞 F)) := {I | CoprimeTo F 𝔪 I ∧ ¬ CoprimeTo F (𝔪 * 𝔭) I} with hBdef
  let g : ClassGroup (𝓞 F) → Ideal (𝓞 F) → ℂ := fun D I => (wideInd D I : ℂ) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)
  have h1 : HasSum (S.indicator (g C)) (Z s) := (hasSum_subtype_iff_indicator (s := S)).mp (hZ.2 s hs)
  have h2 : HasSum (S.indicator (g (C * (cls 𝔭)⁻¹))) (Z' s) :=
    (hasSum_subtype_iff_indicator (s := S)).mp (hZ'.2 s hs)
  have hAS : ∀ I, CoprimeTo F (𝔪 * 𝔭) I → CoprimeTo F 𝔪 I := fun I h =>
    ⟨h.1, eq_top_iff.mpr (h.2.symm.le.trans (sup_le_sup_left Ideal.mul_le_left _))⟩
  have hsplit : S.indicator (g C) = A.indicator (g C) + B.indicator (g C) := by
    funext I
    simp only [Pi.add_apply, Set.indicator, hSdef, hAdef, hBdef, Set.mem_setOf_eq]
    by_cases hA : CoprimeTo F (𝔪 * 𝔭) I
    · simp [hA, hAS I hA]
    · by_cases hS : CoprimeTo F 𝔪 I <;> simp [hA, hS]

  have hmulS : ∀ J, CoprimeTo F 𝔪 J → 𝔭 * J ∈ B := by
    intro J hJ
    refine ⟨⟨mul_ne_zero hp hJ.1, ?_⟩, fun h => ?_⟩
    · rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by rwa [sup_comm]), sup_comm]; exact hJ.2
    · have : 𝔭 * J ⊔ 𝔭 = 𝔭 := sup_eq_right.mpr Ideal.mul_le_left
      have htop : 𝔭 * J ⊔ 𝔭 = ⊤ := eq_top_iff.mpr (h.2.symm.le.trans (sup_le_sup_left Ideal.mul_le_right _))
      exact hmax.ne_top (this.symm.trans htop)
  have hnot : ∀ J, ¬ CoprimeTo F 𝔪 J → 𝔭 * J ∉ B := by
    intro J hJ hB
    apply hJ
    refine ⟨fun h0 => hB.1.1 (by simp [h0]), eq_top_iff.mpr (hB.1.2.symm.le.trans (sup_le_sup_right Ideal.mul_le_right _))⟩
  have hB_range : ∀ I ∈ B, ∃ J, 𝔭 * J = I := by
    intro I hI
    have hItop : I ⊔ 𝔭 ≠ ⊤ := by
      intro h
      apply hI.2
      refine ⟨hI.1.1, ?_⟩
      rw [Ideal.sup_mul_eq_of_coprime_right h]; exact hI.1.2
    have hle : I ≤ 𝔭 := le_sup_left.trans (hmax.eq_of_le hItop le_sup_right).ge
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
    exact ⟨J, hJ.symm⟩
  have hinj : Function.Injective (fun J : Ideal (𝓞 F) => 𝔭 * J) := fun J J' h => mul_left_cancel₀ hp h
  have hcomp : (B.indicator (g C)) ∘ (fun J => 𝔭 * J) =
      fun J => ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * S.indicator (g (C * (cls 𝔭)⁻¹)) J := by
    funext J
    simp only [Function.comp_apply]
    by_cases hJ : CoprimeTo F 𝔪 J
    · rw [Set.indicator_of_mem (hmulS J hJ), Set.indicator_of_mem (show J ∈ S from hJ)]
      simp only [g, wideInd]
      rw [cls_mul hp hJ.1, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      have : (cls 𝔭 * cls J = C) ↔ (cls J = C * (cls 𝔭)⁻¹) := by
        rw [eq_mul_inv_iff_mul_eq, mul_comm]
      by_cases hc : cls J = C * (cls 𝔭)⁻¹
      · simp [hc, this.mpr hc]
      · simp [hc, mt this.mp hc]
    · rw [Set.indicator_of_notMem (hnot J hJ), Set.indicator_of_notMem (show J ∉ S from hJ), mul_zero]
  have h3 : HasSum (B.indicator (g C)) (((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
    rw [← hinj.hasSum_iff (fun I hI => ?_), hcomp]
    · exact h2.mul_left _
    · by_contra hne
      obtain ⟨J, rfl⟩ := hB_range I (Set.mem_of_indicator_ne_zero hne)
      exact hI ⟨J, rfl⟩
  have h4 : HasSum (A.indicator (g C)) (Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
    have := h1.sub h3
    rw [hsplit] at this
    have e : (fun b => (A.indicator (g C) + B.indicator (g C)) b - B.indicator (g C) b) = A.indicator (g C) := by
      funext I; simp
    rwa [e] at this
  exact (hasSum_subtype_iff_indicator (s := A)).mpr h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNarrowRayClassLFunctionTopWideIndicatorIff
section
noncomputable section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.ZetaDenom

theorem isRayL_top_wideInd_iff : ∀ {F : Type} [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ),
    IsRayL (⊤ : Ideal (𝓞 F)) (wideInd C) Z ↔ IsClassZeta C Z := by
  intro F _ _ C Z
  refine and_congr_right fun _ => forall₂_congr fun s _ => ?_
  let g : IdealsIn C → {I : Ideal (𝓞 F) // CoprimeTo F ⊤ I} :=
    fun I => ⟨I.1.1, nonZeroDivisors.coe_ne_zero I.1, sup_top_eq _⟩
  have hg : Function.Injective g := fun I J h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : {I : Ideal (𝓞 F) // CoprimeTo F ⊤ I} => x.1) h))
  rw [← hg.hasSum_iff (f := fun I : {I : Ideal (𝓞 F) // CoprimeTo F ⊤ I} =>
    (wideInd C I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) fun I hI => by
      have : cls I.1 ≠ C := fun h => hI ⟨⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2.1⟩,
        by rw [← h, cls_of_ne_bot I.2.1]⟩, rfl⟩
      simp [wideInd, this]]
  refine iff_of_eq (congrArg (HasSum · (Z s)) (funext fun I => ?_))
  have h1 : cls (I.1 : Ideal (𝓞 F)) = C := by
    rw [cls_of_ne_bot (nonZeroDivisors.coe_ne_zero I.1)]
    exact I.2
  simp [g, wideInd, h1]

end GlobalTheory.ZetaDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentBlockFrobeniusXiAinfOfFrameBlockPStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_blockFrobeniusXi_ainf_of_frameBlockP : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V * blk d k (WittVector.frobenius (xi ε)) 1) := by
  first | exact @GlobalTheory.WinLift.isNil_V_blk_frob_xi | exact GlobalTheory.WinLift.isNil_V_blk_frob_xi | (intros; apply GlobalTheory.WinLift.isNil_V_blk_frob_xi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentInvTransposeBlockFrobeniusAinfOfFrameStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_invTranspose_blockFrobenius_ainf_of_frameNil : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), IsUnit U → IsUnit V → (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε))) := by
  first | exact @GlobalTheory.WinLift.NilF.isNil_frob | exact GlobalTheory.WinLift.NilF.isNil_frob | (intros; apply GlobalTheory.WinLift.NilF.isNil_frob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfNilpotentDividedPowersIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem isNilpotent_of_isDPNilpotent : ∀ {D : Type} [CommRing D] [Algebra ℂ D] {J : Ideal D}
    (dl : DividedPowers J), IsNilDP dl → IsNilpotent J := by
  intro D _ _ J dl hdl
  obtain ⟨N, h⟩ := hdl
  have h0 : ∀ l : List D, (∀ b ∈ l, b ∈ J) → N ≤ l.length → l.prod = 0 := by
    intro l hl hN
    have k := h (l.map fun b ↦ (1, b)) (by simpa using hl)
      (by simpa [List.map_map, Function.comp_def] using hN)
    rw [List.map_map] at k
    have e : l.map ((fun p : ℕ × D ↦ dl.dpow p.1 p.2) ∘ fun b ↦ (1, b)) = l.map id :=
      List.map_congr_left fun b hb ↦ dl.dpow_one (hl b hb)
    rwa [e, List.map_id] at k
  have key : ∀ n : ℕ, ∀ x ∈ J ^ n, ∀ l : List D, (∀ b ∈ l, b ∈ J) →
      N ≤ n + l.length → x * l.prod = 0 := by
    intro n
    induction n with
    | zero => intro x _ l hl hN; rw [h0 l hl (by simpa using hN), mul_zero]
    | succ n ih =>
      intro x hx l hl hN
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_)
        fun a b ha hb ↦ by rw [add_mul, ha, hb, add_zero]
      have := ih a ha (b :: l) (by simpa using ⟨hb, hl⟩) (by simp; omega)
      rwa [List.prod_cons, ← _root_.mul_assoc] at this
  refine ⟨N, eq_bot_iff.2 fun x hx ↦ ?_⟩
  simpa using key N x hx [] (by simp) (by simp)

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIdentityComponentsSmoothGroupScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.IdCompOpen

theorem isOpen_sectionComponents_of_family (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X)
    (hf : Smooth f) (he : e ≫ f = 𝟙 _) (O : X.Opens → Set X) (hO : ∀ U, IsOpen (O U))
    (h1 : ∀ (U : X.Opens) (y : X), e (f y) ∈ U →
      y ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → y ∈ O U)
    (h2 : ∀ (U : X.Opens) (y : X),
      (∀ z ∈ U, f z = f y → z ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}) →
      y ∈ O U → y ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  classical
  have hfe : ∀ t : S, f (e t) = t := fun t => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  refine GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_local_pieces X _ (GlobalTheory.T.stableUnderGeneralization_section_connectedComponentIn X S f e hf he) ?_
  intro x hx
  obtain ⟨U, V₀, V, I, hV, hs, hU, hI, hirr⟩ := GlobalTheory.T.exists_open_nbhd_section_fiber_isPreirreducible X S f e hf he (f x)
  refine ⟨⟨O U, hO U⟩ ⊓ f ⁻¹ᵁ (V₀ ⊓ e ⁻¹ᵁ U), f ⁻¹ᵁ V, I.image (fun c => f.app V c), ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact hV hy.2.1
  · exact ⟨h1 U x hU hx, hs, hU⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
    rw [← Scheme.preimage_basicOpen]
    exact hI d hd
  · intro y hy hJ
    have hpre := hirr (f y) hy.2.1 (fun c hc => by
      have := hJ _ (Finset.mem_image_of_mem _ hc)
      rw [← Scheme.preimage_basicOpen] at this
      exact this)
    refine h2 U y ?_ hy.1
    intro z hz hzy
    have hsub := hpre.isPreconnected.subset_connectedComponentIn
      (x := e (f y)) (F := f ⁻¹' {f y}) ⟨hy.2.2, hfe _⟩ Set.inter_subset_right
    show z ∈ connectedComponentIn (f ⁻¹' {f z}) (e (f z))
    rw [hzy]
    exact hsub ⟨hz, hzy⟩

theorem isOpen_identityComponent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → IsOpen {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G _ hG
  exact isOpen_sectionComponents_of_family G.left S G.hom (η[G]).left hG (Over.w (η[G]))
    (fun U => {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y})
    (GlobalTheory.T.isOpen_snd_image_mul_mem_open_groupScheme S G hG) (GlobalTheory.T.mem_mul_preimage_of_mem_unitComponent S G hG) (GlobalTheory.T.mem_unitComponent_of_mul_mem S G hG)

end GlobalTheory.IdCompOpen
end

