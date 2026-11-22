import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TwoMulPowFourDvdCardGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyLinear
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyFewColumnsLinear
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory

open MvPolynomial in

theorem map_lap_one {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) (P : MvPolynomial (Letter T r n) k) :
    lap r n k' 1 τ τ' a a' (MvPolynomial.map f P) = MvPolynomial.map f (lap r n k 1 τ τ' a a' P) := by
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum,
    Derivation.coeFn_coe, MvPolynomial.smul_eq_C_mul, map_mul, map_C, pderiv_map]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  congr 2
  by_cases h : b = b' <;> simp [Matrix.one_apply, h]

open MvPolynomial in

theorem map_rowShift {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (σ : T) (i i' : Fin (r σ)) (t : k) (P : MvPolynomial (Letter T r n) k) :
    rowShift r n k' σ i i' (f t) (MvPolynomial.map f P) = MvPolynomial.map f (rowShift r n k σ i i' t P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowShift]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [rowShift, aeval_X]
    split_ifs <;> simp

theorem map_mem_HHa {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (hf : Function.Surjective f) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) k) (hP : P ∈ HHa r n k cc isX a) :
    MvPolynomial.map f P ∈ HHa r n k' cc isX a := by
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ b b'
    rw [map_lap_one, h1 τ hτ b b', map_zero]
  · intro σ i i' hi t
    obtain ⟨s, rfl⟩ := hf t
    rw [map_rowShift, h2 σ i i' hi s]
  · intro m hm
    exact h3 m (MvPolynomial.support_map_subset f P hm)

theorem finrank_le_of_span_sup_smul_top {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {n : ℕ} (x : Fin n → M) (I : Ideal R) (hI : I ≠ ⊤)
    (h : Submodule.span R (Set.range x) ⊔ (I • ⊤ : Submodule R M) = ⊤) : Module.finrank R M ≤ n := by
  set N := Submodule.span R (Set.range x) with hN
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (N := N) (N' := ⊤) (P := ⊤) (I := I) Module.Finite.fg_top le_rfl (by rw [h])
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using I.neg_mem hr1
  have hmem : ∀ m : M, (r • (LinearMap.id : M →ₗ[R] M)) m ∈ N := fun m =>
    hr (Submodule.smul_mem_pointwise_smul m r ⊤ Submodule.mem_top)
  have hinj : Function.Injective ((r • (LinearMap.id : M →ₗ[R] M)).codRestrict N hmem) := by
    intro u v huv
    have : r • u = r • v := congrArg Subtype.val huv
    exact smul_right_injective M hr0 this
  haveI : Module.Finite R N := Module.Finite.span_of_finite R (Set.finite_range x)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank R N ≤ n := by
    simpa [Set.finrank] using finrank_range_le_card (R := R) x
  exact h1.trans h2

theorem Mfr_ne_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    Mfr l ≠ ⊤ := by
  intro h
  have hb : l.Mb = ⊤ := by
    rw [Ideal.eq_top_iff_one] at h ⊢
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 h
    have : y = 1 := H.bar.injective (by simpa using hy1)
    exact this ▸ hy
  have hp := l.prod
  rw [hb, Ideal.map_top, Ideal.top_mul] at hp
  have hn := congrArg Ideal.absNorm hp
  rw [Ideal.absNorm_top, Ideal.absNorm_span_natCast] at hn
  have h3 := l.three_le
  have hpos : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
  rcases Nat.pow_eq_one.1 hn.symm with h' | h' <;> omega

theorem admissible_columns_le_and_harmonic_map_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), (∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → Dw.p + Dw.q ≤ n) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  intro E _ _ _ H Dw l Xo c n d
  refine ⟨fun rk x0 hx => ?_, fun a P hP => ?_⟩
  swap
  · have hs : Function.Surjective (d.eF : c.F →+* d.c₂.F) := fun y => ⟨d.eF.symm y, d.eF.apply_symm_apply y⟩
    generalize (d.eF : c.F →+* d.c₂.F) = f at hs ⊢
    exact map_mem_HHa Dw.mult n f hs _ _ _ P hP
  haveI := Dw.fin
  haveI := Dw.proj
  rw [← Dw.rank]
  refine finrank_le_of_span_sup_smul_top x0 (Mfr l) (Mfr_ne_top l) ?_
  unfold AdmX at hx
  refine top_le_iff.1 (hx.ge.trans ?_)
  exact sup_le_sup_right (Submodule.span_mono (Set.image_subset_range _ _)) _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLevGrpAndSpan
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.EtaCard

theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) =
      Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

theorem nonempty_equiv_mod (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (I : Ideal O) [Finite (O ⧸ I)] (r : ℕ)
    (hr : Module.finrank O M = r) :
    Nonempty ((M ⧸ (I • ⊤ : Submodule O M)) ≃ₗ[O] (Fin r → O ⧸ I)) := by
  have : Finite (Ideal (O ⧸ I)) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (MaximalSpectrum (O ⧸ I)) :=
    Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h
  obtain ⟨B⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by
    let := P.isMaximal
    let := Ideal.Quotient.field P.asIdeal
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq,
      finrank_fibre, hr]
  exact ⟨(TensorProduct.quotTensorEquivQuotSMul M I).symm ≪≫ₗ B.equivFun.restrictScalars O⟩

theorem nonempty_aut_equiv (O N : Type) [CommRing O] [AddCommGroup N] [Module O N] (I : Ideal O) (r : ℕ)
    (e : N ≃ₗ[O] (Fin r → O ⧸ I)) : Nonempty ((N ≃ₗ[O] N) ≃ GL (Fin r) (O ⧸ I)) := by
  have hs : Function.Surjective (algebraMap O (O ⧸ I)) := Ideal.Quotient.mk_surjective
  let e1 : (N ≃ₗ[O] N) ≃ ((Fin r → O ⧸ I) ≃ₗ[O ⧸ I] (Fin r → O ⧸ I)) :=
    { toFun := fun g => (e.symm ≪≫ₗ g ≪≫ₗ e).extendScalarsOfSurjective hs
      invFun := fun g => e ≪≫ₗ g.restrictScalars O ≪≫ₗ e.symm
      left_inv := fun g => by ext x; simp
      right_inv := fun g => by ext x; simp }
  exact ⟨e1.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm.toEquiv.trans
    Matrix.GeneralLinearGroup.toLin.symm.toEquiv)⟩

theorem span_sup_pow (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O) (S : Submodule O M)
    (h : S ⊔ Ideal.span {a} • ⊤ = ⊤) (k : ℕ) : S ⊔ Ideal.span {a ^ k} • ⊤ = ⊤ := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine eq_top_iff.2 (ih.ge.trans (sup_le le_sup_left ?_))
    have h2 := congrArg (fun T : Submodule O M => Ideal.span {a ^ k} • T) h
    simp only [Submodule.smul_sup, ← Submodule.mul_smul, Ideal.span_singleton_mul_span_singleton,
      ← pow_succ] at h2
    exact h2.ge.trans (sup_le_sup_right Submodule.smul_le_right _)

variable (E : Type) [Field E] [NumberField E]

theorem finite_quot (k : ℕ) (hk : k ≠ 0) : Finite (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hk)

theorem card_quot (k : ℕ) : Nat.card (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) = k ^ Module.finrank ℚ E := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]

theorem charP_quot (k : ℕ) : CharP (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) k := by
  refine ⟨fun n => ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨fun h => ?_, fun h => Nat.cast_dvd_cast h⟩
  have h2 := map_dvd (Algebra.norm ℤ) h
  rw [← map_natCast (algebraMap ℤ (𝓞 E)), ← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap,
    Algebra.norm_algebraMap, Int.pow_dvd_pow_iff Module.finrank_pos.ne'] at h2
  exact_mod_cast h2

theorem finrank_eq [IsCMField E] : Module.finrank ℚ E = 2 * FD.fdeg E := by
  rw [FD.fdeg, IsTotallyComplex.finrank E]
  omega

theorem card_levGrp_and_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (R : ℕ), 1 < R → Finite (LevGrp Dw (R ^ 4)) ∧ Finite (LatMod Dw R) ∧ Nat.card (LatMod Dw R) = R ^ (2 * FD.fdeg E * (Dw.p + Dw.q)) ∧ Nat.card (LevGrp Dw (R ^ 4)) ≤ R ^ (8 * FD.fdeg E * (Dw.p + Dw.q) ^ 2) ∧ (Odd R → 2 ≤ Dw.p + Dw.q → 2 * R ^ 4 ∣ Nat.card (LevGrp Dw (R ^ 4))) ∧ (∃ x₀ : Fin (Dw.p + Dw.q) → Dw.La, Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤) ∧ ∀ (n : ℕ) (x₀ : Fin n → Dw.La), Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤ → ∀ (y : Fin n → LatMod Dw R) (g : LevGrp Dw (R ^ 4)), Submodule.span (𝓞 E) (Set.range fun b => g (shiftFam R x₀ y b)) = ⊤ := by
  intro E _ _ _ H Dw R hR
  have := Dw.fin
  have := Dw.proj
  have hR0 : R ≠ 0 := by omega
  have := finite_quot E R hR0
  have := finite_quot E (R ^ 4) (pow_ne_zero _ hR0)
  obtain ⟨e1⟩ := nonempty_equiv_mod (𝓞 E) Dw.La (Ideal.span {(R : 𝓞 E)}) _ Dw.rank
  obtain ⟨e4⟩ := nonempty_equiv_mod (𝓞 E) Dw.La (Ideal.span {((R ^ 4 : ℕ) : 𝓞 E)}) _ Dw.rank
  obtain ⟨g4⟩ := nonempty_aut_equiv _ _ _ _ e4
  refine ⟨Finite.of_equiv _ g4.symm, Finite.of_equiv _ e1.symm.toEquiv, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr e1.toEquiv, Nat.card_fun, Nat.card_fin, card_quot, finrank_eq, ← pow_mul]
  · rw [Nat.card_congr g4]
    refine (Nat.card_le_card_of_injective _ Units.val_injective).trans (le_of_eq ?_)
    change Nat.card (Fin (Dw.p + Dw.q) → Fin (Dw.p + Dw.q) → _) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, card_quot, finrank_eq, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  · intro ho h2
    rw [Nat.card_congr g4]
    exact two_mul_pow_four_dvd_card_generalLinearGroup _ R ho (charP_quot E _) hR _ h2
  · choose x₀ hx using fun i => Submodule.Quotient.mk_surjective _ (e1.symm (Pi.single i 1))
    refine ⟨x₀, ?_⟩
    rw [sup_comm, ← Submodule.map_mkQ_eq_top, eq_top_iff]
    intro z _
    choose c hc using fun i => Ideal.Quotient.mk_surjective (e1 z i)
    refine ⟨∑ i, c i • x₀ i, Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), e1.injective ?_⟩
    simp only [map_sum, map_smul, Submodule.mkQ_apply, hx, LinearEquiv.apply_symm_apply]
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi.symm]) (by simp), ← hc]
    simp [Algebra.smul_def]
  · intro n x₀ hx y g
    have h1 : Submodule.span (𝓞 E) (Set.range fun b => x₀ b + R • qRep (y b)) ⊔
        Ideal.span {(R : 𝓞 E)} • ⊤ = ⊤ := by
      refine eq_top_iff.2 (hx.ge.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right))
      rintro _ ⟨b, rfl⟩
      have : x₀ b = (x₀ b + R • qRep (y b)) - (R : 𝓞 E) • qRep (y b) := by
        rw [Nat.cast_smul_eq_nsmul, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨b, rfl⟩))
        (Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial))
    have h2 := span_sup_pow _ _ _ _ h1 4
    rw [← Nat.cast_pow, sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp] at h2
    have h3 := congrArg (Submodule.map g.toLinearMap) h2
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h3
    exact h3

end GlobalTheory.EtaCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyUnimodular
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Harm

open MvPolynomial

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_iff_herm_of_unimod {n : ℕ} {Λ : GenLat E n} (h : Λ.Unimod) (x : Fin n → E) :
    x ∈ Λ.La ↔ ∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y) := by
  have hI : ∀ z : E, IsIntegral ℤ z ↔ z ∈ (algebraMap (𝓞 E) E).range := fun z =>
    ⟨fun hz => ⟨⟨z, hz⟩, rfl⟩, fun ⟨o, ho⟩ => ho ▸ o.isIntegral_coe⟩
  have hc : ∀ z : E, IsIntegral ℤ (IsCMField.complexConj E z) ↔ IsIntegral ℤ z := by
    intro z
    constructor
    · intro hz
      have := hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
      simpa [IsCMField.complexConj_apply_apply] using this
    · intro hz
      exact hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
  have key : ∀ y : Fin n → E, FD.herm 1 x y =
      IsCMField.complexConj E (∑ j, IsCMField.complexConj E (x j) * y j) := by
    intro y
    simp only [FD.herm, FD.cc, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul,
      IsCMField.complexConj_apply_apply]
  rw [h x]
  refine forall₂_congr fun y _ => ?_
  rw [key y, hc, hI]

theorem not_inPsi_and_conjugate (H : Host E) (τ : E →+* ℂ) :
    ¬ (InPsi H τ ∧ InPsi H (ComplexEmbedding.conjugate τ)) := by
  rintro ⟨h1, h2⟩
  unfold InPsi at h1 h2
  rw [ComplexEmbedding.conjugate_coe_eq, h1] at h2
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp h2
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re,
    Complex.natCast_re] at hre
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [mul_self_nonneg H.rt0.re]

private theorem coe_embF {H : Host E} {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : E) :
    ((embF c τ x : c.F) : ℂ) = τ x := rfl

theorem injective_embF_inPsi {H : Host E} {l : Level H} (c : Coeff l) :
    Function.Injective fun s : {τ : E →+* ℂ // InPsi H τ} × Bool =>
      fun x : E => embF c s.1.1 (if s.2 then FD.cc x else x) := by
  rintro ⟨⟨τ, hτ⟩, b⟩ ⟨⟨τ', hτ'⟩, b'⟩ h
  have hx : ∀ x : E, (if b then ComplexEmbedding.conjugate τ else τ) x =
      (if b' then ComplexEmbedding.conjugate τ' else τ') x := by
    intro x
    have := congrArg (fun z : c.F => (z : ℂ)) (congrFun h x)
    simp only [coe_embF] at this
    cases b <;> cases b' <;>
      simpa [FD.cc, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
        using this
  have hf : (if b then ComplexEmbedding.conjugate τ else τ) =
      (if b' then ComplexEmbedding.conjugate τ' else τ') := RingHom.ext hx
  cases b <;> cases b'
  · simp only [Bool.false_eq_true, if_false] at hf
    subst hf
    rfl
  · simp only [Bool.false_eq_true, if_false, if_true] at hf
    exact absurd ⟨hτ', by rw [← hf]; exact hτ⟩ (not_inPsi_and_conjugate H τ')
  · simp only [Bool.false_eq_true, if_false, if_true] at hf
    exact absurd ⟨hτ, by rw [hf]; exact hτ'⟩ (not_inPsi_and_conjugate H τ)
  · simp only [if_true] at hf
    have h2 := (ComplexEmbedding.involutive_conjugate E).injective hf
    subst h2
    rfl

theorem sum_norm_coeff_eq_l1Norm {K σ σ' : Type} [Field K] (e : σ ≃ σ') (f : K →+* ℂ)
    (Q : MvPolynomial σ K) :
    ∑ m ∈ Q.support, ‖f (Q.coeff m)‖ = MvPoly.l1Norm (MvPolynomial.map f (rename e Q)) := by
  rw [MvPolynomial.map_rename, MvPoly.l1Norm_rename_of_injective e.injective, MvPoly.l1Norm_map]

theorem log_le_of_le_of_log_le {x y B : ℝ} (hx : 0 ≤ x) (h : x ≤ y) (hy : Real.log y ≤ B)
    (hB : 0 ≤ B) : Real.log x ≤ B := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero]
    exact hB
  · exact (Real.log_le_log hpos h).trans hy

end SlopeTestRemainingChoices

theorem exists_short_harmL_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n), Λ.Unimod → Λ.La.FG → Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∃ S : Finset (MvPolynomial (LtN Dw n) c.F), (∀ Q ∈ S, Q ∈ harmL c Λ a ∧ ∀ σ' : c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a) ∧ (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P ∈ Submodule.span c.F (S : Set (MvPolynomial (LtN Dw n) c.F))) ∧ S.card ≤ ((2 * (Dw.p + Dw.q) + 1) * DF Dw a + 1) ^ (2 * FD.fdeg E * n * (2 * Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l c n Λ hU hfg hn a L hL hrd hf hDF hnL
  classical
  let _ : Fintype {τ : E →+* ℂ // InPsi H τ} := Fintype.ofFinite _
  obtain ⟨e, hsym, hHH⟩ := theta_letter_dictionary E H Dw l c n
  have hint : ∀ x ∈ Λ.La, ∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y) := fun x hx =>
    (mem_iff_herm_of_unimod hU x).1 hx
  have hdual : ∀ x, (∀ y ∈ Λ.La, IsIntegral ℤ (FD.herm 1 x y)) → x ∈ Λ.La := fun x hx =>
    (mem_iff_herm_of_unimod hU x).2 hx
  have hre : ∀ M : MvPolynomial (GlobalTheory.Harm.Var {τ : E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n)) c.F,
      rename e (rename e.symm M) = M := fun M => by
    rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
  have hre' : ∀ P : MvPolynomial (LtN Dw n) c.F, rename e.symm (rename e P) = P := fun P => by
    rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]
  rcases hHH a with hzero | ⟨k, k', hdeg, hiff⟩
  · refine ⟨∅, by simp, fun P hP => ?_, by simp⟩
    rw [hzero P hP]
    exact Submodule.zero_mem _
  rcases Nat.eq_zero_or_pos (DF Dw a) with h0 | hpos
  ·
    have hconst : ∀ P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H)
        (fun τ i => a (τ, i)) → P = C (P.coeff 0) := by
      intro P hP
      have h1 := isHomogeneous_of_mem_rowHighest ((hiff P).1 hP)
      rw [hdeg, h0] at h1
      have h2 : (rename e P).totalDegree = 0 := Nat.le_zero.1 h1.totalDegree_le
      have h3 : P.totalDegree = 0 := by
        have := totalDegree_rename_le e.symm (rename e P)
        rw [hre', h2] at this
        exact Nat.le_zero.1 this
      exact totalDegree_eq_zero_iff_eq_C.1 h3
    by_cases h1 : (1 : MvPolynomial (LtN Dw n) c.F) ∈
        HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
    · refine ⟨{1}, fun Q hQ => ?_, fun P hP => ?_, ?_⟩
      · rw [Finset.mem_singleton] at hQ
        subst hQ
        refine ⟨⟨h1, Subring.one_mem _⟩, fun σ' => ?_⟩
        simp [h0]
      · rw [hconst P hP, ← mul_one (C (P.coeff 0)), ← smul_eq_C_mul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · simp [h0]
    · refine ⟨∅, by simp, fun P hP => ?_, by simp⟩
      by_cases hr : P.coeff 0 = 0
      · rw [hconst P hP, hr, C_0]
        exact Submodule.zero_mem _
      · exfalso
        apply h1
        have hmem := (hiff P).1 hP
        rw [hconst P hP, rename_C] at hmem
        have h1' : (1 : MvPolynomial (GlobalTheory.Harm.Var {τ : E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n)) c.F)
            = C ((P.coeff 0)⁻¹ * P.coeff 0) := by
          rw [inv_mul_cancel₀ hr, C_1]
        rw [hiff, map_one, h1', C_mul, ← smul_eq_C_mul]
        exact Submodule.smul_mem _ _ hmem

  have ha1 : 1 ≤ typeDegree k k' := by rw [hdeg]; exact hpos
  obtain ⟨S0, hHa, hspan, hnorm, hcard⟩ := short_harmonic_family_few_columns E n Λ.La hfg hint
    hdual Dw.p Dw.q hn {τ : E →+* ℂ // InPsi H τ} k k' ha1
  have hinj := injective_embF_inPsi (H := H) c
  have hsp := hspan c.F (fun t => embF c t.1) hinj
  refine ⟨S0.image fun s => rename e.symm (minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
    fun t b kk => embF c t.1 (FD.cc (s.2 b kk))), fun Q hQ => ?_, fun P hP => ?_, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hQ
    have hM : minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
        (fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) ∈ rowHighest c.F k k' := by
      rw [← hsp]
      exact Submodule.subset_span ⟨s, Finset.mem_coe.2 hs, rfl⟩
    have hS : minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
        (fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) ∈
        GlobalTheory.Harm.symO Dw.p Dw.q (fun t : {τ : E →+* ℂ // InPsi H τ} => embF c t.1) Λ.La := by
      have := hHa c.F (fun t => embF c t.1) s hs
      unfold GlobalTheory.Harm.Ha at this
      exact (Subalgebra.mem_toSubmodule _).1 (Submodule.mem_inf.1 this).2
    refine ⟨⟨(hiff _).2 (by rw [hre]; exact hM), (hsym Λ _).2 (by rw [hre]; exact hS)⟩,
      fun σ' => ?_⟩
    rw [sum_norm_coeff_eq_l1Norm e σ', hre, map_minorProd]
    have hb := hnorm (fun t => σ'.comp (embF c t.1)) s hs
    refine log_le_of_le_of_log_le (MvPoly.l1Norm_nonneg _) hb ?_ ?_
    · rw [hdeg]
      exact log_shortFamilyNumbers_le (Dw.p + Dw.q) n (DF Dw a) (FD.fdeg E) (FD.rdE E) L
        (one_le_add_of_one_le_typeDegree ha1) hn hpos one_le_fdeg one_le_rdE hL hrd hf hDF hnL
    · have hL0 : (0 : ℝ) ≤ L := by linarith
      positivity
  · have h1 : rename e P ∈ Submodule.span c.F ((fun s : (Fin Dw.p → Fin n → E) ×
        (Fin Dw.q → Fin n → E) => minorProd k k' (fun t a kk => embF c t.1 (s.1 a kk))
          fun t b kk => embF c t.1 (FD.cc (s.2 b kk))) '' ↑S0) := by
      rw [hsp]
      exact (hiff P).1 hP
    have h2 := Submodule.mem_map_of_mem
      (f := (rename (R := c.F) (⇑e.symm)).toLinearMap) h1
    rw [Submodule.map_span, ← Set.image_comp] at h2
    rw [Finset.coe_image]
    convert h2 using 1
    all_goals first
      | exact (hre' P).symm
      | simp
  · calc _ ≤ S0.card := Finset.card_image_le
      _ ≤ _ := by rw [← hdeg]; exact hcard

end GlobalTheory.Harm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NotIsBlockProdZero
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BlockThInhab
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.BlockTh

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ)

def lead (τ : E →+* ℂ) (i : ℕ) (hi : i ≤ Dw.mult τ) (hn : i ≤ n) (c : ℕ) (hc : 1 ≤ c) : Bk Dw n :=
  ⟨τ, i, hi, c, hc, Fin.castLE hn, Fin.castLE_injective hn⟩

theorem poly_ne_zero (K : Type) [Field K] (B : Bk Dw n) : B.poly K ≠ 0 := by
  classical
  unfold Bk.poly
  refine pow_ne_zero _ ?_
  intro h
  let v : LtN Dw n → K := fun l => if ∃ a : Fin B.i, l = ⟨B.τ, Fin.castLE B.hi a, B.col a⟩ then 1 else 0
  have h2 := congrArg (MvPolynomial.eval v) h
  rw [RingHom.map_det, map_zero] at h2
  have : (MvPolynomial.eval v).mapMatrix (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X, v, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; rw [if_pos ⟨a, rfl⟩, if_pos rfl]
    · rw [if_neg hab, if_neg]
      rintro ⟨d, hd⟩
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq] at hd
      have h1 : a = d := Fin.castLE_injective _ hd.1
      have h3 : b = d := B.col_inj hd.2
      exact hab (h1.trans h3.symm)
  rw [this, Matrix.det_one] at h2
  exact one_ne_zero h2

theorem not_isBlockProd_zero (K : Type) [Field K] : ¬ IsBlockProd (0 : MvPolynomial (LtN Dw n) K) := by
  rintro ⟨nb, bs, -, h⟩
  exact Finset.prod_ne_zero_iff.2 (fun j _ => poly_ne_zero Dw n K (bs j)) h.symm

end GlobalTheory.BlockThInhab
end
end

