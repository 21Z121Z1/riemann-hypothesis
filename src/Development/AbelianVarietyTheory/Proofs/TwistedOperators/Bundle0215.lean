import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInfiniteDecomp
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryTorusNormClassesAtAllPlaces
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix Topology

noncomputable section
namespace GlobalTheory.SqCls

theorem finite_units_quot_sq_field {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [ProperSpace k]
    (h2 : (2 : k) ≠ 0) (K : Type) [Field K] [Algebra k K] [FiniteDimensional k K] :
    Finite (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) := by
  classical
  set S := (powMonoidHom 2 : Kˣ →* Kˣ).range with hS
  let V := Fin (Module.finrank k K) → k
  let e : K ≃ₗ[k] V := (Module.finBasis k K).equivFun
  let B : V →ₗ[k] V →ₗ[k] V :=
    ((LinearMap.mul k K).compl₁₂ (e.symm : V →ₗ[k] K) (e.symm : V →ₗ[k] K)).compr₂ (e : K →ₗ[k] V)
  have hB : ∀ a b, B a b = e (e.symm a * e.symm b) := fun a b => rfl
  have hsq := eventually_exists_sq_normed h2 B (e := e 1) (fun v => by simp [hB]) (fun v => by simp [hB])
  have key : ∀ y : Kˣ, ∀ᶠ a in 𝓝 (e y), ∀ g : Kˣ, e g = a → y⁻¹ * g ∈ S := by
    intro y
    let f : V →ₗ[k] V := B (e (y⁻¹ : Kˣ))
    have hf : Continuous f := f.continuous_of_finiteDimensional
    have hfy : f (e y) = e 1 := by simp [f, hB]
    have := (hf.tendsto (e y)).eventually (hfy ▸ hsq)
    filter_upwards [this] with a ⟨z, hz⟩ g hg
    have h1 : ((y⁻¹ : Kˣ) : K) * g = e.symm z * e.symm z := by
      apply e.injective
      rw [← hB, hz, ← hg]
      simp [f, hB]
    have hz0 : e.symm z ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact (mul_ne_zero (Units.ne_zero _) (Units.ne_zero g)) h1
    refine ⟨Units.mk0 _ hz0, ?_⟩
    ext
    simp only [powMonoidHom_apply, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [sq, ← h1]
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one k
  set q : ℝ := ‖c‖ ^ 2 with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [hq]; nlinarith
  set C : Set V := Metric.closedBall 0 1 ∩ {b | q ≤ ‖b‖} with hC
  have hCc : IsCompact C := (isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const continuous_norm)
  have hCne : ∀ b ∈ C, e.symm b ≠ 0 := by
    intro b hb h0
    have : b = 0 := by simpa using congrArg e h0
    have := hb.2
    simp_all
  let y : V → Kˣ := fun b => if h : e.symm b ≠ 0 then Units.mk0 _ h else 1
  have hy : ∀ b ∈ C, e (y b) = b := fun b hb => by
    simp only [y, dif_pos (hCne b hb), Units.val_mk0, LinearEquiv.apply_symm_apply]
  let U : V → Set V := fun b => {a | ∀ g : Kˣ, e g = a → (y b)⁻¹ * g ∈ S}
  have hU : ∀ b ∈ C, U b ∈ 𝓝 b := fun b hb => by
    have := key (y b)
    rw [hy b hb] at this
    exact this
  obtain ⟨t, htC, hcov⟩ := hCc.elim_nhds_subcover U hU
  refine Finite.of_surjective (fun b : t => (QuotientGroup.mk (y b.1) : Kˣ ⧸ S)) ?_
  intro x
  induction x using QuotientGroup.induction_on with
  | H g =>
  have ha : 0 < ‖e g‖ := norm_pos_iff.2 (fun h => Units.ne_zero g (e.injective (h.trans (map_zero e).symm)))
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow ha (one_lt_inv_iff₀.2 ⟨hq0, hq1⟩)
  let u : kˣ := Units.mk0 c (norm_pos_iff.1 hc0) ^ (n + 1)
  let w : Kˣ := Units.map (algebraMap k K : k →* K) u
  have hnorm : ‖e (w ^ 2 * g : Kˣ)‖ = q ^ (n + 1) * ‖e g‖ := by
    have : ((w ^ 2 * g : Kˣ) : K) = ((u : k) ^ 2) • (g : K) := by
      simp [w, Algebra.smul_def]
    rw [this, map_smul, norm_smul, norm_pow]
    congr 1
    simp only [u, Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow, hq]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hmem : e (w ^ 2 * g : Kˣ) ∈ C := by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff, hnorm]
      have := mul_le_mul_of_nonneg_left hn2 (zpow_nonneg hq0.le (n + 1))
      rwa [inv_zpow', ← zpow_add₀ hq0.ne', add_neg_cancel, zpow_zero] at this
    · show q ≤ ‖e (w ^ 2 * g : Kˣ)‖
      rw [hnorm]
      have := mul_lt_mul_of_pos_left hn1 (zpow_pos hq0 (n + 1))
      rw [inv_zpow', ← zpow_add₀ hq0.ne', show n + 1 + -n = 1 by ring, zpow_one] at this
      exact this.le
  obtain ⟨b, hbt, hb⟩ := Set.mem_iUnion₂.1 (hcov hmem)
  refine ⟨⟨b, hbt⟩, ?_⟩
  have h3 := hb (w ^ 2 * g) rfl
  have h4 : w ^ 2 ∈ S := ⟨w, rfl⟩
  refine QuotientGroup.eq.2 ?_
  have := S.mul_mem h3 (S.inv_mem h4)
  rw [mul_comm (w ^ 2) g] at this
  convert this using 1
  group

end GlobalTheory.SqCls

namespace GlobalTheory.SqCls

theorem finite_units_quot_sq_of_reduced {k : Type} [Field k]
    (hK : ∀ (K : Type) [Field K] [Algebra k K] [FiniteDimensional k K], Finite (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range))
    (R : Type) [CommRing R] [Algebra k R] [FiniteDimensional k R] [IsReduced R] :
    Finite (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range) := by
  classical
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI hmax : ∀ I : MaximalSpectrum R, I.asIdeal.IsMaximal := fun I => I.isMaximal
  letI : ∀ I : MaximalSpectrum R, Field (R ⧸ I.asIdeal) := fun I => Ideal.Quotient.field _
  haveI : ∀ I : MaximalSpectrum R, FiniteDimensional k (R ⧸ I.asIdeal) := fun I =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I.asIdeal).toLinearMap (Ideal.Quotient.mkₐ_surjective k _)
  haveI : Finite (MaximalSpectrum R) := inferInstance
  haveI : ∀ I : MaximalSpectrum R, Finite ((R ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (R ⧸ I.asIdeal)ˣ →* _).range) :=
    fun I => hK _
  let φ : Rˣ →* ∀ I : MaximalSpectrum R, (R ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (R ⧸ I.asIdeal)ˣ →* _).range :=
    Pi.monoidHom fun I => (QuotientGroup.mk' _).comp (Units.map (Ideal.Quotient.mk I.asIdeal : R →* R ⧸ I.asIdeal))
  have hker : φ.ker ≤ (powMonoidHom 2 : Rˣ →* Rˣ).range := by
    intro u hu
    have h1 : ∀ I : MaximalSpectrum R, ∃ w : (R ⧸ I.asIdeal)ˣ, w ^ 2 = Units.map (Ideal.Quotient.mk I.asIdeal : R →* _) u :=
      fun I => by
        have h' : (QuotientGroup.mk (Units.map (Ideal.Quotient.mk I.asIdeal : R →* R ⧸ I.asIdeal) u) :
            (R ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (R ⧸ I.asIdeal)ˣ →* _).range) = 1 :=
          congrFun ((MonoidHom.mem_ker).1 hu) I
        rw [QuotientGroup.eq_one_iff] at h'
        obtain ⟨w, hw⟩ := h'
        exact ⟨w, hw⟩
    choose w hw using h1
    let e := IsArtinianRing.equivPi R
    have he : ∀ x I, e x I = Ideal.Quotient.mk I.asIdeal x := fun x I => rfl
    let z : R := e.symm fun I => (w I : R ⧸ I.asIdeal)
    let z' : R := e.symm fun I => ((w I)⁻¹ : (R ⧸ I.asIdeal)ˣ)
    have hzz : z * z' = 1 := e.injective (funext fun I => by simp [z, z', map_mul])
    refine ⟨⟨z, z', hzz, by rw [mul_comm, hzz]⟩, ?_⟩
    ext
    apply e.injective
    funext I
    have := congrArg Units.val (hw I)
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe] at this
    have hz : Ideal.Quotient.mk I.asIdeal z = w I := by rw [← he, e.apply_symm_apply]
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val]
    rw [he, he, map_pow, hz, this]
  haveI : Finite (Rˣ ⧸ φ.ker) := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).toEquiv.symm
  exact Finite.of_surjective (QuotientGroup.map _ _ (MonoidHom.id _) hker) (by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g => exact ⟨QuotientGroup.mk g, rfl⟩)

end GlobalTheory.SqCls

namespace GlobalTheory.SqCls

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

def fixSub (P : PPol σ r) (k : Type) [CommRing k] [Algebra F k] : Subalgebra k (k ⊗[F] Fld P) where
  carrier := {a | sigR k (star' P) a = a}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, ha, hb]
  algebraMap_mem' t := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem finite_cls_of_fixSub (P : PPol σ r) (k : Type) [CommRing k] [Algebra F k]
    (h : Finite ((fixSub P k)ˣ ⧸ (powMonoidHom 2 : (fixSub P k)ˣ →* (fixSub P k)ˣ).range)) : Finite (Cls P k) := by
  classical
  have hfix : ∀ x : plusUnits P k, sigR k (star' P) (x.1 : k ⊗[F] Fld P) = x.1 := fun x =>
    congrArg Units.val x.2
  let φ : (fixSub P k)ˣ →* plusUnits P k :=
    { toFun := fun u => ⟨Units.map (fixSub P k).val.toMonoidHom u, Units.ext u.1.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hφ : Function.Surjective φ := by
    intro x
    have h1 := hfix x
    have h2 := hfix x⁻¹
    refine ⟨⟨⟨x.1.1, h1⟩, ⟨(x⁻¹ : plusUnits P k).1.1, h2⟩, Subtype.ext ?_, Subtype.ext ?_⟩, ?_⟩
    · simp
    · simp
    · ext; rfl
  let ψ : (fixSub P k)ˣ →* Cls P k := (QuotientGroup.mk' _).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hsq : (powMonoidHom 2 : (fixSub P k)ˣ →* (fixSub P k)ˣ).range ≤ ψ.ker := by
    rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ (u ^ 2)) : plusUnits P k ⧸ (norms P k).subgroupOf (plusUnits P k)) = 1
    rw [QuotientGroup.eq_one_iff, map_pow, Subgroup.mem_subgroupOf]
    refine ⟨(φ u).1, ?_⟩
    ext
    simp only [MonoidHom.mul_apply, MonoidHom.id_apply, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    rw [hfix (φ u), sq]
  exact Finite.of_surjective (QuotientGroup.lift _ ψ hsq) (by
    intro q
    obtain ⟨u, rfl⟩ := hψ q
    exact ⟨QuotientGroup.mk u, rfl⟩)

end GlobalTheory.SqCls

namespace GlobalTheory.SqCls

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

theorem finite_cls_of_normed [NumberField F] [NumberField E] (P : PPol σ r) (k : Type) [NontriviallyNormedField k]
    [CompleteSpace k] [ProperSpace k] [Algebra F k] (hred : IsReduced (k ⊗[F] Fld P)) : Finite (Cls P k) := by
  have h2 : (2 : k) ≠ 0 := by
    have := (algebraMap F k).injective.ne (two_ne_zero (α := F))
    rwa [map_ofNat, map_zero] at this
  haveI : Module.Finite F (Fld P) := Module.Finite.of_restrictScalars_finite ℚ F (Fld P)
  haveI : IsReduced (fixSub P k) := isReduced_of_injective (fixSub P k).val Subtype.val_injective
  exact finite_cls_of_fixSub P k
    (finite_units_quot_sq_of_reduced (k := k) (by intro K _ _ _; exact finite_units_quot_sq_field h2 K) (fixSub P k))

theorem finite_cls : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), (∀ v : HeightOneSpectrum (𝓞 F), Finite (Cls P (Fv F v))) ∧ ∀ w : InfinitePlace F, Finite (Cls P w.Completion) := by
  intro F E _ _ _ _ _ σ _ r P
  constructor
  · intro v
    obtain ⟨ψ, -, hb, -⟩ := GlobalTheory.TraceClasses.exists_finite_decomp F (Fld P)
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    haveI := GlobalTheory.LocalData.isLocalField v
    haveI : ProperSpace (v.adicCompletion F) :=
      ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (v.adicCompletion F)
    exact finite_cls_of_normed P (v.adicCompletion F) (isReduced_of_injective (Pi.ringHom (ψ v)) (hb v).1)
  · intro w
    obtain ⟨χ, -, hb⟩ := GlobalTheory.TraceClasses.exists_infinite_decomp F (Fld P)
    letI : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := ⟨2, by
          rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
            map_ofNat]
          simp⟩ }
    haveI : ProperSpace w.Completion :=
      ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion
    exact finite_cls_of_normed P w.Completion (isReduced_of_injective (Pi.ringHom (χ w)) (hb w).1)

end GlobalTheory.SqCls
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCreaDir

section Mat

variable {m n : ℕ}

theorem eq_sum_unitMap {Bm : Matrix (Fin m) (Fin m) ℂ} {Am : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit Bm.det)
    (hA : IsUnit Am.det) (z : Matrix (Fin m) (Fin n) ℂ) :
    z = ∑ i, ∑ j, (Bm⁻¹ * z * Am) i j • Formalism.IndefR.Datum.unitMap Am Bm i j := by
  have e : z = Bm * (Bm⁻¹ * z * Am) * Am⁻¹ := by
    rw [← Matrix.mul_assoc Bm, ← Matrix.mul_assoc Bm, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hA]
  have e2 := Matrix.matrix_eq_sum_single (Bm⁻¹ * z * Am)
  calc z = Bm * (∑ i, ∑ j, Matrix.single i j ((Bm⁻¹ * z * Am) i j)) * Am⁻¹ := by rw [← e2, ← e]
    _ = _ := by
      simp only [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have h : Matrix.single i j ((Bm⁻¹ * z * Am) i j) = ((Bm⁻¹ * z * Am) i j) • Matrix.single i j (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [h, Matrix.mul_smul, Matrix.smul_mul, Formalism.IndefR.Datum.unitMap]

theorem Jm_single_Jm (ε : Fin m → Bool) (δ : Fin n → Bool) (i : Fin m) (j : Fin n) :
    Formalism.REAL.Jm ε * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm δ =
      (if (ε i == δ j) then 1 else -1 : ℂ) • Matrix.single i j (1 : ℂ) := by
  ext p q
  rw [Formalism.REAL.Jm, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul]
  by_cases h : i = p ∧ j = q
  · obtain ⟨rfl, rfl⟩ := h
    cases ε i <;> cases δ j <;> simp
  · simp [h]

end Mat

open GlobalTheory.ChainFr

variable {D : D7} {V W : HSp D}

theorem cplxO_unitMap_fr (A : Fr V) (B : Fr W) (τ : D.what₂.Tau) (i : Fin W.rank) (j : Fin V.rank) :
    cplxO (A.cart τ) (B.cart τ) (Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j) =
      ((if (B.ε τ i == A.ε τ j) then 1 else -1 : ℂ) * Complex.I) •
        Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j := by
  have hA := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hB := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
  have h1 : B.cart τ * B.onb τ = B.onb τ * Formalism.REAL.Jm (B.ε τ) := by
    rw [Fr.cart, Fr.onb, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
  have h2 : (A.onb τ)⁻¹ * A.cart τ = Formalism.REAL.Jm (A.ε τ) * (A.onb τ)⁻¹ := by
    rw [Fr.cart, Fr.onb, Matrix.nonsing_inv_nonsing_inv _ hA]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  unfold cplxO Formalism.IndefR.Datum.unitMap
  rw [mul_comm _ Complex.I, ← smul_smul]
  congr 1
  calc B.cart τ * (B.onb τ * Matrix.single i j (1 : ℂ) * (A.onb τ)⁻¹) * A.cart τ
      = (B.cart τ * B.onb τ) * Matrix.single i j (1 : ℂ) * ((A.onb τ)⁻¹ * A.cart τ) := by
        simp only [Matrix.mul_assoc]
    _ = B.onb τ * (Formalism.REAL.Jm (B.ε τ) * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm (A.ε τ)) * (A.onb τ)⁻¹ := by
        rw [h1, h2]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Jm_single_Jm, Matrix.mul_smul, Matrix.smul_mul]

theorem fockScale_ne_zero (D : D7) (τ : D.what₂.Tau) : ((fockScale D τ : ℝ) : ℂ) ≠ 0 := by
  have h0 : 0 < ‖tauE D τ D.host.xi0‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := Formalism.L2.Theta.xi_zero_im_pos D τ
    rw [h] at this
    simp at this
  have : 0 < fockScale D τ := by
    unfold fockScale
    have := Real.sqrt_pos.2 (mul_pos (mul_pos two_pos Real.pi_pos) h0)
    positivity
  exact_mod_cast this.ne'

end GlobalTheory.FockCreaDir

open GlobalTheory.FockCreaDir in

theorem GlobalTheory.FockCreaDir.crea_ptF : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (P : PolF D W.rank V.rank), ∃ Q : PolF D W.rank V.rank, crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) z (GlobalTheory.ChainFr.ptF ψ θ A B f P) = GlobalTheory.ChainFr.ptF ψ θ A B f Q := by
  intro D V W A B θ ψ hψ hθ f hf τ z P
  have hS := GlobalTheory.ChainFr.Model.isCartanInv_cart A
  have hT := GlobalTheory.ChainFr.Model.isCartanInv_cart B
  have hadd : ∀ g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → IsThetaFunO ψ V W (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ v g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W
      (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v g) :=
    fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ v Q,
      pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v
        (pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f Q) := fun v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ V W) hadd hsm hth ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hg : IsThetaFunO ψ V W (GlobalTheory.ChainFr.ptF ψ θ A B f P) :=
    GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ V W) hadd hsm hth hf P
  have hdA : IsUnit (A.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  have hdB : IsUnit (B.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  obtain ⟨c, rfl⟩ : ∃ c : Fin W.rank → Fin V.rank → ℂ,
      z = ∑ i, ∑ j, c i j • Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j := ⟨_, eq_sum_unitMap hdB hdA z⟩
  refine ⟨((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) •
    (MvPolynomial.X (τ, i, j) * P), ?_⟩
  have h1 : ∀ (y : Matrix (Fin W.rank) (Fin V.rank) ℂ) g,
      crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g =
        ((fockScale D τ : ℝ) : ℂ) • Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g := fun y g => by
    rw [Formalism.IndefR.Datum.aPlus, smul_smul, mul_inv_cancel₀ (fockScale_ne_zero D τ), one_smul]
  rw [h1]
  have h2 : GlobalTheory.ChainFr.ptF ψ θ A B f (((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
      (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) • (MvPolynomial.X (τ, i, j) * P)) =
      ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) •
        Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ))
          (Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j) (GlobalTheory.ChainFr.ptF ψ θ A B f P) := by
    unfold GlobalTheory.ChainFr.ptF pureTensorO
    simp only [map_smul, map_sum, hX]
    rfl
  rw [h2]
  congr 1
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ _ _ hg (B.ε τ i == A.ε τ j) _ (cplxO_unitMap_fr A B τ i j)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReduction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameIdem

section General

variable {R : Type} [CommRing R] {n : ℕ}

theorem cut_mem (O : Subring R) {f f' : R} (hf : f ∈ O) (hf' : f' ∈ O) (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, f * A i j ∈ O) (h' : ∀ i j, f' * A i j ∈ O) (i j : Fin n) :
    ((f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R)) i j ∈ O := by
  have e : ((f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R)) i j =
      f * A i j + f' * A i j + (1 - (f + f')) * (1 : Matrix (Fin n) (Fin n) R) i j := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul]
  rw [e]
  refine O.add_mem (O.add_mem (h i j) (h' i j)) (O.mul_mem (O.sub_mem O.one_mem (O.add_mem hf hf')) ?_)
  rw [Matrix.one_apply]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

theorem exists_cut (O : Subring R) {f f' : R} (hf : f ∈ O) (hf' : f' ∈ O) (hff : f * f = f) (hff' : f' * f' = f')
    (h0 : f * f' = 0) (A B : Matrix (Fin n) (Fin n) R) (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i j, f * A i j ∈ O) (hA' : ∀ i j, f' * A i j ∈ O)
    (hB : ∀ i j, f * B i j ∈ O) (hB' : ∀ i j, f' * B i j ∈ O) :
    ∃ Y : GL (Fin n) O, Y.1.map O.subtype = (f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R) ∧
      ∀ {k : Type} [CommRing k] (ρ : O →+* k), ρ ⟨f, hf⟩ = 1 →
        ∀ i j, ρ (Y.1 i j) = ρ ⟨f * A i j, hA i j⟩ := by
  have hφ : (f + f') * (f + f') = f + f' := by
    have h0' : f' * f = 0 := by rw [mul_comm, h0]
    simp only [add_mul, mul_add, hff, hff', h0, h0', add_zero, zero_add]
  let Ym : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, cut_mem O hf hf' A hA hA' i j⟩
  let Ym' : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, cut_mem O hf hf' B hB hB' i j⟩
  have hm : Ym.map O.subtype = (f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R) := rfl
  have hm' : Ym'.map O.subtype = (f + f') • B + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R) := rfl
  have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype) := by
    intro M N h
    ext i j
    exact congrFun (congrFun h i) j
  have e1 : Ym * Ym' = 1 := inj (by
    show (Ym * Ym').map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, hm, hm', GlobalTheory.CompStab.idem_mul _ hφ A B hAB, Matrix.map_one _ (map_zero _) (map_one _)])
  have e2 : Ym' * Ym = 1 := inj (by
    show (Ym' * Ym).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, hm, hm', GlobalTheory.CompStab.idem_mul _ hφ B A hBA, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨⟨Ym, Ym', e1, e2⟩, hm, ?_⟩
  intro k _ ρ hρ i j
  have hz : ρ ⟨f', hf'⟩ = 0 := by
    have : (⟨f, hf⟩ : O) * ⟨f', hf'⟩ = 0 := Subtype.ext h0
    have h2 := congrArg ρ this
    rwa [map_mul, hρ, one_mul, map_zero] at h2
  have hz' : ρ ⟨f' * A i j, hA' i j⟩ = 0 := by
    have : (⟨f, hf⟩ : O) * ⟨f' * A i j, hA' i j⟩ = 0 :=
      Subtype.ext (show f * (f' * A i j) = 0 by rw [← mul_assoc, h0, zero_mul])
    have h2 := congrArg ρ this
    rwa [map_mul, hρ, one_mul, map_zero] at h2
  have hd : ρ ((1 : Matrix (Fin n) (Fin n) O) i j) * 0 = 0 := mul_zero _
  have split : Ym i j = ⟨f * A i j, hA i j⟩ + ⟨f' * A i j, hA' i j⟩ +
      (1 - (⟨f, hf⟩ + ⟨f', hf'⟩)) * (1 : Matrix (Fin n) (Fin n) O) i j := by
    apply Subtype.ext
    show ((f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R)) i j = _
    have : (((1 : Matrix (Fin n) (Fin n) O) i j : O) : R) = (1 : Matrix (Fin n) (Fin n) R) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Subring.coe_add, Subring.coe_mul,
      this]
    rfl
  show ρ (Ym i j) = _
  rw [split, map_add, map_add, map_mul, map_sub, map_add, hρ, hz, hz', map_one]
  simp

end General

theorem frGL_val {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (frGL β Y).1 = β.1 * Y.1.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 := rfl

set_option maxHeartbeats 400000 in

theorem cut_mem_St_red : ∀ {D : D7} (n : ℕ) (β γ y : GL (Fin n) (EAf D)) (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → IsIntM (toEAf D e • γ.1) → IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (EAf D)).1) → IsIntM (toEAf D (cA D e) • γ.1) → IsIntM (toEAf D (cA D e) • (γ⁻¹ : GL (Fin n) (EAf D)).1) → y.1 = β.1 * (toEAf D (e + cA D e) • γ.1 + (1 - toEAf D (e + cA D e)) • (1 : Matrix (Fin n) (Fin n) (EAf D))) * (β⁻¹ : GL (Fin n) (EAf D)).1 → y ∈ St β ∧ ∀ PP ∈ Z, ((redFn β PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) = redM PP (toEAf D e • γ.1) := by
  intro D n β γ y Z e he h1 h2 h3 h4 hy
  obtain ⟨hf, hres⟩ := GlobalTheory.InnerSteps.resS_idemSum he
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hfc : toEAf D e * toEAf D (cA D e) = 0 := by rw [← map_mul, he.2, map_zero]
  have hf' : toEAf D (cA D e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hcc]))
  obtain ⟨Y, hY, hred⟩ := exists_cut (Formalism.L2.Herm.intAf D.host.F D.host.E) hf hf'
    (by rw [← map_mul, hee]) (by rw [← map_mul, hcc]) hfc γ.1 (γ⁻¹ : GL (Fin n) (EAf D)).1
    γ.mul_inv γ.inv_mul h1 h3 h2 h4
  have hyY : y = frGL β Y := by
    have hs : toEAf D (e + cA D e) = toEAf D e + toEAf D (cA D e) := (toEAf D).map_add _ _
    refine Units.ext (hy.trans ?_)
    rw [frGL_val, hY, hs]
  subst hyY
  refine ⟨⟨Y, rfl⟩, fun PP hP => ?_⟩
  rw [redFn_frGL]
  ext i j
  have := hred (resS D.host.F PP) (hres PP hP) i j
  refine this.trans ?_
  unfold redM
  rw [dif_pos (h1 i j)]
  rfl

end GlobalTheory.FrameIdem

end
end

