import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtPointLiftOfSurjectiveLocFinTypeStatement
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExt_point_lift_of_surjective_locFinType : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), LocallyOfFiniteType π → Function.Surjective π → ∀ (K : Type) [Field K] (x : Sp K ⟶ X), ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (y : Sp K' ⟶ Y), σ.Finite ∧ y ≫ π = spMap σ ≫ x := by
  first | exact @GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft | exact GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft | (intros; apply GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePresentationModelOfIsColimit
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.FpDescent

theorem exists_finitePresentation_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (D : Type) [CommRing D] [Algebra c.pt D], Algebra.FinitePresentation c.pt D →
    ∃ (j : J) (A : Type) (_ : CommRing A) (_ : Algebra (F.obj j) A)
      (_ : Algebra.FinitePresentation (F.obj j) A),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc D _ _ hD
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  let P := Algebra.Presentation.ofFinitePresentation c.pt D
  obtain ⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by
    have hfin := P.finite_coeffs
    choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y
    obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (hfin.toFinset.image jx)
    refine ⟨j, fun y hy ↦ ?_⟩
    obtain ⟨f⟩ := hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))
    refine ⟨F.map f (x y), ?_⟩
    have h1 := hx y
    have h2 := congr(($(c.w f)).hom (x y))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact h1
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  letI : Algebra (F.obj j) D := ((algebraMap c.pt D).comp (c.ι.app j).hom).toAlgebra
  haveI : IsScalarTower (F.obj j) c.pt D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : P.HasCoeffs (F.obj j) := ⟨hj⟩
  exact ⟨j, P.ModelOfHasCoeffs (F.obj j), inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv (F.obj j)⟩⟩

end GlobalTheory.FpDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetEqSumAddCosetIndicator
section
open Filter Topology

namespace GlobalTheory.LinSchur

open Classical in

theorem exists_finset_eq_sum_cind {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (L : AddSubgroup X) (hL : IsOpen (L : Set X)) (f : X → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB X)
    (hper : ∀ Y, ∀ C ∈ L, f (Y + C) = f Y) :
    ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y := by
  have hK : IsCompact (tsupport f) := hf.2
  obtain ⟨F0, -, hcov⟩ := hK.elim_nhds_subcover (fun x => {Y | Y - x ∈ L}) (fun x _ =>
    (hL.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp))
  refine ⟨(F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ?_⟩
  have hmk : ∀ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ∀ Y : X,
      Y - y ∈ L ↔ (QuotientAddGroup.mk Y : X ⧸ L) = QuotientAddGroup.mk y := by
    intro y _ Y
    rw [QuotientAddGroup.eq, ← neg_mem_iff]
    simp [sub_eq_add_neg, add_comm]
  funext Y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.LinSchur.cind]
  by_cases hex : ∃ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, Y - y ∈ L
  · obtain ⟨y, hy, hYy⟩ := hex
    rw [Finset.sum_eq_single y]
    · rw [if_pos hYy, mul_one]
      have := hper y (Y - y) hYy
      rw [add_sub_cancel] at this
      exact this
    · intro y' hy' hne
      rw [if_neg, mul_zero]
      intro hY'
      apply hne
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hy'
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hy
      have e1 := (hmk _ hy' Y).mp hY'
      have e2 := (hmk _ hy Y).mp hYy
      simp only [QuotientAddGroup.out_eq'] at e1 e2
      rw [← e1, ← e2]
    · intro h; exact absurd hy h
  · push_neg at hex
    rw [Finset.sum_eq_zero (fun y hy => by rw [if_neg (hex y hy), mul_zero])]
    apply image_eq_zero_of_notMem_tsupport
    intro hY
    have := hcov hY
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at this
    obtain ⟨y0, hy0, hYy0⟩ := this
    have hmem : (QuotientAddGroup.mk y0 : X ⧸ L).out ∈
        (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out :=
      Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨y0, hy0, rfl⟩, rfl⟩
    apply hex _ hmem
    rw [hmk _ hmem, QuotientAddGroup.out_eq']
    rw [← QuotientAddGroup.eq_iff_sub_mem.mpr hYy0]

end GlobalTheory.LinSchur

example : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (L : AddSubgroup X), IsOpen (L : Set X) → ∀ f ∈ GlobalTheory.WeilM.SB X, (∀ Y, ∀ C ∈ L, f (Y + C) = f Y) → ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y :=
  fun L hL f hf hp => GlobalTheory.LinSchur.exists_finset_eq_sum_cind L hL f hf hp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalBranchesOfSeparableReductionStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formal_branches_of_separable_reduction : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℂ)) (c : Fin D → ℂ), P.Monic → (P.map (MvPolynomial.eval c)).Separable → ∃ (n : ℕ) (φ : Fin n → (AdjoinRoot P →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)), (∀ u, (∀ j, φ j u = 0) → u = 0) ∧ ∀ j i, φ j (AdjoinRoot.of P (MvPolynomial.X i)) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  first | exact @GlobalTheory.branches_of_unramified_point | exact GlobalTheory.branches_of_unramified_point | (intros; apply GlobalTheory.branches_of_unramified_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGermOpenAffine
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem liftAll_deg_reg : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → l.Prime → (∀ p ∈ L, 0 < p.1 ∧ Reg q p.1 p.2) →
    deg (liftAll q l L) = deg L ∧ ∀ p ∈ liftAll q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  intro q l L hq hl hL
  induction L with
  | nil => simp [liftAll, deg]
  | cons p L ih =>
    have hp := hL p (by simp)
    have ih' := ih (fun x hx => hL x (by simp [hx]))
    have hcons : liftAll q l (p :: L) = (if l ∣ p.1 then liftL q l [p]
        else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))]) ++ liftAll q l L := by
      simp [liftAll, List.flatMap_cons]
    have hdegapp : ∀ A B : List (ℕ × ℕ), deg (A ++ B) = deg A + deg B := by intro A B; simp [deg]
    have hdegcons : deg (p :: L) = p.1 + deg L := by simp [deg]
    rw [hcons, hdegapp, hdegcons]
    by_cases h : l ∣ p.1
    · obtain ⟨h1, h2⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [p] hq hl.pos (by
        intro x hx; rw [List.mem_singleton] at hx; subst hx; exact ⟨hp.1, h, hp.2⟩)
      rw [if_pos h]
      have hs : deg [p] = p.1 := by simp [deg]
      refine ⟨by rw [h1, hs, ih'.1], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h2 x hx
      · exact ih'.2 x hx
    · rw [if_neg h]
      have hr := (GlobalTheory.T.regular_pair_lift_to_prime_power_field q l p.1 p.2 hq hl hp.1 h hp.2).1
      have hs : deg [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))] = p.1 := by simp [deg]
      refine ⟨by rw [hs, ih'.1], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [List.mem_singleton] at hx; subst hx; exact ⟨hp.1, hr⟩
      · exact ih'.2 x hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusTwistedFrameStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_twisted_frame : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ψ : RL p O Λ →+* RL p O Λ) (ρ : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), IsPsi ψ → IsFrame ρ e → ∃ e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame (fun l => (ρ l).map (phiInv p O)) e' ∧ ∀ w, e' (fun i => ψ (w i)) = fun j => phiInv p O (e w j) := by
  first | exact @GlobalTheory.DetInv.frame_twist | exact GlobalTheory.DetInv.frame_twist | (intros; apply GlobalTheory.DetInv.frame_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLDiagonalCongruentHermitian
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem exists_gl_diagonal_hermitian : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (b : Matrix ν ν E), (b.map c)ᵀ = b → b.det ≠ 0 → ∃ (a : GL ν E) (D : ν → Fˣ), b = (a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ := by
  intro F _ _ E _ _ c δ hE ν _ _ b hb hdet
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hG : ∀ x y, (c : E →+* E) (b x y) = b y x := by
    intro x y
    have := congrFun (congrFun hb y) x
    simpa using this
  obtain ⟨P, d, hP, hPd, hfix, hne⟩ :=
    GlobalTheory.HermDiag.exists_congr_diagonal (c := (c : E →+* E)) h2 (fun t => hE.invol t) (G := b) hG
  have hd0 := hne hdet
  have hPd' : Pᵀ * b * P.map c = diagonal d := hPd
  choose f hf using fun i => hE.exists_of_fixed (hfix i)
  have hf0 : ∀ i, f i ≠ 0 := by
    intro i h; apply hd0 i; rw [hf i, h, map_zero]
  have hQ : (Pᵀ).det ≠ 0 := by rwa [det_transpose]
  set A : Matrix ν ν E := (Pᵀ)⁻¹ with hA
  have hAQ : A * Pᵀ = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hQ)
  have hQA : Pᵀ * A = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQ)
  have hAs : (A.map c)ᵀ * P.map c = 1 := by
    have h1 : (Pᵀ * A).map c = 1 := by rw [hQA]; exact Matrix.map_one _ (map_zero c) (map_one c)
    rw [show (Pᵀ * A).map c = (Pᵀ).map c * A.map c from Matrix.map_mul (f := c.toRingHom)] at h1
    have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h3
    simpa [Matrix.transpose_map] using h3
  have hAs' : P.map c * (A.map c)ᵀ = 1 := mul_eq_one_comm.mp hAs
  have hAdet : A.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hAQ
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet, fun j => Units.mk0 (f j) (hf0 j), ?_⟩
  have hD : diagonal (fun j => algebraMap F E ((Units.mk0 (f j) (hf0 j) : Fˣ) : F)) = diagonal d := by
    congr 1; funext j; simp [hf j]
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  rw [hD, ← hPd']
  calc b = (A * Pᵀ) * b * (P.map c * (A.map c)ᵀ) := by rw [hAQ, hAs', Matrix.one_mul, Matrix.mul_one]
    _ = A * (Pᵀ * b * P.map c) * (A.map c)ᵀ := by simp only [Matrix.mul_assoc]

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataIterated
section
open IsLocalRing TensorProduct

namespace GlobalTheory

open MvPolynomial in

theorem derivation_sumAlgEquiv_eq_pderiv {Λ : Type} [CommRing Λ] {σ τ : Type}
    (d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ))
      (MvPolynomial τ (MvPolynomial σ Λ)))
    (h1 : ∀ t x, d (Sum.inl t) x = pderiv t x)
    (h2 : ∀ s x, d (Sum.inr s) (C x) = C (pderiv s x))
    (h3 : ∀ s t, d (Sum.inr s) (X t) = 0) (u : τ ⊕ σ) (y : MvPolynomial (τ ⊕ σ) Λ) :
    d u (sumAlgEquiv Λ τ σ y) = sumAlgEquiv Λ τ σ (pderiv u y) := by
  classical
  have eC : ∀ a : Λ, sumAlgEquiv Λ τ σ (C a) = C (C a) := fun a => by
    simp [sumAlgEquiv_C_inl]
  have eL : ∀ t : τ, sumAlgEquiv Λ τ σ (X (Sum.inl t)) = X t := fun t => by
    simp [sumAlgEquiv_X_inl]
  have eR : ∀ s : σ, sumAlgEquiv Λ τ σ (X (Sum.inr s)) = C (X s) := fun s => by
    simp [sumAlgEquiv_X_inr]
  have hX : ∀ v : τ ⊕ σ,
      d u (sumAlgEquiv Λ τ σ (X v)) = sumAlgEquiv Λ τ σ (pderiv u (X v)) := by
    intro v
    rcases u with t | s <;> rcases v with t' | s'
    · rw [eL, h1]
      by_cases h : t = t'
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero]
    · rw [eR, h1, pderiv_C, pderiv_X_of_ne (by simp), map_zero]
    · rw [eL, h3, pderiv_X_of_ne (by simp), map_zero]
    · rw [eR, h2]
      by_cases h : s = s'
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero,
          map_zero]
  induction y using MvPolynomial.induction_on with
  | C a =>
    rw [eC, pderiv_C, map_zero]
    rcases u with t | s
    · rw [h1, pderiv_C]
    · rw [h2, pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, hX, map_add, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, map_mul]

theorem exists_generic_jacobian_data_iterated : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ τ : Type) [Finite σ] [Finite τ] (Q : Ideal (MvPolynomial τ (MvPolynomial σ Λ))) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0) → ∀ d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ)) (MvPolynomial τ (MvPolynomial σ Λ)), (∀ t x, d (Sum.inl t) x = MvPolynomial.pderiv t x) → (∀ s x, d (Sum.inr s) (MvPolynomial.C x) = MvPolynomial.C (MvPolynomial.pderiv s x)) → (∀ s t, d (Sum.inr s) (MvPolynomial.X t) = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial τ (MvPolynomial σ Λ)) (s : Fin h → τ ⊕ σ) (g : MvPolynomial τ (MvPolynomial σ Λ)), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => d (s i) (f j)).det ∉ Q := by
  intro Λ _ _ _ _ σ τ _ _ Q _ hQ d h1 h2 h3
  let e := MvPolynomial.sumAlgEquiv Λ τ σ
  have eC : ∀ a : Λ, e (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := fun a => by
    simp [e, MvPolynomial.sumAlgEquiv_C_inl]
  obtain ⟨h, f, s, g, hg, hf, hx, hdet⟩ := GlobalTheory.T.exists_local_generators_jacobian_det_not_mem Λ (τ ⊕ σ) (Q.comap e)
    (fun a ha => hQ a (by rw [← eC]; exact ha))
  refine ⟨h, fun j => e (f j), s, e g, hg, hf, fun x hxQ => ?_, ?_⟩
  · have h4 := hx (e.symm x) (by simpa [Ideal.mem_comap] using hxQ)
    have h5 := Ideal.mem_map_of_mem e h4
    rw [Ideal.map_span, ← Set.range_comp, map_mul, AlgEquiv.apply_symm_apply] at h5
    exact h5
  · intro hmem
    apply hdet
    rw [Ideal.mem_comap, AlgEquiv.map_det]
    convert hmem using 2
    ext i j : 1
    exact (derivation_sumAlgEquiv_eq_pderiv d h1 h2 h3 _ _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecCompleteLocalRingThickeningsStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_spec_complete_localRing_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X), (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) → ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e := by
  first | exact @GlobalTheory.LocalThickGlue.exists_glue | exact GlobalTheory.LocalThickGlue.exists_glue | (intros; apply GlobalTheory.LocalThickGlue.exists_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicParamOfDegZeroCompatible
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_param_of_deg_zero {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hK : K.Rich) (G : C0 K.Oc)
    (hG : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) :
    ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p := by
  let a : ∀ k, Hol (K.W k) := fun k ↦ G (K.triv k)
  have h1 : ∀ k k' (e : K.le 0 k' k), sh e (a k) = a k' := fun k k' e ↦
    (hG (K.triv k) (K.triv k') (ptHom (K.triv k') e) rfl).symm
  have h2 : ∀ k i, dw i (a k) = 0 := fun k i ↦ by
    have e0 : G (K.jet k) = TrivSqZeroExt.inl (sh (K.le_refl k) (a k)) := hG _ _ (jet0 k) rfl
    have e1 : G (K.jet k) = tszeSec dw (a k) := hG _ _ (jet1 k) rfl
    have e2 := congrArg (fun x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) ↦ x.snd i) (e1.symm.trans e0)
    exact (snd_tszeSec dw (a k) i).symm.trans e2
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_parameter_function_of_fibreDeriv_zero K hK a h1 h2
  refine ⟨p, fun T ↦ ?_⟩
  have e : G T = T.ρ (sh (K.le_refl T.k) (a T.k)) := hG _ _ (ptHom T (K.le_refl T.k)) rfl
  rw [e, sh_refl, hp, T.ρ_cst]

end GlobalTheory.AnPer.Charts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfBigCellGenericRelations
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem groupChunk_extend {G H : Type} [Group G] [Group H] (C : G → Prop) (f : G → H)
    (hmul : ∀ x y, C x → C y → C (x * y) → f (x * y) = f x * f y)
    (hgen : ∀ s : Finset G, ∃ u : G, ∀ g ∈ s, C (g * u)) :
    ∃ Φ : G →* H, ∀ g u, C u → C (g * u) → Φ g = f (g * u) * (f u)⁻¹ := by
  classical

  have key : ∀ g u w, C u → C (g * u) → C w → C (g * w) → C (u⁻¹ * w) →
      f (g * u) * (f u)⁻¹ = f (g * w) * (f w)⁻¹ := by
    intro g u w hu hgu hw hgw huw
    have h1 : f w = f u * f (u⁻¹ * w) := by
      have h := hmul u (u⁻¹ * w) hu huw (by rwa [mul_inv_cancel_left])
      rwa [mul_inv_cancel_left] at h
    have h2 : f (g * w) = f (g * u) * f (u⁻¹ * w) := by
      have h := hmul (g * u) (u⁻¹ * w) hgu huw (by rwa [mul_assoc, mul_inv_cancel_left])
      rwa [mul_assoc, mul_inv_cancel_left] at h
    rw [h1, h2]
    group
  choose u₀ hu₀ using fun g : G => hgen {1, g}
  have hu₀1 : ∀ g, C (u₀ g) := fun g => by simpa using hu₀ g 1 (by simp)
  have hu₀g : ∀ g, C (g * u₀ g) := fun g => hu₀ g g (by simp)
  let φ : G → H := fun g => f (g * u₀ g) * (f (u₀ g))⁻¹
  have hφ : ∀ g u, C u → C (g * u) → φ g = f (g * u) * (f u)⁻¹ := by
    intro g u hu hgu
    obtain ⟨w, hw⟩ := hgen {1, g, u⁻¹, (u₀ g)⁻¹}
    have hw1 : C w := by simpa using hw 1 (by simp)
    have hwg : C (g * w) := hw g (by simp)
    have hwu : C (u⁻¹ * w) := hw u⁻¹ (by simp)
    have hwu₀ : C ((u₀ g)⁻¹ * w) := hw (u₀ g)⁻¹ (by simp)
    rw [key g u w hu hgu hw1 hwg hwu]
    exact key g (u₀ g) w (hu₀1 g) (hu₀g g) hw1 hwg hwu₀
  refine ⟨MonoidHom.mk' φ ?_, fun g u hu hgu => hφ g u hu hgu⟩
  intro g h
  obtain ⟨w, hw⟩ := hgen {1, h, g * h}
  have hw1 : C w := by simpa using hw 1 (by simp)
  have hwh : C (h * w) := hw h (by simp)
  have hwgh : C (g * h * w) := hw (g * h) (by simp)
  rw [hφ (g * h) w hw1 hwgh, hφ h w hw1 hwh, hφ g (h * w) hwh (by rwa [← mul_assoc]),
    ← mul_assoc g h w]
  group

theorem bigCell_hom : ∀ (G H : Type) [Group G] [Group H] (P : Subgroup G) (w : G) (ρ : P →* H) (W : H), (∀ p q : P, w * p = q * w → W * ρ p = ρ q * W) → (∀ p : P, (∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂) → ∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂ ∧ W * ρ p * W = ρ p₁ * W * ρ p₂) → (∀ s : Finset G, ∃ u : G, ∀ g ∈ s, ∃ p₁ p₂ : P, g * u = p₁ * w * p₂) → ∃ Φ : G →* H, (∀ p : P, Φ p = ρ p) ∧ Φ w = W := by
  classical
  intro G H _ _ P w ρ W ha hb hc
  let C : G → Prop := fun g => ∃ p₁ p₂ : P, g = p₁ * w * p₂

  have hwd : ∀ p₁ p₂ q₁ q₂ : P, (p₁ : G) * w * p₂ = q₁ * w * q₂ →
      ρ p₁ * W * ρ p₂ = ρ q₁ * W * ρ q₂ := by
    intro p₁ p₂ q₁ q₂ h
    have h' : w * ((p₂ * q₂⁻¹ : P) : G) = ((p₁⁻¹ * q₁ : P) : G) * w := by
      push_cast
      calc w * ((p₂ : G) * (q₂ : G)⁻¹)
          = (p₁ : G)⁻¹ * ((p₁ : G) * w * p₂) * (q₂ : G)⁻¹ := by group
        _ = (p₁ : G)⁻¹ * ((q₁ : G) * w * q₂) * (q₂ : G)⁻¹ := by rw [h]
        _ = (p₁ : G)⁻¹ * q₁ * w := by group
    have h'' := ha _ _ h'
    rw [map_mul, map_mul, map_inv, map_inv] at h''
    calc ρ p₁ * W * ρ p₂ = ρ p₁ * (W * (ρ p₂ * (ρ q₂)⁻¹)) * ρ q₂ := by group
      _ = ρ p₁ * ((ρ p₁)⁻¹ * ρ q₁ * W) * ρ q₂ := by rw [h'']
      _ = ρ q₁ * W * ρ q₂ := by group
  let f : G → H := fun g => if h : C g then ρ h.choose * W * ρ h.choose_spec.choose else 1
  have hf : ∀ p₁ p₂ : P, f (p₁ * w * p₂) = ρ p₁ * W * ρ p₂ := by
    intro p₁ p₂
    have hC : C (p₁ * w * p₂) := ⟨p₁, p₂, rfl⟩
    dsimp only [f]
    rw [dif_pos hC]
    exact hwd _ _ _ _ hC.choose_spec.choose_spec.symm
  have hmul : ∀ x y, C x → C y → C (x * y) → f (x * y) = f x * f y := by
    rintro x y ⟨p₁, p₂, rfl⟩ ⟨q₁, q₂, rfl⟩ ⟨r₁, r₂, hr⟩
    have hin : ∃ a b : P, w * ((p₂ * q₁ : P) : G) * w = a * w * b :=
      ⟨p₁⁻¹ * r₁, r₂ * q₂⁻¹, by
        push_cast
        calc w * ((p₂ : G) * q₁) * w
            = (p₁ : G)⁻¹ * ((p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂)) * (q₂ : G)⁻¹ := by group
          _ = (p₁ : G)⁻¹ * ((r₁ : G) * w * r₂) * (q₂ : G)⁻¹ := by rw [hr]
          _ = (p₁ : G)⁻¹ * r₁ * w * ((r₂ : G) * (q₂ : G)⁻¹) := by group⟩
    obtain ⟨a, b, hab, hW⟩ := hb _ hin
    rw [map_mul] at hW
    have hxy : (p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂) = ((p₁ * a : P) : G) * w * ((b * q₂ : P) : G) := by
      calc (p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂)
          = (p₁ : G) * (w * ((p₂ * q₁ : P) : G) * w) * q₂ := by push_cast; group
        _ = (p₁ : G) * ((a : G) * w * b) * q₂ := by rw [hab]
        _ = ((p₁ * a : P) : G) * w * ((b * q₂ : P) : G) := by push_cast; group
    rw [hxy, hf, hf, hf, map_mul, map_mul]
    calc ρ p₁ * ρ a * W * (ρ b * ρ q₂) = ρ p₁ * (ρ a * W * ρ b) * ρ q₂ := by group
      _ = ρ p₁ * (W * (ρ p₂ * ρ q₁) * W) * ρ q₂ := by rw [hW]
      _ = ρ p₁ * W * ρ p₂ * (ρ q₁ * W * ρ q₂) := by group
  obtain ⟨Φ, hΦ⟩ := groupChunk_extend C f hmul hc
  refine ⟨Φ, fun p => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hc {1}
    obtain ⟨a, b, hab⟩ := hu 1 (by simp)
    rw [one_mul] at hab
    have e1 : (p : G) * u = ((p * a : P) : G) * w * b := by
      rw [hab]
      push_cast
      group
    rw [hΦ p u ⟨a, b, hab⟩ ⟨p * a, b, e1⟩, e1, hab, hf, hf, map_mul]
    group
  · obtain ⟨u, hu⟩ := hc {1, w}
    obtain ⟨a, b, hab⟩ := hu 1 (by simp)
    rw [one_mul] at hab
    obtain ⟨c, d, hcd⟩ := hu w (by simp)
    have hin : ∃ p₁ p₂ : P, w * (a : G) * w = p₁ * w * p₂ :=
      ⟨c, d * b⁻¹, by
        calc w * (a : G) * w = w * u * (b : G)⁻¹ := by rw [hab]; group
          _ = (c : G) * w * d * (b : G)⁻¹ := by rw [hcd]
          _ = (c : G) * w * ((d * b⁻¹ : P) : G) := by push_cast; group⟩
    obtain ⟨r₁, r₂, hr, hW⟩ := hb a hin
    have e1 : w * u = (r₁ : G) * w * ((r₂ * b : P) : G) := by
      rw [hab]
      push_cast
      calc w * ((a : G) * w * b) = w * a * w * b := by group
        _ = (r₁ : G) * w * ((r₂ : G) * b) := by rw [hr]; group
    rw [hΦ w u ⟨a, b, hab⟩ ⟨c, d, hcd⟩, e1, hab, hf, hf, map_mul]
    calc ρ r₁ * W * (ρ r₂ * ρ b) * (ρ a * W * ρ b)⁻¹ = (ρ r₁ * W * ρ r₂) * (ρ a * W)⁻¹ := by group
      _ = (W * ρ a * W) * (ρ a * W)⁻¹ := by rw [hW]
      _ = W := by group

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfFieldPointRelationProperStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_of_fieldPoint_relation_proper : ∀ (Q P S : Scheme.{0}) (q : Q ⟶ S) (p : P ⟶ S) [IsProper p] [IsNoetherian Q] [GlobalTheory.IsNormalScheme Q] (R : ∀ (K : Type) [Field K], (Sp K ⟶ Q) → (Sp K ⟶ P) → Prop), (∀ (K : Type) [Field K] (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → z ≫ q = w ≫ p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! w, R K z w) → (∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → R K' (spMap ι ≫ z) (spMap ι ≫ w)) → (∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ Q) (v : Sp A ⟶ P), u ≫ q = v ≫ p → R (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) → R (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v)) → ∃ h : Q ⟶ P, h ≫ p = q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), R K z (z ≫ h) := by
  first | exact @GlobalTheory.FieldPointGraph.exists_hom_of_rel | exact GlobalTheory.FieldPointGraph.exists_hom_of_rel | (intros; apply GlobalTheory.FieldPointGraph.exists_hom_of_rel <;> assumption)
end

