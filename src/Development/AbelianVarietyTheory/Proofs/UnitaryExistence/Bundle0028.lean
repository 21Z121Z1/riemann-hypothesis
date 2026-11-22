import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicNormWeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsPreconnectedBlockUnits
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNatMulInt
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClassSumCompare

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
open scoped TensorProduct nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem tmul_eq (a : AdF E) (e : E) :
    (show AdE E from a ⊗ₜ[maximalRealSubfield E] e) = inclF E a * diagE E e := by
  show a ⊗ₜ[maximalRealSubfield E] e = (a ⊗ₜ[maximalRealSubfield E] (1 : E)) * ((1 : AdF E) ⊗ₜ[maximalRealSubfield E] e)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem incl_mem {a : AdF E} (ha : ∀ v : Plc E, a v ∈ v.adicCompletionIntegers (maximalRealSubfield E)) :
    inclF E a ∈ intAd E := Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)

theorem diag_int_mem (o : 𝓞 E) : diagE E (o : E) ∈ intAd E := Subring.subset_closure (Or.inr ⟨o, rfl⟩)

theorem mem_hat_of_mem {x : AdE E} (hx : x ∈ intAd E) :
    (show GlobalTheory.AdLat.RA (maximalRealSubfield E) E from x) ∈
      GlobalTheory.AdLat.hat1 (maximalRealSubfield E) ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  have h1 : (1 : E) ∈ ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := FractionalIdeal.one_mem_one _
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, ha, rfl⟩ | ⟨o, rfl⟩
    · exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral _ ha h1
    · exact GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
  | zero => exact zero_mem _
  | one => exact GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet _ h1
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy =>
    refine GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem _ (fun a ha b hb => ?_) hx hy
    have := FractionalIdeal.mul_mem_mul ha hb
    rwa [mul_one] at this

theorem diag_mem_iff (x : E) : diagE E x ∈ intAd E ↔ ∃ o : 𝓞 E, (o : E) = x := by
  refine ⟨fun h => ?_, ?_⟩
  · exact (FractionalIdeal.mem_one_iff _).1
      ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff (maximalRealSubfield E) 1 x).1 (mem_hat_of_mem h))
  · rintro ⟨o, rfl⟩; exact diag_int_mem o

theorem star_diag (x : E) : star (diagE E x) = diagE E (IsCMField.complexConj E x) := rfl

theorem star_incl (a : AdF E) : star (inclF E a) = inclF E a := by
  show adConj E (a ⊗ₜ 1) = a ⊗ₜ 1
  simp [adConj]

theorem conj_int (a : 𝓞 E) : ∃ b : 𝓞 E, (b : E) = IsCMField.complexConj E (a : E) :=
  ⟨RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv a, rfl⟩

theorem star_mem {x : AdE E} (hx : x ∈ intAd E) : star x ∈ intAd E := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, ha, rfl⟩ | ⟨o, rfl⟩
    · rw [star_incl]; exact incl_mem ha
    · show star (diagE E o) ∈ _
      rw [star_diag, diag_mem_iff]; exact conj_int o
  | zero => rw [star_zero]; exact zero_mem _
  | one => rw [star_one]; exact one_mem _
  | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
  | neg x _ hx => rw [star_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [star_mul]; exact mul_mem hy hx

theorem exists_nat_mul_int (e : E) : ∃ k : ℕ, 0 < k ∧ ∃ o : 𝓞 E, (o : E) = k * e := by
  obtain ⟨k, hk, h⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
  refine ⟨k.natAbs, Int.natAbs_pos.2 hk, ?_⟩
  have h1 := h e (by simp)
  rcases Int.natAbs_eq k with h2 | h2
  · refine ⟨⟨k • e, h1⟩, ?_⟩
    show k • e = _
    conv_lhs => rw [h2]
    simp
  · refine ⟨⟨-(k • e), h1.neg⟩, ?_⟩
    show -(k • e) = _
    conv_lhs => rw [h2]
    simp

theorem diag_algebraMap (x : maximalRealSubfield E) :
    diagE E (algebraMap _ E x) = inclF E (algebraMap _ (AdF E) x) := by
  show (1 : AdF E) ⊗ₜ[maximalRealSubfield E] (algebraMap _ E x) = (algebraMap _ (AdF E) x) ⊗ₜ[maximalRealSubfield E] (1 : E)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_tmul_int (a : AdF E) (e : E) : ∃ (t : maximalRealSubfield E) (o : 𝓞 E),
    inclF E a * diagE E e = inclF E (algebraMap _ (AdF E) t * a) * diagE E (o : E) := by
  obtain ⟨k, hk, o, ho⟩ := exists_nat_mul_int e
  refine ⟨(k : maximalRealSubfield E)⁻¹, o, ?_⟩
  have hk' : (k : E) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  rw [map_mul, ← diag_algebraMap, ho, mul_comm (diagE E _) (inclF E a), mul_assoc, ← map_mul]
  congr 2
  rw [map_inv₀, map_natCast]
  field_simp

theorem approx (m : ℕ) (hm : 0 < m) (x : AdE E) : ∃ e : E, ∃ u ∈ intAd E, x = diagE E e + (m : AdE E) * u := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by show (0 : AdE E) = _; simp⟩
  | tmul a e =>
    obtain ⟨t, o, h⟩ := exists_tmul_int a e
    obtain ⟨x, a', ha', h'⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul _ m hm (algebraMap _ (AdF E) t * a)
    refine ⟨algebraMap _ E x * o, inclF E a' * diagE E o, mul_mem (incl_mem ha') (diag_int_mem o), ?_⟩
    refine (tmul_eq a e).trans ?_
    rw [h, h', map_add, map_mul, diag_algebraMap, map_nsmul, nsmul_eq_mul]
    ring
  | add x y hx hy =>
    obtain ⟨e, u, hu, hx⟩ := hx
    obtain ⟨e', u', hu', hy⟩ := hy
    refine ⟨e + e', u + u', add_mem hu hu', ?_⟩
    show (show AdE E from x) + (show AdE E from y) = _
    rw [show (show AdE E from x) = _ from hx, show (show AdE E from y) = _ from hy, map_add]
    ring

end GlobalTheory.ClassSumCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPeriodMulVec
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PeriodLin

open NumberField AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in

theorem _root_.GlobalTheory.PeriodLin.exists_period_mulVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P → IsUnit h₀.det → (∀ j j', h₀ j j' ≠ 0 → ty j = ty j') → ∃ P' : D.La →+ (Fin g → ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P' ∧ ∀ a, P' a = h₀ *ᵥ P a := by
  intro E _ _ _ H D g ty P h₀ hP hu hty
  refine ⟨(h₀.mulVecLin).toAddMonoidHom.comp P,
    _root_.GlobalTheory.PeriodConn.isPeriod_mulVec hP (isUnit_iff_ne_zero.mp hu) fun i j hij => ?_,
    fun a => rfl⟩
  by_contra hne
  exact hij (hty i j hne)

end GlobalTheory.PeriodLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_module_universal_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X), ∃ (N : Type) (_ : AddCommGroup N) (_ : Module S N) (v : N → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (ρ : 𝓞 E →+* Module.End S N), Function.Injective v ∧ (∀ w, IsTanAt x w ↔ w ∈ Set.range v) ∧ (∀ (n : ℕ) (b : Fin n → N) (a : Fin n → S) w, IsCombAt x (fun i => v (b i)) a w ↔ w = v (∑ i, a i • b i)) ∧ (∀ a m, v (ρ a m) = v m ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (s : S) m, v (s • m) = spMap (epsMul s) ≫ v m := by
  first | exact @GlobalTheory.TanMod.exists_tangent_module | exact GlobalTheory.TanMod.exists_tangent_module | (intros; apply GlobalTheory.TanMod.exists_tangent_module <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTriangularFrameRingOverTestRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem exists_testRing_universal_partially_invertible (K : Type) [Field K] (σ : Type) [Finite σ]
    (D : σ → Prop) (p : TRing K) :
    ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (x : σ → A.R), (∀ i, D i → IsUnit (x i)) ∧
      ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : p.R →ₐ[K] T) (t : σ → T), (∀ i, D i → IsUnit (t i)) →
        ∃! k : A.R →ₐ[K] T, k.comp π = ψ ∧ ∀ i, k (x i) = t i := by
  classical
  have := Fintype.ofFinite σ
  obtain ⟨hft, hred⟩ := (reduced_finiteType_iff_testRing K).2 p
  let P := MvPolynomial σ p.R
  let f : P := ∏ i ∈ Finset.univ.filter D, MvPolynomial.X i
  let B := Localization.Away f
  have hPred : _root_.IsReduced P := ⟨fun q hq => by
    ext i
    exact IsReduced.eq_zero _ (MvPolynomial.isNilpotent_iff.1 hq i)⟩
  have hBred : _root_.IsReduced B := isReduced_localizationPreserves (Submonoid.powers f) B hPred
  have hPft : Algebra.FiniteType K P := Algebra.FiniteType.trans hft inferInstance
  have hBft : Algebra.FiniteType K B :=
    Algebra.FiniteType.trans hPft (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) B)
  obtain ⟨A, ⟨e⟩⟩ := (reduced_finiteType_iff_testRing K).1 B hBft hBred
  let emb : P →ₐ[K] B := IsScalarTower.toAlgHom K P B
  let c : p.R →ₐ[K] P := IsScalarTower.toAlgHom K p.R P
  refine ⟨A, (e.symm : B →ₐ[K] A.R).comp (emb.comp c), fun i => e.symm (emb (MvPolynomial.X i)), ?_, ?_⟩
  · intro i hi
    refine IsUnit.map e.symm ?_
    have hf : IsUnit (emb f) := IsLocalization.Away.algebraMap_isUnit f
    refine isUnit_of_dvd_unit (map_dvd emb ?_) hf
    exact Finset.dvd_prod_of_mem _ (by simp [hi])
  · intro T _ _ ψ t ht
    let φ : P →ₐ[K] T := MvPolynomial.aevalTower ψ t
    have hφ : IsUnit (φ f) := by
      simp only [f, map_prod]
      refine IsUnit.prod_iff.2 fun i hi => ?_
      simp only [φ, P, MvPolynomial.aevalTower_X]
      exact ht i (by simpa using hi)
    have hφ' : ∀ y : Submonoid.powers f, IsUnit (φ y) := by
      rintro ⟨_, n, rfl⟩
      simpa using hφ.pow n
    let k₀ : B →ₐ[K] T := IsLocalization.liftAlgHom (M := Submonoid.powers f) hφ'
    have hk₀ : ∀ q, k₀ (emb q) = φ q := fun q => IsLocalization.lift_eq hφ' q
    refine ⟨k₀.comp (e : A.R →ₐ[K] B), ⟨?_, ?_⟩, ?_⟩
    · refine AlgHom.ext fun r => ?_
      change k₀ (e (e.symm (emb (c r)))) = ψ r
      rw [AlgEquiv.apply_symm_apply, hk₀]
      exact MvPolynomial.aevalTower_algebraMap ψ t r
    · intro i
      change k₀ (e (e.symm (emb (MvPolynomial.X i)))) = t i
      rw [AlgEquiv.apply_symm_apply, hk₀]
      exact MvPolynomial.aevalTower_X ψ t i
    · rintro k ⟨h1, h2⟩
      have h3 : ∀ q, k (e.symm (emb q)) = φ q := by
        intro q
        induction q using MvPolynomial.induction_on with
        | C r =>
          have := AlgHom.congr_fun h1 r
          exact this.trans (MvPolynomial.aevalTower_algebraMap ψ t r).symm
        | add a b ha hb => simp only [map_add, ha, hb]
        | mul_X a i ha =>
          simp only [map_mul, ha, h2]
          rw [show φ (MvPolynomial.X i) = t i from MvPolynomial.aevalTower_X ψ t i]
      have h4 : (k.comp (e.symm : B →ₐ[K] A.R)).toRingHom = k₀.toRingHom :=
        IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun q => (h3 q).trans (hk₀ q).symm)
      refine AlgHom.ext fun a => ?_
      have := RingHom.congr_fun h4 (e a)
      simpa using this

theorem exists_testRing_triRing :
    ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (p : TRing K), ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), TriRing m π X s := by
  intro K _ J _ m p
  classical
  obtain ⟨A, π, x, hx, hu⟩ := exists_testRing_universal_partially_invertible K
    (Option (Σ τ : J, {q : Fin (m τ) × Fin (m τ) // q.2 ≤ q.1}))
    (fun o => o.elim True fun z => z.2.1.1 = z.2.1.2) p
  refine ⟨A, π, fun τ => Matrix.of fun i j => if h : j ≤ i then x (some ⟨τ, ⟨(i, j), h⟩⟩) else 0,
    (hx none trivial).unit, ?_, ?_, ?_⟩
  · intro τ i
    simp only [Matrix.of_apply, le_refl, dif_pos]
    exact hx _ rfl
  · intro τ i j hij
    exact dif_neg (not_le.2 hij)
  · intro T _ _ ψ g a hg1 hg2
    obtain ⟨k, ⟨hk1, hk2⟩, hk3⟩ := hu T ψ (fun o => o.elim (a : T) fun z => g z.1 z.2.1.1 z.2.1.2) (by
      rintro (_ | ⟨τ, ⟨i, j⟩, h⟩) hD
      · exact a.isUnit
      · obtain rfl : i = j := hD
        exact hg1 τ i)
    refine ⟨k, ⟨hk1, fun τ => ?_, hk2 none⟩, ?_⟩
    · ext i j
      simp only [Matrix.map_apply, Matrix.of_apply]
      by_cases h : j ≤ i
      · rw [dif_pos h]
        exact hk2 _
      · rw [dif_neg h, map_zero, hg2 τ i j (not_le.1 h)]
    · rintro k' ⟨h1, h2, h3⟩
      refine hk3 k' ⟨h1, ?_⟩
      rintro (_ | ⟨τ, ⟨i, j⟩, h⟩)
      · exact h3
      · have := congrFun (congrFun (h2 τ) i) j
        simp only [Matrix.map_apply, Matrix.of_apply, dif_pos h] at this
        exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueCmEmbeddingEigenvectorSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem existsUnique_eigen_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (N : Type) [AddCommGroup N] [Module S N] (ρ : 𝓞 E →+* Module.End S N) (m : N), ∃! f : (E →+* ℂ) → N, (∀ τ a, ρ a (f τ) = algebraMap c.F S (embK c τ a) • f τ) ∧ ∑ τ, f τ = m := by
  intro E _ _ _ H l c S _ _ N _ _ ρ m
  classical
  have hσ₀ : Function.Injective (fun τ : E →+* ℂ => embK c τ) := fun τ τ' h =>
    (EigenSplit.isSplitting_complex E).injective
      (RingHom.ext fun a => by
        have h1 := embK_coe c τ a
        have h2 := embK_coe c τ' a
        have h3 : embK c τ a = embK c τ' a := RingHom.congr_fun h a
        exact h1.symm.trans ((congrArg _ h3).trans h2))
  have hσ : EigenSplit.IsSplitting fun τ : E →+* ℂ => (algebraMap c.F S).comp (embK c τ) :=
    EigenSplit.isSplitting_of_isDomain hσ₀ (NumberField.Embeddings.card E ℂ) (algebraMap c.F S) (by
      simpa using (EigenSplit.isUnit_discr_of_charZero (E := E) c.F).map (algebraMap c.F S))
  have hI := EigenSplit.isInternal_eigenSub hσ ρ
  let A := fun τ : E →+* ℂ => EigenSplit.eigenSub ρ ((algebraMap c.F S).comp (embK c τ))
  have hsum : ∀ x : DirectSum _ (fun τ => A τ), DirectSum.coeAddMonoidHom A x = ∑ τ, (x τ : N) :=
    fun x => by
      conv_lhs => rw [← DirectSum.sum_univ_of x]
      simp [map_sum, DirectSum.coeAddMonoidHom_of]
  obtain ⟨x, hx⟩ := hI.2 m
  refine ⟨fun τ => x τ, ⟨fun τ a => EigenSplit.mem_eigenSub.1 (x τ).2 a, (hsum x).symm.trans hx⟩, ?_⟩
  rintro f ⟨hf, hm⟩
  let y : DirectSum _ (fun τ => A τ) :=
    DFinsupp.equivFunOnFintype.symm fun τ => ⟨f τ, EigenSplit.mem_eigenSub.2 (hf τ)⟩
  have hy : y = x := hI.1 (((hsum y).trans hm).trans hx.symm)
  funext τ
  rw [← hy]
  rfl

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueGlueDualStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_glue_dualNumber : ∀ (S : Type) [CommRing S] (Y : Scheme.{0}) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ w : ∀ i, Sp (DualNumber (Localization.Away (h i))) ⟶ Y, (∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j)) (β : Localization.Away (h j) →+* Localization.Away (h i * h j)), α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → spMap (dualMap α) ≫ w i = spMap (dualMap β) ≫ w j) → ∃! w₀ : Sp (DualNumber S) ⟶ Y, ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = w i := by
  first | exact @GlobalTheory.Frames.existsUnique_glue_dual | exact GlobalTheory.Frames.existsUnique_glue_dual | (intros; apply GlobalTheory.Frames.existsUnique_glue_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (a : S) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s : LB.Sec (PPx x), ∃! s' : LB.Sec (PPx x'), SecBC φ a x x' s s' := by
  first | exact @GlobalTheory.Frames.SecPull.existsUnique_secBC | exact GlobalTheory.Frames.SecPull.existsUnique_secBC | (intros; apply GlobalTheory.Frames.SecPull.existsUnique_secBC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.IsoExt

theorem exists_gl_of_equiv {E : Type} [Field E] [NumberField E] {r : ℕ} {L L' : Type}
    [AddCommGroup L] [Module (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L']
    (φ : L →ₗ[𝓞 E] (Fin r → E)) (φ' : L' →ₗ[𝓞 E] (Fin r → E))
    (hφ : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hφ' : Function.Injective φ') (hspan' : Submodule.span E (Set.range φ') = ⊤)
    (gam : L ≃ₗ[𝓞 E] L') : ∃ γ : GL (Fin r) E,
      ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ' (gam v) := by
  obtain ⟨A, hA⟩ := GlobalTheory.FrameFibre.exists_matrix φ hφ hspan (φ' ∘ₗ gam.toLinearMap)
  obtain ⟨B, hB⟩ := GlobalTheory.FrameFibre.exists_matrix φ' hφ' hspan' (φ ∘ₗ gam.symm.toLinearMap)
  have hA' : ∀ v, A *ᵥ φ v = φ' (gam v) := hA
  have hB' : ∀ v, B *ᵥ φ' v = φ (gam.symm v) := hB
  have hAB : A * B = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range hspan' fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hB', hA',
      Matrix.one_mulVec, LinearEquiv.apply_symm_apply]
  exact ⟨⟨A, B, hAB, mul_eq_one_comm.1 hAB⟩, hA'⟩

theorem exists_unitary_of_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (gam : D.La ≃ₗ[𝓞 E] D'.La), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) → (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) → ∃ γ : GL (Fin r) E, (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ ∀ a, φ' (gam a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  intro E _ _ _ H D D' r ξ Gm φ φ' gam _ hl hl' hiso
  obtain ⟨γ, hγ⟩ := exists_gl_of_equiv φ φ' hl.1 hl.2.1 hl'.1 hl'.2.1 gam
  refine ⟨γ, ?_, fun a => (hγ a).symm⟩
  by_cases hξ : ξ = 0
  · have h0 : ∀ x : D.La, x = 0 := fun x => by
      apply D.unimod.1
      rw [map_zero]
      refine LinearMap.ext fun y => ?_
      have h := hl.2.2.2.2 x y
      rw [hξ, zero_mul, map_zero] at h
      exact_mod_cast h
    have h1 : ∀ u : Fin r → E, u = 0 := fun u => by
      have hu : u ∈ Submodule.span E (Set.range φ) := by rw [hl.2.1]; trivial
      have hle : Submodule.span E (Set.range φ) ≤ ⊥ := Submodule.span_le.2 (by
        rintro _ ⟨x, rfl⟩
        rw [h0 x, map_zero]
        exact Submodule.zero_mem _)
      exact hle hu
    intro u v
    rw [h1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u), h1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v), h1 u,
      h1 v]
  · exact GlobalTheory.FrameFibre.herm_of_trace φ hl.2.1 Gm γ ξ hξ fun v w => by
      rw [hγ, hγ, ← hl.2.2.2.2, ← hl'.2.2.2.2, hiso]

end GlobalTheory.IsoExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem isDerivAt0_ex_isTanAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → (∀ w v, IsDerivAt0 (fun z => (F.ex k P z).left) w v → IsTanAt (F.u k P) v) ∧ (∀ w, ∃! v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsDerivAt0 (fun z => (F.ex k P z).left) w v) ∧ ∀ v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsTanAt (F.u k P) v → ∃! w, IsDerivAt0 (fun z => (F.ex k P z).left) w v := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P hP
  have h0 := (F.ex_ker k P hP 0).2 (zero_mem _)
  refine ⟨fun w v hv => ⟨((HolHom.isDerivAt0_iff _ _ _).1 hv).over, ?_⟩, fun w => ?_, fun v hv => ?_⟩
  · exact hv.1.trans (congrArg (·.left) h0)
  · obtain ⟨v, hv, -⟩ := (F.ex_diff k P hP).1 w
    exact ⟨v.left, hv, fun v' hv' =>
      ((HolHom.isDerivAt0_iff _ _ _).1 hv').unique ((HolHom.isDerivAt0_iff _ _ _).1 hv)⟩
  · exact (F.ex_diff k P hP).2 (Over.homMk v hv.1) (hv.2.trans (congrArg (·.left) h0).symm)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameChange_comm_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T) (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : S), FrChg g a y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ a) z z') := by
  first | exact @GlobalTheory.Frames.ChgBC.frChg_baseChange | exact GlobalTheory.Frames.ChgBC.frChg_baseChange | (intros; apply GlobalTheory.Frames.ChgBC.frChg_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIffStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_baseChange_unique_refl_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), (∀ z z' : FrPt Xo c T, FrMap φ y z → FrMap φ y z' → z = z') ∧ FrMap (AlgHom.id c.F S) y y ∧ ∀ z : FrPt Xo c T, FrMap φ y z ↔ (z.x = spMap φ.toRingHom ≫ y.x ∧ (∀ τ i, z.u τ i = spMap (dualMap φ.toRingHom) ≫ y.u τ i) ∧ SecBC φ.toRingHom 1 y.x z.x y.s z.s) := by
  first | exact @GlobalTheory.Frames.frMap_unique_refl_iff | exact GlobalTheory.Frames.frMap_unique_refl_iff | (intros; apply GlobalTheory.Frames.frMap_unique_refl_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralIff
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

set_option autoImplicit false

namespace GlobalTheory.IntegralData

theorem integralIff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntegralIffSt Xo c := by
  intro E _ _ _ H Dw l Xo c T io y
  constructor
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩
    exact ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩⟩
  · rintro ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩

end GlobalTheory.IntegralData
end

