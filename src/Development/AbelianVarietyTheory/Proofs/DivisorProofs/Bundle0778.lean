import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0087
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0766
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0767
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0775
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersSplitAugmentationExtension

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsFlatNormalStageAtOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsOfConstants_flat_normal_stage_at_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (sA : A), sA ≠ 0 →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsIntegrallyClosed B') (_ : Algebra A' B') (_ : Module.Flat A' B')
      (ι : A →+* A') (α : A' →+* T) (β : Localization.AtPrime QA →+* B') (γ : B' →+* O),
      (algebraMap A' B').comp ι = β.comp (algebraMap A (Localization.AtPrime QA)) ∧
      γ.comp β = jA ∧ γ.comp (algebraMap A' B') = (algebraMap T O).comp α ∧ ι sA ≠ 0 ∧
      ∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → ι sA ∈ 𝔭 →
        (𝔭.map (algebraMap A' B')).IsPrime := by
  first | (exact @GlobalTheory.GoodStageOrigin.good_stage) | (exact GlobalTheory.GoodStageOrigin.good_stage) | (intros; apply GlobalTheory.GoodStageOrigin.good_stage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEmbeddingDeterminantValue
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem ringHom_eq_of_eq_on_generator {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
    {α : Λ} (hα : Algebra.adjoin ℤ_[p] {α} = ⊤) (σ τ : Λ →+* O) (h : σ α = τ α) : σ = τ := by
  have hbase : σ.comp (algebraMap ℤ_[p] Λ) = τ.comp (algebraMap ℤ_[p] Λ) :=
    GlobalTheory.padicInt_ringHom_ext_of_isHausdorff p O _ _
  ext x
  have hx : x ∈ Algebra.adjoin ℤ_[p] {α} := hα ▸ Algebra.mem_top
  refine Algebra.adjoin_induction (fun y hy => ?_) (fun r => ?_) (fun y z _ _ hy hz => ?_)
    (fun y z _ _ hy hz => ?_) hx
  · rw [Set.mem_singleton_iff.1 hy]; exact h
  · exact congrArg (fun f : ℤ_[p] →+* O => f r) hbase
  · rw [map_add, map_add, hy, hz]
  · rw [map_mul, map_mul, hy, hz]

theorem shift_linear_isom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ₀ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ), ∃ r : NNReal, r ≠ 0 ∧ IsShift C v D ((γ : O →+* O).comp τ₀) r ∧ Real.log r = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ := by
  classical
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ τ₀
  obtain ⟨α, hα⟩ := GlobalTheory.MonoGen.exists_adjoin_eq_top_padicInt p Λ
  obtain ⟨κ₀, κ', hlin⟩ := GlobalTheory.T.psi_embedding_determinant_property p C v O hv ε hε Λ τ₀
  obtain ⟨hfin, -⟩ := GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ
  haveI := hfin
  letI := Fintype.ofFinite (Λ →+* O)
  let c : (Λ →+* O) → ℝ := fun σ => if σ = τ₀ then 0 else
    Real.log (v (algebraMap O C (τ₀ α) - algebraMap O C (σ α)))
  refine ⟨κ₀, fun σ => κ' σ - c σ, ?_⟩
  intro γ hγ N h hh D
  obtain ⟨γC, hγC, hvγ⟩ := hγ
  set τ : Λ →+* O := (γ : O →+* O).comp τ₀ with hτ
  obtain ⟨⟨ι, hι, -⟩, -⟩ := GlobalTheory.T.tilt_lattice_bound_second p C v O hv ε hε Λ N h hh D τ
  obtain ⟨lam, hlam, hlat⟩ := GlobalTheory.T.tilt_lattice_bound_third p C v O hv ε hε Λ N h hh D τ ι hι
  have hsh := GlobalTheory.T.dvr_alpha_determinant_valuation p C v O hv ε hε Λ α hα N h hh D τ ι lam hι hlat
  have hlog := hlin γ ⟨γC, hγC, hvγ⟩ N h hh D ι lam hι hlam hlat

  have hsep : ∀ σ : Λ →+* O, σ ≠ τ →
      v (algebraMap O C (τ α) - algebraMap O C (σ α)) ≠ 0 := by
    intro σ hσ
    refine (Valuation.ne_zero_iff v).mpr ?_
    rw [← map_sub]
    intro h0
    apply hσ
    refine (ringHom_eq_of_eq_on_generator hα σ τ ?_)
    have h1 : τ α - σ α = 0 := hv.hom_inj (by rw [h0, map_zero])
    exact (sub_eq_zero.1 h1).symm
  have hv0 : v lam ≠ 0 := (Valuation.ne_zero_iff v).mpr hlam
  set P : NNReal := ∏ᶠ σ : {σ : Λ →+* O // σ ≠ τ},
    v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1 with hP
  have hPe : P = ∏ σ : {σ : Λ →+* O // σ ≠ τ},
      v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1 :=
    finprod_eq_prod_of_fintype _
  have hP0 : P ≠ 0 := by
    rw [hPe]
    exact Finset.prod_ne_zero_iff.mpr fun σ _ => pow_ne_zero _ (hsep σ.1 σ.2)
  refine ⟨v lam * P⁻¹, mul_ne_zero hv0 (inv_ne_zero hP0), hsh, ?_⟩

  have hlogP : Real.log (P : ℝ) = ∑ σ : {σ : Λ →+* O // σ ≠ τ},
      (D.lieRank σ.1 : ℝ) * Real.log (v (algebraMap O C (τ α) - algebraMap O C (σ.1 α))) := by
    rw [hPe, NNReal.coe_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun σ _ => ?_
      rw [NNReal.coe_pow, Real.log_pow]
    · intro σ _
      exact_mod_cast pow_ne_zero _ (hsep σ.1 σ.2)
  have hlr : Real.log ((v lam * P⁻¹ : NNReal) : ℝ) = Real.log (v lam) - Real.log (P : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_inv, Real.log_mul, Real.log_inv, sub_eq_add_neg]
    · exact_mod_cast hv0
    · exact inv_ne_zero (by exact_mod_cast hP0)

  let e : (Λ →+* O) ≃ (Λ →+* O) :=
    { toFun := fun σ => (γ : O →+* O).comp σ
      invFun := fun σ => (γ.symm : O →+* O).comp σ
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  have hsub : ∑ σ : {σ : Λ →+* O // σ ≠ τ},
      (D.lieRank σ.1 : ℝ) * Real.log (v (algebraMap O C (τ α) - algebraMap O C (σ.1 α))) =
      ∑ σ : Λ →+* O, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * c σ := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun σ => σ ≠ τ) (by simp)
      (fun σ => (D.lieRank σ : ℝ) * Real.log (v (algebraMap O C (τ α) - algebraMap O C (σ α)))),
      Finset.sum_filter]
    symm
    refine Fintype.sum_equiv e _ _ fun σ => ?_
    show (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * c σ = if (γ : O →+* O).comp σ ≠ τ then _ else 0
    by_cases hσ : σ = τ₀
    · have heq : (γ : O →+* O).comp σ = τ := by rw [hσ]
      rw [if_neg (not_not.2 heq)]
      simp only [c, if_pos hσ, mul_zero]
    · have hne : (γ : O →+* O).comp σ ≠ τ := by
        intro heq
        apply hσ
        ext x
        exact γ.injective (congrArg (fun f : Λ →+* O => f x) heq)
      rw [if_pos hne]
      simp only [c, if_neg hσ]
      have hiso : v (algebraMap O C (τ₀ α) - algebraMap O C (σ α)) =
          v (algebraMap O C (γ (τ₀ α)) - algebraMap O C (γ (σ α))) := by
        rw [← hγC, ← hγC, ← map_sub γC, hvγ]
      rw [hiso]
      rfl
  rw [hlr, hlogP, hsub, hlog, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EopPreservesLeftUnipotentInvarianceStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eop_preserves_left_unipotent_invariance : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (f : Sm E a), (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a) (x : BlockIx a r → Ad E) (g : GA E a), (Eop τ i j f).1 (unip x * g) = (Eop τ i j f).1 g := by
  first | exact @GlobalTheory.CuspRep.UnipInv.Eop_unip_left | exact GlobalTheory.CuspRep.UnipInv.Eop_unip_left | (intros; apply GlobalTheory.CuspRep.UnipInv.Eop_unip_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfShearAutomorphismLiftNilpotentStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_shear_automorphism_lift_nilpotent : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left), l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i →
    ∀ (m : X ⊗ X ⟶ X), l ≫ m.left = (μ[A₀]).left ≫ i → IsIso (lift (fst X X) m) →
    ∀ (P : Over (Sp R)) (P₀ : Over (Sp R₀)) (k : P₀.left ⟶ P.left), IsPullback k P₀.hom P.hom (spMap π) →
    Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
    ∀ (ε : Sp R ⟶ P.left), ε ≫ P.hom = 𝟙 _ → ∀ (f f' : P ⟶ X), k ≫ f.left = k ≫ f'.left → ε ≫ f.left = ε ≫ f'.left → f = f' := by
  first | exact @GlobalTheory.ShearLift.eq_of_shear | exact GlobalTheory.ShearLift.eq_of_shear | (intros; apply GlobalTheory.ShearLift.eq_of_shear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOddEllipticOfTendsto
section
open Filter PeriodPair Polynomial
open scoped Topology

namespace GlobalTheory

private lemma eq_zero_of_tendsto_eval_cobounded {B : ℂ[X]} {l : Filter ℂ} [l.NeBot] {u : ℂ → ℂ}
    (hu : Tendsto u l (Bornology.cobounded ℂ))
    (h : Tendsto (fun z ↦ B.eval (u z)) l (𝓝 0)) : B = 0 := by
  by_cases hd : 0 < B.degree
  · exfalso
    have h1 := B.tendsto_norm_atTop hd (tendsto_norm_atTop_iff_cobounded.mpr hu)
    have h2 := h.norm
    exact h1.not_tendsto (disjoint_nhds_atTop _).symm h2
  · rw [eq_C_of_degree_le_zero (not_lt.mp hd)] at h ⊢
    simp only [eval_C] at h
    rw [tendsto_nhds_unique tendsto_const_nhds h, C_0]

private lemma exists_eq_mul_of_three_roots {A : ℂ[X]} {a b c : ℂ} (hab : b ≠ a) (hac : c ≠ a)
    (hbc : c ≠ b) (ha : A.eval a = 0) (hb : A.eval b = 0) (hc : A.eval c = 0) :
    ∃ B : ℂ[X], A = (X - C a) * ((X - C b) * ((X - C c) * B)) := by
  obtain ⟨A₁, rfl⟩ := dvd_iff_isRoot.mpr ha
  have hb₁ : A₁.eval b = 0 := by simpa [sub_eq_zero, hab] using hb
  obtain ⟨A₂, rfl⟩ := dvd_iff_isRoot.mpr hb₁
  have hc₂ : A₂.eval c = 0 := by simpa [sub_eq_zero, hac, hbc] using hc
  obtain ⟨B, rfl⟩ := dvd_iff_isRoot.mpr hc₂
  exact ⟨B, rfl⟩

theorem eq_zero_of_odd_elliptic_of_tendsto : ∀ (L : PeriodPair) (f : ℂ → ℂ), (∀ z, z ∉ L.lattice → DifferentiableAt ℂ f z) → (∀ z l, z ∉ L.lattice → l ∈ L.lattice → f (z + l) = f z) → (∀ z, z ∉ L.lattice → f (-z) = -f z) → Filter.Tendsto (fun z : ℂ => z ^ 3 * f z) (𝓝[≠] 0) (𝓝 0) → ∀ z, z ∉ L.lattice → f z = 0 := by
  classical
  intro L f hd hp ho ht
  let g : ℂ → ℂ := fun z ↦ if z ∈ L.lattice then 0 else f z ^ 2
  have hgd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z := fun z hz ↦ by
    refine ((hd z hz).pow 2).congr_of_eventuallyEq ?_
    filter_upwards [eventually_notMem_periodLattice L hz] with w hw
    simp [g, hw]
  have hgp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z := fun z l hl ↦ by
    by_cases hz : z ∈ L.lattice
    · simp [g, hz, add_mem hz hl]
    · simp [g, hz, L.lattice.add_mem_iff_left hl, hp z l hz hl]
  have hge : ∀ z, g (-z) = g z := fun z ↦ by
    by_cases hz : z ∈ L.lattice
    · simp [g, hz]
    · simp [g, hz, ho z hz]
  have hgt : Tendsto (fun z : ℂ ↦ z ^ 6 * g z) (𝓝[≠] 0) (𝓝 0) := by
    have h1 := ht.pow 2
    rw [zero_pow two_ne_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw
    simp only [g, hw, if_false]
    ring
  have hgm : MeromorphicAt g 0 := by
    refine ⟨6, Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_⟩
    · filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw
      have := hgd w hw
      fun_prop
    · rw [continuousAt_iff_punctured_nhds]
      simpa using hgt
  obtain ⟨A, hA⟩ := exists_eq_polynomial_weierstrassP L hgm hgd hgp hge
  have hhalf : ∀ z ∉ L.lattice, z + z ∈ L.lattice → A.eval (℘[L] z) = 0 := fun z hz h2 ↦ by
    have h1 := hp (-z) (z + z) (by simpa using hz) h2
    rw [ho z hz, show -z + (z + z) = z by ring, CharZero.eq_neg_self_iff] at h1
    rw [← hA z hz]
    simp [g, h1]
  have key : ∀ a b : ℚ, (a * L.ω₁ + b * L.ω₂ : ℂ) ∈ L.lattice ↔ a.den = 1 ∧ b.den = 1 :=
    fun a b ↦ L.mul_ω₁_add_mul_ω₂_mem_lattice
  let p : ℚ → ℚ → ℂ := fun a b ↦ a * L.ω₁ + b * L.ω₂
  have padd : ∀ a b c d, p a b + p c d = p (a + c) (b + d) := fun a b c d ↦ by
    simp only [p]; push_cast; ring
  have psub : ∀ a b c d, p a b - p c d = p (a - c) (b - d) := fun a b c d ↦ by
    simp only [p]; push_cast; ring
  have pm : ∀ a b, p a b ∈ L.lattice ↔ a.den = 1 ∧ b.den = 1 := key
  have n1 : p (1 / 2) 0 ∉ L.lattice := by rw [pm]; norm_num
  have n2 : p 0 (1 / 2) ∉ L.lattice := by rw [pm]; norm_num
  have n3 : p (1 / 2) (1 / 2) ∉ L.lattice := by rw [pm]; norm_num
  obtain ⟨B, hB⟩ := exists_eq_mul_of_three_roots (A := A) (a := ℘[L] (p (1 / 2) 0))
    (b := ℘[L] (p 0 (1 / 2))) (c := ℘[L] (p (1 / 2) (1 / 2)))
    (by rw [Ne, weierstrassP_eq_iff L n2 n1, padd, psub, pm, pm]; norm_num)
    (by rw [Ne, weierstrassP_eq_iff L n3 n1, padd, psub, pm, pm]; norm_num)
    (by rw [Ne, weierstrassP_eq_iff L n3 n2, padd, psub, pm, pm]; norm_num)
    (hhalf _ n1 (by rw [padd, pm]; norm_num))
    (hhalf _ n2 (by rw [padd, pm]; norm_num))
    (hhalf _ n3 (by rw [padd, pm]; norm_num))
  set a := ℘[L] (p (1 / 2) 0)
  set b := ℘[L] (p 0 (1 / 2))
  set c := ℘[L] (p (1 / 2) (1 / 2))
  let w : ℂ → ℂ := fun z ↦ z ^ 2 * L.weierstrassPExcept 0 z + 1
  have hw : AnalyticAt ℂ w 0 := by fun_prop
  have hw' : ∀ z ≠ 0, w z = z ^ 2 * ℘[L] z := fun z hz ↦ by
    simpa [hz, w] using (L.ite_eq_one_sub_sq_mul_weierstrassP 0 (zero_mem _) z).symm
  let q : ℂ → ℂ := fun z ↦ (w z - z ^ 2 * a) * ((w z - z ^ 2 * b) * (w z - z ^ 2 * c))
  have hq : ContinuousAt q 0 := by
    have := hw.continuousAt
    fun_prop
  have hq0 : q 0 = 1 := by simp [q, w]
  have hq1 : Tendsto q (𝓝[≠] 0) (𝓝 1) := hq0 ▸ hq.tendsto.mono_left nhdsWithin_le_nhds
  have hB0 : B = 0 := by
    refine eq_zero_of_tendsto_eval_cobounded (tendsto_weierstrassP_cobounded L (zero_mem _)) ?_
    have h1 := hgt.div hq1 one_ne_zero
    rw [zero_div] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_notMem_periodLattice L 0, self_mem_nhdsWithin,
      hq1.eventually_ne one_ne_zero] with z hz hz0 hqz
    rw [Pi.div_apply, div_eq_iff hqz, hA z hz, hB]
    simp only [q, hw' z hz0, eval_mul, eval_sub, eval_X, eval_C]
    ring
  intro z hz
  have h1 := hA z hz
  rw [hB, hB0] at h1
  simpa [g, hz] using h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantEuclideanComplex
section
open NumberField
open scoped Matrix InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.EquivariantEuclideanComplex

open Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.IndefiniteRowSideFullHecke.RationalTransitionKernel

section Lin

variable {K : Type} [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K)

theorem cpt_single {n : ℕ} (k : Fin n) : cpt v.embedding (Pi.single k (1 : K)) = Pi.single k 1 := by
  funext i
  by_cases hi : i = k <;> simp [cpt, hi]

variable {E : Type} [AddCommGroup E] [Module ℂ E]

theorem ext_cpt {n : ℕ} {f g : (Fin n → ℂ) →ₗ[ℂ] E}
    (h : ∀ x : Fin n → K, f (cpt v.embedding x) = g (cpt v.embedding x)) : f = g := by
  rw [← lin_basis f, ← lin_basis g]
  congr 1
  funext i
  rw [← cpt_single v i, h]

def RatRel {D n : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E) (g : (Fin n → ℂ) →ₗ[ℂ] E) : Prop :=
  ∃ Y : Matrix (Fin D) (Fin n) K, Function.Bijective Y.mulVec ∧ g = f ∘ₗ cx v Y

end Lin

section Dict

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] {F : DefFam K G Pl0 T J}

def thetaOf (X : CxData F.amb) (t : T) : (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] X.EE :=
  lin fun k => X.Θ t (X.jR t ((F.R t).S.basis k))

def IsCoord {fc : DefSub F.amb → DefFace F.base} (cr : Crd F.amb fc) (b : Bool) (Zs : DefSub F.amb)
    (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ t, Function.Injective (cr.toR Zs b t) ∧
    LinearMap.range (cr.toR Zs b t) = LinearMap.range ((F.R t).toF (F.lvl P ψ) (Zs.Z t))

def RowsBij (X : CxData F.amb) {fc : DefSub F.amb → DefFace F.base} (cr : Crd F.amb fc) (b : Bool) : Prop :=
  ∀ t, Function.Injective (X.iC cr b t) ∧ LinearMap.range (X.iC cr b t) = LinearMap.range (X.iC cr b F.μ0)

def MetricTie (X : CxData F.amb) : Prop :=
  ∀ t, ∃ c : ℝ, 0 < c ∧ ∀ x y : Fin (F.R t).S.dim → K,
    ⟪X.jR t ((F.R t).S.basis.equivFun.symm x), X.jR t ((F.R t).S.basis.equivFun.symm y)⟫_ℂ =
      (c : ℂ) * F.v0.embedding (hform (F.R t).S.H x y)

variable (X : CxData F.amb) {fc : DefSub F.amb → DefFace F.base} (cr : Crd F.amb fc) (b : Bool)
  (P : Subgroup G) (ψ : P →* Kˣ)

theorem orth_span {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] {S : Set A} {f : A}
    (hf : ∀ p ∈ S, ⟪p, f⟫_ℂ = 0) : ∀ p ∈ Submodule.span ℂ S, ⟪p, f⟫_ℂ = 0 := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact hf x hx
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

def EquivariantRat (ρ : Representation ℂ G X.EE) : Prop :=
  ∀ (t : T) (g : G), ∀ x ∈ (F.R t).goodF F.X, X.Θ t (X.jR t ((F.R t).r g x)) = ρ g (X.Θ t (X.jR t x))

end Dict

section Concrete

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

theorem isCoord_base (Zs : DefSub A.fam.amb) : IsCoord (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false Zs P0 ψ0 :=
  fun t => ⟨(A.fam.R t).toF_injective _ _, rfl⟩

end Concrete

section Onto

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J)
  {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (Θ : ∀ t : T, (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] EE)

def fr (t : T) : Matrix (Fin (F.R t).S.dim) (Fin (F.R t).S.dim) ℂ := frameOf ((F.R t).S.H.map F.v0.embedding)

def toEuc (t : T) : (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (F.R t).S.dim) :=
  (WithLp.linearEquiv 2 ℂ (Fin (F.R t).S.dim → ℂ)).symm.toLinearMap ∘ₗ (fr F t)⁻¹.mulVecLin

def ofEuc (t : T) : EuclideanSpace ℂ (Fin (F.R t).S.dim) →ₗ[ℂ] (Fin (F.R t).S.dim → ℂ) :=
  (fr F t).mulVecLin ∘ₗ (WithLp.linearEquiv 2 ℂ (Fin (F.R t).S.dim → ℂ)).toLinearMap

def cxOf : CxData F.amb where
  FC t := EuclideanSpace ℂ (Fin (F.R t).S.dim)
  jR t := (toEuc F t).comp ((cptL F.v0.embedding _).comp
    ((F.R t).S.basis.equivFun : (F.R t).S.Forms →ₗ[K] (Fin (F.R t).S.dim → K)))
  EE := EE
  Θ t := Θ t ∘ₗ ofEuc F t
  EEp _ := ⊤
  EEl _ := ⊤
  FLC _ _ := EuclideanSpace ℂ (Fin 0)
  jL _ _ := 0
  W _ := EuclideanSpace ℂ (Fin 0)
  θ' _ _ := 0
  Wp _ _ := ⊤
  dW _ _ := 0
  WC _ _ _ := EuclideanSpace ℂ (Fin 0)
  bW _ _ _ _ := 0
  eW _ _ := 0
  M _ _ := ⊤
  nP _ := 1
  μ _ := F.μ0
  Tw := ∅
  κ _ := 1
  lam _ _ _ _ := 1
  err0 _ _ := 0

variable {F} {s : ℕ} (hF : F.Ok s)

include hF

end Onto

example {K : Type} [Field K] (σ : K →+* ℂ) :
    IsRat σ (relMat (0 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) LinearMap.id) := by
  intro i k
  refine ⟨0, ?_⟩
  have h : ¬ ∃ y, (0 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) y = Pi.single k 1 := by
    rintro ⟨y, hy⟩
    simpa using congrFun hy k
  simp only [relMat, Matrix.of_apply, LinearMap.id_apply, solve, dif_neg h, map_zero, Pi.zero_apply]

end GlobalTheory.EquivariantEuclideanComplex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationSepClosureIsEquivalenceStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCechAugmentation_sepClosure_isEquivalence : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω], Eqv R (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) F := by
  first
  | exact @GlobalTheory.SepCech.cechAug_sepClosure_eqv
  | exact GlobalTheory.SepCech.cechAug_sepClosure_eqv
  | (intros; apply GlobalTheory.SepCech.cechAug_sepClosure_eqv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNeighbourhoodKillsClass
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_neighbourhood_kills_class : ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) → ∀ (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∀ (m i : ℤ), 0 < m → ∀ y : Ht q (sp B) m i, ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D), Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧ pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.oneCoh_main) | (exact GlobalTheory.EtC.oneCoh_main) | (intros; apply GlobalTheory.EtC.oneCoh_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersDividedPowerPolyAlgebraAugIdeStatement
section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dividedPowers_dividedPowerPolyAlgebra_augIdeal : ∀ (B : Type) [CommRing B] (Q : PDPoly B), ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  first | exact @GlobalTheory.PDA.exists_dividedPowers_aug | exact GlobalTheory.PDA.exists_dividedPowers_aug | (intros; apply GlobalTheory.PDA.exists_dividedPowers_aug <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersSplitAugmentationExtensionStatement
section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dividedPowers_split_augmentation_extension : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (P : Type) [CommRing P] [Algebra B P] (ε : P →ₐ[B] B) (𝔞 : Ideal P) (η : DividedPowers 𝔞), (∀ p, p ∈ 𝔞 ↔ ε p = 0) → ∃ θ : DividedPowers (J.map (algebraMap B P) ⊔ 𝔞), IsDPMorphism δ θ (algebraMap B P) ∧ ∀ n, ∀ p ∈ 𝔞, θ.dpow n p = η.dpow n p := by
  first | exact @GlobalTheory.SplitDP.exists_dp_ext | exact GlobalTheory.SplitDP.exists_dp_ext | (intros; apply GlobalTheory.SplitDP.exists_dp_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisLiftResidueCongruencePadicStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_lift_residue_congruence_padic : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] L] (J : Type) (a b : J → PadicAlgCl l), (∀ j, ‖a j‖ ≤ 1) → (∀ j, ‖b j‖ ≤ 1) → (∀ p : MvPolynomial J (PadicAlgCl l), (∀ n, p.coeff n ∈ L ∧ ‖p.coeff n‖ ≤ 1) → (‖MvPolynomial.eval a p‖ < 1 ↔ ‖MvPolynomial.eval b p‖ < 1)) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ j, ‖g (a j) - b j‖ < 1 := by
  first | exact @GlobalTheory.ResidueLift.main | exact GlobalTheory.ResidueLift.main | (intros; apply GlobalTheory.ResidueLift.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPMorphismOfFlatAlgebraStatement
section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isDPMorphism_of_flat_algebra : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] (I : Ideal R) (κ : DividedPowers I), ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  first | exact @GlobalTheory.DPFlat.exists_isDPMorphism_of_flat | exact GlobalTheory.DPFlat.exists_isDPMorphism_of_flat | (intros; apply GlobalTheory.DPFlat.exists_isDPMorphism_of_flat <;> assumption)
end

