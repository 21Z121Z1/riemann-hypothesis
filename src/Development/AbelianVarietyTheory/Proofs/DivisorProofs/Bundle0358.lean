import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
import ReciprocityTheory.SemistableReduction.Bundle0025
import ReciprocityTheory.SemistableReduction.Bundle0002
import ReciprocityTheory.SemistableReduction.Bundle0010
import ReciprocityTheory.SemistableReduction.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeConnectingCocycleShortComplexDegreeZe
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeConn

set_option backward.isDefEq.respectTransparency false in

theorem cone_connecting_class : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R))
    (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
    S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
    ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
    CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc))
        (mappingCone.fst (resMap R S.f)) (zero_add 1)) =
      CohomologyClass.mk (zcomp (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)))) w (zero_add 1)) := by
  intro R _ S hc φ ψ hφ hψ w hw
  let Φ : Cochain (sgl S.X₂) (res R S.X₁) 0 := Cochain.fromSingleMk φ (zero_add 0)
  have hw1 : w.1 = Cochain.fromSingleMk ψ (zero_add 1) := by
    obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective w.1 1 (zero_add 1)
    rw [← hf]; congr 1
    rw [← hw, ← hf, Cochain.fromSingleMk_v]; exact (Iso.inv_hom_id_assoc _ _).symm
  have h1 : δ 0 1 Φ = (Cochain.ofHom (S.map (CochainComplex.singleFunctor (Shv R) 0)).g).comp w.1 (zero_add 1) := by
    rw [hw1, Cochain.δ_fromSingleMk φ (zero_add 0) 1 1 (zero_add 1), ← hψ]
    exact Cochain.fromSingleMk_precomp S.g ψ (zero_add 1)
  have h2 : (Cochain.ofHom (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).comp Φ (zero_add 0) =
      Cochain.ofHom (resAug S.X₁) := by
    refine (Cochain.fromSingleMk_precomp S.f φ (zero_add 0)).symm.trans ?_
    rw [hφ]
    apply (Cochain.fromSingleEquiv (X := S.X₁) (K := res R S.X₁) (p := 0) (zero_add 0)).injective
    rw [Cochain.fromSingleEquiv_fromSingleMk]
    change resι R S.X₁ = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 S.X₁).inv ≫ (Cochain.ofHom (resAug S.X₁)).v 0 0 (add_zero 0)
    rw [Cochain.ofHom_v]; rfl
  have h3 : Cochain.ofHom (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) =
      (mappingCone.snd (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).comp
        (Cochain.ofHom (S.map (CochainComplex.singleFunctor (Shv R) 0)).g) (zero_add 0) := by
    rw [mappingCone.descShortComplex, mappingCone.ofHom_desc, mappingCone.descCochain]
    simp
  have h4 : (Cochain.ofHom (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc)).comp
      (mappingCone.fst (resMap R S.f)).1 (zero_add 1) =
      (mappingCone.fst (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).1.comp
        (Cochain.ofHom (resAug S.X₁)) (add_zero 1) := by
    simp [mappingCone.map, mappingCone.ofHom_desc, mappingCone.descCochain, Cochain.add_comp]
    rfl
  symm
  refine sub_eq_zero.1 ((CohomologyClass.mk_sub _ _).symm.trans ?_)
  refine (CohomologyClass.mk_eq_zero_iff _).2 ((mem_coboundaries_iff _ 0 (zero_add 1)).2
    ⟨(mappingCone.snd (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).comp Φ (zero_add 0), ?_⟩)
  have e1 := δ_zero_cochain_comp (mappingCone.snd (S.map (CochainComplex.singleFunctor (Shv R) 0)).f) Φ 1 (zero_add 1)
  rw [h1, mappingCone.δ_snd, Int.negOnePow_zero, one_smul, Cochain.neg_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain, h2,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← h3, ← h4] at e1
  refine e1.trans ?_
  simp [zcomp, sub_eq_add_neg]

end GlobalTheory.EtC.ConeConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingPolarGaussianProbabilityComplex
section
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.SphereMeanDrop

theorem measurePreserving_polar_gaussProb (n : ℕ) (hn : 0 < n) :
    MeasurePreserving (fun p : UnitSphereC n × Ioi (0:ℝ) => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n)))
      ((sphereProb n).prod (radProb n)) (gaussProb n) := by
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)
  set f : UnitSphereC n × Ioi (0:ℝ) → EuclideanSpace ℂ (Fin n) :=
    fun p => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n)) with hf_def
  set S := (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere with hS
  set R0 := Measure.volumeIoiPow (2 * n - 1) with hR0
  set h : Ioi (0:ℝ) → ENNReal := fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2)) with hh_def
  set g : EuclideanSpace ℂ (Fin n) → ENNReal := fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) with hg_def
  have hfm : Measurable f := by
    apply Continuous.measurable
    exact (continuous_subtype_val.comp continuous_snd).smul (continuous_subtype_val.comp continuous_fst)
  have hhm : Measurable h := Measurable.ennreal_ofReal (by fun_prop)
  have hgm : Measurable g := Measurable.ennreal_ofReal (by fun_prop)

  have hA : MeasurePreserving f (S.prod R0) volume := by
    have h1 := Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))
    rw [finrank_euclidean_complex] at h1
    have h2 : MeasurePreserving (homeomorphUnitSphereProd (EuclideanSpace ℂ (Fin n))).toMeasurableEquiv
      _ _ := h1
    have h3 := h2.symm
    have h4 : MeasurePreserving (Subtype.val : ({(0 : EuclideanSpace ℂ (Fin n))}ᶜ : Set _) → _)
        ((volume : Measure (EuclideanSpace ℂ (Fin n))).comap Subtype.val) volume := by
      refine ⟨measurable_subtype_coe, ?_⟩
      rw [map_comap_subtype_coe (measurableSet_singleton _).compl, restrict_compl_singleton]
    have h5 := h4.comp h3
    convert h5 using 1
    funext p
    simp [hf_def]

  have hB : MeasurePreserving f (S.prod (R0.withDensity h))
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) := by
    refine ⟨hfm, ?_⟩
    rw [prod_withDensity_right hhm]
    ext s hs
    rw [Measure.map_apply hfm hs, withDensity_apply _ (hfm hs), withDensity_apply _ hs]
    have hpt : ∀ z : UnitSphereC n × Ioi (0:ℝ), h z.2 = g (f z) := by
      intro z
      simp only [hh_def, hg_def, hf_def, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < z.2 from z.2.2)]
      have : ‖(z.1 : EuclideanSpace ℂ (Fin n))‖ = 1 := by simp
      rw [this, mul_one]
    simp_rw [hpt]
    exact hA.setLIntegral_comp_preimage hs hgm

  have ha0 : S univ ≠ 0 := by
    rw [hS, Measure.toSphere_apply_univ, finrank_euclidean_complex]
    exact mul_ne_zero (by simp; omega) (Metric.measure_ball_pos _ _ one_pos).ne'
  have haT : S univ ≠ ⊤ := measure_ne_top _ _
  have hsph : sphereProb n = (S univ)⁻¹ • S := sphereProb_eq n
  have hrad : radProb n = ((R0.withDensity h) univ)⁻¹ • R0.withDensity h := by
    simp only [radProb, ProbabilityTheory.cond, Measure.restrict_univ]; rfl
  have hgau : gaussProb n = (((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) univ)⁻¹ •
      (volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g := by
    simp only [gaussProb, ProbabilityTheory.cond, Measure.restrict_univ]; rfl
  have hmass : ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) univ
      = S univ * (R0.withDensity h) univ := by
    rw [← hB.map_eq, Measure.map_apply hfm MeasurableSet.univ, preimage_univ, ← univ_prod_univ,
      Measure.prod_prod]
  refine ⟨hfm, ?_⟩
  rw [hsph, hrad, hgau, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul, hB.map_eq, hmass, ENNReal.mul_inv (Or.inl ha0) (Or.inl haT)]

end GlobalTheory.SphereMeanDrop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeEqZeroOfSqDvd
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open Polynomial

namespace RatDilation

theorem coe_comp_C_mul_X {F : Type} [Field F] (a : F) (f : F[X]) :
    ((f.comp (C a * X) : F[X]) : PowerSeries F) = PowerSeries.rescale a (f : PowerSeries F) := by
  ext n
  rw [PowerSeries.coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe]
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial m c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
    split_ifs with h <;> simp [h, mul_comm]

theorem natDegree_comp_two {F : Type} [Field F] [CharZero F] (f : F[X]) :
    (f.comp (C (2:F) * X)).natDegree = f.natDegree := by
  rw [natDegree_comp, natDegree_C_mul_X _ two_ne_zero, mul_one]

theorem natDegree_eq_zero_of_sq_dvd {F : Type} [Field F] [CharZero F] (f g : F[X]) (hf : f ≠ 0)
    (hc : IsCoprime f g) (h : f.comp (C (2:F) * X) * g ^ 2 = g.comp (C (2:F) * X) * f ^ 2) :
    f.natDegree = 0 := by
  have hd : f ^ 2 ∣ f.comp (C (2:F) * X) := by
    have : f ^ 2 ∣ f.comp (C (2:F) * X) * g ^ 2 := h ▸ dvd_mul_left _ _
    exact (hc.pow).dvd_of_dvd_mul_right this
  have hne : f.comp (C (2:F) * X) ≠ 0 := by
    intro h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨_, h0⟩
    · exact hf h0
    · have := congrArg natDegree h0
      rw [natDegree_C_mul_X _ two_ne_zero, natDegree_C] at this
      exact one_ne_zero this
  have := natDegree_le_of_dvd hd hne
  rw [natDegree_comp_two, natDegree_pow] at this
  omega

end RatDilation

open RatDilation in

theorem rat_dilation_eq_one (F : Type) [Field F] [CharZero F] (φ : PowerSeries F) (hr : IsRat φ)
    (h0 : PowerSeries.constantCoeff φ = 1) (h2 : PowerSeries.rescale 2 φ = φ ^ 2) : φ = 1 := by
  classical
  obtain ⟨p₀, q₀, hq₀, hpq₀⟩ := hr
  set g := GCDMonoid.gcd p₀ q₀ with hg
  have hg0 : g ≠ 0 := fun h => hq₀ ((gcd_eq_zero_iff _ _).1 h).2
  set p := p₀ / g
  set q := q₀ / g
  have hcop : IsCoprime p q := isCoprime_div_gcd_div_gcd hq₀
  have hp₀ : p₀ = g * p := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)).symm
  have hq₀' : q₀ = g * q := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right _ _)).symm
  have hq : q ≠ 0 := by rintro h; rw [h, mul_zero] at hq₀'; exact hq₀ hq₀'
  have hgc : ((g : F[X]) : PowerSeries F) ≠ 0 := by
    rwa [Ne, Polynomial.coe_eq_zero_iff]
  have hpq : (q : PowerSeries F) * φ = (p : PowerSeries F) := by
    rw [hp₀, hq₀', Polynomial.coe_mul, Polynomial.coe_mul, mul_assoc] at hpq₀
    exact mul_left_cancel₀ hgc hpq₀
  have hφ0 : φ ≠ 0 := by
    rintro rfl; simp at h0
  have hp : p ≠ 0 := by
    rintro h
    rw [h, Polynomial.coe_zero] at hpq
    rcases mul_eq_zero.1 hpq with h' | h'
    · exact hq ((Polynomial.coe_eq_zero_iff).1 h')
    · exact hφ0 h'
  have key : p.comp (C (2:F) * X) * q ^ 2 = q.comp (C (2:F) * X) * p ^ 2 := by
    apply Polynomial.coe_inj.1
    have e := congrArg (PowerSeries.rescale (2:F)) hpq
    rw [map_mul, h2, ← coe_comp_C_mul_X, ← coe_comp_C_mul_X] at e
    simp only [Polynomial.coe_mul, Polynomial.coe_pow]
    rw [← e, ← hpq]; ring
  have dq := natDegree_eq_zero_of_sq_dvd q p hq hcop.symm key.symm
  have dp := natDegree_eq_zero_of_sq_dvd p q hp hcop key
  rw [eq_C_of_natDegree_eq_zero dq, eq_C_of_natDegree_eq_zero dp] at hpq
  rw [Polynomial.coe_C, Polynomial.coe_C] at hpq
  have hc := congrArg PowerSeries.constantCoeff hpq
  simp only [map_mul, h0, mul_one, PowerSeries.constantCoeff_C] at hc
  rw [← hc] at hpq
  have ha : (PowerSeries.C (q.coeff 0) : PowerSeries F) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    rw [PowerSeries.constantCoeff_C, map_zero] at h'
    apply hq; rw [eq_C_of_natDegree_eq_zero dq, h', C_0]
  exact mul_left_cancel₀ ha (hpq.trans (mul_one _).symm)

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
section
namespace GlobalTheory.IntBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal Matrix

noncomputable section

abbrev Low (r : ℕ) : Type := {p : Fin r × Fin r // p.2 < p.1}

def lowMat {r : ℕ} (w : Low r → ℂ) : Matrix (Fin r) (Fin r) ℂ := fun a b =>
  if h : b < a then w ⟨(a, b), h⟩ else if a = b then 1 else 0

def colGram {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) (k : Fin (q + 1)) : ℝ := ‖lminor (Mᴴ * M) k‖

def blkW {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : Matrix (Fin (r - 1)) (Fin (r - 1)) ℂ := fun i j =>
  if p0 = 1 then lowMat w ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ else lowMat w ⟨i, by omega⟩ ⟨j, by omega⟩

def gB {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : ℝ :=
  ∏ k : Fin (r - 1), colGram (blkW p0 w) k.castSucc ^ (-2 : ℤ)

def hB {r : ℕ} (p0 : ℕ) : (Low r → ℂ) → ℝ≥0∞ :=
  Set.indicator {w | ∀ p : Low r, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
    fun w => ENNReal.ofReal (gB p0 w)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def zOf (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Low r → ℂ := fun p =>
  z (Fintype.equivFin (Ent X) ⟨τ, p⟩)

def bnd (X : Data E r) (z : V (nd X)) : ℝ := ∏ τ, gB X.p0 (zOf X z τ)

theorem nmat_eq_lowMat (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (Matrix.of (nmat X z τ) : Matrix (Fin r) (Fin r) ℂ) = lowMat (zOf X z τ) := by
  ext a b
  simp only [Matrix.of_apply, nmat, lowMat, zOf]

end

end GlobalTheory.IntBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCyclotomicPrimitiveRootsOfStrictlyHensel
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

open Polynomial in

theorem prim_of_strictlyHenselian : ∀ (q : ℕ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → Nonempty (Prim q A) := by
  intro q A _ hSH hq
  obtain ⟨hH, hsep⟩ := hSH
  let k := IsLocalRing.ResidueField A
  have hqk : IsUnit ((q : ℕ) : k) := by
    have := hq.map (IsLocalRing.residue A)
    rwa [map_natCast] at this
  haveI : NeZero ((q : ℕ) : k) := ⟨hqk.ne_zero⟩
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hqk
    · exact h
  have hsepk : (cyclotomic q k).Separable := separable_cyclotomic q k
  obtain ⟨a₀, ha₀⟩ := IsSepClosed.exists_root (cyclotomic q k)
    (degree_cyclotomic_pos q k hq0).ne' hsepk
  have hmap : (cyclotomic q A).map (algebraMap A k) = cyclotomic q k := map_cyclotomic q _
  have h1 : aeval a₀ (cyclotomic q A) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hmap]; exact ha₀
  have h2 : aeval a₀ (derivative (cyclotomic q A)) ≠ 0 := by
    rw [aeval_def, eval₂_eq_eval_map, ← derivative_map, hmap]
    have := hsepk.aeval_derivative_ne_zero (x := a₀) (by simpa [aeval_def] using ha₀)
    simpa [aeval_def] using this
  have hT := (HenselianLocalRing.TFAE A).out 0 1
  obtain ⟨a, ha, -⟩ := hT.mp hH (cyclotomic q A) (cyclotomic.monic q A) a₀ h1 h2
  refine ⟨⟨a, hq, ?_⟩⟩
  have : (cyclotomic q ℤ).map (Int.castRingHom A) = cyclotomic q A := map_cyclotomic q _
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, this]
  exact ha

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCharacterUnitEqOneHeisenbergStatement
section
open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_character_unit_eq_one_heisenberg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤) →
    ∀ (_i0 : Fin n) (u : kˣ), valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1 := by
  first | exact @GlobalTheory.HeisUnit.norm_char_unit_eq_one | exact GlobalTheory.HeisUnit.norm_char_unit_eq_one | (intros; apply GlobalTheory.HeisUnit.norm_char_unit_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMulNormalisedAbsPowHalfEqOneStatement
section
open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by
  first | exact @GlobalTheory.CharNormHalf.norm_mul_apow_eq_one | exact GlobalTheory.CharNormHalf.norm_mul_apow_eq_one | (intros; apply GlobalTheory.CharNormHalf.norm_mul_apow_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmCoeffProdLinear
section
set_option autoImplicit false

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open Polynomial in

theorem coeff_max_mul_linear {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    (p : F[X]) (N : Γ) (α β : F) (h1 : ∀ i, v (p.coeff i) ≤ N) (h2 : ∃ i, v (p.coeff i) = N) :
    (∀ i, v (((C α + C β * X) * p).coeff i) ≤ max (v α) (v β) * N) ∧
      ∃ i, v (((C α + C β * X) * p).coeff i) = max (v α) (v β) * N := by
  classical
  have c0 : ((C α + C β * X) * p).coeff 0 = α * p.coeff 0 := by
    simp [add_mul, mul_assoc]
  have cs : ∀ i, ((C α + C β * X) * p).coeff (i + 1) = α * p.coeff (i + 1) + β * p.coeff i := by
    intro i
    simp [add_mul, mul_assoc, coeff_X_mul]
  have hle : ∀ i, v (((C α + C β * X) * p).coeff i) ≤ max (v α) (v β) * N := by
    intro i
    cases i with
    | zero =>
      rw [c0, map_mul]
      exact mul_le_mul' (le_max_left _ _) (h1 _)
    | succ i =>
      rw [cs]
      refine v.map_add_le ?_ ?_
      · rw [map_mul]; exact mul_le_mul' (le_max_left _ _) (h1 _)
      · rw [map_mul]; exact mul_le_mul' (le_max_right _ _) (h1 _)
  refine ⟨hle, ?_⟩
  by_cases hz : max (v α) (v β) * N = 0
  · exact ⟨0, le_antisymm (hle 0) (hz ▸ zero_le')⟩
  have hM : max (v α) (v β) ≠ 0 := left_ne_zero_of_mul hz
  have hN : N ≠ 0 := right_ne_zero_of_mul hz
  rcases le_or_gt (v β) (v α) with h | h
  · rw [max_eq_left h] at hM ⊢
    have hs := Nat.find_spec h2
    have hm := fun j => @Nat.find_min _ _ h2 j
    refine ⟨Nat.find h2, ?_⟩
    generalize Nat.find h2 = i at hs hm
    cases i with
    | zero => rw [c0, map_mul, hs]
    | succ i =>
      have hlt : v (p.coeff i) < N := lt_of_le_of_ne (h1 i) (hm i (Nat.lt_succ_self i))
      rw [cs, v.map_add_eq_of_lt_left, map_mul, hs]
      rw [map_mul, map_mul, hs]
      calc v β * v (p.coeff i) ≤ v α * v (p.coeff i) := mul_le_mul' h le_rfl
        _ < v α * N := mul_lt_mul_of_pos_left hlt (zero_lt_iff.2 hM)
  · rw [max_eq_right h.le]
    obtain ⟨i, hi⟩ := h2
    refine ⟨i + 1, ?_⟩
    rw [cs, v.map_add_eq_of_lt_right, map_mul, hi]
    rw [map_mul, map_mul, hi]
    calc v α * v (p.coeff (i + 1)) ≤ v α * N := mul_le_mul' le_rfl (h1 _)
      _ < v β * N := mul_lt_mul_of_pos_right h (zero_lt_iff.2 hN)

open Polynomial in

theorem coeff_max_prod_linear {F Γ ι : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    (α β : ι → F) (s : Finset ι) :
    (∀ i, v ((∏ j ∈ s, (C (α j) + C (β j) * X)).coeff i) ≤ ∏ j ∈ s, max (v (α j)) (v (β j))) ∧
      ∃ i, v ((∏ j ∈ s, (C (α j) + C (β j) * X)).coeff i) = ∏ j ∈ s, max (v (α j)) (v (β j)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun i => ?_, 0, by simp⟩
    by_cases h : i = 0 <;> simp [coeff_one, h]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact coeff_max_mul_linear v _ _ _ _ ih.1 ih.2

theorem nrm_coeff_prod_linear : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ (v : Place k F) (m : ℕ) (α β : Fin m → F), nrm v (fun a : Fin (m + 1) => (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a) = ∏ j, max (v.1 (α j)) (v.1 (β j)) := by
  intro k F _ _ _ v m α β
  obtain ⟨h1, i, hi⟩ := coeff_max_prod_linear v.1 α β Finset.univ
  have hdeg : (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).natDegree ≤ m := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc _ ≤ ∑ _j : Fin m, 1 := Finset.sum_le_sum fun j _ => by
            rw [add_comm]; exact Polynomial.natDegree_linear_le
      _ = m := by simp
  refine le_antisymm (Finset.sup_le fun a _ => h1 a) ?_
  rw [← hi]
  by_cases him : i < m + 1
  · exact Finset.le_sup (f := fun a : Fin (m + 1) =>
      v.1 ((∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a))
      (Finset.mem_univ (⟨i, him⟩ : Fin (m + 1)))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
    exact zero_le'

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagram
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem ContCone.iff_of_eqv (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I]
    (G G' : I ⥤ Spc) (c : Cone G) (c' : Cone G') (α : G ⟶ G') (β : c.pt ⟶ c'.pt)
    (h : ∀ i, c.π.app i ≫ α.app i = β ≫ c'.π.app i) (hα : ∀ i, Eqv R (α.app i) F) (hβ : Eqv R β F) :
    ContCone R F c ↔ ContCone R F c' := by
  have hsq : ∀ n i (y' : H R (G'.obj i) F n),
      pull R (c.π.app i) F n (pull R (α.app i) F n y') = pull R β F n (pull R (c'.π.app i) F n y') := by
    intro n i y'
    rw [← pull_comp, ← pull_comp, h i]
  have hnat : ∀ n {k i : I} (f : k ⟶ i) (y' : H R (G'.obj i) F n),
      pull R (G.map f) F n (pull R (α.app i) F n y') = pull R (α.app k) F n (pull R (G'.map f) F n y') := by
    intro n k i f y'
    rw [← pull_comp, ← pull_comp, α.naturality f]
  constructor
  · intro hc n
    refine ⟨fun x' => ?_, fun i y' hy' => ?_⟩
    · obtain ⟨i, y, hy⟩ := (hc n).1 (pull R β F n x')
      obtain ⟨y', rfl⟩ := (hα i n).2 y
      refine ⟨i, y', (hβ n).1 ?_⟩
      rw [← hsq, hy]
    · obtain ⟨k, f, hf⟩ := (hc n).2 i (pull R (α.app i) F n y') (by rw [hsq, hy', map_zero])
      refine ⟨k, f, (hα k n).1 ?_⟩
      rw [← hnat, hf, map_zero]
  · intro hc n
    refine ⟨fun x => ?_, fun i y hy => ?_⟩
    · obtain ⟨x', rfl⟩ := (hβ n).2 x
      obtain ⟨i, y', hy'⟩ := (hc n).1 x'
      exact ⟨i, pull R (α.app i) F n y', by rw [hsq, hy']⟩
    · obtain ⟨y', rfl⟩ := (hα i n).2 y
      have h0 : pull R (c'.π.app i) F n y' = 0 := (hβ n).1 (by rw [← hsq, hy, map_zero])
      obtain ⟨k, f, hf⟩ := (hc n).2 i y' h0
      exact ⟨k, f, by rw [hnat, hf, map_zero]⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialOperatorFderivFormulaStatement
section
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_operator_fderiv_formula : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ),
    Differentiable ℝ (qOp P f) ∧ ∀ (s v : κ ⊕ κ₁' → V),
      fderiv ℝ (qOp P f) s v = qOp P (pd (padL (κ' := κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s := by
  first | exact @GlobalTheory.SliceOp.differentiable_qOp_and_fderiv | exact GlobalTheory.SliceOp.differentiable_qOp_and_fderiv | (intros; apply GlobalTheory.SliceOp.differentiable_qOp_and_fderiv <;> assumption)
end

