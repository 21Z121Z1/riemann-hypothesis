import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupFiniteDimensionalRepContainsHighestW
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumNormEmb
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.TopIntegrand

def extId {R : Type} [CommRing R] {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (P : Matrix (Fin n) (Fin m) R)
    (x : Matrix (Fin n) (Fin n) R) : Matrix (Fin m) (Fin m) R := 1 + M * (x - 1) * P

theorem map_emb {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : ℕ} (M : Matrix (Fin m) (Fin n) R)
    (P : Matrix (Fin n) (Fin m) R) (x : Matrix (Fin n) (Fin n) R) :
    (extId M P x).map f = extId (M.map f) (P.map f) (x.map f) := by
  rw [extId, extId, Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub f),
    Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_one _ (map_zero f) (map_one f)]

theorem sum_norm_emb {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (P : Matrix (Fin n) (Fin m) ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Matrix (Fin n) (Fin n) ℂ,
      ∑ i, ∑ j, ‖extId M P x i j‖ ≤ c * (1 + ∑ k, ∑ l, ‖x k l‖) := by
  refine ⟨∑ i, ∑ j, (‖(1 - M * P : Matrix (Fin m) (Fin m) ℂ) i j‖ + ∑ l, ∑ k, ‖M i k‖ * ‖P l j‖), by positivity, fun x => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have e : extId M P x = (1 - M * P) + M * x * P := by
    rw [extId, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
  have hS : 0 ≤ ∑ k, ∑ l, ‖x k l‖ := by positivity
  have hx : ∀ k l, ‖x k l‖ ≤ 1 + ∑ k, ∑ l, ‖x k l‖ := fun k l =>
    ((Finset.single_le_sum (f := fun l => ‖x k l‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun k => ∑ l, ‖x k l‖) (fun _ _ => by positivity) (Finset.mem_univ k))).trans
      (by linarith)
  rw [e, Matrix.add_apply, add_mul]
  refine (norm_add_le _ _).trans (add_le_add (le_mul_of_one_le_right (norm_nonneg _) (by linarith)) ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul, mul_right_comm]
  exact mul_le_mul_of_nonneg_left (hx k l) (by positivity)

variable {D : D7} {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (hι : HSpace.IsIsomEmb B A ι)

abbrev emb : GA D B →* GA D A := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embA D.sp.cm B A ι hι

theorem matHom_emb (h : GA D B) : (matHom A (emb hι h)).1 =
    extId ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat B A ι).map (incA D)) ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat D.sp.cm B A ι).map (incA D))
      (matHom B h).1 := rfl

theorem emb_ker {S : Type} [CommRing S] (f : AF D.host.F ⊗[D.host.F] D.host.E →+* S) (h : GA D B)
    (hh : Formalism.UG.bc f (matHom B h) = 1) : Formalism.UG.bc f (matHom A (emb hι h)) = 1 := by
  have h1 : (matHom B h).1.map f = 1 := congrArg Units.val hh
  refine Units.ext ?_
  change (matHom A (emb hι h)).1.map f = 1
  rw [matHom_emb, map_emb, h1, extId, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem emb_GfC {h : GA D B} (hh : h ∈ GfC B) : emb hι h ∈ GfC A := emb_ker hι _ h hh

theorem emb_GinfC {h : GA D B} (hh : h ∈ GinfC B) : emb hι h ∈ GinfC A := emb_ker hι _ h hh

theorem infMat_emb (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) : ∃ M P, ∀ h : GA D B,
    infMat D.sp.cm.sig A.gram θ (emb hι h) = extId M P (infMat D.sp.cm.sig B.gram θ h) := by
  refine ⟨?_, ?_, fun h => ?_⟩
  rotate_left 2
  change ((matHom A (emb hι h)).1.map
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom).map θ = _
  rw [matHom_emb, map_emb, map_emb]
  rfl

theorem normInf_emb (θ : InfF D) : ∃ c : ℝ, 0 ≤ c ∧ ∀ h : GA D B,
    normInf θ A (emb hι h) ≤ c * (1 + normInf θ B h) := by
  choose M P hMP using fun τ => infMat_emb hι (θ τ)
  choose c hc0 hc using fun τ => sum_norm_emb (M τ) (P τ)
  refine ⟨∑ τ, 2 * c τ, Finset.sum_nonneg fun τ _ => by have := hc0 τ; positivity, fun h => ?_⟩
  rw [Finset.sum_mul, normInf]
  refine Finset.sum_le_sum fun τ _ => ?_
  have h0 : ∑ i, ∑ j, (‖infMat D.sp.cm.sig B.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig B.gram (θ τ) h⁻¹ i j‖) ≤
      normInf θ B h := Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
        (‖infMat D.sp.cm.sig B.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig B.gram (θ τ) h⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  simp only [Finset.sum_add_distrib] at h0 ⊢
  rw [← map_inv, hMP, hMP]
  have h1 := hc τ (infMat D.sp.cm.sig B.gram (θ τ) h)
  have h2 := hc τ (infMat D.sp.cm.sig B.gram (θ τ) h⁻¹)
  have h3 := mul_le_mul_of_nonneg_left h0 (hc0 τ)
  have h4 := mul_nonneg (hc0 τ) (GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) h)
  nlinarith

theorem emb_moderate {θ : InfF D} (hθ : IsInfFam θ) (hc : Continuous (emb hι)) (hQ : ∀ γ ∈ GQ B, emb hι γ ∈ GQ A)
    {φ : GA D A → ℂ} (hφ : IsAutFunSm θ A φ) :
    ∃ (N : ℕ) (C : ℝ), ∀ g, ‖φ (emb hι g)‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ N := by
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  obtain ⟨S, C₀, M, hS⟩ := GlobalTheory.SmoothForms.reduction hθ ((GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ B) (U.comap (emb hι)) (hU.preimage hc)
  obtain ⟨N, hN⟩ := hφ.growth
  choose C hC using hN [] (by simp)
  obtain ⟨c, hc0, hc⟩ := normInf_emb hι θ
  refine ⟨M * N, (∑ x ∈ S, |C (emb hι x)|) * (c * (1 + |C₀|)) ^ N, fun g => ?_⟩
  obtain ⟨γ, hγ, x, hx, a, ha, k, hk, hk', e, hb⟩ := hS g
  rw [← hφ.left _ (hQ γ hγ), ← map_mul, e, map_mul, map_mul, hUφ _ hk (emb_GfC hι hk'), pow_mul, mul_assoc, ← mul_pow]
  have h1 : (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ M :=
    one_le_pow₀ (by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ B g)
  have h2 : normInf θ A (emb hι a) ≤ c * (1 + |C₀|) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ M := by
    refine (hc a).trans ?_
    rw [mul_assoc, add_mul, one_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add h1 (hb.trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans h1)))) hc0
  exact (hC _ _ (emb_GinfC hι ha)).trans (mul_le_mul ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |C (emb hι x)|) (fun _ _ => abs_nonneg _) hx))
    (pow_le_pow_left₀ (GlobalTheory.SmoothForms.normInf_nonneg _) h2 N) (pow_nonneg (GlobalTheory.SmoothForms.normInf_nonneg _) N)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _))

theorem topInt (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) : TopInt D := by
  intro θ hθ A B ι hι μ 𝓕 hq s hs φ φ' hφ hφ'
  obtain rfl : s = emb hι := funext fun h => (GlobalTheory.AutFunCompare.embRel_iff A B ι hι _ _).1 (hs h)
  obtain ⟨s, hc, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D A B ι hι
  have e : ∀ h, emb hι h = s h := fun h => (hrel h _).1 (hs h)
  have hc' : Continuous (emb hι) := by rw [show ⇑(emb hι) = s from funext e]; exact hc
  have hQ' : ∀ γ ∈ GQ B, emb hι γ ∈ GQ A := fun γ hγ => e γ ▸ hQ γ hγ
  obtain ⟨N, C, hC⟩ := emb_moderate hι hθ hc' hQ' hφ
  obtain ⟨K, hK⟩ := (GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hφ'.1 hφ'.2).mul_bounded
    (ψ := fun g => φ (emb hι g)) (fun γ hγ g => by simp only [map_mul]; exact hφ.left _ (hQ' γ hγ) _) hC
  have : BorelSpace (GA D B) := ⟨rfl⟩
  refine Measure.integrableOn_of_bounded (M := K)
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B μ 𝓕 hq.1 hq.2).ne
    (((hφ.cont.comp hc').star.mul hφ'.1.cont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
  rw [norm_mul, norm_star]
  exact hK g

end GlobalTheory.Mem.TopIntegrand

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffEqTensorSquareTopCoefficient
section
noncomputable section

open MvPolynomial TensorProduct

namespace GlobalTheory.GrassModel.TopRead

variable {n : ℕ}

theorem list_prod_gen {m : ℕ} (x : Fin m → Fin n × Fin n) :
    (List.ofFn fun j => gen n (x j)).prod =
      (List.ofFn fun j => vec n (x j).1).prod ⊗ₜ (List.ofFn fun j => vec n (x j).2).prod := by
  induction m with
  | zero => simp [Algebra.TensorProduct.one_def]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => x j.succ)]
    simp only [List.ofFn_succ, List.prod_cons, gen, Algebra.TensorProduct.tmul_mul_tmul]

theorem topBig_toEven_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    topBig n ((toEven n (∏ j, X (x j)) : EvenPart n) : Big n) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) := by
  have h1 : ((toEven n (∏ j, X (x j)) : EvenPart n) : Big n) = (List.ofFn fun j => gen n (x j)).prod := by
    rw [map_prod, ← List.prod_ofFn, ← Subalgebra.coe_val, map_list_prod, List.map_ofFn]
    congr 1
    exact congrArg List.ofFn (funext fun j => by simp [toEven, aeval_X])
  rw [h1, list_prod_gen, topBig_tmul]
  simp only [topExt, vec]
  rw [← ExteriorAlgebra.ιMulti_apply, ← ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.liftAlternating_apply_ιMulti, ExteriorAlgebra.liftAlternating_apply_ιMulti]

theorem toMultiset_sum_single {α : Type*} [DecidableEq α] {m : ℕ} (x : Fin m → α) :
    Finsupp.toMultiset (∑ j, Finsupp.single (x j) 1) = Finset.univ.val.map x := by
  rw [map_sum, Finset.sum_eq_multiset_sum]
  simp only [Finsupp.toMultiset_single, one_nsmul]
  have : (fun j => ({x j} : Multiset α)) = (fun a => ({a} : Multiset α)) ∘ x := rfl
  rw [this, ← Multiset.map_map, Multiset.sum_map_singleton]

theorem toMultiset_injective' {α : Type*} [DecidableEq α] :
    Function.Injective (Finsupp.toMultiset : (α →₀ ℕ) → Multiset α) := fun f g h => by
  rw [← Finsupp.toMultiset_toFinsupp f, h, Finsupp.toMultiset_toFinsupp]

theorem coeff_prod_X {m : ℕ} (x : Fin m → Fin n × Fin n) (d : Fin n × Fin n →₀ ℕ) :
    coeff d (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) =
      if Finset.univ.val.map x = Finsupp.toMultiset d then 1 else 0 := by
  classical
  have e : (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (x j) 1) 1 :=
    (monomial_sum_one _ _).symm
  rw [e, coeff_monomial, ← toMultiset_sum_single]
  simp only [toMultiset_injective'.eq_iff]

theorem topForm_self (v : Fin n → Fin n → ℂ) : topForm n n v = (Pi.basisFun ℂ (Fin n)).det v := by
  simp [topForm]

theorem det_single_perm (π : Equiv.Perm (Fin n)) :
    (Pi.basisFun ℂ (Fin n)).det (fun j => Pi.single (π j) 1) = ((Equiv.Perm.sign π : ℤ) : ℂ) := by
  have : (fun j => (Pi.single (π j) 1 : Fin n → ℂ)) = (Pi.basisFun ℂ (Fin n)) ∘ π := by
    funext j; simp
  rw [this, AlternatingMap.map_perm, Module.Basis.det_self, Units.smul_def, zsmul_eq_mul, mul_one]

theorem det_single_not_inj (a : Fin n → Fin n) (ha : ¬ Function.Injective a) :
    (Pi.basisFun ℂ (Fin n)).det (fun j => Pi.single (a j) 1) = 0 := by
  refine AlternatingMap.map_eq_zero_of_not_injective _ _ fun h => ha fun i j hij => h ?_
  simp [hij]

open Classical in

theorem topCoeff_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    GlobalTheory.GoodMetric.topCoeff (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) := by
  unfold GlobalTheory.GoodMetric.topCoeff
  simp_rw [coeff_prod_X, toMultiset_sum_single]
  by_cases hm : m = n
  swap
  · have h0 : topForm n m = 0 := by simp [topForm, hm]
    rw [h0]
    simp only [AlternatingMap.zero_apply, mul_zero]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    intro heq
    have := congrArg Multiset.card heq
    simp at this
    exact hm this
  subst hm
  rw [topForm_self, topForm_self]
  set a : Fin m → Fin m := fun j => (x j).1 with ha_def
  set b : Fin m → Fin m := fun j => (x j).2 with hb_def

  have hcond : ∀ w : Equiv.Perm (Fin m),
      Finset.univ.val.map x = Finset.univ.val.map (fun c => (c, w c)) →
        Function.Injective a ∧ Function.Injective b := by
    intro w heq
    have h1 := congrArg (Multiset.map Prod.fst) heq
    have h2 := congrArg (Multiset.map Prod.snd) heq
    simp only [Multiset.map_map] at h1 h2
    have e1 : Multiset.map (Prod.fst ∘ fun c => (c, w c)) Finset.univ.val = Finset.univ.val := by
      simp
    have e2 : Multiset.map (Prod.snd ∘ fun c => (c, w c)) Finset.univ.val = Finset.univ.val := by
      simpa using Multiset.map_univ_val_equiv w
    rw [e1] at h1
    rw [e2] at h2
    constructor
    · have hn : (Multiset.map (Prod.fst ∘ x) Finset.univ.val).Nodup := by rw [h1]; exact Finset.univ.nodup
      exact fun i j hij => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hn i (by simp) j (by simp) hij
    · have hn : (Multiset.map (Prod.snd ∘ x) Finset.univ.val).Nodup := by rw [h2]; exact Finset.univ.nodup
      exact fun i j hij => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hn i (by simp) j (by simp) hij
  by_cases hab : Function.Injective a ∧ Function.Injective b
  swap
  · have : (Pi.basisFun ℂ (Fin m)).det (fun j => Pi.single (x j).1 1) *
        (Pi.basisFun ℂ (Fin m)).det (fun j => Pi.single (x j).2 1) = 0 := by
      rcases not_and_or.mp hab with h | h
      · rw [det_single_not_inj a h, zero_mul]
      · rw [det_single_not_inj b h, mul_zero]
    rw [this]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    exact fun heq => hab (hcond w heq)
  obtain ⟨ha, hb⟩ := hab
  let π : Equiv.Perm (Fin m) := Equiv.ofBijective a (Finite.injective_iff_bijective.mp ha)
  let τ : Equiv.Perm (Fin m) := Equiv.ofBijective b (Finite.injective_iff_bijective.mp hb)
  have hπ : ∀ j, (x j).1 = π j := fun j => rfl
  have hτ : ∀ j, (x j).2 = τ j := fun j => rfl
  simp_rw [hπ, hτ, det_single_perm]
  have hx : x = (fun c => (c, (τ * π⁻¹) c)) ∘ π := by
    funext j
    simp [Prod.ext_iff, hπ, hτ]
  have hmap : Finset.univ.val.map x = Finset.univ.val.map (fun c => (c, (τ * π⁻¹) c)) := by
    rw [hx, ← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [Finset.sum_eq_single (τ * π⁻¹)]
  · rw [if_pos hmap, mul_one, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    push_cast
    ring
  · intro w _ hw
    rw [if_neg, mul_zero]
    intro heq
    apply hw
    ext c
    have hc : (c, w c) ∈ Finset.univ.val.map (fun c => (c, (τ * π⁻¹) c)) := by
      rw [← hmap, heq]; simp
    obtain ⟨c', _, hc'⟩ := Multiset.mem_map.mp hc
    simp only [Prod.mk.injEq] at hc'
    obtain ⟨rfl, h⟩ := hc'
    exact congrArg Fin.val h.symm
  · intro h; exact absurd (Finset.mem_univ _) h

theorem topCoeff_eq_topBig (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    GlobalTheory.GoodMetric.topCoeff P = topBig n (toEven n P : Big n) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    obtain ⟨l, hl⟩ : ∃ l : List (Fin n × Fin n), (l : Multiset _) = Finsupp.toMultiset u :=
      ⟨_, Multiset.coe_toList _⟩
    have hu : u = ∑ j, Finsupp.single (l.get j) 1 := by
      apply toMultiset_injective'
      rw [toMultiset_sum_single, Fin.univ_val_map, List.ofFn_get, hl]
    have hmon : (monomial u c : MvPolynomial (Fin n × Fin n) ℂ) = c • ∏ j, X (l.get j) := by
      rw [hu, show (∏ j, X (l.get j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (l.get j) 1) 1 from
        (monomial_sum_one _ _).symm, smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, Subalgebra.coe_smul, map_smul, smul_eq_mul, topBig_toEven_prod, ← topCoeff_prod]
    unfold GlobalTheory.GoodMetric.topCoeff
    simp only [coeff_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => by ring
  | add p q hp hq =>
    rw [map_add, Subalgebra.coe_add, map_add, ← hp, ← hq]
    unfold GlobalTheory.GoodMetric.topCoeff
    simp only [coeff_add, mul_add, Finset.sum_add_distrib]

end GlobalTheory.GrassModel.TopRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingSchurOrthogonalityDefiniteCoefficients
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.SchurW

set_option maxHeartbeats 8000000 in

theorem schurW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (t : T) (h h' : (R.HX t).H) (a a' : R.cX.W), IntegrableOn (fun g => star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ) (R.fdX t) (R.νX t) ∧ (Module.finrank ℂ R.cX.W : ℂ) * ∫ g in R.fdX t, star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ ∂(R.νX t) = ⟪a', a⟫_ℂ * ⟪h, h'⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB t h h' a a'
  haveI : IsTopologicalGroup (GA D D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D D.sp.X') := ⟨rfl⟩
  haveI : Countable (GQ D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig D.sp.X'.gram
  have hμ := hB.models.νX t
  haveI := hμ.1.1
  have hc := hB.models.cX
  have hH := hB.models.HX t
  let J := (levEnv D.sp.X' R.βX (R.datXt t)).J
  let χ := (levEnv D.sp.X' R.βX (R.datXt t)).χ
  let Ω : Subgroup (GA D D.sp.X') := (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)).comap (finE D.sp.X')
  have hK : ∀ g : GA D D.sp.X', g ∈ Ω ↔ (finHom D.sp.X').rangeRestrict g ∈ J := fun g => Iff.rfl
  have hΩo : IsOpen (Ω : Set (GA D D.sp.X')) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level D.sp.X' R.βX (R.datXt t)] with κ hκ
    exact (hK κ).2 hκ.1
  have hΩ1 : R.νX t (Ω : Set (GA D D.sp.X')) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ.1
  have hF : ∀ x, (R.HX t).e x ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ := fun x => by
    have := LinearMap.mem_range_self (R.HX t).e x
    rw [hH.2.1] at this
    exact this
  have hinv : ∀ (u : GA D D.sp.X') v, R.cX.ρ u⁻¹ (R.cX.ρ u v) = v := fun u v => by
    have := congrArg (fun T : Module.End ℂ R.cX.W => T v) (show R.cX.ρ u⁻¹ * R.cX.ρ u = 1 by rw [← map_mul, inv_mul_cancel, map_one])
    exact this
  have hext : ∀ f, f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ → ∀ (γ : GA D D.sp.X'), γ ∈ GQ D.sp.X' →
      ∀ g, R.cX.ext f (γ * g) = R.cX.ext f g := by
    intro f hf γ hγ g
    show R.cX.ρ (γ * g)⁻¹ (f ((finHom D.sp.X').rangeRestrict (γ * g))) = R.cX.ρ g⁻¹ (f ((finHom D.sp.X').rangeRestrict g))
    have := hf ⟨γ, hγ⟩ ((finHom D.sp.X').rangeRestrict g) 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at this
    rw [map_mul]
    erw [this]
    show R.cX.ρ (γ * g)⁻¹ (R.cX.ρ γ _) = _
    rw [_root_.mul_inv_rev, map_mul]
    exact congrArg (R.cX.ρ g⁻¹) (hinv γ _)
  choose y' hy'1 hy'2 using fun c => GlobalTheory.DefiniteMult.exists_fin_lift D.sp.X' ((R.B.R t).pres.y c)
  have hnorm : ∀ k : J, ‖((χ k : ℂˣ) : ℂ)‖ = 1 := fun k => GlobalTheory.AdelicScalar.norm_levFn _ _ _
  have hloc : ∀ f, f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ → ∀ c, ∀ k (hk : k ∈ Ω),
      R.cX.ext f (y' c * k) = ((χ ⟨_, (hK k).1 hk⟩ : ℂˣ) : ℂ) • R.cX.ρ k⁻¹ (f ((R.B.R t).pres.y c)) := by
    intro f hf c k hk
    have e1 : (finHom D.sp.X').rangeRestrict (y' c * k) = (R.B.R t).pres.y c * (finHom D.sp.X').rangeRestrict k := by
      rw [MonoidHom.map_mul, hy'2]
    have e2 := GlobalTheory.DefiniteMult.adForms_level hf ((R.B.R t).pres.y c) ⟨_, (hK k).1 hk⟩
    have e3 : R.cX.ρ (y' c * k)⁻¹ = R.cX.ρ k⁻¹ := by
      rw [_root_.mul_inv_rev, map_mul, hc.1 _ (inv_mem (hy'1 c)), mul_one]
    show R.cX.ρ (y' c * k)⁻¹ (f ((finHom D.sp.X').rangeRestrict (y' c * k))) = _
    refine (congrArg (R.cX.ρ (y' c * k)⁻¹) ((congrArg f e1).trans e2)).trans ?_
    refine (map_smul _ _ _).trans ?_
    exact congrArg (_ • ·) (LinearMap.congr_fun e3 _)
  let φ : GA D D.sp.X' → ℂ := fun g =>
    star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ
  have hpt : ∀ c, ∀ k ∈ Ω, φ (y' c * k) = star ⟪a, R.cX.ρ k⁻¹ ((R.HX t).e h ((R.B.R t).pres.y c))⟫_ℂ *
      ⟪a', R.cX.ρ k⁻¹ ((R.HX t).e h' ((R.B.R t).pres.y c))⟫_ℂ := by
    intro c k hk
    have key : ∀ z p q : ℂ, ‖z‖ = 1 → star (z * p) * (z * q) = star p * q := by
      intro z p q hz
      have e : star z * z = 1 := by
        rw [Complex.star_def, Complex.conj_mul', hz]; norm_num
      rw [star_mul']
      linear_combination (star p * q) * e
    have hz := hnorm ⟨_, (hK k).1 hk⟩
    refine (congrArg₂ (fun u v : ℂ => star u * v) (congrArg (inner ℂ a) (hloc _ (hF h) c k hk))
      (congrArg (inner ℂ a') (hloc _ (hF h') c k hk))).trans ?_
    simp only [inner_smul_right]
    exact key _ _ _ hz
  have hmeas : ∀ x y : R.cX.W, Measurable fun g => ⟪x, R.cX.ρ g y⟫_ℂ := fun x y =>
    (continuous_const.inner (hc.2.2.1 y)).measurable
  have hirr : ∀ U : Submodule ℂ R.cX.W, (∀ g ∈ Ω, U.map (R.cX.ρ g) ≤ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hc.2.2.2.2 U fun g => ?_
    obtain ⟨a0, ha0, k0, hk0, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D D.sp.X').1 g
    rw [map_mul, hc.1 k0 hk0, mul_one]
    refine hU a0 ((hK a0).2 ?_)
    have e : (finHom D.sp.X').rangeRestrict a0 = 1 := Subtype.ext ha0
    exact e ▸ J.one_mem
  have hS := fun c => GlobalTheory.T.schur_orthogonality_subgroup_measure_one (R.νX t) Ω hΩo.measurableSet hΩ1 R.cX.ρ hc.2.1 hmeas hirr a a'
    ((R.HX t).e h ((R.B.R t).pres.y c)) ((R.HX t).e h' ((R.B.R t).pres.y c))
  have huniq : ∀ x : GA D D.sp.X', ∃! i, ∃ γ ∈ GQ D.sp.X', ∃ k ∈ Ω, x = γ * y' i * k := by
    intro x
    refine (existsUnique_congr fun i => ?_).1 ((R.B.R t).pres.reps ((finHom D.sp.X').rangeRestrict x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, (γ * y' i)⁻¹ * x, (hK _).2 ?_, by group⟩
      have e' : (finHom D.sp.X').rangeRestrict ((γ * y' i)⁻¹ * x) = k := by
        simp only [map_mul, map_inv, hy'2, e]
        change (Bridge.ratF D.sp.X' γ * _)⁻¹ * (Bridge.ratF D.sp.X' γ * _ * k) = _
        exact inv_mul_cancel_left _ _
      exact cast (congrArg (· ∈ J) e').symm k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      refine ⟨⟨γ, hγ⟩, ⟨_, (hK k).1 hk⟩, ?_⟩
      simp only [map_mul, hy'2]
      rfl
  have hSet : ∀ c, {γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω} =
      Subtype.val '' (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c) : Set (GQ D.sp.X')) := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, Bridge.mem_stab]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨γ, h1⟩, ?_, rfl⟩
      have := (hK _).1 h2
      simp only [map_mul, map_inv, hy'2] at this
      exact this
    · rintro ⟨δ, h2, rfl⟩
      refine ⟨δ.2, (hK _).2 ?_⟩
      simp only [map_mul, map_inv, hy'2]
      exact h2
  have hfinS : ∀ c, Finite (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) := fun c =>
    Finite.of_equiv _ ((R.B.R t).pres.stabI c).toEquiv
  have hfin : ∀ c, {γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω}.Finite := fun c => by
    rw [hSet]
    haveI := hfinS c
    exact (Set.toFinite _).image _
  have hcard : ∀ c, ({γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω}.ncard : ℂ) =
      (Nat.card (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) : ℂ) := fun c => by
    have e := congrArg Set.ncard (hSet c)
    rw [Set.ncard_image_of_injective _ Subtype.val_injective] at e
    exact (congrArg (Nat.cast : ℕ → ℂ) e).trans (congrArg (Nat.cast : ℕ → ℂ) (Nat.card_coe_set_eq _).symm)
  have hintc : ∀ c, IntegrableOn (fun k => φ (y' c * k)) Ω (R.νX t) := fun c =>
    (hS c).1.congr_fun (fun k hk => (hpt c k hk).symm) hΩo.measurableSet
  have hIc : ∀ c, ∫ k in (Ω : Set (GA D D.sp.X')), φ (y' c * k) ∂(R.νX t) =
      ∫ k in (Ω : Set (GA D D.sp.X')), star ⟪a, R.cX.ρ k⁻¹ ((R.HX t).e h ((R.B.R t).pres.y c))⟫_ℂ *
        ⟪a', R.cX.ρ k⁻¹ ((R.HX t).e h' ((R.B.R t).pres.y c))⟫_ℂ ∂(R.νX t) := fun c =>
    setIntegral_congr_fun hΩo.measurableSet fun k hk => hpt c k hk
  have hfl : ∀ γ : GA D D.sp.X', γ ∈ GQ D.sp.X' → ∀ x : GA D D.sp.X', φ (γ * x) = φ x := fun γ hγ x => by
    show star ⟪a, R.cX.ext ((R.HX t).e h) (γ * x)⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') (γ * x)⟫_ℂ =
      star ⟪a, R.cX.ext ((R.HX t).e h) x⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') x⟫_ℂ
    exact congrArg₂ (fun u v => star ⟪a, u⟫_ℂ * ⟪a', v⟫_ℂ) (hext _ (hF h) γ hγ x) (hext _ (hF h') γ hγ x)
  have U1 := GlobalTheory.T.integral_fundamentalDomain_eq_sum_doubleCoset_unfold (GA D D.sp.X') (R.νX t) (GQ D.sp.X') Ω (R.fdX t) hμ.2 hΩo _ y' huniq hfin φ hfl hintc
  refine ⟨U1.1, ?_⟩
  change (Module.finrank ℂ R.cX.W : ℂ) * ∫ g in R.fdX t, φ g ∂(R.νX t) = _
  refine (congrArg (_ * ·) U1.2).trans ?_
  refine Eq.trans ?_ (congrArg (⟪a', a⟫_ℂ * ·) (hH.2.2 h h').symm)
  simp only [Bridge.adInner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine (congrArg₂ (fun (u v : ℂ) => (Module.finrank ℂ R.cX.W : ℂ) * (u⁻¹ * v)) (hcard c) (hIc c)).trans ?_
  linear_combination ((Nat.card (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) : ℂ)⁻¹) * (hS c).2

end GlobalTheory.Mem.SchurW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupFiniteDimensionalRepContainsHighestWStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_finiteDimensionalRep_contains_highestWeightRep : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V), (∀ (l : Module.Dual ℂ V) (v : V), Continuous fun u => l (ρ u v)) → ∃ (lam : DomWeight n) (f : (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam).IntertwiningMap ρ), f ≠ 0 := by
  first | exact @GlobalTheory.UnitaryContainsType.exists_smallRep_intertwining | exact GlobalTheory.UnitaryContainsType.exists_smallRep_intertwining | (intros; apply GlobalTheory.UnitaryContainsType.exists_smallRep_intertwining <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformiseStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_nonsplit_exists_conj_involution_uniformiser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w → ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q := by
  first | exact @GlobalTheory.InertPlaceConj.exists_conj_isUnramInv | exact GlobalTheory.InertPlaceConj.exists_conj_isUnramInv | (intros; apply GlobalTheory.InertPlaceConj.exists_conj_isUnramInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightFiltrationStrandDecompositionStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_filtration_strand_decomposition : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (m : ℕ), (∀ (k : ℤ) (σ : Weil h), ∀ v ∈ wtSpace a k, a.ρ σ v ∈ wtSpace a k) → (∀ (k : ℤ), ∀ v ∈ wtSpace a k, a.N v ∈ wtSpace a (k + 2)) → (∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥) → IsSubWD a (strand a.N (wtSpace a (-(m : ℤ))) m) ∧ IsSubWD a (lowPart (wtSpace a) a.N m) := by
  first | exact @GlobalTheory.WeilDeligne.PrimDecomp.SubStab.strand_and_lowPart_stable | exact GlobalTheory.WeilDeligne.PrimDecomp.SubStab.strand_and_lowPart_stable | (intros; apply GlobalTheory.WeilDeligne.PrimDecomp.SubStab.strand_and_lowPart_stable <;> assumption)
end

