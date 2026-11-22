import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieBundleIntersection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStabilizerIff
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Formalism.LatticeTheta.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWeightSpaceProjectiveTensorEq
section
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.WtRank

abbrev chr (k : Type) [Field k] (C : Type) [CommRing C] (χ : C →+* k) : k ⊗[ℤ] C →ₐ[k] k :=
  Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem finrank_fix {k A M : Type*} [Field k] [CommRing A] [Algebra k A] [AddCommGroup M] [Module A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] (e : A) (W : Submodule k M)
    (hW : ∀ m, m ∈ W ↔ e • m = m) :
    Module.finrank k W = Module.finrank k (M ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A M)) := by
  set f : M →ₗ[k] M := DistribSMul.toLinearMap k M (1 - e)
  have hker : W = LinearMap.ker f := by
    ext m
    rw [hW, LinearMap.mem_ker]
    simp only [f, DistribSMul.toLinearMap_apply, sub_smul, one_smul, sub_eq_zero, eq_comm]
  have hrange : (Ideal.span {1 - e} • ⊤ : Submodule A M).restrictScalars k = LinearMap.range f := by
    ext m
    rw [Submodule.restrictScalars_mem, Submodule.ideal_span_singleton_smul, LinearMap.mem_range,
      Submodule.mem_smul_pointwise_iff_exists]
    simp [f]
  have e1 := (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {1 - e} • ⊤ : Submodule A M)).finrank_eq
  rw [← e1, hrange, hker]
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  omega

theorem weight_finrank_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H), (letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom; Module.Projective (k ⊗[ℤ] C) H) → ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) = Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  intro k _ _ C _ _ _ H _ _ _ σ
  letI inst : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift
    (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom
  intro hP χ
  have hP' : Module.Projective (k ⊗[ℤ] C) H := hP
  have hact : ∀ (a : k ⊗[ℤ] C) (h : H), a • h = (Algebra.TensorProduct.lift
      (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)) a h := fun _ _ => rfl
  haveI : IsScalarTower k (k ⊗[ℤ] C) H := ⟨fun l a h => by
    rw [hact, hact, map_smul, LinearMap.smul_apply]⟩
  obtain ⟨e, he, h1, hn⟩ := GlobalTheory.T.exists_idempotent_local_of_character k (k ⊗[ℤ] C) (chr k C χ)
  have hσ : ∀ c, σ c = DistribSMul.toLinearMap k H ((1 : k) ⊗ₜ[ℤ] c) := by
    intro c; ext h
    rw [DistribSMul.toLinearMap_apply, hact]
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  have hlm : ∀ c, ((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c =
      DistribSMul.toLinearMap k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c) := by
    intro c; ext x
    simp [Algebra.TensorProduct.includeRight_apply]
  have eH : (⨅ c : C, (σ c).maxGenEigenspace (χ c)) =
      ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k H ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
    iInf_congr fun c => by rw [hσ]
  have eA : (⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) =
      ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
    iInf_congr fun c => by rw [hlm]
  rw [eH, eA]
  rw [finrank_fix e _ (GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq k C H χ e he h1 hn), finrank_fix e _ (GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq k C (k ⊗[ℤ] C) χ e he h1 hn),
    GlobalTheory.T.finrank_quot_one_sub_idempotent_eq_mul k (k ⊗[ℤ] C) (chr k C χ) e he h1 hn H]
  have hq : Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) =
      Module.finrank k (H ⧸ (RingHom.ker (chr k C χ) • ⊤ : Submodule (k ⊗[ℤ] C) H)) := by
    have heq : GlobalTheory.HTRho.mSub σ χ ⊤ = (RingHom.ker (chr k C χ) • ⊤ : Submodule (k ⊗[ℤ] C) H).restrictScalars k := by
      ext x; rw [Submodule.restrictScalars_mem]; exact GlobalTheory.T.characterAugmentationSubspace_top_eq_ker_smul k C H σ χ x
    rw [heq]; exact (Submodule.Quotient.restrictScalarsEquiv k _).finrank_eq
  rw [hq]
  congr 1
  have hI : (Ideal.span {1 - e} • ⊤ : Submodule (k ⊗[ℤ] C) (k ⊗[ℤ] C)) = Ideal.span {1 - e} := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact ((Submodule.quotEquivOfEq _ _ hI).restrictScalars k).finrank_eq.symm

end GlobalTheory.WtRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumConjClassesCentralizerOrbitsEqPairOrbits
section
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

noncomputable section

namespace GlobalTheory.OrbitUnfold

def conjClassesEquivOrbits (Γ : Type) [Group Γ] :
    ConjClasses Γ ≃ MulAction.orbitRel.Quotient Γ (ConjSelf Γ) :=
  Quotient.congr (⟨of, val, fun _ => rfl, fun _ => rfl⟩ : Γ ≃ ConjSelf Γ) (by
    intro a b
    show IsConj a b ↔ of a ∈ MulAction.orbit Γ (of b)
    rw [isConj_comm, isConj_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, congrArg of hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, congrArg val hc⟩)

theorem conjClassesEquivOrbits_mk {Γ : Type} [Group Γ] (γ : Γ) :
    conjClassesEquivOrbits Γ (Quotient.mk (IsConj.setoid Γ) γ) =
      Quotient.mk (MulAction.orbitRel Γ (ConjSelf Γ)) (of γ) := rfl

theorem finsum_conjClasses_centralizer_orbits {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (_hstab : ∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite)
    (hsupp : ∀ y : Y, (Function.support (F y)).Finite)
    (hfin : {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite) :
    ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y,
      ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} :
        Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) = pairSum F := by
  set e := conjClassesEquivOrbits Γ
  have key := GlobalTheory.T.finsum_orbitRel_fibred_equivariant (H := Γ) (X := Y × ConjSelf Γ) (B := ConjSelf Γ) (E := Y)
    Prod.snd (fun _ _ => rfl) (fun b => Subgroup.centralizer {val b})
    (fun b => by rw [stabilizer_eq_centralizer])
    (fun b y => (y, b)) (fun b y y' h => congrArg Prod.fst h) (fun _ _ => rfl)
    (fun b x hx => ⟨x.1, Prod.ext rfl hx.symm⟩)
    (fun b h hh y => by
      have : h • b = b := by
        rw [← MulAction.mem_stabilizer_iff, stabilizer_eq_centralizer]; exact hh
      show (h • y, b) = (h • y, h • b)
      rw [this])
    (fun q => of (Quotient.out (e.symm q)))
    (fun q => by
      show Quotient.mk _ (of (Quotient.out (e.symm q))) = q
      have hout : ∀ c : ConjClasses Γ, (Quotient.mk (IsConj.setoid Γ) (Quotient.out c) : ConjClasses Γ) = c :=
        fun c => Quotient.out_eq c
      rw [← conjClassesEquivOrbits_mk, hout, Equiv.apply_symm_apply])
    (fun o => pairTerm F (Quotient.out o))
    (GlobalTheory.T.finite_support_stabilizerWeightedPairTerm F hF hsupp hfin)
  unfold pairSum
  rw [key, ← finsum_comp_equiv e]
  refine finsum_congr (fun c => ?_)
  have hc : e.symm (e c) = c := e.symm_apply_apply c
  generalize e.symm (e c) = c' at hc ⊢
  subst hc
  simp only [val_of]
  refine finsum_congr (fun o => ?_)
  rw [pairTerm_out F hF]
  unfold pairTerm
  rw [stabilizer_pair]
  rfl

end GlobalTheory.OrbitUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRegroupCommutativeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_doubleCoset_regroup_commutative : ∀ (G : Type) [Group G] (T Γ C K' : Subgroup G) (φ : G → ℂ), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → C ≤ T → (∀ x : G, T ⊓ K'.map (MulAut.conj x).toMonoidHom ≤ C ∧ (T ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0) → (∀ t ∈ T, ∀ k ∈ K', ∀ x, φ (t * x * k) = φ x) → ∑ᶠ q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G), ((Nat.card ((Γ ⊓ T) ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out q) = (Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (Γ ⊓ C : Subgroup G) : ℂ) * ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K' : Set G), (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * φ (Quotient.out q) := by
  first | exact @GlobalTheory.finsum_doubleCoset_regroup | exact GlobalTheory.finsum_doubleCoset_regroup | (intros; apply GlobalTheory.finsum_doubleCoset_regroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOverConjPairsEqOrbitSum
section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_over_conj_pairs_eq_orbit_sum : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    (∀ x : X, Finite (MulAction.stabilizer H x)) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    ∀ x : X, ∑ᶠ O : {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) //
        (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x},
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O.1)) : ℂ)) *
          f (Quotient.out O.1).elt (Quotient.out O.1).pt =
      (1 / (Nat.card (MulAction.stabilizer H x) : ℂ)) * ∑ᶠ γ : H, f γ x := by
  first | exact @GlobalTheory.PtFib.ptFib_mass | exact GlobalTheory.PtFib.ptFib_mass | (intros; apply GlobalTheory.PtFib.ptFib_mass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeFormula
section
open MvPolynomial Finset Formalism.DegreeFormula

namespace GlobalTheory.FlagPoly

open MvPolynomial Finset in
private theorem coeff_linearForm_pow_eq_factorial_mul_prod {σ : Type} [Fintype σ] [DecidableEq σ] (c : σ → ℝ) (n : ℕ)
    (d : σ →₀ ℕ) (hd : d.degree = n) :
    coeff d ((∑ x, C (c x) * X x) ^ n) =
      (n.factorial : ℝ) * ∏ x, (c x ^ d x / ((d x).factorial : ℝ)) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    ← map_natCast (C : ℝ →+* MvPolynomial σ ℝ), ← mul_assoc, ← map_mul, coeff_C_mul,
    coeff_prod_X_pow]
  have hsum : ∑ i, d i = n := by
    rw [← hd, Finsupp.degree_eq_sum]
  rw [Finset.sum_eq_single (⇑d)]
  · have hind : d = Finsupp.indicator univ (fun i _ => d i) := by
      ext i; simp
    rw [if_pos hind, mul_one]
    have hspec := Nat.multinomial_spec (univ : Finset σ) (⇑d)
    rw [hsum] at hspec
    have hpos : (∏ i, ((d i).factorial : ℝ)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]; intro i _; exact_mod_cast (Nat.factorial_pos _).ne'
    rw [Finset.prod_div_distrib, ← hspec]
    push_cast
    field_simp
  · intro k _ hk
    rw [if_neg, mul_zero]
    intro h
    apply hk
    funext i
    have := congrArg (fun f : σ →₀ ℕ => f i) h
    simpa using this.symm
  · intro h
    exfalso; apply h
    rw [Finset.mem_piAntidiag]
    exact ⟨hsum, fun i _ => Finset.mem_univ i⟩

open MvPolynomial Finset in
private theorem prod_factorial_rev_eq_prod_sub (N : ℕ) :
    ∏ j : Fin N, ((j.rev : ℕ).factorial : ℝ) =
      ∏ i : Fin N, ∏ k ∈ Ioi i, (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by
  cases N with
  | zero => simp
  | succ n =>
    have h1 : ∏ i : Fin (n + 1), ∏ k ∈ Ioi i, (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) =
        (n.superFactorial : ℝ) := by
      rw [← Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) n, Matrix.det_vandermonde]
    rw [h1, ← Nat.prod_range_succ_factorial, Nat.cast_prod,
      ← Fin.prod_univ_eq_prod_range (fun x => ((x.factorial : ℕ) : ℝ)) (n + 1)]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun j => rfl)

open MvPolynomial Finset in
private theorem sum_sign_prod_pow_div_factorial_eq_prod {N : ℕ} (v : Fin N → ℝ) :
    ∑ π : Equiv.Perm (Fin N), ((Equiv.Perm.sign π : ℤ) : ℝ) *
        ∏ i, (v i ^ (N - 1 - (π i : ℕ)) / ((N - 1 - (π i : ℕ)).factorial : ℝ)) =
      ∏ i : Fin N, ∏ k : Fin N,
        if i < k then (v i - v k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1 := by
  have hrev : ∀ j : Fin N, N - 1 - (j : ℕ) = (j.rev : ℕ) := by
    intro j; rw [Fin.val_rev]; omega
  have hterm : ∀ π : Equiv.Perm (Fin N),
      ∏ i, (v i ^ (N - 1 - (π i : ℕ)) / ((N - 1 - (π i : ℕ)).factorial : ℝ)) =
        (∏ i, Matrix.transpose (Matrix.projVandermonde 1 v) (π i) i) *
          ∏ j : Fin N, (((j.rev : ℕ).factorial : ℝ))⁻¹ := by
    intro π
    simp_rw [div_eq_mul_inv, Finset.prod_mul_distrib, hrev]
    congr 1
    · simp [Matrix.projVandermonde_apply]
    · exact Fintype.prod_equiv π _ _ (fun i => rfl)
  simp_rw [hterm, ← mul_assoc, ← Finset.sum_mul, ← Matrix.det_apply', Matrix.det_transpose,
    Matrix.det_projVandermonde, Finset.prod_inv_distrib, prod_factorial_rev_eq_prod_sub,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_div_distrib, div_eq_mul_inv]
  simp only [Pi.one_apply, one_mul]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  congr 1
  ext k
  simp

open MvPolynomial Finset in

theorem _root_.GlobalTheory.FlagPoly.flagDegFormula : _root_.Formalism.DegreeFormula.FlagDegFormula := by
  unfold _root_.Formalism.DegreeFormula.FlagDegFormula
  intro ι _ _ N lam
  unfold _root_.Formalism.DegreeFormula.flagDeg _root_.Formalism.DegreeFormula.weylProd _root_.Formalism.DegreeFormula.linRoot
  rw [neg_pow, ← map_one (C : ℝ →+* MvPolynomial (ι × Fin N) ℝ), ← map_neg, ← map_pow, _root_.Formalism.DegreeFormula.PPowSum.degFl_C_mul]
  unfold _root_.Formalism.DegreeFormula.degFl
  simp_rw [coeff_linearForm_pow_eq_factorial_mul_prod _ _ _ (_root_.Formalism.DegreeFormula.PPowSum.degree_permExp _)]
  have hexp : ∀ (σ : ι → Equiv.Perm (Fin N)) (τ : ι) (i : Fin N),
      (_root_.Formalism.DegreeFormula.permExp σ) (τ, i) = N - 1 - ((σ τ) i : ℕ) := by
    intro σ τ i
    unfold _root_.Formalism.DegreeFormula.permExp
    rfl
  simp_rw [Fintype.prod_prod_type, hexp]
  rw [← Finset.prod_congr rfl (fun τ _ => sum_sign_prod_pow_div_factorial_eq_prod (lam τ)),
    Fintype.prod_sum]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.FlagPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfEssentiallyEtaleLocalAlgebras
section
open IsLocalRing

namespace GlobalTheory

theorem flat_of_algHom_atPrime (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Etale R A] [Algebra.Etale R B] (p : Ideal B) [p.IsPrime] (φ : A →ₐ[R] Localization.AtPrime p) :
    φ.toRingHom.Flat := by
  obtain ⟨g, hg, ψ, hψ⟩ := GlobalTheory.T.algHom_localizationAtPrime_factors_through_away R A B p φ
  set h := Localization.awayLift (algebraMap B (Localization.AtPrime p)) g
    (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) with hh
  have e : φ.toRingHom = h.comp ψ.toRingHom := by ext a; exact (hψ a).symm
  rw [e]
  refine RingHom.Flat.comp ?_ ?_
  · letI : Algebra A (Localization.Away g) := ψ.toRingHom.toAlgebra
    haveI : IsScalarTower R A (Localization.Away g) :=
      IsScalarTower.of_algebraMap_eq (fun r => (ψ.commutes r).symm)
    haveI : Algebra.Etale A (Localization.Away g) := Algebra.Etale.of_restrictScalars R A _
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · letI : Algebra (Localization.Away g) (Localization.AtPrime p) := h.toAlgebra
    haveI : IsScalarTower B (Localization.Away g) (Localization.AtPrime p) :=
      IsScalarTower.of_algebraMap_eq (fun b => by
        change _ = h _
        simp [hh, Localization.awayLift, IsLocalization.Away.lift])
    have : Module.Flat (Localization.Away g) (Localization.AtPrime p) :=
      (Module.flat_iff_of_isLocalization (Localization.Away g) (Submonoid.powers g)
        (Localization.AtPrime p)).mpr inferInstance
    exact RingHom.flat_algebraMap_iff.mpr this

theorem flat_of_essEtale : ∀ (R L₁ L₂ : Type) [CommRing R] [CommRing L₁] [CommRing L₂] [Algebra R L₁] [Algebra R L₂] [Algebra L₁ L₂] [IsScalarTower R L₁ L₂], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₁)) → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₂)) → Module.Flat L₁ L₂ := by
  intro R L₁ L₂ _ _ _ _ _ _ _ ⟨A, _, _, _, q, _, ⟨e₁⟩⟩ ⟨A', _, _, _, q', _, ⟨e₂⟩⟩
  let φ : A →ₐ[R] Localization.AtPrime q' :=
    (e₂.symm.toAlgHom.comp (IsScalarTower.toAlgHom R L₁ L₂)).comp
      (e₁.toAlgHom.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q)))
  have hφ := flat_of_algHom_atPrime R A A' q' φ
  let f : A →+* L₁ := e₁.toRingHom.comp (algebraMap A (Localization.AtPrime q))
  letI : Algebra A L₁ := f.toAlgebra
  letI : Algebra A L₂ := ((algebraMap L₁ L₂).comp f).toAlgebra
  haveI : IsScalarTower A L₁ L₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e₁' : Localization.AtPrime q ≃ₐ[A] L₁ := { e₁ with commutes' := fun _ => rfl }
  haveI : IsLocalization q.primeCompl L₁ := IsLocalization.isLocalization_of_algEquiv q.primeCompl e₁'
  have hflat : Module.Flat A L₂ := by
    rw [← RingHom.flat_algebraMap_iff]
    have : algebraMap A L₂ = e₂.toRingHom.comp φ.toRingHom := by
      ext a; simp [φ, f, RingHom.algebraMap_toAlgebra]
    rw [this]
    exact RingHom.Flat.comp hφ (RingHom.Flat.of_bijective e₂.bijective)
  exact (Module.flat_iff_of_isLocalization L₁ q.primeCompl L₂).mpr hflat

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfLocalRetractionsModMaximalIdealPowStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_local_retractions_mod_maximalIdeal_pow : ∀ {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ], (∀ n : ℕ, ∃ ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1), ψ.comp φ = Ideal.Quotient.mk _) → (∀ n : ℕ, ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ → IsLocalHom g₂ → g₁.comp φ = g₂.comp φ → g₁ = g₂) → φ.Flat := by
  first | exact @GlobalTheory.flat_of_retractions_mod_pow | exact GlobalTheory.flat_of_retractions_mod_pow | (intros; apply GlobalTheory.flat_of_retractions_mod_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleAwayOfEtaleOffMaximalIdealStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyEtale_away_of_etale_off_maximalIdeal : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g) (TensorProduct R (Localization.Away g) A) := by
  first | exact @GlobalTheory.EtaleAway.formallyEtale_away | exact GlobalTheory.EtaleAway.formallyEtale_away | (intros; apply GlobalTheory.EtaleAway.formallyEtale_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierLipschitzOneVariableKernelEqStatement
section
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_lipschitzOneVariableKernel_eq : ∀ (k : ℕ), 2 ≤ k → Even k → ∀ (w : ℂ), w.im ≠ 0 → ∀ (x : ℝ), 𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) := by
  first | exact @GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow | exact GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow | (intros; apply GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclicStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ (η (inr s) : ℂ) = ζ ∧ ∀ X Y : G ⋊[φ] Γ → ℂ, ((Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g) * star (Y (inl g)) = ∑ a ∈ Finset.range (Nat.card Γ), ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a)) ∧ (Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = ∑ a ∈ Finset.range (Nat.card Γ), ζ ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) := by
  first | (exact @GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (exact GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (intros; apply GlobalTheory.Shin.CosetFourier.fourier_coset_sums  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDualStatement
section
open ReciprocityTheory.PGsh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_dual_frame_of_isSatFrame : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (i d : ℕ) (u : Fin i → Fin d → C), IsSatFrame v u → ∃ l : Fin i → Fin d → C, (∀ a e, IsIntV v (l a e)) ∧ ∀ a a', ∑ e, l a e * u a' e = if a = a' then 1 else 0 := by
  first | exact @GlobalTheory.FrameDual.frameDual | exact GlobalTheory.FrameDual.frameDual | (intros; apply GlobalTheory.FrameDual.frameDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMatrixCompositionUnique
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem isMat_calculus : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (e e' e'' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), (∀ X X' Y Y', IsMat e e' X Y → IsMat e' e'' X' Y' → IsMat e e'' (X' * X) (Y' * Y)) ∧ (∀ X Y Y', IsMat e e' X Y → IsMat e e' X Y' → Y = Y') ∧ ∀ c : Ainf p O, IsMat e e (c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) ((inA c : RL p O Λ) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ))) := by
  intro p _ O _ _ _ Λ _ _ N h e e' e''
  refine ⟨?_, ?_, ?_⟩
  · intro X X' Y Y' h1 h2 w
    rw [← Matrix.mulVec_mulVec, h1 w, h2 (Y *ᵥ w), Matrix.mulVec_mulVec]
  · intro X Y Y' h1 h2
    have key : ∀ w, Y *ᵥ w = Y' *ᵥ w := fun w => e'.injective ((h1 w).symm.trans (h2 w))
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    simpa using this
  · intro c w
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← map_smul, algebraMap_smul]

end GlobalTheory.DetInv
end

