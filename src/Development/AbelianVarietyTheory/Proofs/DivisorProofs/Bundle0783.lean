import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0024
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0017
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInvStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharpolyMemVirtualCharactersGLStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0036
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqOfIsPrimitiveOfEqOnEllipticFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0153
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0768
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabel
section
noncomputable section

namespace GlobalTheory.CuspFormula

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.GoodCharsCompare

theorem esymm_mem_virt (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d k s : ℕ) :
    (fun x : GL (Fin d) F => (((Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)).map
      (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s) ∈ Virt ℂ ℂ (GL (Fin d) F) := by
  refine GlobalTheory.T.esymm_mem_virtualCharacters_of_powerSum_eigenvalues _ _ _ (GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL F θ hθ d k) (fun x j _ => ?_) s
  rw [rootSum, ← Matrix.charpoly_map, ← Matrix.charpoly_map, Units.val_pow_eq_pow_val, Matrix.map_pow,
    GlobalTheory.T.roots_charpoly_pow_eq_map_pow, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp, map_pow, ← pow_mul, mul_comm]

theorem exists_regular (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d : ℕ) (hd : 0 < d)
    (χ : GL (Fin d) F → ℂ) (hi : IsIrrChar ℂ ℂ χ) (hp : IsPrimitive (extZero χ)) :
    ∃ k : ℕ, (∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1]) ∧
      ∀ x : GL (Fin d) F, χ x = (-1) ^ (d - 1) *
        psi (rootSum θ k) (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) := by
  classical
  have h := isCharacter_of_isIrreducibleCharacter_complex hi
  have hv : χ ∈ Virt ℂ ℂ (GL (Fin d) F) := AddSubgroup.subset_closure h
  obtain ⟨hval, -, hip, hcl⟩ := GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties F d χ
  have hc := hcl (GlobalTheory.T.isCharacterOverSubfield_restrict_classFunction_one ℂ ℂ _ χ h).2.1
  have hr : Module.finrank F (Fin d → F) = d := by simp
  have hg := generalLinearGroupCardComplex_finiteField_ne_zero F d
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨a, ha, -⟩ := GlobalTheory.T.exists_int_coeff_primitive_GL_character F θ hθ d χ hd h hp
  have haa := sum_coef_mul_eq_pair F θ hθ d hd χ χ h h hp hp a a ha ha
  rw [GlobalTheory.T.finiteGroupFunctionPairing_self_irreducible_algClosed ℂ _ χ hi, mul_one] at haa
  have hinv : ∀ k l i : ℕ, k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ d - 1] → a k = a l := by
    intro k l i hkl
    have := GlobalTheory.T.innerProduct_rootPowerSum_eq_of_frobenius_modEq F (Fin d → F) θ _ hc hp (by rw [hr]; exact hd) k l i (by rw [hr]; exact hkl)
    rw [ha, ha] at this
    exact_mod_cast mul_right_cancel₀ hg this
  have hdvd : ∀ k s : ℕ, (d : ℤ) ∣ ∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, Nat.card F ^ i) := by
    intro k s
    obtain ⟨m, hm⟩ := GlobalTheory.T.virtualCharacter_inner_eq_int_mul_card _ χ _ hv (esymm_mem_virt F θ hθ d k s)
    refine ⟨m, ?_⟩
    have : Fintype (GL (Fin d) F) := Fintype.ofFinite _
    have key : ((∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, Nat.card F ^ i) : ℤ) : ℂ) * glCard F d =
        d * (m * glCard F d) := by
      push_cast
      rw [Finset.sum_mul]
      simp only [← ha, hip]
      rw [glCard, ← hm]
      simp only [finsum_eq_sum_of_fintype]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.mul_sum, hval, ← star_sum, Matrix.charpoly_toLin']
      by_cases hx : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧
          LinearMap.charpoly (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = f ^ m
      · obtain ⟨f, m, hf, hirr, -, e⟩ := hx
        rw [Matrix.charpoly_toLin'] at e
        have hdeg : (f ^ m).natDegree = d := by rw [← e, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        have := GlobalTheory.T.natDegree_mul_esymm_roots_pow' F θ f m k s hf hirr
        rw [hdeg] at this
        rw [e, ← this, star_mul', star_natCast]
        ring
      · have := GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F _ _ hc hp (by rw [hr]; exact hd) _ hx
        rw [hval] at this
        simp [this]
    rw [← mul_assoc] at key
    exact_mod_cast mul_right_cancel₀ hg key
  obtain ⟨k, hk0, hk⟩ := GlobalTheory.T.exists_regular_exponent_of_sum_sq_eq' _ d a hq hd hinv (by simp only [sq]; exact_mod_cast haa)
    (GlobalTheory.T.dvd_of_period_of_dvd_sum_powersetCard' _ d a hq hd hinv hdvd)
  refine ⟨k, hk, ?_⟩
  obtain ⟨h', hn⟩ := GlobalTheory.T.isCharacter_cuspidal_rootSum_regular F θ hθ d k hd hk
  have hv' := AddSubgroup.subset_closure (k := {χ | IsChar ℂ ℂ χ}) h'
  have hsq : ((-1 : ℂ) ^ (d - 1)) * (-1) ^ (d - 1) = 1 := by rw [← mul_pow]; simp
  have hi' := ((GlobalTheory.T.irreducible_of_virtualCharacter_norm_one _ _ hv' (by
    rw [hip] at hn
    rw [← glCard, ← hn]
    refine finsum_congr fun x => ?_
    rw [star_mul', star_pow, star_neg, star_one, mul_mul_mul_comm, hsq, one_mul])).2 h').1
  by_contra hne
  have h0 := GlobalTheory.T.finiteGroupFunctionPairing_eq_zero_of_distinct_irreducible _ _ _ hi hi' (fun e => hne (congrFun e))
  have h1 := GlobalTheory.T.invertibleEndomorphismInnerProduct_primitive_mobiusInverse F (Fin d → F) _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1 _ hp
  rw [ha, hip] at h1
  rw [pair, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact hg (inv_eq_zero.1 h0)
  · have h2 : ∑ᶠ x : GL (Fin d) F, χ x * ((-1) ^ (d - 1) * psi (rootSum θ k) (Fin d → F)
        (Matrix.toLin' ((x⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F))) = (-1) ^ (d - 1) * (a k * glCard F d) := by
      have : Fintype (GL (Fin d) F) := Fintype.ofFinite _
      rw [← h1]
      simp only [finsum_eq_sum_of_fintype]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← GlobalTheory.T.star_virtualCharacter_eq_apply_inv _ _ hv' x, hval, star_mul', star_pow, star_neg, star_one]
      ring
    rw [h2] at h0
    exact mul_ne_zero (pow_ne_zero _ (by simp)) (mul_ne_zero (by exact_mod_cast hk0) hg) h0

variable {g : ℕ} [Fact g.Prime]

theorem cuspVal_eq_psi (ω : Fbar g →*₀ ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 0 < Fintype.card ι)
    {x : Fbar g} (hx : x ^ (g ^ Fintype.card ι - 1) = 1) {k : ℕ} (hk : ω x = rootC (g ^ Fintype.card ι - 1) ^ k)
    (M : Matrix ι ι (ZMod g)) (hM : M.det ≠ 0) :
    cuspVal ω x M = (-1) ^ (Fintype.card ι - 1) *
      psi (rootSum (ω : Fbar g →* ℂ) k) (ι → ZMod g) (Matrix.toLin' M) := by
  classical
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hs := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod g) (ω : Fbar g →* ℂ) k).1
  unfold cuspVal
  split_ifs with hh
  · obtain ⟨p, m, hp, hm⟩ := hh
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_aeval_eq_zero (Fbar g) p (degree_pos_of_irreducible hp).ne'
    have hdeg := M.charpoly_natDegree_eq_dim
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · rw [hm] at hdeg
        simp at hdeg
        omega
      · exact h
    have hf : M.charpoly = minpoly (ZMod g) y ^ m := by
      have h1 := minpoly.eq_of_irreducible hp hy
      have h2 : p.leadingCoeff ^ m = 1 := by
        rw [← leadingCoeff_pow, ← hm]
        exact M.charpoly_monic
      rw [← h1, mul_pow, ← C_pow, inv_pow, h2, inv_one, C_1, mul_one, hm]
    have hirr := minpoly.irreducible (isInt y)
    have hR : (rootsBar M.charpoly).toFinset = (rootsBar (minpoly (ZMod g) y)).toFinset := by
      rw [hf, rootsBar_pow, Multiset.toFinset_nsmul _ _ hm0.ne']
    have hcard : (rootsBar M.charpoly).toFinset.card = dg y := by
      rw [hR, Multiset.toFinset_card_of_nodup (nodup_minpoly y), card_rootsBar]
    have he := fun z (hz : aeval z (minpoly (ZMod g) y) = 0) => GlobalTheory.T.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace' (ZMod g) ι M _ z hirr hz
    rw [GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_primary_eq (ZMod g) _ _ hs _ _ m _ (minpoly.monic (isInt y)) hirr hm0
      (by rw [Matrix.charpoly_toLin', hf]) (he y (minpoly.aeval _ _)), Nat.card_zmod]
    congr 1
    have e1 : rootSum (ω : Fbar g →* ℂ) k (minpoly (ZMod g) y) =
        ∑ z ∈ (rootsBar M.charpoly).toFinset, ω z ^ k := by
      rw [hR, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, (nodup_minpoly y).dedup]
      rfl
    rw [e1, Finset.sum_mul]
    convert Finset.sum_congr rfl (s₁ := (rootsBar M.charpoly).toFinset) fun z hz => ?_
    have hz1 := root_pow hM hp hm (Multiset.mem_toFinset.1 hz)
    have hz2 : aeval z (minpoly (ZMod g) y) = 0 := by
      rw [hR, Multiset.mem_toFinset] at hz
      exact (mem_rootsBar hirr.ne_zero).1 hz
    obtain ⟨a, ha⟩ := exists_log ω hd hz1
    have ht := Nat.eq_of_mul_eq_mul_left (dg_pos y) ((he z hz2).symm.trans (he y (minpoly.aeval _ _)))
    rw [labelChar_eq ω hd hx ha, hk, ha, ← pow_mul, ← pow_mul, mul_comm a k, ht]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hcard]
  · rw [GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow (ZMod g) _ _ (fun e u => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj _ _ _ _ e u) (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse _ _ _ hs) (by simpa using hd),
      mul_zero]
    rintro ⟨f, m, -, hf, -, e⟩
    exact hh ⟨f, m, hf, by rw [← e, Matrix.charpoly_toLin']⟩

theorem exists_label {ω : Fbar g →*₀ ℂ} (hω : Function.Injective ω) {d : ℕ} (hd : 0 < d) {k : ℕ}
    (hk : ∀ i : ℕ, 0 < i → i < d → ¬ k * g ^ i ≡ k [MOD g ^ d - 1]) :
    ∃ x : Fbar g, x ^ (g ^ d - 1) = 1 ∧ ω x = rootC (g ^ d - 1) ^ k ∧ (minpoly (ZMod g) x).natDegree = d := by
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hprim := rootC_prim (g := g) hd
  obtain ⟨x, hx, hx'⟩ := exists_preimage hω hd (z := rootC (g ^ d - 1) ^ k)
    (by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow])
  refine ⟨x, hx, hx', (GlobalTheory.T.regular_iff_natDegree_and_exists_elliptic_GL (ZMod g) d hd x (by simpa [Nat.card_zmod] using hx)).1.1 fun e he hed h => ?_⟩
  rw [Nat.card_zmod] at h
  have h1 := congrArg ω h
  rw [map_pow, hx', ← pow_mul] at h1
  have h0 := hprim.ne_zero (g_pow_sub_pos hd).ne'
  have hu : (Units.mk0 _ h0) ^ (k * g ^ e) = (Units.mk0 _ h0) ^ k := by
    ext; simpa using h1
  rw [pow_eq_pow_iff_modEq, ← orderOf_units, Units.val_mk0, ← hprim.eq_orderOf] at hu
  exact hk e he hed hu

end GlobalTheory.CuspFormula
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonicSimpleRootGeneratorResidue
section
open IsLocalRing GlobalTheory.Toroidal Polynomial

namespace GlobalTheory

theorem exists_monic_simple_root_generator_residue : ∀ (O R' Ω : Type) [CommRing O] [IsLocalRing O] [CommRing R']
    [IsLocalRing R'] [Field Ω] (φ' : O →+* R') (u' : R' →+* Ω), IsEtaleCompletion φ' →
    ((residue R').comp φ').FormallyUnramified → RingHom.ker u' = maximalIdeal R' →
    ∃ (G : Polynomial O) (β : Ω), G.Monic ∧ (G.map (u'.comp φ')).eval β = 0 ∧
      (G.map (u'.comp φ')).derivative.eval β ≠ 0 ∧
      ∀ r : R', ∃ q : Polynomial O, u' r = (q.map (u'.comp φ')).eval β := by
  intro O R' Ω _ _ _ _ _ φ u hφ hur hker
  obtain ⟨-, hmax, hfin⟩ := hφ
  haveI : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : φ a ∈ maximalIdeal R' := hmax ▸ Ideal.mem_map_of_mem φ ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 h1 ha
  have hcomp : (ResidueField.map φ).comp (residue O) = (residue R').comp φ :=
    ResidueField.map_comp_residue φ
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← hcomp] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hur' : (ResidueField.map φ).FormallyUnramified := by
    rw [← hcomp] at hur
    exact RingHom.FormallyUnramified.of_comp hur
  letI := (ResidueField.map φ).toAlgebra
  haveI : FiniteDimensional (ResidueField O) (ResidueField R') := hfin'
  haveI : Algebra.FormallyUnramified (ResidueField O) (ResidueField R') := hur'
  haveI : Algebra.IsSeparable (ResidueField O) (ResidueField R') :=
    Algebra.FormallyUnramified.isSeparable _ _
  let ι : ResidueField R' →+* Ω := Ideal.Quotient.lift (maximalIdeal R') u
    (fun a ha => by rwa [← RingHom.mem_ker, hker])
  have hι : ∀ r, ι (residue R' r) = u r := fun r => Ideal.Quotient.lift_mk _ _ _
  have hres : ∀ (P : O[X]) (x : ResidueField R'),
      (P.map (u.comp φ)).eval (ι x) = ι (aeval x (P.map (residue O))) := by
    intro P x
    rw [aeval_def, hom_eval₂, eval₂_map, eval_map]
    congr 1
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField O) (ResidueField R')
  have hint : IsIntegral (ResidueField O) α := Algebra.IsIntegral.isIntegral α
  have hpm : (minpoly (ResidueField O) α).Monic := minpoly.monic hint
  have hlift : minpoly (ResidueField O) α ∈ lifts (residue O) :=
    (lifts_iff_coeff_lifts _).2 fun n => residue_surjective _
  obtain ⟨G, hGmap, -, hGm⟩ := lifts_and_degree_eq_and_monic hlift hpm
  refine ⟨G, ι α, hGm, ?_, ?_, ?_⟩
  · rw [hres, hGmap, minpoly.aeval, map_zero]
  · rw [derivative_map, hres, ← derivative_map, hGmap]
    refine (map_ne_zero ι).2 ?_
    exact (Algebra.IsSeparable.isSeparable (ResidueField O) α).aeval_derivative_ne_zero (minpoly.aeval _ _)
  · intro r
    have hr : residue R' r ∈ Algebra.adjoin (ResidueField O) {α} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
        IntermediateField.mem_toSubalgebra, hα]
      exact IntermediateField.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
    obtain ⟨pb, hpb⟩ := hr
    obtain ⟨P, hP⟩ := map_surjective (residue O) residue_surjective pb
    refine ⟨P, ?_⟩
    rw [hres, hP, ← hι]
    exact congrArg ι hpb.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionAdelicFromArchimedean
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

noncomputable section
namespace GlobalTheory
open Classical

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

theorem ainf_single_mul (a b : w.Completion) :
    (show Ainf F from Pi.single w (a * b)) = (show Ainf F from Pi.single w a) * (show Ainf F from Pi.single w b) := by
  funext u
  change (Pi.single w (a*b) : ∀ v : InfinitePlace F, v.Completion) u =
    (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w b : ∀ v : InfinitePlace F, v.Completion) u
  by_cases h : u = w
  · subst h; simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h, mul_zero]

theorem ainf_idem_mul (e : Ainf F) (h1 : e w = 1) (h0 : ∀ u, u ≠ w → e u = 0) (a : w.Completion) :
    e * (show Ainf F from Pi.single w a) = (show Ainf F from Pi.single w a) := by
  funext u
  change (e : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u = (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u
  by_cases h : u = w
  · subst h; rw [h1, one_mul]
  · simp only [Pi.single_eq_of_ne h, mul_zero]

theorem ainf_single_one (e : Ainf F) (h1 : e w = 1) (h0 : ∀ u, u ≠ w → e u = 0) :
    (show Ainf F from Pi.single w 1) = e := by
  funext u
  change (Pi.single w 1 : ∀ v : InfinitePlace F, v.Completion) u = e u
  by_cases h : u = w
  · subst h; rw [h1, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, h0 u h]

theorem af_zero (y : Af F) (h : ∀ v, evalV F v y = 0) : y = 0 := by
  ext v
  exact congrArg _ (h v)

theorem af_ext {p q : AF F} (h1 : fstA F p = fstA F q) (h2 : sndA F p = sndA F q) : p = q :=
  Prod.ext h1 h2

def placeAtInf : w.Completion →ₗ[F] AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).comp (LinearMap.single F (fun u : InfinitePlace F => u.Completion) w)

theorem fstA_placeAtInf (a : w.Completion) : fstA F (placeAtInf F w a) = (show Ainf F from Pi.single w a) := rfl
theorem sndA_placeAtInf (a : w.Completion) : sndA F (placeAtInf F w a) = 0 := rfl

theorem placeAtInf_mul (a b : w.Completion) :
    placeAtInf F w (a * b) = placeAtInf F w a * placeAtInf F w b := by
  apply af_ext
  · have e2 : fstA F (placeAtInf F w a * placeAtInf F w b) =
        fstA F (placeAtInf F w a) * fstA F (placeAtInf F w b) := map_mul (fstA F) _ _
    exact (fstA_placeAtInf F w (a * b)).trans ((ainf_single_mul F w a b).trans
      (e2.trans (congrArg₂ (· * ·) (fstA_placeAtInf F w a) (fstA_placeAtInf F w b))).symm)
  · have e2 : sndA F (placeAtInf F w a * placeAtInf F w b) =
        sndA F (placeAtInf F w a) * sndA F (placeAtInf F w b) := map_mul (sndA F) _ _
    exact (sndA_placeAtInf F w (a * b)).trans ((mul_zero (0 : Af F)).symm.trans
      (e2.trans (congrArg₂ (· * ·) (sndA_placeAtInf F w a) (sndA_placeAtInf F w b))).symm)

variable {F w}

theorem idem_mul_placeAtInf {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (a : w.Completion) :
    ε * placeAtInf F w a = placeAtInf F w a := by
  apply af_ext
  · have e2 : fstA F (ε * placeAtInf F w a) = fstA F ε * fstA F (placeAtInf F w a) := map_mul (fstA F) _ _
    exact e2.trans ((congrArg (fstA F ε * ·) (fstA_placeAtInf F w a)).trans
      ((ainf_idem_mul F w _ (hε.1 w (Finset.mem_singleton_self w))
        (fun u hu => hε.2.1 u (by simpa using hu)) a).trans (fstA_placeAtInf F w a).symm))
  · have e2 : sndA F (ε * placeAtInf F w a) = sndA F ε * sndA F (placeAtInf F w a) := map_mul (sndA F) _ _
    exact e2.trans ((congrArg (sndA F ε * ·) (sndA_placeAtInf F w a)).trans
      ((mul_zero _).trans (sndA_placeAtInf F w a).symm))

theorem placeAtInf_one {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) : placeAtInf F w 1 = ε := by
  apply af_ext
  · refine (fstA_placeAtInf F w 1).trans ?_
    exact ainf_single_one F w _ (hε.1 w (Finset.mem_singleton_self w))
      (fun u hu => hε.2.1 u (by simpa using hu))
  · refine (sndA_placeAtInf F w 1).trans ?_
    exact (af_zero F _ (fun v => hε.2.2.2 v (Finset.notMem_empty v))).symm

variable (F w) (E : Type) [Field E] [Algebra F E]

def placeAtInfE : w.Completion ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  LinearMap.rTensor E (placeAtInf F w)

theorem placeAtInfE_tmul (a : w.Completion) (e : E) :
    placeAtInfE F w E (a ⊗ₜ e) = placeAtInf F w a ⊗ₜ e := rfl

theorem placeAtInfE_mul (x y : w.Completion ⊗[F] E) :
    placeAtInfE F w E (x * y) = placeAtInfE F w E x * placeAtInfE F w E y := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add a b ha hb => rw [add_mul, map_add, map_add, ha, hb, add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add c d hc hd => rw [mul_add, map_add, map_add, hc, hd, mul_add]
    | tmul b f =>
      unfold placeAtInfE
      rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul, placeAtInf_mul]

theorem placeAtInfE_sig (σ : E →ₐ[F] E) (x : w.Completion ⊗[F] E) :
    placeAtInfE F w E (sigR w.Completion σ x) = sigR (AF F) σ (placeAtInfE F w E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, placeAtInfE_tmul]

variable {F w E}

theorem idem_mul_placeAtInfE {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (x : w.Completion ⊗[F] E) :
    algebraMap (AF F) (AF F ⊗[F] E) ε * placeAtInfE F w E x = placeAtInfE F w E x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
  | tmul a e =>
    rw [placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, Algebra.algebraMap_self, RingHom.id_apply, idem_mul_placeAtInf hε]

theorem placeAtInfE_incl {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (c : E) :
    placeAtInfE F w E (inclR w.Completion c) = algebraMap (AF F) (AF F ⊗[F] E) ε * inclR (AF F) c := by
  simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, Algebra.algebraMap_self, RingHom.id_apply, placeAtInf_one hε]

theorem normEq_inf_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : InfinitePlace F) (ε : AF F), IsPlacesIdem {w} ∅ ε → ∀ c : E,
    (∃ t : w.Completion ⊗[F] E, t * sigR w.Completion σ t + inclR w.Completion c = 0) →
    ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  intro F E _ _ _ _ σ w ε hε c ⟨t, ht⟩
  refine ⟨placeAtInfE F w E t, ?_⟩
  rw [← placeAtInfE_sig, ← placeAtInfE_mul, mul_add, idem_mul_placeAtInfE hε, ← placeAtInfE_incl hε,
    ← map_add, ht, map_zero]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlacesIdempotentNearOneAdeles
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section
namespace GlobalTheory

open Filter

theorem placesIdem_mem_nhds_one (F : Type) [Field F] [NumberField F] (U : Set (AF F)) (hU : U ∈ 𝓝 (1 : AF F)) :
    ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F),
      IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U := by
  classical
  let x : Finset (HeightOneSpectrum (𝓞 F)) → Π v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun T v => if v ∈ T then ⟨1, (v.adicCompletionIntegers F).one_mem⟩ else ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  let one' : Π v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨1, (v.adicCompletionIntegers F).one_mem⟩
  let sm := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  let e : Finset (HeightOneSpectrum (𝓞 F)) → AF F := fun T => ((1 : Ainf F), (sm (x T) : Af F))
  have hx : Tendsto x atTop (𝓝 one') := by
    rw [tendsto_pi_nhds]
    intro v
    apply tendsto_atTop_of_eventually_const (i₀ := {v})
    intro T hT
    simp [x, one', hT (Finset.mem_singleton_self v)]
  have h1 : (sm one' : Af F) = 1 := by
    ext v; rfl
  have he : Tendsto e atTop (𝓝 (1 : AF F)) := by
    have hc : Continuous sm := RestrictedProduct.isEmbedding_structureMap.continuous
    have h2 : Tendsto (fun T => (sm (x T) : Af F)) atTop (𝓝 (1 : Af F)) := by
      have h3 := (hc.tendsto one').comp hx
      rw [h1] at h3
      exact h3
    exact Tendsto.prodMk_nhds tendsto_const_nhds h2
  obtain ⟨T, hT⟩ := (he.eventually hU).exists
  refine ⟨Finset.univ, T, e T, ⟨?_, ?_, ?_, ?_⟩, hT⟩
  · intro w _; rfl
  · intro w hw; exact absurd (Finset.mem_univ w) hw
  · intro v hv
    show ((x T v : v.adicCompletion F)) = 1
    simp [x, hv]
  · intro v hv
    show ((x T v : v.adicCompletion F)) = 0
    simp [x, hv]

theorem placesIdem_tendsto_one : ∀ (F : Type) [Field F] [NumberField F], ∀ U : Set (AF F), U ∈ 𝓝 (1 : AF F) →
    ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F),
      IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U :=
  fun F _ _ U hU => placesIdem_mem_nhds_one F U hU

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionStrictHenselisationClosedFibrePointStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_strictHenselisation_closedFibre_point : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := by
  first | exact @GlobalTheory.LocAcyc.exists_section_strictHenselisation_at_closed | exact GlobalTheory.LocAcyc.exists_section_strictHenselisation_at_closed | (intros; apply GlobalTheory.LocAcyc.exists_section_strictHenselisation_at_closed <;> assumption)
end

