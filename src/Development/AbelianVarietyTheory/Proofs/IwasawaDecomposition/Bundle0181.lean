import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrResidueLiftIrreducible
section
open IsLocalRing GlobalTheory.LN Polynomial

namespace GlobalTheory.UnramExt

theorem mem_smul_top_iff_repr {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ (I • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    have hle : (I • ⊤ : Submodule R M) ≤ Submodule.comap (b.coord i) I :=
      Submodule.smul_le.2 fun r hr m _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isAdicComplete_of_finite_basis {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) [hI : IsAdicComplete I R] :
    IsAdicComplete I M := by
  have htop : ∀ k : ℕ, (I ^ k • ⊤ : Submodule R R) = I ^ k := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus' (I := I) _ fun n => ?_
    have := hx n
    rw [SModEq.zero, mem_smul_top_iff_repr b] at this
    rw [SModEq.zero, htop]
    exact this i
  have hP' : IsPrecomplete I M := by
    rw [isPrecomplete_iff]
    intro F hF
    have hP := hI.toIsPrecomplete
    rw [isPrecomplete_iff] at hP
    have hc : ∀ i, ∃ L : R, ∀ k, b.repr (F k) i ≡ L [SMOD (I ^ k • ⊤ : Submodule R R)] := by
      intro i
      refine hP (fun k => b.repr (F k) i) fun {m n} hmn => ?_
      have := hF hmn
      rw [SModEq.sub_mem, mem_smul_top_iff_repr b] at this
      rw [SModEq.sub_mem, htop]
      simpa using this i
    choose L hL using hc
    refine ⟨∑ i, L i • b i, fun k => ?_⟩
    rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
    intro i
    have := hL i k
    rw [SModEq.sub_mem, htop] at this
    have hr : b.repr (∑ j, L j • b j) i = L i := by
      have h := congrFun (b.equivFun.apply_symm_apply L) i
      rwa [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply] at h
    rw [map_sub, Finsupp.sub_apply, hr]
    exact this
  exact { toIsHausdorff := hH, toIsPrecomplete := hP' }

theorem exists_unit_mul_pow {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    {π : V} (hπ : maximalIdeal V = Ideal.span {π}) (x : V) (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : V), IsUnit u ∧ x = u * π ^ n := by
  classical
  have hK : ⨅ n : ℕ, (maximalIdeal V) ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top
  have hex : ∃ n, x ∉ (maximalIdeal V) ^ n := by
    by_contra h
    push_neg at h
    apply hx
    have : x ∈ ⨅ n : ℕ, (maximalIdeal V) ^ n := (Submodule.mem_iInf _).2 h
    rwa [hK] at this
  have hspec := Nat.find_spec hex
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    rw [h0, pow_zero, Ideal.one_eq_top] at hspec
    exact hspec Submodule.mem_top
  have hmem : x ∈ (maximalIdeal V) ^ k := by
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    simpa using this
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
  obtain ⟨u, hu⟩ := hmem
  refine ⟨k, u, ?_, hu.symm⟩
  by_contra hnu
  have hu' : u ∈ maximalIdeal V := (mem_maximalIdeal u).2 hnu
  apply hspec
  rw [hk, ← hu, hπ, Ideal.span_singleton_pow, pow_succ]
  rw [hπ] at hu'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu'
  exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩

theorem isDomain_of_maximalIdeal_eq_span {V : Type} [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] {π : V} (hπ : maximalIdeal V = Ideal.span {π}) (hn : ∀ n : ℕ, π ^ n ≠ 0) :
    IsDomain V := by
  have : NoZeroDivisors V := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra h
    push_neg at h
    obtain ⟨n, u, hu, rfl⟩ := exists_unit_mul_pow hπ a h.1
    obtain ⟨m, w, hw, rfl⟩ := exists_unit_mul_pow hπ b h.2
    have : (u * w) * π ^ (n + m) = 0 := by rw [← hab]; ring
    exact hn (n + m) ((hu.mul hw).mul_right_eq_zero.1 this)
  exact NoZeroDivisors.to_isDomain V

end GlobalTheory.UnramExt

open GlobalTheory.UnramExt in

theorem GlobalTheory.exists_unramified_ext_residue : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ {L : Type} [Field L] (v : ResidueField W →+* L), v.Finite → v.FormallyUnramified → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (τ : L →+* ResidueField V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ (∀ ϖ : W, Irreducible ϖ → Irreducible (f ϖ)) ∧ ∀ w : W, τ (v (residue W w)) = residue V (f w) := by
  intro W _ _ _ hW L _ v hfin hfu
  obtain ⟨hdvr, hcomp, hchar⟩ := (cDvr_iff W).1 hW
  letI : Algebra (ResidueField W) L := v.toAlgebra
  haveI : Module.Finite (ResidueField W) L := hfin
  haveI : Algebra.FormallyUnramified (ResidueField W) L := hfu
  haveI : Algebra.IsSeparable (ResidueField W) L := Algebra.FormallyUnramified.isSeparable _ _
  let pb : PowerBasis (ResidueField W) L := Field.powerBasisOfFiniteOfSeparable _ L
  set gb := minpoly (ResidueField W) pb.gen with hgb
  have hgb_mon : gb.Monic := minpoly.monic pb.isIntegral_gen
  have hgb_irr : Irreducible gb := minpoly.irreducible pb.isIntegral_gen
  have hgb_deg : 0 < gb.natDegree := minpoly.natDegree_pos pb.isIntegral_gen
  have hlift : gb ∈ lifts (residue W) :=
    (lifts_iff_coeff_lifts gb).2 fun n => residue_surjective _
  obtain ⟨g, hgmap, hgdeg, hgmon⟩ := lifts_and_natDegree_eq_and_monic hlift hgb_mon
  have hgdeg' : g.degree ≠ 0 := by
    rw [degree_eq_natDegree hgmon.ne_zero, hgdeg]
    exact_mod_cast hgb_deg.ne'
  let V := AdjoinRoot g
  let f : W →+* V := algebraMap W V
  have hfof : f = AdjoinRoot.of g := AdjoinRoot.algebraMap_eq g
  have hfinj : Function.Injective f := by
    rw [hfof]; exact AdjoinRoot.of.injective_of_degree_ne_zero hgdeg'
  let pbV : PowerBasis W V := AdjoinRoot.powerBasis' hgmon
  haveI : Module.Finite W V := pbV.finite
  haveI : Algebra.IsIntegral W V := inferInstance
  haveI : IsNoetherianRing V := isNoetherian_of_tower W (inferInstance : IsNoetherian W V)
  set mW := maximalIdeal W with hmWdef
  set M : Ideal V := Ideal.map f mW with hMdef

  have hirr : Irreducible (g.map (Ideal.Quotient.mk mW)) := by
    have := hgb_irr
    rw [← hgmap] at this
    exact this
  haveI hmWmax : mW.IsMaximal := maximalIdeal.isMaximal W
  letI : Field (W ⧸ mW) := Ideal.Quotient.field mW
  have hM : M.IsMaximal := by
    have h1 := PrincipalIdealRing.isMaximal_of_irreducible hirr
    have h2 := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 h1
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    have e := AdjoinRoot.quotEquivQuotMap g mW
    rw [hMdef, hfof]
    exact MulEquiv.isField h2 e.toRingEquiv.toMulEquiv
  have huniq : ∀ P : Ideal V, P.IsMaximal → P = M := by
    intro P hP
    have h1 : (P.comap (algebraMap W V)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    have h2 : P.comap f = mW := IsLocalRing.eq_maximalIdeal h1
    have h3 : M ≤ P := Ideal.map_le_iff_le_comap.2 h2.ge
    exact (hM.eq_of_le hP.ne_top h3).symm
  haveI : IsLocalRing V := IsLocalRing.of_unique_max_ideal ⟨M, hM, fun P hP => huniq P hP⟩
  have hmV : maximalIdeal V = M := huniq _ (maximalIdeal.isMaximal V)
  have hspan : ∀ ϖ : W, Irreducible ϖ → maximalIdeal V = Ideal.span {f ϖ} := by
    intro ϖ hϖ
    rw [hmV, hMdef, hmWdef, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hpow : ∀ n : ℕ, f ϖ₀ ^ n ≠ 0 := by
    intro n h
    rw [← map_pow, ← map_zero f] at h
    exact pow_ne_zero n hϖ₀.ne_zero (hfinj h)
  haveI hdom : IsDomain V := isDomain_of_maximalIdeal_eq_span (hspan ϖ₀ hϖ₀) hpow
  have hirrV : Irreducible (f ϖ₀) := by
    have hprime : (Ideal.span {f ϖ₀}).IsPrime := by
      rw [← hspan ϖ₀ hϖ₀]; exact (maximalIdeal.isMaximal V).isPrime
    have hne : f ϖ₀ ≠ 0 := by simpa using hpow 1
    exact ((Ideal.span_singleton_prime hne).1 hprime).irreducible
  haveI hdvrV : IsDiscreteValuationRing V := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨f ϖ₀, hirrV, ?_⟩
    intro x hx
    obtain ⟨n, u, hu, rfl⟩ := exists_unit_mul_pow (hspan ϖ₀ hϖ₀) x hx
    exact ⟨n, hu.unit, by simp [mul_comm]⟩
  haveI hloc : IsLocalHom f := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : f a ∈ maximalIdeal V := by
      rw [hmV]; exact Ideal.mem_map_of_mem f ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 this ha
  haveI : IsAdicComplete mW W := hcomp
  have hcompV : IsAdicComplete (maximalIdeal V) V := by
    rw [hmV, hMdef]
    exact (IsAdicComplete.map_algebraMap_iff mW V).2 (isAdicComplete_of_finite_basis pbV.basis mW)
  haveI : CharZero W := hchar
  have hcharV : CharZero V := charZero_of_injective_ringHom hfinj

  letI : Algebra (ResidueField W) (ResidueField V) := (ResidueField.map f).toAlgebra
  have hroot : aeval (residue V (AdjoinRoot.root g)) gb = 0 := by
    rw [aeval_def, ← hgmap, eval₂_map]
    change eval₂ ((ResidueField.map f).comp (residue W)) _ g = 0
    rw [ResidueField.map_comp_residue, ← hom_eval₂, hfof, AdjoinRoot.eval₂_root, map_zero]
  let τ : L →ₐ[ResidueField W] ResidueField V := pb.lift _ hroot
  refine ⟨V, inferInstance, hdom, inferInstance, f, τ.toRingHom, (cDvr_iff V).2 ⟨hdvrV, hcompV, hcharV⟩,
    hfinj, hloc, fun ϖ hϖ => ?_, fun w => ?_⟩
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer (f ϖ)).2 (hspan ϖ hϖ)
  · have := τ.commutes (residue W w)
    exact this.trans (ResidueField.map_residue f w)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRef.RealMove

theorem exists_factor {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ (p : ℕ) (U : Matrix (Fin m) (Fin p) ℂ) (V : Matrix (Fin p) (Fin m) ℂ), U * V = P ∧ V * U = 1 := by
  let L := Matrix.toLin' P
  let b := Module.finBasis ℂ (LinearMap.range L)
  let e := Pi.basisFun ℂ (Fin m)
  refine ⟨_, LinearMap.toMatrix b e (LinearMap.range L).subtype, LinearMap.toMatrix e b L.rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp, LinearMap.subtype_comp_codRestrict, LinearMap.toMatrix_eq_toMatrix']
    exact LinearMap.toMatrix'_toLin' P
  · rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id b]
    congr 1
    ext ⟨_, y, rfl⟩ : 1
    apply Subtype.ext
    show L (L y) = L y
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hP]

theorem det_idem_kron {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ p : ℕ, P.trace = p ∧ ∀ a : Matrix (Fin n) (Fin n) ℂ,
      (P ⊗ₖ a + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)).det = a.det ^ p := by
  obtain ⟨p, U, V, h1, h2⟩ := exists_factor P hP
  refine ⟨p, by rw [← h1, Matrix.trace_mul_comm, h2]; simp, fun a => ?_⟩
  have e : P ⊗ₖ a + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
      1 + (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * (V ⊗ₖ (a - 1)) := by
    rw [← Matrix.mul_kronecker_mul, h1, Matrix.one_mul, ← Matrix.one_kronecker_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply]
    ring
  have e2 : 1 + (V ⊗ₖ (a - 1)) * (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) = (1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ a := by
    rw [← Matrix.mul_kronecker_mul, h2, Matrix.mul_one, ← Matrix.one_kronecker_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply]
    ring
  rw [e, Matrix.det_one_add_mul_comm, e2, Matrix.det_kronecker]
  simp

theorem detPlus_one {m n : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) (hs : s * s = 1) :
    ∃ p : ℕ, s.trace = 2 * p - m ∧ ∀ (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ), s * b = b * s →
      GlobalTheory.WeilParts.detPlus 1 s a b = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det ^ n * a.det ^ p ∧
      b.det = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det *
        ((1 / 2 : ℂ) • (1 - s) * b + (1 / 2 : ℂ) • (1 + s)).det := by
  obtain ⟨P, hPd⟩ : ∃ P, P = (1 / 2 : ℂ) • (1 + s) := ⟨_, rfl⟩
  have hQ : (1 / 2 : ℂ) • (1 - s) = 1 - P := by rw [hPd]; module
  have hP : P * P = P := by
    rw [hPd, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, mul_add, hs, one_mul, mul_one, one_mul]; module
  obtain ⟨p, hp, hd⟩ := det_idem_kron (n := n) P hP
  refine ⟨p, ?_, fun a b hb => ?_⟩
  · rw [hPd, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at hp
    linear_combination 2 * hp
  have hc : P * b = b * P := by
    rw [hPd, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hb, one_mul, mul_one]
  have hc2 : P * b * P = P * b := by rw [mul_assoc, ← hc, ← mul_assoc, hP]
  rw [← hPd, hQ]
  constructor
  · have e1 : (1 / 2 : ℂ) • ((1 + s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ) * (b ⊗ₖ aᵀ)) +
        (1 / 2 : ℂ) • (1 - s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ) =
        (P * b) ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← hQ, hPd, Matrix.transpose_one, add_mul, ← Matrix.mul_kronecker_mul, Matrix.smul_mul, add_mul, one_mul, one_mul,
        one_mul, ← Matrix.one_kronecker_one]
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have e2 : (P * b) ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
        ((P * b + (1 - P)) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) *
          (P ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      have f1 : (P * b + (1 - P)) * P = P * b := by rw [add_mul, hc2, sub_mul, one_mul, hP, sub_self, add_zero]
      have f2 : (P * b + (1 - P)) * (1 - P) = 1 - P := by rw [mul_sub, f1, mul_one]; abel
      rw [mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, f1, f2, one_mul, one_mul]
    unfold GlobalTheory.WeilParts.detPlus
    rw [e1, e2, Matrix.det_mul, hd, Matrix.det_kronecker]
    simp
  · rw [← Matrix.det_mul]
    congr 1
    have f3 : P * b * ((1 - P) * b) = 0 := by
      rw [← mul_assoc, mul_sub, mul_one, hc2, sub_self, zero_mul]
    have f4 : (1 - P) * ((1 - P) * b) = (1 - P) * b := by
      rw [← mul_assoc, sub_mul, mul_sub, mul_sub, hP]; simp
    have f5 : (1 - P) * P = 0 := by rw [sub_mul, hP, one_mul, sub_self]
    rw [add_mul, mul_add, mul_add, f3, f4, f5, hc2, sub_mul]; simp

variable {D : D7}

theorem hasInfExp_twist {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ (1 / 2)) (k : ℕ) : HasInfExp D (χ * (η ^ k)⁻¹) τ (a - k / 2) := by
  obtain ⟨n, hn, h0, h⟩ := hχ
  obtain ⟨n', hn', -, h'⟩ := hη
  have e : n' = 1 := by
    have : (n' : ℚ) = 1 := by rw [hn']; norm_num
    exact_mod_cast this
  subst e
  refine ⟨n - k, by push_cast; rw [hn]; ring, h0, fun θ hθ x h1 h2 => ?_⟩
  have hne : θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) ≠ 0 := by
    have := h' θ hθ x h1 h2
    rw [zpow_one] at this
    rw [← this]; exact Circle.coe_ne_zero _
  rw [zpow_sub₀ hne, ← h θ hθ x h1 h2, zpow_natCast]
  have := h' θ hθ x h1 h2
  rw [zpow_one] at this
  rw [← this]
  simp [div_eq_mul_inv]

theorem adele_ext {θ : InfFam D} (hθ : IsInfFam θ) {x y : AE D} (h1 : finPart D x = finPart D y)
    (h2 : ∀ τ, θ τ (infPart D x) = θ τ (infPart D y)) : x = y := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  rw [← sub_eq_zero]
  exact hσ.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
    rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]

open Classical in

theorem exists_idele_at {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : ℂ) (hw : w ≠ 0) :
    ∃ x : (AE D)ˣ, finPart D (x : AE D) = 1 ∧ ∀ τ', θ τ' (infPart D (x : AE D)) = if τ' = τ then w else 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have key : ∀ w : ℂ, ∃ x : AE D, finPart D x = 1 ∧ ∀ τ', θ τ' (infPart D x) = if τ' = τ then w else 1 := fun w =>
    ⟨1 + σ fun τ' => (if τ' = τ then w else 1) - 1, by rw [RingHom.map_add, hσ.fin, RingHom.map_one, add_zero], fun τ' => by
      rw [RingHom.map_add, RingHom.map_add, hσ.comp, RingHom.map_one, RingHom.map_one]; ring⟩
  obtain ⟨x, hx1, hx2⟩ := key w
  obtain ⟨y, hy1, hy2⟩ := key w⁻¹
  have hxy : x * y = 1 := adele_ext hθ (by rw [RingHom.map_mul, hx1, hy1, RingHom.map_one, one_mul]) fun τ' => by
    rw [RingHom.map_mul, RingHom.map_mul, hx2, hy2, RingHom.map_one, RingHom.map_one]
    split_ifs
    · exact mul_inv_cancel₀ hw
    · exact one_mul 1
  have hyx : y * x = 1 := (mul_comm y x).trans hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_, ?_⟩
  · rw [Units.val_mk]; exact hx1
  · rw [Units.val_mk]; exact hx2

theorem det_compAt (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE D)) :
    (compAt θ τ M).det = θ τ (infPart D M.det) :=
  (RingHom.map_det ((θ τ).comp (infPart D)) M).symm

theorem finPart_cA (z : AE D) (hz : finPart D z = 1) : finPart D (cA D z) = 1 := by
  have key : ∀ z : AE D, finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a x => rfl
  rw [key, hz, map_one]

theorem exists_root {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : ∀ τ, (gramAt D V τ).det ≠ 0)
    (g : GA D V) (hg : g ∈ GinfC V) :
    ∃ x, IsDetRoot V g x ∧ ∀ (ν : (AE D)ˣ →* Circle) (c : D.what₂.Tau → ℤ), (∀ τ, HasInfExp D ν τ (c τ)) →
      ((ν x : Circle) : ℂ) = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g)).det ^ c τ := by
  classical
  have hu : ∀ τ, ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ = 1 := fun τ => by
    have h : (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have h2 := congrArg (fun M => ‖Matrix.det M‖) h
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at h2
    have h3 : ‖(gramAt D V τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hV τ)
    have h4 : ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ ^ 2 = 1 := by
      apply mul_left_cancel₀ h3; linear_combination h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  have hw : ∀ τ, ∃ w : ℂ, w ^ 2 = (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∧ ‖w‖ = 1 := fun τ => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (compAt θ τ (Formalism.L2.Theta.mt V g)).det two_pos
    refine ⟨w, hw, (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_⟩
    rw [← norm_pow, hw, hu]
  choose w hw1 hw2 using hw
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h => by simpa [h] using hw2 τ
  choose x hx1 hx2 using fun τ => exists_idele_at hθ τ (w τ) (hw0 τ)
  have hf : finPart D ((∏ τ, x τ : (AE D)ˣ) : AE D) = 1 := by
    rw [Units.coe_prod, map_prod]; exact Finset.prod_eq_one fun τ _ => hx1 τ
  have hi : ∀ τ, θ τ (infPart D ((∏ τ, x τ : (AE D)ˣ) : AE D)) = w τ := fun τ => by
    rw [Units.coe_prod, map_prod, map_prod]
    simp [hx2]
  refine ⟨∏ τ, x τ, ?_, fun ν c hc => ?_⟩
  · refine adele_ext hθ ?_ fun τ => ?_
    · have hd : finPart D (Formalism.L2.Theta.mt V g).det = 1 := by
        have hg' : finHom V g = 1 := hg
        have : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val hg'
        rw [RingHom.map_det]
        exact (congrArg Matrix.det this).trans Matrix.det_one
      rw [map_mul, hf]
      exact ((congrArg₂ (· * ·) hd (finPart_cA _ hf)).trans (one_mul 1)).symm
    · rw [map_mul, map_mul, hi]
      have e1 := GlobalTheory.FockCompare.comp_cA hθ τ ((∏ τ, x τ : (AE D)ˣ) : AE D)
      have e2 := det_compAt θ τ (Formalism.L2.Theta.mt V g)
      rw [hi] at e1
      refine Eq.trans ?_ (congrArg₂ (· * ·) e2 e1.symm)
      have : w τ * starRingEnd ℂ (w τ) = 1 := by rw [Complex.mul_conj', hw2]; simp
      rw [← hw1]; linear_combination (-w τ) * this
  · rw [map_prod]
    rw [show ((∏ τ, ν (x τ) : Circle) : ℂ) = ∏ τ, (ν (x τ) : ℂ) from map_prod Circle.coeHom _ _]
    refine Finset.prod_congr rfl fun τ _ => ?_
    obtain ⟨n, hn, -, h⟩ := hc τ
    have e : n = 2 * c τ := by exact_mod_cast hn
    rw [h θ hθ (x τ) (hx1 τ) (fun τ' h' => by rw [hx2, if_neg h']), hx2, if_pos rfl, hw2, e, ← hw1, _root_.zpow_mul]
    simp

end GlobalTheory.OneMapRef.RealMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GraphClosure

theorem charZero_residueField_of_flat {R : Type} [CommRing R] [IsDomain R] [CharZero R] {W : Scheme.{0}}
    (s : W ⟶ Sp R) [Flat s] {x : W} (hx : x ∈ genericPoints W) : CharZero (W.residueField x) := by
  have hsp : genericPoint (Sp R) ⤳ s x := (genericPoint_spec (Sp R)).specializes trivial
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap s hsp
  obtain rfl := eq_of_specializes_of_mem_genericPoints hx hx'
  have : CharZero ((Sp R).residueField (s x')) := by
    rw [e]
    have : Nonempty (⊤ : (Sp R).Opens) := ⟨⟨genericPoint (Sp R), trivial⟩⟩
    have : CharZero (Sp R).functionField :=
      charZero_of_injective_ringHom (R := R)
        (f := ((Scheme.ΓSpecIso (.of R)).inv ≫ (Sp R).germToFunctionField ⊤).hom)
        (((Sp R).germToFunctionField_injective ⊤).comp
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1)
    exact charZero_of_injective_ringHom (R := (Sp R).functionField)
      ((Sp R).residue (genericPoint (Sp R))).hom.injective
  exact charZero_of_injective_ringHom (s.residueFieldMap x').hom.injective

theorem exists_normalised_graph_closure : ∀ (O O₂ : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [CommRing O₂] (b : O₂ →+* O) (X₁ X₂ : Scheme.{0}) (s₁ : X₁ ⟶ Sp O) (s₂ : X₂ ⟶ Sp O₂) (U : X₁.Opens) (g : U.toScheme ⟶ X₂), IsProjOver s₁ → IsProjOver s₂ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X₁ → Flat s₁ → g ≫ s₂ = U.ι ≫ s₁ ≫ spMap b → ∃ (X' : Scheme.{0}) (f₁ : X' ⟶ X₁) (f₂ : X' ⟶ X₂) (j : U.toScheme ⟶ X'), IsProjOver (f₁ ≫ s₁) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ Flat (f₁ ≫ s₁) ∧ IsPullback j (𝟙 U.toScheme) f₁ U.ι ∧ Dense (Set.range j) ∧ j ≫ f₂ = g ∧ IsFinite (prod.lift f₁ f₂) := by
  intro O O₂ _ _ _ _ b X₁ X₂ s₁ s₂ U g h₁ h₂ hn _ w
  have : IsProper s₁ := ((isProjOver_iff_isProper_and_exists_isAmpleLB s₁).mp h₁).1
  have : IsProper s₂ := ((isProjOver_iff_isProper_and_exists_isAmpleLB s₂).mp h₂).1
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian s₁
  obtain ⟨P, p₁, p₂, H, hP⟩ : ∃ (P : Scheme.{0}) (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂),
      IsPullback p₁ p₂ (s₁ ≫ spMap b) s₂ ∧ IsProjOver (p₁ ≫ s₁) :=
    ⟨_, _, _, ((IsPullback.of_hasPullback s₁ (pullback.snd s₂ (spMap b))).paste_vert
      (IsPullback.of_hasPullback s₂ (spMap b)).flip),
      ProjSpace.isProjOver_pullback h₁ (ProjSpace.isProjOver_pullback_snd b h₂)⟩
  have : IsProper p₁ := MorphismProperty.of_isPullback H.flip ‹IsProper s₂›
  let h : U.toScheme ⟶ P := H.lift U.ι g w.symm
  have e₁ : h ≫ p₁ = U.ι := H.lift_fst _ _ _
  have e₂ : h ≫ p₂ = g := H.lift_snd _ _ _
  have : QuasiCompact (h ≫ p₁) := e₁ ▸ inferInstance
  have : QuasiCompact h := .of_comp h p₁
  have : IsSeparated (h ≫ p₁) := e₁ ▸ inferInstance
  have : IsSeparated h := .of_comp h p₁
  have : LocallyOfFiniteType (h ≫ p₁) := e₁ ▸ inferInstance
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h p₁
  have : IsFinite h.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType (o := CommRingCat.of O) h (p₁ ≫ s₁)
      fun x hx => charZero_residueField_of_flat (U.ι ≫ s₁) hx
  have : Flat (h.toNormalization ≫ (h.fromNormalization ≫ p₁) ≫ s₁) := by
    rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization_assoc, reassoc_of% e₁]
    infer_instance
  let c : U.toScheme ⟶ pullback p₁ U.ι := pullback.lift h (𝟙 _) (by simpa using e₁)
  have hc₁ : c ≫ pullback.fst _ _ = h := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion (c ≫ pullback.snd _ _) := by rw [hc₂]; infer_instance
  have : IsClosedImmersion c := .of_comp c (pullback.snd _ _)
  have Q := (isPullback_toNormalization_of_mono c (pullback.fst p₁ U.ι) h hc₁.symm).paste_vert
    (IsPullback.of_hasPullback p₁ U.ι)
  rw [hc₂] at Q
  have : IsSeparated (terminal.from X₂) := by
    rw [← terminal.comp_from s₂]; infer_instance
  have : IsSeparated (prod.fst : X₁ ⨯ X₂ ⟶ X₁) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasBinaryProduct' X₁ X₂).flip this
  have : IsProper (prod.lift p₁ p₂ ≫ prod.fst) := by rwa [prod.lift_fst]
  have : IsProper (prod.lift p₁ p₂) := .of_comp _ prod.fst
  have : Mono (prod.lift p₁ p₂) := ⟨fun u v e => H.hom_ext
    (by simpa only [Category.assoc, prod.lift_fst] using congrArg (· ≫ prod.fst) e)
    (by simpa only [Category.assoc, prod.lift_snd] using congrArg (· ≫ prod.snd) e)⟩
  have : IsClosedImmersion (prod.lift p₁ p₂) :=
    (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨inferInstance, inferInstance⟩
  refine ⟨h.normalization, h.fromNormalization ≫ p₁, h.fromNormalization ≫ p₂, h.toNormalization, ?_,
    IsNormalScheme.pred _, flat_normalization h _, Q, h.toNormalization.denseRange, by simp [e₂], ?_⟩
  · rw [Category.assoc]
    exact isProjOver_comp_of_isFinite _ hP
  · rw [← prod.comp_lift]
    infer_instance

end GlobalTheory.GraphClosure
end

