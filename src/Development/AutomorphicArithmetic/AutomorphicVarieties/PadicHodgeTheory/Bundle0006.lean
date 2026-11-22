import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0008
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.Bundle0003

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem UpperTheory.V.Loc.ci_closed (l : ℕ) [Fact l.Prime] (x y : PadicAlgCl l) :
    IsClosed {σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l | σ x = y} := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hx
  have hU := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ_[l] {x})
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro σ hσ
  have hc : Continuous fun τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l => σ⁻¹ * τ := by fun_prop
  have h1 := (hU.preimage hc).mem_nhds (x := σ) (by simp)
  refine Filter.mem_of_superset h1 fun τ hτ h => hσ ?_
  have h2 : (σ⁻¹ * τ) x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x (IntermediateField.mem_adjoin_simple_self _ _)
  have h3 : τ x = y := h
  have h4 : σ ((σ⁻¹ * τ) x) = τ x := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
  show σ x = y
  rw [← h3, ← h4, h2]

private theorem UpperTheory.V.Loc.ci_dvd_sub_iff (l : ℕ) [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    (l : ℤ_[l]) ^ r ∣ x - y ↔ PadicInt.toZModPow r x = PadicInt.toZModPow r y := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]

private theorem UpperTheory.V.Loc.ci_pow_congr {K : Type*} [Monoid K] {x : K} {M a b : ℕ} (hx : x ^ M = 1)
    (h : a ≡ b [MOD M]) : x ^ a = x ^ b := by
  rw [pow_eq_pow_mod a hx, pow_eq_pow_mod b hx, h]

private theorem UpperTheory.V.Loc.ci_crt (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) (M : ℕ) (hM : M ≠ 0) :
    ∃ c : ℕ, c.Coprime M ∧ c ≡ 1 [MOD ordCompl[l] M] ∧
      ∀ k ≤ M.factorization l, (c : ZMod (l ^ k)) = PadicInt.toZModPow k (a : ℤ_[l]) := by
  have hp : l.Prime := Fact.out
  set v := M.factorization l with hv
  have hcop : Nat.Coprime (ordCompl[l] M) (l ^ v) := (Nat.coprime_ordCompl hp hM).symm.pow_right _
  haveI : NeZero (l ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨c, h1, h2⟩ := Nat.chineseRemainder hcop 1 (PadicInt.toZModPow v (a : ℤ_[l])).val
  have hc : ((c : ℕ) : ZMod (l ^ v)) = PadicInt.toZModPow v (a : ℤ_[l]) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]
  have hcoP : c.Coprime (l ^ v) := by
    rw [← ZMod.isUnit_iff_coprime, hc]
    exact (Units.isUnit a).map _
  have hcoN : c.Coprime (ordCompl[l] M) := by
    unfold Nat.Coprime
    rw [h1.gcd_eq, Nat.gcd_one_left]
  refine ⟨c, ?_, h1, fun k hk => ?_⟩
  · have := Nat.Coprime.mul_right hcoP hcoN
    rwa [hv, Nat.ordProj_mul_ordCompl_eq_self] at this
  · have hd : (l : ℤ_[l]) ^ v ∣ (c : ℤ_[l]) - (a : ℤ_[l]) := by
      rw [UpperTheory.V.Loc.ci_dvd_sub_iff, map_natCast, hc]
    have := (pow_dvd_pow _ hk).trans hd
    rwa [UpperTheory.V.Loc.ci_dvd_sub_iff, map_natCast] at this

private theorem UpperTheory.V.Loc.ci_fin (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) (n : ℕ) :
    ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l),
      (∀ m ≤ n, 0 < m → ¬ l ∣ m → ∀ x : PadicAlgCl l, x ^ m = 1 → σ x = x) ∧
      ∀ k ≤ n, ∀ x : PadicAlgCl l, x ^ l ^ k = 1 → σ x = x ^ (PadicInt.toZModPow k (a : ℤ_[l])).val := by
  have hp : l.Prime := Fact.out
  obtain ⟨M, hM⟩ : ∃ M, M = n.factorial * l ^ n := ⟨_, rfl⟩
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact mul_ne_zero n.factorial_ne_zero (pow_ne_zero _ hp.ne_zero)
  have hv : n ≤ M.factorization l :=
    (hp.pow_dvd_iff_le_factorization hM0).1 (by rw [hM]; exact Dvd.intro_left _ rfl)
  obtain ⟨c, hcM, hc1, hc2⟩ := UpperTheory.V.Loc.ci_crt l a M hM0
  have hval : ∀ (N : ℕ) (h : c.Coprime N), ((ZMod.unitOfCoprime c h : (ZMod N)ˣ) : ZMod N).val ≡ c [MOD N] := by
    intro N h
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_modEq _ _
  obtain ⟨σ, hσ⟩ := (UpperTheory.HF.loc_roots l M (Nat.pos_of_ne_zero hM0)).2 (ZMod.unitOfCoprime c hcM) 0
    (by rw [pow_zero]; exact ((hval M hcM).of_dvd (Nat.ordCompl_dvd _ _)).trans hc1)
  have hσc : ∀ d, d ∣ M → ∀ x : PadicAlgCl l, x ^ d = 1 → σ x = x ^ c := by
    intro d ⟨e, he⟩ x hx
    have hxM : x ^ M = 1 := by rw [he, pow_mul, hx, one_pow]
    rw [hσ x hxM]
    exact UpperTheory.V.Loc.ci_pow_congr hxM (hval M hcM)
  refine ⟨σ, fun m hm hm0 hlm x hx => ?_, fun k hk x hx => ?_⟩
  · have hmM : m ∣ M := by
      rw [hM]
      exact (Nat.dvd_factorial hm0 hm).mul_right _
    have hm' : m ∣ ordCompl[l] M := Nat.dvd_ordCompl_of_dvd_not_dvd hmM hlm
    rw [hσc m hmM x hx, UpperTheory.V.Loc.ci_pow_congr hx (hc1.of_dvd hm'), pow_one]
  · have hkM : l ^ k ∣ M := by
      rw [hM]
      exact (pow_dvd_pow _ hk).mul_left _
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [hσc _ hkM x hx]
    refine UpperTheory.V.Loc.ci_pow_congr hx ?_
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    exact hc2 k (le_trans hk hv)

private theorem UpperTheory.V.Loc.ci_surj (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) : ∃ g ∈ Iq l, cyc l l g = a := by
  have hp : l.Prime := Fact.out
  let S : ℕ → Set (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) := fun n =>
    {σ | (∀ m ≤ n, 0 < m → ¬ l ∣ m → ∀ x : PadicAlgCl l, x ^ m = 1 → σ x = x) ∧
      ∀ k ≤ n, ∀ x : PadicAlgCl l, x ^ l ^ k = 1 → σ x = x ^ (PadicInt.toZModPow k (a : ℤ_[l])).val}
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    simp only [S, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_iInter fun _ => UpperTheory.V.Loc.ci_closed l _ _
    · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        UpperTheory.V.Loc.ci_closed l _ _
  haveI : IsGalois ℚ_[l] (PadicAlgCl l) := {}
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
    (fun n σ hσ => ⟨fun m hm => hσ.1 m (hm.trans n.le_succ), fun k hk => hσ.2 k (hk.trans n.le_succ)⟩)
    (fun n => UpperTheory.V.Loc.ci_fin l a n) (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_, ?_⟩
  · unfold MaximalUnramifiedExtension at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, hm0, hlm, hx⟩ := hx
      exact (hσ m).1 m le_rfl hm0 hlm x hx
    | algebraMap r => exact σ.commutes r
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  · haveI (i : ℕ) : HasEnoughRootsOfUnity (PadicAlgCl l) (l ^ i) := by
      haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
      infer_instance
    refine Units.ext (PadicInt.ext_of_toZModPow.1 fun k => ?_)
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) (l ^ k)
    have h1 := cyclotomicCharacter.spec l (n := k)
      (MulSemiringAction.toRingAut (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (PadicAlgCl l) σ) η hη.pow_eq_one
    have h2 := (hσ k).2 k le_rfl η hη.pow_eq_one
    have h3 := h1.symm.trans h2
    exact ZMod.val_injective _ (hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

private theorem UpperTheory.V.Loc.ci_inf (l : ℕ) [Fact l.Prime] : ∃ u : ℤ_[l]ˣ, ¬ IsOfFinOrder u := by
  have hp : l.Prime := Fact.out
  have hu : IsUnit (((l + 1 : ℕ)) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  refine ⟨hu.unit, fun h => ?_⟩
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have h2 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, hu.unit_spec, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one,
    Nat.pow_eq_one] at h2
  have := hp.one_lt
  omega

theorem UpperTheory.V.Loc.cycInertia :
    ∀ (l : ℕ) [Fact l.Prime], (∀ u : ℤ_[l]ˣ, ∃ g ∈ Iq l, cyc l l g = u) ∧ ∀ U : Subgroup (GQ l), IsOpen (U : Set (GQ l)) → IsOpen (((U ⊓ Iq l).map (cyc l l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) ∧ ∃ s ∈ U ⊓ Iq l, ¬ IsOfFinOrder (cyc l l s) := by
  intro l _
  refine ⟨UpperTheory.V.Loc.ci_surj l, fun U hU => ?_⟩
  haveI : IsGalois ℚ_[l] (Om l) := {}
  haveI : Finite (GQ l ⧸ U) := U.quotient_finite_of_isOpen hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : Continuous (cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (Om l)
  constructor
  · have hs : Function.Surjective ((cyc l l).comp (Iq l).subtype) := fun u => by
      obtain ⟨g, hg, h⟩ := UpperTheory.V.Loc.ci_surj l u
      exact ⟨⟨g, hg⟩, h⟩
    have he : (U ⊓ Iq l).map (cyc l l) = (U.subgroupOf (Iq l)).map ((cyc l l).comp (Iq l).subtype) := by
      rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
    haveI : ((U ⊓ Iq l).map (cyc l l)).FiniteIndex := ⟨by
      rw [he]
      exact ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero (Subgroup.index_map_dvd _ hs)⟩
    refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
    rw [Subgroup.coe_map, Subgroup.coe_inf]
    exact (((U.isClosed_of_isOpen hU).inter
      (InfiniteGalois.fixingSubgroup_isClosed (MaximalUnramifiedExtension l))).isCompact.image hc).isClosed
  · obtain ⟨u, hu⟩ := UpperTheory.V.Loc.ci_inf l
    obtain ⟨g, hg, h⟩ := UpperTheory.V.Loc.ci_surj l u
    obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.FiniteIndex.index_ne_zero (H := U)) g
    refine ⟨g ^ n, ⟨hgn, pow_mem hg n⟩, fun hf => hu ?_⟩
    rw [map_pow, h] at hf
    exact hf.of_pow hn.ne'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantBlockDetNormEqPowOfMemSpectrum
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem norm_eq_of_aeval_minpoly_eq_zero' {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) (a μ : Om l)
    (h : Polynomial.aeval μ (minpoly L a) = 0) : ‖μ‖ = ‖a‖ := by
  haveI : Algebra.IsAlgebraic L (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic a) h
  rw [← hσ]
  exact spectralNorm_eq_of_equiv (K := ℚ_[l]) (L := PadicAlgCl l) (σ.restrictScalars ℚ_[l]) μ

private theorem aeval_mul_eq_mul_aeval_of_semiconj {K : Type} [Field K] {d r : ℕ} (F : Matrix (Fin d) (Fin d) K)
    (Y : Matrix (Fin d) (Fin r) K) (F' : Matrix (Fin r) (Fin r) K) (h : F * Y = Y * F')
    (q : Polynomial K) : Polynomial.aeval F q * Y = Y * Polynomial.aeval F' q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c =>
    have hpow : ∀ m : ℕ, F ^ m * Y = Y * F' ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, hpow]

private theorem norm_det_eq_pow_of_aeval_minpoly_eq_zero {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ↥L) (a : Om l) (hA : Polynomial.aeval A (minpoly L a) = 0) :
    ‖((A.det : ↥L) : Om l)‖ = ‖a‖ ^ r := by
  set M : Matrix (Fin r) (Fin r) (Om l) := A.map (algebraMap ↥L (Om l)) with hMdef
  have hdet : ((A.det : ↥L) : Om l) = M.det := by
    rw [hMdef]
    exact RingHom.map_det (algebraMap ↥L (Om l)) A
  have hMp : Polynomial.aeval M (minpoly L a) = 0 := by
    have e := Polynomial.aeval_algHom_apply ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin r)) A (minpoly L a)
    rw [hA, map_zero] at e
    exact e
  have hroot : ∀ μ ∈ M.charpoly.roots, ‖μ‖ = ‖a‖ := by
    intro μ hμ
    have hr : Polynomial.IsRoot M.charpoly μ := (Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hμ
    have hs : μ ∈ spectrum (Om l) M := Matrix.mem_spectrum_of_isRoot_charpoly hr
    have hs2 := spectrum.subset_polynomial_aeval M ((minpoly L a).map (algebraMap ↥L (Om l))) ⟨μ, hs, rfl⟩
    rw [Polynomial.aeval_map_algebraMap, hMp] at hs2
    have hz : Polynomial.eval μ ((minpoly L a).map (algebraMap ↥L (Om l))) = 0 := by
      by_contra hx
      rw [spectrum.mem_iff, sub_zero] at hs2
      exact hs2 ((Units.mk0 _ hx).isUnit.map (algebraMap (Om l) (Matrix (Fin r) (Fin r) (Om l))))
    rw [Polynomial.eval_map_algebraMap] at hz
    exact norm_eq_of_aeval_minpoly_eq_zero' L a μ hz
  rw [hdet, Matrix.det_eq_prod_roots_charpoly]
  have hn := map_multiset_prod (normHom : Om l →*₀ ℝ) M.charpoly.roots
  simp only [normHom_apply] at hn
  rw [hn, Multiset.map_congr rfl hroot, Multiset.map_const', Multiset.prod_replicate,
    IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

private theorem exists_invariant_subspace_in_ker_of_det_zero {K : Type} [Field K] {d : ℕ} (F P : Matrix (Fin d) (Fin d) K)
    (hP : P.det = 0) (hc : F * P = P * F) :
    ∃ (r : ℕ) (Y : Matrix (Fin d) (Fin r) K) (Z : Matrix (Fin r) (Fin d) K) (F' : Matrix (Fin r) (Fin r) K),
      0 < r ∧ Z * Y = 1 ∧ F * Y = Y * F' ∧ P * Y = 0 := by
  classical
  set W := LinearMap.ker (Matrix.toLin' P) with hWdef
  have hW : W ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hP
    intro h
    have hvW : v ∈ W := by
      rw [hWdef, LinearMap.mem_ker, Matrix.toLin'_apply]
      exact hv
    rw [h, Submodule.mem_bot] at hvW
    exact hv0 hvW
  have hr : 0 < Module.finrank K W := Nat.pos_of_ne_zero (fun h => hW (Submodule.finrank_eq_zero.mp h))
  have hinv : ∀ w ∈ W, Matrix.toLin' F w ∈ W := by
    intro w hw
    rw [hWdef, LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  set e := (Module.finBasis K W).equivFun
  set ι : (Fin (Module.finrank K W) → K) →ₗ[K] (Fin d → K) := W.subtype ∘ₗ e.symm.toLinearMap with hι
  have hιker : LinearMap.ker ι = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp e.symm.injective
  obtain ⟨g, hg⟩ := ι.exists_leftInverse_of_injective hιker
  set G := e.toLinearMap ∘ₗ (Matrix.toLin' F).restrict hinv ∘ₗ e.symm.toLinearMap with hG
  refine ⟨Module.finrank K W, LinearMap.toMatrix' ι, LinearMap.toMatrix' g, LinearMap.toMatrix' G, hr, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · have hcomp : ι ∘ₗ G = Matrix.toLin' F ∘ₗ ι := by
      apply LinearMap.ext
      intro x
      simp [hι, hG, LinearMap.restrict_apply]
    calc F * LinearMap.toMatrix' ι = LinearMap.toMatrix' (Matrix.toLin' F) * LinearMap.toMatrix' ι := by
          rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (Matrix.toLin' F ∘ₗ ι) := (LinearMap.toMatrix'_comp _ _).symm
      _ = LinearMap.toMatrix' (ι ∘ₗ G) := by rw [hcomp]
      _ = _ := LinearMap.toMatrix'_comp _ _
  · have hzero : Matrix.toLin' P ∘ₗ ι = 0 := by
      apply LinearMap.ext
      intro x
      rw [LinearMap.comp_apply, LinearMap.zero_apply]
      exact (e.symm x).2
    calc P * LinearMap.toMatrix' ι = LinearMap.toMatrix' (Matrix.toLin' P) * LinearMap.toMatrix' ι := by
          rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (Matrix.toLin' P ∘ₗ ι) := (LinearMap.toMatrix'_comp _ _).symm
      _ = 0 := by rw [hzero, map_zero]

theorem UpperTheory.exists_invariant_block_det_norm_eq_pow_of_mem_spectrum :
    ∀ {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {d : ℕ} (F : Matrix (Fin d) (Fin d) ↥L), ∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥L (Om l))), ∃ (r : ℕ) (Y : Matrix (Fin d) (Fin r) ↥L) (Z : Matrix (Fin r) (Fin d) ↥L) (F' : Matrix (Fin r) (Fin r) ↥L), 0 < r ∧ Z * Y = 1 ∧ F * Y = Y * F' ∧ ‖((F'.det : ↥L) : Om l)‖ = ‖a‖ ^ r := by
  intro l _ L d F a ha
  set p := minpoly (↥L) a with hp
  have hPdet : (Polynomial.aeval F p).det = 0 := by
    have hs2 := spectrum.subset_polynomial_aeval (F.map (algebraMap ↥L (Om l)))
      (p.map (algebraMap ↥L (Om l))) ⟨a, ha, rfl⟩
    beta_reduce at hs2
    rw [Polynomial.eval_map_algebraMap, hp, minpoly.aeval, Polynomial.aeval_map_algebraMap] at hs2
    have e := Polynomial.aeval_algHom_apply ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin d)) F (minpoly (↥L) a)
    rw [show ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin d)) F = F.map (algebraMap ↥L (Om l)) from rfl] at e
    rw [e, spectrum.zero_mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hs2
    have h3 : algebraMap ↥L (Om l) (Polynomial.aeval F (minpoly (↥L) a)).det = 0 := by
      rw [RingHom.map_det]
      exact hs2
    exact (map_eq_zero_iff _ (algebraMap ↥L (Om l)).injective).mp h3
  have hcomm : F * Polynomial.aeval F p = Polynomial.aeval F p * F := (aeval_mul_eq_mul_aeval_of_semiconj F F F rfl p).symm
  obtain ⟨r, Y, Z, F', hr, hZY, hFY, hPY⟩ := exists_invariant_subspace_in_ker_of_det_zero F (Polynomial.aeval F p) hPdet hcomm
  have hF' : Polynomial.aeval F' p = 0 := by
    have h1 := aeval_mul_eq_mul_aeval_of_semiconj F Y F' hFY p
    rw [hPY] at h1
    calc Polynomial.aeval F' p = (Z * Y) * Polynomial.aeval F' p := by rw [hZY, Matrix.one_mul]
      _ = Z * (Y * Polynomial.aeval F' p) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [← h1, Matrix.mul_zero]
  exact ⟨r, Y, Z, F', hr, hZY, hFY, norm_det_eq_pow_of_aeval_minpoly_eq_zero L F' a hF'⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsMonicUnitCoeffZeroAnnihilatingOfSpectrumNo
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem exists_monic_integral_unit_root {l : ℕ} [Fact l.Prime] (a : Om l) (ha : ‖a‖ = 1) :
    ∃ Q : ℤ_[l][X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧
      (X - C a) ∣ Q.map ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])) := by
  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  have hm : (minpoly ℚ_[l] a).Monic := minpoly.monic hint
  have hs : spectralNorm ℚ_[l] (Om l) a = 1 := ha
  have hc : ∀ n, ‖(minpoly ℚ_[l] a).coeff n‖ ≤ 1 :=
    (spectralValue_le_one_iff hm).1 (le_of_eq hs)
  have h0 : ‖(minpoly ℚ_[l] a).coeff 0‖ = 1 := by
    have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (Om l) a
    rw [hs] at h
    have hpos : (0 : ℝ) < (minpoly ℚ_[l] a).natDegree := by
      exact_mod_cast minpoly.natDegree_pos hint
    have h2 := congrArg (fun t : ℝ => t ^ (((minpoly ℚ_[l] a).natDegree : ℕ) : ℝ)) h
    simp only [Real.one_rpow] at h2
    rw [← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hpos.ne', Real.rpow_one] at h2
    exact h2.symm
  have hl : minpoly ℚ_[l] a ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨Q, hQm, ?_, ?_⟩
  · rw [PadicInt.isUnit_iff]
    rw [← hQ, coeff_map] at h0
    exact h0
  · rw [← Polynomial.map_map, hQ, dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap]
    exact minpoly.aeval _ _

private theorem aux_mul {l : ℕ} [Fact l.Prime] (s : Multiset (Om l)) (hs : ∀ a ∈ s, ‖a‖ = 1) :
    ∃ Q : ℤ_[l][X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧
      (s.map (fun a => X - C a)).prod ∣
        Q.map ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])) := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, monic_one, by simp, by simp⟩
  | cons a s ih =>
    obtain ⟨Q, h1, h2, h3⟩ := ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))
    obtain ⟨R, g1, g2, g3⟩ := exists_monic_integral_unit_root a (hs a (Multiset.mem_cons_self a s))
    refine ⟨R * Q, g1.mul h1, ?_, ?_⟩
    · rw [mul_coeff_zero]; exact g2.mul h2
    · rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul]
      exact mul_dvd_mul g3 h3

theorem UpperTheory.exists_monic_unit_coeff_zero_annihilating_of_spectrum_norm_one :
    ∀ {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {d : ℕ} (F : Matrix (Fin d) (Fin d) ↥L), (∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥L (Om l))), ‖a‖ = 1) → ∃ P : ℤ_[l][X], P.Monic ∧ IsUnit (P.coeff 0) ∧ aeval F (P.map ((algebraMap ℚ_[l] ↥L).comp (algebraMap ℤ_[l] ℚ_[l]))) = 0 := by
  intro l _ L d F hF
  set χ := (F.map (algebraMap ↥L (Om l))).charpoly with hχ
  have hχm : χ.Monic := Matrix.charpoly_monic _
  obtain ⟨Q, h1, h2, h3⟩ := aux_mul χ.roots (fun a ha =>
    hF a (Matrix.mem_spectrum_iff_isRoot_charpoly.2 ((mem_roots hχm.ne_zero).1 ha)))
  refine ⟨Q, h1, h2, ?_⟩
  rw [← (IsAlgClosed.splits χ).eq_prod_roots_of_monic hχm, hχ, Matrix.charpoly_map,
    IsScalarTower.algebraMap_eq ℚ_[l] L (Om l), RingHom.comp_assoc, ← Polynomial.map_map,
    map_dvd_map'] at h3
  obtain ⟨R, hR⟩ := h3
  rw [hR, map_mul, Matrix.aeval_self_charpoly, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsSquareSubmatrixDetNeZeroOfLeftInverse
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

theorem UpperTheory.exists_square_submatrix_det_ne_zero_of_left_inverse :
    ∀ {B : Type} [CommRing B] [IsDomain B] {d r : ℕ} (X : Matrix (Fin d) (Fin r) B) (Z : Matrix (Fin r) (Fin d) B), Z * X = 1 → ∃ s : Fin r → Fin d, (X.submatrix s id).det ≠ 0 := by
  intro B _ _ d r X Z hZX
  classical
  by_contra h
  push_neg at h
  have hM : (Z * X) = fun a => ∑ k, Z a k • X k := by
    funext a b
    simp [Matrix.mul_apply, Finset.sum_apply, smul_eq_mul]
  have key : (Z * X).det = ∑ s : Fin r → Fin d, (∏ a, Z a (s a)) * (X.submatrix s id).det := by
    have e1 : (Z * X).det = Matrix.detRowAlternating (fun a => ∑ k, Z a k • X k) := by
      rw [← hM]
      rfl
    rw [e1]
    have e2 := (Matrix.detRowAlternating : (Fin r → B) [⋀^Fin r]→ₗ[B] B).toMultilinearMap.map_sum
      (fun a k => Z a k • X k)
    simp only [AlternatingMap.coe_multilinearMap] at e2
    rw [e2]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have e3 := (Matrix.detRowAlternating : (Fin r → B) [⋀^Fin r]→ₗ[B] B).toMultilinearMap.map_smul_univ
      (fun a => Z a (s a)) (fun a => X (s a))
    simp only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at e3
    rw [e3]
    rfl
  have h0 : (Z * X).det = 0 := by
    rw [key]
    exact Finset.sum_eq_zero (fun s _ => by rw [h s, mul_zero])
  rw [hZX, Matrix.det_one] at h0
  exact one_ne_zero h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobDense
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem fd_pow_root {K : Type*} [Field K] {m n : ℕ} {y : K} (h : y ^ m = 1) :
    (y ^ n) ^ m = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

private theorem fd_level {v : ℕ} [Fact v.Prime] {x : Om v} (hx : x ∈ MaximalUnramifiedExtension v) :
    ∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g x = h x := by
  have hv : v.Prime := Fact.out
  have key : ∀ {a b : Om v},
      (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g a = h a) →
      (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g b = h b) →
      ∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) →
        g a = h a ∧ g b = h b := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, fun h => (hv.dvd_mul.mp h).elim hm hn, fun g h hgh => ⟨ha g h fun y hy => ?_,
      hb g h fun y hy => ?_⟩⟩
    · exact hgh y (by rw [pow_mul, hy, one_pow])
    · exact hgh y (by rw [mul_comm, pow_mul, hy, one_pow])
  unfold MaximalUnramifiedExtension at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, -, hm, hx⟩ := hx
    exact ⟨m, hm, fun g h hgh => hgh x hx⟩
  | algebraMap x =>
    exact ⟨1, hv.not_dvd_one, fun g h _ => by rw [AlgEquiv.commutes, AlgEquiv.commutes]⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, h⟩ := key hx hy
    exact ⟨m, hm, fun g k hgk => by rw [map_add, map_add, (h g k hgk).1, (h g k hgk).2]⟩
  | inv x _ hx =>
    obtain ⟨m, hm, h⟩ := hx
    exact ⟨m, hm, fun g k hgk => by rw [map_inv₀, map_inv₀, h g k hgk]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm, h⟩ := key hx hy
    exact ⟨m, hm, fun g k hgk => by rw [map_mul, map_mul, (h g k hgk).1, (h g k hgk).2]⟩

private theorem fd_frob {v : ℕ} [Fact v.Prime] {σ : GQ v} (hσ : IsFrob σ) {m : ℕ} (hm : ¬ v ∣ m)
    (j : ℕ) (y : Om v) (hy : y ^ m = 1) : (σ ^ j) y = y ^ v ^ j := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have h1 : σ y = y ^ v := by
    have hn : ‖y‖ ^ m = 1 := by rw [← norm_pow, hy, norm_one]
    have hn' := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp hn
    exact KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, hy, map_one])
      (fd_pow_root hy) (hσ y hn'.le)
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h1, ← pow_mul, pow_succ']

theorem UpperTheory.V.Loc.frobDense :
    ∀ {v : ℕ} [Fact v.Prime] (σ : GQ v), IsFrob σ → (Iq v ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ := by
  intro v _ σ hσ
  let H : ClosedSubgroup (GQ v) :=
    ⟨(Iq v ⊔ Subgroup.zpowers σ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
  have hH := InfiniteGalois.fixingSubgroup_fixedField H
  have hle : Iq v ⊔ Subgroup.zpowers σ ≤ (H : Subgroup (GQ v)) := Subgroup.le_topologicalClosure _
  refine eq_top_iff.mpr fun g _ => ?_
  change g ∈ (H : Subgroup (GQ v))
  rw [← hH, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [IntermediateField.mem_fixedField_iff] at hx
  have hxK : x ∈ MaximalUnramifiedExtension v := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension v), IntermediateField.mem_fixedField_iff]
    exact fun f hf => hx f (hle (Subgroup.mem_sup_left hf))
  obtain ⟨m, hm, h⟩ := fd_level hxK
  obtain ⟨j, hj⟩ := KStar.IdealValuations.exists_pow_of_aut g hm
  rw [h g (σ ^ j) fun y hy => by rw [hj y hy, fd_frob hσ hm j y hy]]
  exact hx _ (hle (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers σ j)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.z1fMap :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (φ : G →* GQ l) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {A' : Type} [CommRing A'] [Algebra ℚ_[l] A'] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A G V) (ρ' : Representation A' G V'), (ContAction ρ → ReciprocityTheory.Gal.B1 ρ ≤ UpperTheory.V.Loc.finiteCocycles φ ρ) ∧ ∀ f : V →ₗ[ℚ_[l]] V', (∀ g x, f (ρ g x) = ρ' g (f x)) → ∀ c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ, (fun g => f (c g)) ∈ UpperTheory.V.Loc.finiteCocycles φ ρ' := by
  intro l _ G _ _ φ A _ _ A' _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ'
  refine ⟨fun hρ => ?_, fun f hf c hc => ?_⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨⟨?_, fun g h => ?_⟩, v ⊗ₜ[ℚ_[l]] (1 : Bcr l), fun g => ?_⟩
    · have h1 : Continuous fun g : G => ρ g v :=
        Continuous.comp (g := fun p : G × V => ρ p.1 p.2) (f := fun g : G => (g, v)) hρ (by fun_prop)
      exact h1.sub continuous_const
    · simp [ReciprocityTheory.Gal.d0]
    · simp [ReciprocityTheory.Gal.d0, actC, sub_tmul]
  · obtain ⟨⟨hc, hcc⟩, x, hx⟩ := hc
    have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
    refine ⟨⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Bcr l) f x, fun g => ?_⟩
    · simp only [hcc g h, map_add, hf]
    · have key : ∀ y : V ⊗[ℚ_[l]] Bcr l, LinearMap.rTensor (Bcr l) f (actC φ ρ g y) =
          actC φ ρ' g (LinearMap.rTensor (Bcr l) f y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [actC, hf]
        | add a b ha hb => simp only [map_add, ha, hb]
      rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
end

