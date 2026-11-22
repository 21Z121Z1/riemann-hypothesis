import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodTraceIntegral
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.DetBound

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

theorem ιMulti_eq_det_smul {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {n : ℕ}
    (b : Module.Basis (Fin n) O M) (v : Fin n → M) :
    exteriorPower.ιMulti O n v = b.det v • exteriorPower.ιMulti O n b := by
  have h : exteriorPower.ιMulti O n (M := M) = b.det.smulRight (exteriorPower.ιMulti O n b) := by
    refine Module.Basis.ext_alternating b fun i hi => ?_
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)
    change exteriorPower.ιMulti O n (b ∘ σ) = b.det (b ∘ σ) • exteriorPower.ιMulti O n b
    rw [AlternatingMap.map_perm, AlternatingMap.map_perm, Module.Basis.det_self, smul_assoc, one_smul]
  exact DFunLike.congr_fun h v

theorem exists_wedge_generator {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Module.Free O M]
    [Module.Finite O M] {n : ℕ} (hn : Module.finrank O M = n) : ∃ ω : ⋀[O]^n M, O ∙ ω = ⊤ := by
  let b := Module.finBasisOfFinrankEq O M hn
  refine ⟨exteriorPower.ιMulti O n b, ?_⟩
  rw [eq_top_iff, ← exteriorPower.ιMulti_span O n M, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  rw [ιMulti_eq_det_smul b v]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem exists_wedge_eq_smul_dvd {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Module.Free O M]
    [Module.Finite O M] {n : ℕ} (hn : Module.finrank O M = n) (v : Fin n → M) (D : O)
    (hD : ∀ x : M, D • x ∈ Submodule.span O (Set.range v)) (ω : ⋀[O]^n M) (hω : O ∙ ω = ⊤) :
    ∃ u : O, exteriorPower.ιMulti O n v = u • ω ∧ u ∣ D ^ n := by
  let b := Module.finBasisOfFinrankEq O M hn
  let L := exteriorPower.alternatingMapLinearEquiv b.det
  have hL : ∀ w, L (exteriorPower.ιMulti O n w) = b.det w := fun w =>
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 (hω ▸ Submodule.mem_top : exteriorPower.ιMulti O n v ∈ O ∙ ω)
  obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.1 (hω ▸ Submodule.mem_top : exteriorPower.ιMulti O n b ∈ O ∙ ω)
  have hu' : b.det v = u * L ω := by rw [← hL, ← hu, map_smul, smul_eq_mul]
  let A : M →ₗ[O] M := b.constr O v
  have hA : ∀ j, A (b j) = v j := fun j => b.constr_basis O v j
  have hAv : b.det v = LinearMap.det A := by
    have : (A ∘ b) = v := funext hA
    rw [← this, Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  have hrange : ∀ j, ∃ y, A y = D • b j := by
    intro j
    have h := hD (b j)
    rw [← b.constr_range O (f := v)] at h
    exact h
  choose y hy using hrange
  let B' : M →ₗ[O] M := b.constr O y
  have hAB : A ∘ₗ B' = D • LinearMap.id := by
    refine b.ext fun j => ?_
    simp only [LinearMap.comp_apply, B', b.constr_basis, hy, LinearMap.smul_apply, LinearMap.id_apply]
  have hdet : LinearMap.det A * LinearMap.det B' = D ^ n := by
    rw [← LinearMap.det_comp, hAB, LinearMap.det_smul, LinearMap.det_id, mul_one, hn]
  refine ⟨u, hu.symm, ⟨L ω * LinearMap.det B', ?_⟩⟩
  rw [← hdet, ← hAv, hu', mul_assoc]

theorem val_bounds_of_dvd (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K] (l : ℕ) (hl : (l : O) ≠ 0) (hlm : (l : O) ∈ IsLocalRing.maximalIdeal O) (u D : O) (n : ℕ)
    (hD : D ≠ 0) (hu : u ∣ D ^ n) :
    0 ≤ val_vp O l (algebraMap O K u) ∧ val_vp O l (algebraMap O K u) ≤ n • val_vp O l (algebraMap O K D) := by
  obtain ⟨w, hw⟩ := hu
  have hDn : D ^ n ≠ 0 := pow_ne_zero _ hD
  have hu0 : u ≠ 0 := by rintro rfl; exact hDn (by simp [hw])
  have hw0 : w ≠ 0 := by rintro rfl; exact hDn (by simp [hw])
  have hinj := IsFractionRing.injective O K
  have hne : ∀ a : O, a ≠ 0 → algebraMap O K a ≠ 0 := fun a ha => (map_ne_zero_iff _ hinj).2 ha
  have hVne : ∀ a : O, a ≠ 0 →
      (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K a) ≠ 0 := by
    intro a ha; simpa using hne a ha
  have key : ∀ a : O, a ≠ 0 → 0 ≤ ord_vw O (algebraMap O K a) := by
    intro a ha
    unfold ord_vw
    rw [neg_nonneg, WithZero.log_le_iff_le_exp (hVne a ha), WithZero.exp_zero]
    exact HeightOneSpectrum.valuation_le_one _ a
  have hmul : ord_vw O (algebraMap O K (D ^ n)) = ord_vw O (algebraMap O K u) + ord_vw O (algebraMap O K w) := by
    unfold ord_vw
    rw [hw, map_mul, Valuation.map_mul, WithZero.log_mul (hVne u hu0) (hVne w hw0), neg_add]
  have hpow : ord_vw O (algebraMap O K (D ^ n)) = n * ord_vw O (algebraMap O K D) := by
    unfold ord_vw
    rw [map_pow, Valuation.map_pow, WithZero.log_pow, nsmul_eq_mul, mul_neg]
  have hlK : (l : K) = algebraMap O K (l : O) := (map_natCast _ _).symm
  have hlpos : 0 < ord_vw O (l : K) := by
    rw [hlK]
    refine lt_of_le_of_ne (key _ hl) ?_
    intro h4
    have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K (l : O)) < 1 := by
      rw [HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hlm
    unfold ord_vw at h4
    have := WithZero.exp_log (hVne _ hl)
    rw [neg_eq_zero.1 h4.symm, WithZero.exp_zero] at this
    exact h1.ne this.symm
  have hw' := key w hw0
  have hu' := key u hu0
  rw [val_vp, if_neg (hne u hu0), val_vp, if_neg (hne D hD)]
  have hL : (0 : ℚ) < (ord_vw O (l : K) : ℚ) := by exact_mod_cast hlpos
  refine ⟨WithTop.coe_nonneg.2 (div_nonneg (by exact_mod_cast hu') hL.le), ?_⟩
  rw [← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hL.le
  have : ord_vw O (algebraMap O K u) ≤ n * ord_vw O (algebraMap O K D) := by omega
  exact_mod_cast this

theorem inK_injective {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] : Function.Injective (inK K H (O := O)) := by
  have h : (inK K H (O := O)) = ((Algebra.linearMap O K).rTensor H) ∘ₗ (TensorProduct.lid O H).symm.toLinearMap := by
    ext h; simp [inK]
  rw [h, LinearMap.coe_comp]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective O K)).comp
    (TensorProduct.lid O H).symm.injective

theorem cmType_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K] {I : Type}
    {φ : I → E →+* K} (hφ : IsCMTypeIn φ) : Function.Injective φ := by
  intro i j h
  obtain ⟨k, _, hk⟩ := hφ (φ i)
  exact (hk i (Or.inl rfl)).trans (hk j (Or.inl h)).symm

theorem gens_mem_linearIndependent {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] {D : O} {I : Type} [Fintype I] {φ : I → E →+* K} (hφ : IsCMTypeIn φ)
    {H : Type} [AddCommGroup H] [Module O H] {ρ : orderC c →+* Module.End O H} {Fil : Submodule O H}
    {B : LinearMap.BilinForm O H} (hL : IsCMLattice φ ρ Fil B) (hE : EigenClaims φ ρ Fil B D) {e f : I → H}
    (hG : IsGens φ ρ e f) : (∀ i, e i ∈ Fil) ∧ LinearIndependent O e := by
  haveI : Module.Free O H := hL.1
  have hself : ∀ i, e i ∈ eigLat (K := K) ρ (φ i) := fun i => (hG i).1 ▸ Submodule.mem_span_singleton_self _
  refine ⟨fun i => ?_, ?_⟩
  · have h := hE.2.2.2.1 i
    exact (inf_eq_right.1 h) (hself i)
  · have hi : iSupIndep (fun σ : E →+* K => eigLat (K := K) ρ σ) := hE.2.2.1.1
    refine iSupIndep.linearIndependent _ (hi.comp (cmType_injective hφ)) hself ?_
    intro i h0
    obtain ⟨g, hg, hgs⟩ := (hE.2.1 (φ i)).2.1
    have : g ∈ eigLat (K := K) ρ (φ i) := hgs ▸ Submodule.mem_span_singleton_self _
    rw [(hG i).1, h0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at this
    exact hg this

theorem smul_mem_span_gens {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] {D : O} {I : Type} [Fintype I] {φ : I → E →+* K} (hφ : IsCMTypeIn φ)
    {H : Type} [AddCommGroup H] [Module O H] {ρ : orderC c →+* Module.End O H} {Fil : Submodule O H}
    {B : LinearMap.BilinForm O H} (hL : IsCMLattice φ ρ Fil B) (hE : EigenClaims φ ρ Fil B D) {e f : I → H}
    (hG : IsGens φ ρ e f) (e' : I → Fil) (he' : ∀ i, (e' i : H) = e i) (x : Fil) :
    D • x ∈ Submodule.span O (Set.range e') := by
  haveI : Module.Free O H := hL.1
  have hind : iSupIndep (fun σ : E →+* K => eigK ρ σ) := hE.1.submodule_iSupIndep
  have hxK : inK (O := O) K H (D • (x : H)) ∈ ⨆ i, eigK ρ (φ i) := by
    rw [← hL.2.2.2.2.2.1]
    exact Submodule.tmul_mem_baseChange_of_mem 1 (Fil.smul_mem D x.2)
  obtain ⟨F, hF, hFs⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (hE.2.2.1.2 (x : H))
  have hzero : ∀ σ, σ ∉ Set.range φ → F σ = 0 := by
    intro σ₀ hσ₀
    apply inK_injective (O := O) K H
    rw [map_zero]
    have h1 : inK (O := O) K H (F σ₀) ∈ eigK ρ σ₀ := hF σ₀
    have h2 : inK (O := O) K H (F σ₀) ∈ ⨆ (j : E →+* K) (_ : j ≠ σ₀), eigK ρ j := by
      have hsum : inK (O := O) K H (F σ₀) = inK (O := O) K H (D • (x : H)) - ∑ σ ∈ F.support.erase σ₀, inK (O := O) K H (F σ) := by
        rw [← hFs, Finsupp.sum, map_sum]
        by_cases hm : σ₀ ∈ F.support
        · rw [← Finset.add_sum_erase _ _ hm, add_sub_cancel_right]
        · rw [Finsupp.notMem_support_iff.1 hm, map_zero, Finset.erase_eq_of_notMem hm, sub_self]
      rw [hsum]
      refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun σ hσ => ?_)
      · have hle : (⨆ i, eigK ρ (φ i)) ≤ ⨆ (j : E →+* K) (_ : j ≠ σ₀), eigK ρ j := iSup_le fun i =>
          le_iSup₂_of_le (f := fun (j : E →+* K) (_ : j ≠ σ₀) => eigK ρ j) (φ i) (fun h => hσ₀ ⟨i, h⟩) le_rfl
        exact hle hxK
      · exact (le_iSup₂_of_le (f := fun (j : E →+* K) (_ : j ≠ σ₀) => eigK ρ j) σ
          (Finset.ne_of_mem_erase hσ) le_rfl) (hF σ)
    exact Submodule.disjoint_def.1 (hind σ₀) _ h1 h2
  have hH : D • (x : H) ∈ Submodule.span O (Set.range e) := by
    rw [← hFs, Finsupp.sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    by_cases hσ : σ ∈ Set.range φ
    · obtain ⟨i, rfl⟩ := hσ
      have h := hF (φ i)
      rw [(hG i).1, Submodule.mem_span_singleton] at h
      obtain ⟨a, ha⟩ := h
      rw [← ha]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [hzero σ hσ]; exact Submodule.zero_mem _
  have hspan : Submodule.span O (Set.range e) = (Submodule.span O (Set.range e')).map Fil.subtype := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    exact (he' i).symm
  rw [hspan] at hH
  obtain ⟨y, hy, hyx⟩ := hH
  have : y = D • x := Subtype.ext hyx
  exact this ▸ hy

theorem detClaims : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → DetClaims K l Fil D e := by
  intro E _ _ _ c _ l hl O _ _ _ _ K _ _ _ hlm _ D hD _ I _ φ hφ H _ _ ρ Fil B hL hE e f hG
  haveI : Module.Free O H := hL.1
  haveI : Module.Finite O H := hL.2.1
  obtain ⟨hmem, hli⟩ := gens_mem_linearIndependent hφ hL hE hG
  let e₀ : I → Fil := fun i => ⟨e i, hmem i⟩
  have he₀ : ∀ i, (e₀ i : H) = e i := fun i => rfl
  have hli₀ : LinearIndependent O e₀ := LinearIndependent.of_comp Fil.subtype hli
  have hrank : Module.finrank O Fil = Fintype.card I := by
    apply le_antisymm
    · let g : Fil →ₗ[O] Submodule.span O (Set.range e₀) :=
        ((LinearMap.lsmul O Fil D).codRestrict _ (fun x => smul_mem_span_gens hφ hL hE hG e₀ he₀ x))
      have hg : Function.Injective g := by
        intro x y hxy
        have : D • x = D • y := congrArg Subtype.val hxy
        exact smul_right_injective _ hD this
      exact (LinearMap.finrank_le_finrank_of_injective hg).trans (finrank_range_le_card e₀)
    · exact hli₀.fintype_card_le_finrank
  refine ⟨inferInstance, hrank, hmem, exists_wedge_generator hrank, ?_⟩
  intro ω hω s e' he'
  obtain ⟨u, hu, hdvd⟩ := exists_wedge_eq_smul_dvd hrank (fun j => e' (s j)) D (by
    intro x
    have h := smul_mem_span_gens hφ hL hE hG e' he' x
    have : Set.range (fun j => e' (s j)) = Set.range e' := s.surjective.range_comp e'
    rw [this]; exact h) ω hω
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  exact ⟨u, hu, val_bounds_of_dvd O K l hl0 hlm u D _ hD hdvd⟩

end GlobalTheory.DetBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductEqZeroOfVanishingOnCover
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem cup_supp_chainsMap_mono (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) [Mono f] (p : ℤ) :
    Mono (((chains R).map f).f p) := by
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
    have hnat := ((GlobalTheory.EtC.chains_basic R).2.1 f N)
    have hm : Mono ((free R).map (f.app (op (SimplexCategory.mk N)))) :=
      ((GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R (f.app (op (SimplexCategory.mk N)))).1 inferInstance)
    have : ((chains R).map f).f (-(N : ℤ)) =
        ((chains R).map f).f (-(N : ℤ)) ≫ (chainsXIso R E N).hom ≫ (chainsXIso R E N).inv := by simp
    rw [this, ← Category.assoc, hnat, Category.assoc]
    infer_instance
  · haveI := (GlobalTheory.EtC.chains_basic R).1 U
    exact IsZero.mono (isZero_of_isStrictlyLE _ 0 p hp) _

theorem cup_supp_extend (R : Type) [CommRing R] {I : Cx R} (hI : ∀ s, Injective (I.X s)) {U E : Spc} (f : U ⟶ E) [Mono f]
    {n : ℤ} (β : Cochain ((chains R).obj U) I n) :
    ∃ β' : Cochain ((chains R).obj E) I n, (Cochain.ofHom ((chains R).map f)).comp β' (zero_add n) = β := by
  refine ⟨Cochain.mk fun p q h => by
    haveI := cup_supp_chainsMap_mono R f p
    haveI := hI q
    exact Injective.factorThru (β.v p q h) (((chains R).map f).f p), ?_⟩
  refine Cochain.ext _ _ fun p q h => ?_
  haveI := cup_supp_chainsMap_mono R f p
  haveI := hI q
  rw [Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) h, Cochain.ofHom_v, Cochain.mk_v]
  exact Injective.comp_factorThru (J := I.X q) (β.v p q h) (((chains R).map f).f p)

theorem cup_supp_vanish (R : Type) [CommRing R] {K : Cx R} {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g)
    {k : ℤ} (γ : Cochain ((chains R).obj E) K k)
    (hf : (Cochain.ofHom ((chains R).map f)).comp γ (zero_add k) = 0)
    (hg : (Cochain.ofHom ((chains R).map g)).comp γ (zero_add k) = 0) : γ = 0 := by
  refine Cochain.ext _ _ fun p q h => ?_
  rw [Cochain.zero_v]
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
    have hf' := congrArg (fun z => z.v (-(N : ℤ)) q h) hf
    have hg' := congrArg (fun z => z.v (-(N : ℤ)) q h) hg
    simp only [Cochain.comp_v _ _ (zero_add k) (-(N : ℤ)) (-(N : ℤ)) q (add_zero _) h, Cochain.ofHom_v,
      Cochain.zero_v] at hf' hg'
    have nf := (GlobalTheory.EtC.chains_basic R).2.1 f N
    have ng := (GlobalTheory.EtC.chains_basic R).2.1 g N
    haveI := hc.2.2 (op (SimplexCategory.mk N))
    have key : biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
        ((free R).map (g.app (op (SimplexCategory.mk N)))) ≫ ((chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q h) = 0 := by
      apply biprod.hom_ext'
      · rw [biprod.inl_desc_assoc, comp_zero]
        have : (free R).map (f.app (op (SimplexCategory.mk N))) =
            (chainsXIso R U N).inv ≫ ((chains R).map f).f (-(N : ℤ)) ≫ (chainsXIso R E N).hom := by
          rw [nf]; simp
        rw [this]; simp [hf']
      · rw [biprod.inr_desc_assoc, comp_zero]
        have : (free R).map (g.app (op (SimplexCategory.mk N))) =
            (chainsXIso R V N).inv ≫ ((chains R).map g).f (-(N : ℤ)) ≫ (chainsXIso R E N).hom := by
          rw [ng]; simp
        rw [this]; simp [hg']
    have h0 : (chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q h = 0 := by
      rw [← cancel_epi (biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
        ((free R).map (g.app (op (SimplexCategory.mk N))))), key, comp_zero]
    have : γ.v (-(N : ℤ)) q h = (chainsXIso R E N).hom ≫ ((chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q h) := by simp
    rw [this, h0, comp_zero]
  · haveI := (GlobalTheory.EtC.chains_basic R).1 E
    exact (isZero_of_isStrictlyLE _ 0 p hp).eq_of_src _ _

theorem cup_supp_rep (R : Type) [CommRing R] {I : Cx R} (hI : ∀ s, Injective (I.X s)) {U E : Spc} (f : U ⟶ E) [Mono f]
    {n : ℤ} (a : CohomologyClass ((chains R).obj E) I n) (ha : cpull ((chains R).map f) I n a = 0) :
    ∃ α : Cocycle ((chains R).obj E) I n, CohomologyClass.mk α = a ∧
      (Cochain.ofHom ((chains R).map f)).comp α.1 (zero_add n) = 0 := by
  obtain ⟨α, rfl⟩ := a.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)) = 0 at ha
  rw [CohomologyClass.mk_eq_zero_iff] at ha
  obtain ⟨n', hn', β, hβ⟩ := ha
  have hβ2 : δ n' n β = (Cochain.ofHom ((chains R).map f)).comp α.1 (zero_add n) := hβ
  obtain ⟨β', hβ'⟩ := cup_supp_extend R hI f β
  let c : Cocycle ((chains R).obj E) I n := Cocycle.mk (δ n' n β') (n + 1) rfl (δ_δ _ _ _ _)
  refine ⟨α - c, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff]
    exact ⟨n', hn', β', rfl⟩
  · change (Cochain.ofHom ((chains R).map f)).comp (α.1 - δ n' n β') (zero_add n) = 0
    rw [Cochain.comp_sub, ← δ_ofHom_comp, hβ', hβ2, sub_self]

theorem cup_supp (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (hI : ∀ s, Injective (I.X s))
    (hJ : ∀ s, Injective (J.X s)) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g) {n m k : ℤ}
    (hk : n + m = k) (a : CohomologyClass ((chains R).obj E) I n) (b : CohomologyClass ((chains R).obj E) J m)
    (ha : cpull ((chains R).map f) I n a = 0) (hb : cpull ((chains R).map g) J m b = 0) : μ.cup E hk a b = 0 := by
  haveI := hc.1
  haveI := hc.2.1
  obtain ⟨α, rfl, hα⟩ := cup_supp_rep R hI f a ha
  obtain ⟨β, rfl, hβ⟩ := cup_supp_rep R hJ g b hb
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ hk).2 α β γ hγ, CohomologyClass.mk_eq_zero_iff]
  have evK := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := K) (n := k)
  have evI := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)
  have evJ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := J) (n := m)
  have h1 : (Cochain.ofHom ((chains R).map f)).comp γ.1 (zero_add k) = 0 := by
    have evKU := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := U) (I := K) (n := k)
    have evIU := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := U) (I := I) (n := n)
    apply evKU.2.2.1
    intro N w h U' x
    rw [evK.2.2.2.1 f γ.1 N w h U' x, (evKU.1 0 0 N w h U' x).2.2.1, hγ N w h U' (x.map f)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.2.1 0 i (by omega)).2.1 f,
      ← evI.2.2.2.1 f α.1, hα, (evIU.1 0 0 _ _ rfl U' (x.sub 0 i (by omega))).2.2.1]
    simp
  have h2 : (Cochain.ofHom ((chains R).map g)).comp γ.1 (zero_add k) = 0 := by
    have evKV := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := V) (I := K) (n := k)
    have evJV := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := V) (I := J) (n := m)
    apply evKV.2.2.1
    intro N w h U' x
    rw [evK.2.2.2.1 g γ.1 N w h U' x, (evKV.1 0 0 N w h U' x).2.2.1, hγ N w h U' (x.map g)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.2.1 i (N - i) (by omega)).2.1 g,
      ← evJ.2.2.2.1 g β.1, hβ, (evJV.1 0 0 _ _ rfl U' (x.sub i (N - i) (by omega))).2.2.1]
    simp
  have h0 : γ = 0 := Cocycle.ext (cup_supp_vanish R f g hc γ.1 h1 h2)
  rw [h0]
  exact zero_mem _

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantValuationOrder
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem rank_G_map_eq_lieRank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ) (Φ : FreeForm D N ψ) (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → (Φ.G.map ((algebraMap O C).comp f)).rank = D.lieRank σ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D ψ Φ σ f hf
  obtain ⟨-, -, -, hθ, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := hθ y
    exact ⟨a ⊗ₜ (1 : Λ), by rw [hf]; simp⟩
  obtain ⟨⟨indT, supT, dimT⟩, ⟨-, supH, dimH⟩⟩ := GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ N h hh D
  obtain ⟨πT, hπT⟩ := GlobalTheory.T.exists_theta_projection p O C Λ N h σ f Φ.eT hf
  obtain ⟨πH, hπH⟩ := GlobalTheory.T.exists_theta_projection p O C Λ N h σ f Φ.eM hf
  have hT : (fun l => (rhoTA D l).map (WittVector.fontaineTheta O p)) = actT D := by
    funext l; rw [rhoTA, Matrix.map_map]; rfl
  have hH : (fun l => (D.ρM l).map (WittVector.fontaineTheta O p)) = actH D := rfl
  have keyT := GlobalTheory.T.theta_projection_surjective_eigen p O C Λ N h σ f (rhoTA D) Φ.eT πT hinj hθ hfs hf Φ.frameT hπT
  rw [hT] at keyT
  obtain ⟨qT, hqT, -⟩ := keyT supT (dimT σ)
  have keyH := GlobalTheory.T.theta_projection_surjective_eigen p O C Λ N h σ f (fun l => D.ρM l) Φ.eM πH hinj hθ hfs hf Φ.frameM hπH
  rw [hH] at keyH
  obtain ⟨qH, hqH, -⟩ := keyH supH (dimH σ)
  obtain ⟨-, -, hGρ, -, -⟩ := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
  have hX : ∀ l, D.G.map (WittVector.fontaineTheta O p) * actH D l =
      actT D l * D.G.map (WittVector.fontaineTheta O p) := by
    intro l
    rw [← congrFun hT l, ← congrFun hH l]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hGρ l]
  obtain ⟨hle, hrange⟩ := GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actH D) (actT D) (D.G.map (WittVector.fontaineTheta O p)) hX
  have hb : Matrix.toLin' ((D.G.map (WittVector.fontaineTheta O p)).map (algebraMap O C)) = bC C D := by
    rw [Matrix.map_map]; rfl
  rw [hb] at hle hrange
  have hlie := GlobalTheory.T.lie_rank_eq_finrank_eigen_inter p C v O hv ε Λ h D σ
  rw [hrange supH indT σ] at hlie
  let g : eig C (actH D) σ →ₗ[C] eig C (actT D) σ :=
    (bC C D).restrict (fun x hx => hle σ (Submodule.mem_map_of_mem hx))
  have hmat := GlobalTheory.T.theta_projection_intertwining p O C Λ N h f Φ.eM Φ.eT πH πT D.G Φ.G hπH hπT Φ.matG
  have hcomm : qT.toLinearMap ∘ₗ g = (Φ.G.map ((algebraMap O C).comp f)).mulVecLin ∘ₗ qH.toLinearMap := by
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    rw [hqT, hqH]
    exact hmat x
  have e1 : (eig C (actH D) σ).map (bC C D) = (LinearMap.range g).map (eig C (actT D) σ).subtype := by
    have : bC C D ∘ₗ (eig C (actH D) σ).subtype = (eig C (actT D) σ).subtype ∘ₗ g :=
      LinearMap.ext fun x => rfl
    rw [← LinearMap.range_comp, ← this, LinearMap.range_comp, Submodule.range_subtype]
  rw [hlie, e1, ← (Submodule.equivMapOfInjective _ (eig C (actT D) σ).injective_subtype
    (LinearMap.range g)).finrank_eq, ← qT.finrank_map_eq (LinearMap.range g),
    ← LinearMap.range_comp, hcomm,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range qH)]
  rfl

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenPartProjectionMatrixMapMulVecOfEigenvectorStatement
section
open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenPartProjectionMatrix_map_mulVec_of_eigenvector : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K)
    (i : Fin D.a) (v : Fin n → K), (∀ c : 𝓞 D.F, (M c).map g *ᵥ v = g (βB (b.t i c)) • v) →
      (projMat b βB M i).map g *ᵥ v = v := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig) | (exact GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig) | (intros; apply GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfUpwardFamilyStandardCover
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

theorem sep_of_covBy : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Sep (G ⋙ F) Sg := by
  intro R _ C _ C' _ F G _ _ H _ t Sg _ hcov
  obtain ⟨n, b, hb, hc⟩ := hcov
  intro x hx
  refine sep_std H hb x fun S u ⟨i, hi⟩ ↦ ?_
  obtain ⟨t', a, ha, ⟨w⟩⟩ := hc i S u hi
  have e : u = G.map a ≫ w := Subsingleton.elim _ _
  have h0 : mp F (G.map a) x = 0 := hx t' a ha
  rw [e, mp_comp, h0, map_zero]

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeSequenceExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_mayerVietoris_free_sequence_exact : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∃ w, (ShortComplex.mk (biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))) (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) w).Exact := by
  first | (exact @GlobalTheory.EtC.MVExact.mv_exact) | (exact GlobalTheory.EtC.MVExact.mv_exact) | (intros; apply GlobalTheory.EtC.MVExact.mv_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorIsFinitaryStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)), PreservesFilteredColimitsOfSize.{0, 0} M → Finitary (ofRings R M) := by
  first
  | exact @GlobalTheory.ofRings_finitary
  | exact GlobalTheory.ofRings_finitary
  | (intros; apply GlobalTheory.ofRings_finitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyCoprodSchemesBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem coh_coprod_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ n : ℤ, Function.Bijective (fun (x : H R (sch.obj U) F n) (i : ι) => pull R (sch.map (j i)) F n x) := by
  intro R _ F U ι V j hc n
  refine GlobalTheory.T.etaleSpaceCohomology_levelwise_coproduct_bijective R F (sch.obj U) ι (fun i => sch.obj (V i)) (fun i => sch.map (j i)) ?_ n
  intro k
  exact GlobalTheory.T.freeEtaleSheaf_presheaf_over_coproduct_eq_sum R U ι V j hc (yoneda.obj U) (𝟙 _) (fun i => yoneda.obj (V i)) (fun i => yoneda.map (j i))
    (fun _ => 𝟙 _) (fun i => IsPullback.of_vert_isIso (by simp))

end GlobalTheory
end

