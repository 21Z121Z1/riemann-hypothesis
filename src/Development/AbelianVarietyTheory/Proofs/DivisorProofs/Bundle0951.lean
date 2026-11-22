import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.Adelic GlobalTheory.CechPic

namespace GlobalTheory.FieldChangeInter

variable {X X' : Scheme.{0}}

def cechIso {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X) {κ : Type} [LinearOrder κ]
    (D : κ → X.Opens) :
    letI := algebraΓOfHom f
    cechLB f M D ≅ cech R (LB.toMod M) ⊤ D :=
  letI := algebraΓOfHom f
  (cechFunctor κ R).mapIso (Cube.isoMk (fun s => LinearEquiv.ofBijective
    (M := SecOnR f M (⨅ i ∈ s, D i)) (M₂ := sectionsOn (LB.toMod M) (⊤ ⊓ ⨅ i ∈ s, D i))
    (SecOnR.restrict f M (inf_le_right : ⊤ ⊓ (⨅ i ∈ s, D i) ≤ ⨅ i ∈ s, D i))
    (SecOnR.restrict_bijective f _ (le_inf le_top le_rfl)))
    fun {s t} h x => (SecOnR.restrict_restrict f _ inf_le_right x).trans
      (SecOnR.restrict_restrict f inf_le_right (cechOpen_anti ⊤ D h) x).symm)

theorem nonempty_homology_equiv {R : Type} (O : Type) [CommRing R] [CommRing O]
    [Algebra R O] [Module.Flat R O] (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Nonempty ((((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj
      C).homology n ≃ₗ[O] O ⊗[R] C.homology n) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R O))
  have : (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R O)).isLeftAdjoint
  obtain ⟨e⟩ := Semicont.nonempty_extendScalars_obj_equiv O (C.homology n)
  exact ⟨((C.sc n).mapHomologyIso
    (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O))).toLinearEquiv ≪≫ₗ e⟩

theorem nonempty_coh_equiv {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (hM : M.IsLB)
    {κ : Type} [LinearOrder κ] [Finite κ] {D : κ → X.Opens} (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) (n : ℕ) :
    letI := algebraΓOfHom f
    Nonempty ((cechLB f M D).homology n ≃ₗ[R] coh (twist (structureModule X) M) n) := by
  letI := algebraΓOfHom f
  haveI := LB.isQuasicoherent_toMod hM
  exact ⟨((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechIso f M D)).toLinearEquiv ≪≫ₗ
    cechHEquivCoh R hc hD (LB.toMod M) n ≪≫ₗ (cohOn.mapIso R ⊤ n (Twist.unitTwistIso M)).symm⟩

variable {k E : Type} [Field k] [Field E] [Algebra k E] {f : X ⟶ Spec (CommRingCat.of k)}
  {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X}

theorem hdim_pull [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    hdim E (twist (structureModule X') (M.pull π)) n = hdim k (twist (structureModule X) M) n := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  obtain ⟨e₁⟩ := nonempty_coh_equiv f hM hc hD' n
  obtain ⟨e₂⟩ := nonempty_coh_equiv f' (LB.isLB_pull hM π) (D := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := nonempty_homology_equiv E (cechLB f M D) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechLBBaseChangeIso hM H hD')).toLinearEquiv
  rw [hdim_def, hdim_def, ← e₁.finrank_eq, ← e₂.finrank_eq]
  exact e₄.finrank_eq.symm.trans (e₃.finrank_eq.trans Module.finrank_baseChange)

theorem interNum_pull [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {ι : Type} [Fintype ι] {L : ι → LB X}
    (hL : ∀ i, (L i).IsLB) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    interNum E (structureModule X') (fun i => (L i).pull π) = interNum k (structureModule X) L := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have h : chiPic k (structureModule X) = chiPic E (structureModule X') ∘ pull π := by
    funext c
    obtain ⟨M, hM, rfl⟩ := cls_surj c
    exact finsum_congr fun n => congrArg (fun a : ℕ => (-1 : ℤ) ^ n * a) (hdim_pull H hM n).symm
  rw [interNum_eq_multiDiff k _ hL, h, multiDiff_comap, Function.comp_apply, map_zero,
    interNum_eq_multiDiff E _ fun i ↦ pull_isLB (hL i) π]
  rfl

theorem del_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (S : LinSys k),
    IsProjOver S.str → (S.baseChange E).del = S.del := by
  intro k E _ _ _ S h
  have : IsProper S.str := by
    obtain ⟨N, i, hi, e⟩ := h
    have := isProper_str k N
    rw [← e]
    infer_instance
  exact interNum_pull (ι := Fin S.D) (L := fun _ => S.L) (S.isPullback_baseChange E) fun _ => S.isLB

end GlobalTheory.FieldChangeInter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.HeightExt

open NumberField IsDedekindDomain GlobalTheory.ChowHt GlobalTheory.Adelic

section Places

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def locDeg (K : Type) [Field K] [NumberField K] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) : ℕ :=
  w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)

theorem mk_algebraMap (w : HeightOneSpectrum (𝓞 L)) (x : K) :
    FinitePlace.mk w (algebraMap K L x) = FinitePlace.mk (w.under (𝓞 K)) x ^ locDeg K w := by
  set v := w.under (𝓞 K) with hv
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have he : 0 < w.asIdeal.ramificationIdx (𝓞 K) := Ideal.ramificationIdx_pos _ _
  have hf : 0 < w.asIdeal.inertiaDeg (𝓞 K) := Ideal.inertiaDeg_pos _ _
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero, map_zero, locDeg, zero_pow (Nat.mul_pos he hf).ne']
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hn
  have h0 : v.valuation K x ≠ 0 := (v.valuation K).ne_zero_iff.2 hx
  rw [FinitePlace.mk_apply, FinitePlace.mk_apply, FinitePlace.norm_embedding', FinitePlace.norm_embedding',
    ← HeightOneSpectrum.valuation_liesOver L v w x, map_pow, WithZeroMulInt.toNNReal_neg_apply _ h0,
    WithZeroMulInt.toNNReal_neg_apply _ h0, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot, hn, locDeg]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem finite_fiber (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.Finite := by
  have h : (v.asIdeal.primesOver (𝓞 L)).Finite := Set.toFinite _
  refine (h.preimage (f := fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset fun w hw => ?_
  exact ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩

theorem sum_locDeg (v : HeightOneSpectrum (𝓞 K)) :
    ∑ w ∈ (finite_fiber (L := L) v).toFinset, locDeg K w = Module.finrank K L := by
  classical
  have hsumN : ∑ q : v.asIdeal.primesOver (𝓞 L), q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) =
      Module.finrank K L := by
    rw [Ideal.sum_ramification_inertia_eq_finrank, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]
  rw [← hsumN]
  refine Finset.sum_bij (fun w hw => ⟨w.asIdeal, w.isPrime,
    ⟨(congrArg HeightOneSpectrum.asIdeal (((finite_fiber (L := L) v).mem_toFinset).1 hw)).symm⟩⟩) (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => HeightOneSpectrum.ext (congrArg Subtype.val h)) (fun q _ => ?_) fun _ _ => rfl
  refine ⟨⟨q.1, q.2.1, fun h0 => v.ne_bot ?_⟩, (Set.Finite.mem_toFinset _).2 (HeightOneSpectrum.ext q.2.2.over.symm),
    rfl⟩
  have h1 : v.asIdeal = q.1.comap (algebraMap (𝓞 K) (𝓞 L)) := q.2.2.over
  rw [h1, h0]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

theorem finsum_locDeg_mul (g : HeightOneSpectrum (𝓞 K) → ℝ) (hg : (Function.support g).Finite) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 L), (locDeg K w : ℝ) * g (w.under (𝓞 K)) = Module.finrank K L * ∑ᶠ v, g v := by
  classical
  have hS : {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ Function.support g}.Finite :=
    (hg.biUnion fun v _ => finite_fiber (L := L) v).subset fun w hw => Set.mem_biUnion hw rfl
  rw [finsum_eq_sum_of_support_subset _ (s := hS.toFinset) fun w hw => by
      simpa using right_ne_zero_of_mul hw,
    finsum_eq_sum g hg, Finset.mul_sum,
    ← Finset.sum_fiberwise_of_maps_to (t := hg.toFinset) (g := fun w => w.under (𝓞 K)) fun w hw => by simpa using hw]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [← sum_locDeg v, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr ?_ fun w hw => by rw [(Set.Finite.mem_toFinset _).1 hw]
  ext w
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv ⊢
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hv, h⟩⟩

theorem sum_comp_algebraMap (f : (K →+* ℂ) → ℝ) :
    ∑ σ : L →+* ℂ, f (σ.comp (algebraMap K L)) = Module.finrank K L * ∑ τ : K →+* ℂ, f τ := by
  classical
  have hfib : ∀ τ : K →+* ℂ, (Finset.univ.filter fun σ : L →+* ℂ => σ.comp (algebraMap K L) = τ).card =
      Module.finrank K L := by
    intro τ
    let _ : Algebra K ℂ := τ.toAlgebra
    let e : {σ : L →+* ℂ // σ.comp (algebraMap K L) = τ} ≃ (L →ₐ[K] ℂ) :=
      { toFun := fun σ => ⟨σ.1, fun a => congrFun (congrArg DFunLike.coe σ.2) a⟩
        invFun := fun φ => ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩
        left_inv := fun σ => rfl
        right_inv := fun φ => rfl }
    rw [← Fintype.card_subtype, Fintype.card_congr e, AlgHom.card]
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : L →+* ℂ => σ.comp (algebraMap K L))
    (fun σ => f (σ.comp (algebraMap K L))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2], Finset.sum_const, hfib τ,
    nsmul_eq_mul]

end Places

theorem iSup_pow {ι : Type} [Finite ι] [Nonempty ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (m : ℕ) :
    ⨆ i, a i ^ m = (⨆ i, a i) ^ m := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := a)
  refine le_antisymm (ciSup_le fun j => pow_le_pow_left₀ (ha j) (le_ciSup (Set.finite_range _).bddAbove j) m) ?_
  rw [← hi]
  exact le_ciSup (f := fun i => a i ^ m) (Set.finite_range _).bddAbove i

theorem finite_support_log_iSup {K ι : Type} [Field K] [NumberField K] [Finite ι] {z : ι → K} (hz : z ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (⨆ k, v (z k))).Finite := by
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hz
  have : Nonempty ι := ⟨k₀⟩
  refine (Set.finite_iUnion fun k : {k // z k ≠ 0} => FinitePlace.hasFiniteMulSupport k.2).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at h
  refine hv ?_
  have : ⨆ k, v (z k) = 1 := le_antisymm (ciSup_le fun k => by
      rcases eq_or_ne (z k) 0 with h0 | h0
      · rw [h0, map_zero]; exact zero_le_one
      · exact (h ⟨k, h0⟩).le)
    ((h ⟨k₀, hk₀⟩).ge.trans (le_ciSup (f := fun k => v (z k)) (Set.finite_range _).bddAbove k₀))
  simp only [this, Real.log_one]

theorem finsum_log_iSup_algebraMap {K L ι : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Finite ι] {z : ι → K} (hz : z ≠ 0) :
    ∑ᶠ w : FinitePlace L, Real.log (⨆ k, w (algebraMap K L (z k))) =
      Module.finrank K L * ∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (z k)) := by
  obtain ⟨k₀, -⟩ := Function.ne_iff.1 hz
  have : Nonempty ι := ⟨k₀⟩
  rw [← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := L)).symm,
    ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm,
    ← finsum_locDeg_mul _ ((finite_support_log_iSup hz).preimage
      (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective.injOn)]
  refine finsum_congr fun w => ?_
  rw [← Real.log_pow, ← iSup_pow _ fun _ => apply_nonneg _ _]
  exact congrArg Real.log (iSup_congr fun k => mk_algebraMap w (z k))

theorem pointHeight_algebraMap : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] (y : Fin N → K),
      y ≠ 0 → pointHeight w A (fun j => algebraMap K K' (y j)) = pointHeight w A y := by
  intro F K _ _ _ _ _ N n w A hw _ K' _ _ _ _ _ y hy
  classical
  have hz : (fun k => ∑ j, algebraMap F K (w j k) * y j) ≠ 0 := fun h => by
    have hp := finSize_pos hw (algebraMap F K) AbsoluteValue.trivial hy
    have h' : ∀ k, ∑ j, algebraMap F K (w j k) * y j = 0 := congrFun h
    simp [finSize, h'] at hp
  have h₁ := finsum_log_iSup_algebraMap (L := K') hz
  have h₂ := sum_comp_algebraMap (L := K')
    fun τ : K →+* ℂ => Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j))
  simp only [map_sum, map_mul, ← IsScalarTower.algebraMap_apply] at h₁
  simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, RingHom.comp_apply] at h₂
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hKL : (0 : ℝ) < Module.finrank K K' := by exact_mod_cast Module.finrank_pos
  rw [pointHeight_eq, pointHeight_eq, h₂, ← Module.finrank_mul_finrank ℚ K K']
  simp only [finSize, ← FinitePlace.coe_apply]
  rw [h₁]
  push_cast
  field_simp

end GlobalTheory.Adelic.HeightExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

namespace GlobalTheory.Adelic.HeightScaling

variable {F K : Type} [Field F] [Field K] [NumberField K] {N n : ℕ}

theorem finite_support_log {c : K} (hc : c ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (v c)).Finite := by
  refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport hc) fun v hv h1 => hv ?_
  simp only at h1
  simp [h1]

theorem sum_log_eq_zero {c : K} (hc : c ≠ 0) :
    (∑ᶠ v : FinitePlace K, Real.log (v c)) + ∑ τ : K →+* ℂ, Real.log ‖τ c‖ = 0 := by
  have hmul : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  have h1 : ∑ᶠ w : FinitePlace K, Real.log (w c) = Real.log (∏ᶠ w : FinitePlace K, w c) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hc).ne')]
    intro w hw
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    simp [h1]
  have h2 : ∑ φ : K →+* ℂ, Real.log ‖φ c‖ = Real.log |Algebra.norm ℚ c| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hc))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ c)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ c‖) (fun φ => ‖φ c‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv, neg_add_cancel]

theorem finite_support_log_finSize {w : Matrix (Fin N) (Fin n) F} (hw : Submodule.span F (Set.range w.col) = ⊤)
    (φ : F →+* K) {y : Fin N → K} (hy : y ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (finSize w φ v.1 y)).Finite := by
  have hfin : (⋃ k : {k : Fin n // ∑ j, φ (w j k) * y j ≠ 0},
      Function.mulSupport fun v : FinitePlace K => v (∑ j, φ (w j k.1) * y j)).Finite :=
    Set.finite_iUnion fun k => FinitePlace.hasFiniteMulSupport k.2
  refine hfin.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ k : Fin n, ∑ j, φ (w j k) * y j ≠ 0 → v.1 (∑ j, φ (w j k) * y j) = 1 := fun k hk => by
    by_contra h
    exact hn (Set.mem_iUnion.2 ⟨⟨k, hk⟩, h⟩)
  have hpos := finSize_pos hw φ v.1 hy
  have hle : finSize w φ v.1 y ≤ 1 := Real.iSup_le (fun k => by
    by_cases hk : ∑ j, φ (w j k) * y j = 0
    · rw [hk, map_zero]; exact zero_le_one
    · exact (h1 k hk).le) zero_le_one
  have hge : 1 ≤ finSize w φ v.1 y := by
    by_contra h
    refine hpos.not_ge (Real.iSup_le (fun k => ?_) le_rfl)
    by_cases hk : ∑ j, φ (w j k) * y j = 0
    · rw [hk, map_zero]
    · exact absurd ((h1 k hk).ge.trans (le_finSize w φ v.1 y k)) h
  simp only [le_antisymm hle hge, Real.log_one]

theorem pointHeight_smul : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (y : Fin N → K) (c : K), y ≠ 0 → c ≠ 0 → pointHeight w A (c • y) = pointHeight w A y := by
  intro F K _ _ _ _ _ N n w A hw hA y c hy hc
  rw [pointHeight_eq, pointHeight_eq]
  congr 1
  have e1 : ∀ v : FinitePlace K, Real.log (finSize w (algebraMap F K) v.1 (c • y)) =
      Real.log (v c) + Real.log (finSize w (algebraMap F K) v.1 y) := fun v => by
    rw [finSize_smul, Real.log_mul (v.1.ne_zero hc) (finSize_pos hw _ v.1 hy).ne']
    rfl
  have e2 : ∀ τ : K →+* ℂ, Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ ((c • y) j)) =
      Real.log ‖τ c‖ + Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j)) := fun τ => by
    have h0 : (fun j => τ (y j)) ≠ 0 := fun h => hy (funext fun j => (map_eq_zero τ).1 (congrFun h j))
    have h1 : (fun j => τ ((c • y) j)) = τ c • fun j => τ (y j) := funext fun j => by simp
    rw [h1, archSize_smul, Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero τ).2 hc)) (archSize_pos (hA _) h0).ne']
  rw [finsum_congr e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_add_distrib,
    finsum_add_distrib (finite_support_log hc) (finite_support_log_finSize hw _ hy)]
  linarith [sum_log_eq_zero hc]

end GlobalTheory.Adelic.HeightScaling
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NvEqOneOfIsCompact
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

noncomputable section

namespace GlobalTheory.LKLoc.GLOneUnit

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)

def nv : GL (Fin 1) (Kn p K r) →* ℝ where
  toFun g := ‖((((GeneralLinearGroup.det g : (Kn p K r)ˣ) : Kn p K r) : PadicAlgCl p))‖
  map_one' := by simp
  map_mul' a b := by simp [norm_mul]

theorem nv_apply (g : GL (Fin 1) (Kn p K r)) :
    nv p K r g = ‖(((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p)‖ := by
  show ‖((((GeneralLinearGroup.det g : (Kn p K r)ˣ) : Kn p K r) : PadicAlgCl p))‖ = _
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

theorem nv_pos (g : GL (Fin 1) (Kn p K r)) : 0 < nv p K r g := by
  show 0 < ‖((((GeneralLinearGroup.det g : (Kn p K r)ˣ) : Kn p K r) : PadicAlgCl p))‖
  refine norm_pos_iff.2 fun h => (GeneralLinearGroup.det g).ne_zero ?_
  exact Subtype.ext h

theorem nv_inv (g : GL (Fin 1) (Kn p K r)) : nv p K r g⁻¹ = (nv p K r g)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])

theorem comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem mem_intR {x : Kn p K r} : x ∈ intR p K r ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 :=
  mem_Obar_iff

theorem mem_Kint_of_nv (g : GL (Fin 1) (Kn p K r)) (h : nv p K r g = 1) : g ∈ Kint p K 1 r := by
  rw [nv_apply] at h
  have hinv : (((g⁻¹ : GL (Fin 1) (Kn p K r)) : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0) *
      ((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0) = 1 := by
    have := congrArg (fun M : Matrix (Fin 1) (Fin 1) (Kn p K r) => M 0 0) (Units.inv_mul g)
    simpa [Matrix.mul_apply] using this
  have hi : ‖((((g⁻¹ : GL (Fin 1) (Kn p K r)) : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) :
      PadicAlgCl p)‖ = 1 := by
    have := congrArg (fun x : Kn p K r => ‖(x : PadicAlgCl p)‖) hinv
    simpa [norm_mul, h] using this
  have h0 : (((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
  refine ⟨⟨Matrix.of fun _ _ => ⟨_, (mem_intR p K r).2 h.le⟩,
    Matrix.of fun _ _ => ⟨_, (mem_intR p K r).2 hi.le⟩, ?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i; fin_cases j
    simp [Matrix.mul_apply, h0]
  · ext i j; fin_cases i; fin_cases j
    simp [Matrix.mul_apply, h0]
  · apply GeneralLinearGroup.ext
    intro i j
    fin_cases i; fin_cases j
    rfl

theorem sig_eq_of_mem (g : GL (Fin 1) (Kn p K r))
    (hg : (((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p) ∈ K) :
    sig p K 1 r g = g := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i; fin_cases j
  apply Subtype.ext
  exact (frobK p K).commutes ⟨_, hg⟩

theorem mem_twCent_of_mem (δ g : GL (Fin 1) (Kn p K r))
    (hg : (((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p) ∈ K) :
    g ∈ GlobalTheory.BCT.twCent (sig p K 1 r) δ := by
  show g * δ = δ * sig p K 1 r g
  rw [sig_eq_of_mem p K r g hg, comm]

theorem exists_decomp (hK : FiniteDimensional ℚ_[p] K) (hr : 0 < r) (δ x : GL (Fin 1) (Kn p K r)) :
    ∃ t ∈ GlobalTheory.BCT.twCent (sig p K 1 r) δ, ∃ k ∈ Kint p K 1 r, x = t * k := by
  obtain ⟨y, hy, hxy⟩ := norm_Kn p K hK hr ((x : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0).2
  have hxy' : nv p K r x = ‖y‖ := by rw [nv_apply]; exact hxy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hxy'
    exact (nv_pos p K r x).ne' hxy'
  let u : (Kn p K r)ˣ := Units.mk0 ⟨y, le_Kn p K r hy⟩ (fun h => hy0 (congrArg Subtype.val h))
  let t : GL (Fin 1) (Kn p K r) :=
    Units.map (Matrix.scalar (Fin 1) : Kn p K r →+* Matrix (Fin 1) (Fin 1) (Kn p K r)).toMonoidHom u
  have ht00 : (((t : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p) = y := by
    simp [t, u]
  refine ⟨t, mem_twCent_of_mem p K r δ t (by rw [ht00]; exact hy), t⁻¹ * x,
    mem_Kint_of_nv p K r _ ?_, (mul_inv_cancel_left t x).symm⟩
  rw [map_mul, nv_inv, hxy', nv_apply, ht00]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hy0)

end GlobalTheory.LKLoc.GLOneUnit

namespace GlobalTheory.LKLoc.GLOneUnit

end GlobalTheory.LKLoc.GLOneUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerCoordExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perCoord : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar), ∃ d, PerCoord D ρ d := by
  first | exact @GlobalTheory.PerCoordU.perCoord_exists | exact GlobalTheory.PerCoordU.perCoord_exists | (intros; apply GlobalTheory.PerCoordU.perCoord_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeBelowComplexEmbeddingLabelIsMaximalCard
section
set_option autoImplicit false

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PrimePart

theorem ker_isMaximal_card {E k : Type} [Field E] [NumberField E] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : 𝓞 E →+* k) :
    (RingHom.ker f).IsMaximal ∧ ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ RingHom.ker f) = p ^ h := by
  have hp : p.Prime := Fact.out
  have hmem : ((p : ℕ) : 𝓞 E) ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero k p
  have hne : RingHom.ker f ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hp.ne_zero (Nat.cast_eq_zero.1 hmem)
  have hmax : (RingHom.ker f).IsMaximal := (RingHom.ker_isPrime f).isMaximal hne
  refine ⟨hmax, ?_⟩
  haveI : Finite (𝓞 E ⧸ RingHom.ker f) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  letI : Fintype (𝓞 E ⧸ RingHom.ker f) := Fintype.ofFinite _
  letI : Field (𝓞 E ⧸ RingHom.ker f) := Ideal.Quotient.field _
  haveI : CharP (𝓞 E ⧸ RingHom.ker f) p := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (Ideal.Quotient.mk (RingHom.ker f)), Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ RingHom.ker f) p
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem primeBelow_isMaximal_card (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (τ : E →+* ℂ) :
    (primeBelow io X τ).IsMaximal ∧ ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h := by
  haveI := charP_residueField_of_irreducible X
  rw [primeBelow_eq_ker]
  exact ker_isMaximal_card p (red io X τ)

end GlobalTheory.PrimePart
end

