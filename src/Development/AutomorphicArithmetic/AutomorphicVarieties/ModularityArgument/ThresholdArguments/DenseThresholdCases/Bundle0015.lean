import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0041
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgRes
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base
section
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
private theorem val_of_norm
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [h2, toAdd_pow, nsmul_eq_mul]
variable [Algebra K L]
private theorem normV_under (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem tendsto_under' :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl
omit [Algebra K L] in
private theorem ev_notMem (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)
variable (L) in
private noncomputable def cN (χ : HChar K) : HChar L :=
  ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩
private theorem cN_loc (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (x : (w.adicCompletion L)ˣ) : ∃ y : ((w.under (𝓞 K)).adicCompletion K)ˣ,
      (cN L χ).loc w x = χ.loc (w.under (𝓞 K)) y ∧
      Valued.v (y : (w.under (𝓞 K)).adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, congrArg χ.1 h, val_of_norm _ w _ x hm' f hf⟩
private theorem cN_val (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (hχ : χ.UnrAt (w.under (𝓞 K))) : (cN L χ).UnrAt w ∧ (cN L χ).val w = χ.val (w.under (𝓞 K)) ^ f := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, hv⟩ := cN_loc χ w f hf x
    rw [hy]
    apply hχ
    unfold IsUnitAt at *
    rw [hv, hx, one_pow]
  · obtain ⟨y, hy, hv⟩ := cN_loc χ w f hf (atFin w (unif w))
    have h1 := unif_spec w
    have h2 := unif_spec (w.under (𝓞 K))
    have hu : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]
      exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
    have h3 := hχ _ hu
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    exact hy.trans h3
private theorem norm_infDiag (k : Lˣ) :
    GroundTheory.Global.ideleNorm K L (infDiag k) = infDiag (Units.map (Algebra.norm K : L →* K) k) := by
  refine Units.ext (Prod.ext (funext fun v => ?_) (Subtype.ext (funext fun v => ?_)))
  · have h1 := GroundTheory.Global.ideleNorm_fst (K := K) (infDiag k) v
    have h2 := GroundTheory.Global.ideleNorm_fst (K := K) (GroundTheory.Global.IdeleGroup.diagonal L k) v
    rw [GroundTheory.Global.ideleNorm_diagonal] at h2
    rw [GlobalTheory.HeckeGal.infDiag_eq] at h1 ⊢
    rw [GlobalTheory.HeckeGal.infDiag_eq]
    exact h1.trans h2.symm
  · have h1 := GroundTheory.Global.ideleNorm_snd (K := K) (infDiag k) v
    rw [GlobalTheory.HeckeGal.infDiag_eq] at h1 ⊢
    rw [GlobalTheory.HeckeGal.infDiag_eq]
    refine h1.trans (Finset.prod_eq_one fun w _ => ?_)
    exact map_one _
open Classical in
private theorem emb_norm (φ : K →+* ℂ) (x : L) :
    φ (Algebra.norm K x) = ∏ ψ ∈ Finset.univ.filter fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = φ, ψ x := by
  letI := φ.toAlgebra
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have h := Algebra.norm_eq_prod_embeddings K ℂ x
  refine h.trans ?_
  refine Finset.prod_bij (fun σ _ => (σ : L →+* ℂ)) (fun σ _ => ?_) (fun a _ b _ e => AlgHom.coe_ringHom_injective e)
    (fun ψ hψ => ⟨⟨ψ, fun r => DFunLike.congr_fun (Finset.mem_filter.1 hψ).2 r⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, RingHom.ext σ.commutes⟩
private theorem norm_pos (k : Lˣ) (hk : ∀ φ : L →+* ℝ, 0 < φ (k : L)) (φ : K →+* ℝ) : 0 < φ (Algebra.norm K (k : L)) := by
  classical
  have h := emb_norm (Complex.ofRealHom.comp φ) (k : L)
  have h0 : ∀ ψ : L →+* ℂ, ψ (k : L) ≠ 0 := fun ψ => (map_ne_zero ψ).2 k.ne_zero
  have h1 : ∏ ψ ∈ Finset.univ.filter fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = Complex.ofRealHom.comp φ,
      (ψ (k : L) / ((‖ψ (k : L)‖ : ℝ) : ℂ)) = 1 := by
    refine Finset.prod_involution (fun ψ _ => ComplexEmbedding.conjugate ψ) (fun ψ _ => ?_) (fun ψ _ hne e => hne ?_)
      (fun ψ hψ => ?_) fun ψ _ => star_star ψ
    · have : ((‖ψ (k : L)‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0 ψ
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, div_eq_one_iff_eq (mul_ne_zero this this)]
      push_cast; ring
    · have hr : ComplexEmbedding.IsReal ψ := ComplexEmbedding.isReal_iff.2 e
      have := hk hr.embedding
      rw [← ComplexEmbedding.IsReal.coe_embedding_apply hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos this]
      exact div_self (Complex.ofReal_ne_zero.2 this.ne')
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, RingHom.ext fun r => ?_⟩
      have e : ψ (algebraMap K L r) = ((φ r : ℝ) : ℂ) := DFunLike.congr_fun (Finset.mem_filter.1 hψ).2 r
      show ComplexEmbedding.conjugate ψ (algebraMap K L r) = ((φ r : ℝ) : ℂ)
      rw [ComplexEmbedding.conjugate_coe_eq, e, Complex.conj_ofReal]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun ψ _ => by simpa using h0 ψ),
    ← Complex.ofReal_prod] at h1
  have h2 : ((φ (Algebra.norm K (k : L)) : ℝ) : ℂ) = _ := h.trans h1
  rw [Complex.ofReal_inj.1 h2]
  exact Finset.prod_pos fun ψ _ => norm_pos_iff.2 (h0 ψ)
private theorem cN_alg {χ : HChar K} {a : (K →+* ℂ) → ℤ} (h : IsAlgPos χ a) :
    IsAlgPos (cN L χ) fun ψ => a (ψ.comp (algebraMap K L)) := by
  classical
  intro k hk
  have e : (cN L χ).inf k = χ.inf (Units.map (Algebra.norm K : L →* K) k) := congrArg χ.1 (norm_infDiag k)
  rw [e, h _ (norm_pos k hk), ← Finset.prod_fiberwise (s := Finset.univ) (g := fun ψ : L →+* ℂ => ψ.comp (algebraMap K L))]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [Units.coe_map, emb_norm, ← Finset.prod_zpow]
  exact Finset.prod_congr (by convert rfl) fun ψ hψ => by simp only [(Finset.mem_filter.1 hψ).2]
end
theorem UpperTheory.V.Sd.alg_restriction_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.AlgRes := by
  intro P F E Ω _ _ _ _ _ _ _ _ _ _ l _ ι κ ⟨hc, art, χ, a, ha, h1, h⟩
  obtain ⟨art', ha'⟩ := P.litN.aut.art E Ω
  have h1' := cN_alg (L := E) h1
  obtain ⟨μ, hμ, hL⟩ := ha'.exists_isLAdicOf ι h1'
  have hc' : Continuous (κ.comp (galEmb F E Ω)) := hc.comp (continuous_restrictScalarsHom F E Ω)
  have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ (cN E χ).UnrAt w ∧
      CharEig ι (κ.comp (res F Ω E)) w ((cN E χ).val w : ℂˣ) := by
    filter_upwards [(tendsto_under' (K := F) (L := E)).eventually
      ((Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)).and (ev_notMem l)), ev_notMem (K := E) l]
      with w ⟨hu, hl⟩ hl'
    have hf := normV_under (K := F) w
    obtain ⟨k1, k2⟩ := cN_val χ w _ hf hu
    refine ⟨hl', k1, ?_⟩
    rw [k2, Units.val_pow_eq_pow_val]
    refine (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ hf).2 κ _ fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw) (f := fun s => κ.comp (galEmb F E Ω) s) (f' := fun s => μ s)
    hc' hμ fun v hv _ A hA σ hσ => by
      obtain ⟨hl, hu, hE⟩ := not_not.1 hv
      have e := (hE A hA).2 σ hσ
      refine Units.ext ?_
      rw [hL.frob_unr ha' (Or.inl hl) hu hA hσ, ← e, ι.symm_apply_apply, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      rfl
  have e : κ.comp (galEmb F E Ω) = μ := MonoidHom.ext fun s => congrFun key s
  rw [e]
  exact ⟨hμ, art', _, _, ha', h1', hL⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TInVec
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
private theorem thinOut {α β : Type} [DecidableEq α] (f : α → β) (S T : Finset α) (hinj : Set.InjOn f (S : Set α)) :
    ∃ T' : Finset α, S ⊆ T' ∧ Set.InjOn f (T' : Set α) ∧ (∀ t ∈ T', t ∉ S → ∀ s ∈ S, f s ≠ f t) ∧
      ∀ t ∈ T, ∃ t' ∈ T', f t' = f t := by
  induction T using Finset.induction_on with
  | empty => exact ⟨S, subset_rfl, hinj, fun t h h' => absurd h h', by simp⟩
  | insert a T₀ _ ih =>
    obtain ⟨T', h1, h2, h3, h4⟩ := ih
    by_cases h : ∃ t' ∈ T', f t' = f a
    · refine ⟨T', h1, h2, h3, fun t ht => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact h
      · exact h4 t ht
    · push_neg at h
      refine ⟨insert a T', h1.trans (Finset.subset_insert _ _), ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with h₁ | h₁ <;>
          rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with h₂ | h₂
        · rw [h₁, h₂]
        · subst h₁
          exact absurd hxy.symm (h y h₂)
        · subst h₂
          exact absurd hxy (h x h₁)
        · exact h2 h₁ h₂ hxy
      · intro t ht htS s hs
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact h s (h1 hs)
        · exact h3 t ht htS s hs
      · intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact ⟨_, Finset.mem_insert_self _ _, rfl⟩
        · obtain ⟨t', a', b⟩ := h4 t ht
          exact ⟨t', Finset.mem_insert_of_mem a', b⟩
section
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
private theorem away_congr {n : ℕ} {w w' : Plc L} (h : w.under (𝓞 (Lp L)) = w'.under (𝓞 (Lp L))) :
    away n w = away n w' := by
  simp only [away, h]
private theorem cLoc_away {n : ℕ} {w : Plc L} {y : UA L n} (hy : y ∈ away n w) : cLoc w y = 1 :=
  Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy w) rfl
private noncomputable def AT (S : Finset (Plc L)) (W : ∀ w : Plc L, Sig.Lev (Kw w)) (T : Finset (Plc L)) : Subgroup (UA L 2) :=
  lev (Kall L 2) S W ⊓ ⨅ w ∈ T, away 2 w
private theorem step [DecidableEq (Plc L)] {V : Type} [AddCommGroup V] [Module ℂ V] (S T₀ : Finset (Plc L))
    (W : ∀ w : Plc L, Sig.Lev (Kw w)) (w : Plc L)
    (hS : ∀ v ∈ S, v ≠ w → v.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)))
    (hT : ∀ t ∈ T₀, t.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)))
    (R : Representation ℂ (InfinitePlace L → GL (Fin 2) ℂ) V) (φ φ' : UA L 2 → V)
    (hspan : InSpan w φ φ') (hAF : IsAF R (AT S W (insert w T₀)) φ)
    (hinv : ∀ x ∈ locU 2 w, x ∈ Kall L 2 → (w ∈ S → cLoc w x ∈ (W w).J 2) → ∀ g, φ' (g * x) = φ' g) :
    IsAF R (AT S W T₀) φ' := by
  have h1 : AT S W (insert w T₀) ≤ away 2 w :=
    inf_le_right.trans (iInf₂_le w (Finset.mem_insert_self _ _))
  have h2 := (spanKeep L 2 V w φ φ' hspan).2.1 R _ h1 hAF
  refine ⟨h2.left, h2.inf, ?_⟩
  intro u hu g
  obtain ⟨x, hx, y, hy, rfl⟩ := (factor L 2 w).2.1 u
  obtain ⟨hlev, hTa⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hK, hJ⟩ := Subgroup.mem_inf.1 hlev
  have hxy := ((factor L 2 w).2.2.2.2.2 x hx y hy).1 hK
  have hJ' : ∀ v ∈ S, cLoc v (x * y) ∈ (W v).J 2 := fun v hv =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hJ v) hv
  have hyw : cLoc w y = 1 := cLoc_away hy
  have hyA : y ∈ AT S W (insert w T₀) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxy.2, ?_⟩, ?_⟩
    · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
      show cLoc v y ∈ (W v).J 2
      by_cases hvw : v = w
      · subst hvw
        rw [hyw]
        exact one_mem _
      · have hxv : cLoc v x = 1 :=
          cLoc_away ((factor L 2 v).2.2.1 w (hS v hv hvw).symm hx)
        have := hJ' v hv
        rwa [map_mul, hxv, one_mul] at this
    · refine Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht => ?_
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hy
      · have hxt : x ∈ away 2 t := (factor L 2 t).2.2.1 w (hT t ht).symm hx
        have hxyt : x * y ∈ away 2 t := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hTa t) ht
        exact (Subgroup.mul_mem_cancel_left _ hxt).1 hxyt
  rw [← mul_assoc, h2.level y hyA, hinv x hx hxy.1 ?_]
  intro hwS
  have := hJ' w hwS
  rwa [map_mul, hyw, mul_one] at this
end
theorem UpperTheory.V.Z.Sym.Al.inVec_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (π : Submodule ℂ (UA L 2 → ℂ)), IsAutRepU π → ∀ j : ℕ,
        (∀ v : InfinitePlace L, ∃ lam, HasWeightAt π v.embedding lam ∧ lam.w 0 - lam.w 1 = j) →
        ∀ S : Finset (Plc L), Places (S : Set (Plc L)) →
        (∀ w : Plc L, (∀ w' ∈ S, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) → IsUnramU π w) →
        ∀ (W : ∀ w : Plc L, Sig.Lev (Kw w)) (ψ : ∀ w : Plc L, Fin 2 → (Kw w)ˣ →* ℂˣ),
        (∀ w ∈ S, CompEq π w (ψ w) ∧ ∀ i, ∀ u ∈ (W w).H, ψ w i u = 1) →
        ∃ (e : InfinitePlace L → ℤ) (φ : UA L 2 → Wt.VD (InfinitePlace L) j), φ ≠ 0 ∧ IsAF (repE j e) (lev (Kall L 2) S W) φ ∧
          ∀ w ∈ S, EigT φ w (W w) (ψ w) := by
  intro hN L _ _ _ π hπ j hwt S hS hun W ψ hψ
  classical
  haveI : FiniteDimensional ℂ (Wt.VD (InfinitePlace L) j) := Wt.finMH (InfinitePlace L) 2 _
  obtain ⟨e, φ₀, hne, hco, hAF⟩ := infVec L π hπ j hwt
  obtain ⟨U, hUo, hUi⟩ := openLev L 2 _ π hπ φ₀ hco
  obtain ⟨T, hT⟩ := (cof L 2).1 U hUo
  obtain ⟨T', hST, hthin, hsep, hcov⟩ := thinOut (fun w : Plc L => w.under (𝓞 (Lp L))) S T hS.inj
  have key : ∀ D : Finset (Plc L), D ⊆ T' →
      ∃ φ : UA L 2 → Wt.VD (InfinitePlace L) j, φ ≠ 0 ∧ CoefIn φ π ∧ IsAF (repE j e) (AT S W (T' \ D)) φ ∧
        ∀ w ∈ S, w ∉ T' \ D → EigT φ w (W w) (ψ w) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨φ₀, hne, hco, ⟨hAF.left, hAF.inf, fun u hu g => hUi u ?_ g⟩, fun w hw hw' => ?_⟩
      · obtain ⟨hlev, hTa⟩ := Subgroup.mem_inf.1 hu
        refine hT (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hlev).1, ?_⟩)
        refine Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht => ?_
        obtain ⟨t', ht', hf⟩ := hcov t ht
        rw [← away_congr hf]
        exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hTa t') (by simpa using ht')
      · exact absurd (by simpa using hST hw) hw'
    | insert w D₀ hwD ih =>
      intro hsub
      have hwT : w ∈ T' := hsub (Finset.mem_insert_self _ _)
      obtain ⟨φ, hφ, hc, hA, hE⟩ := ih ((Finset.subset_insert _ _).trans hsub)
      have hins : T' \ D₀ = insert w (T' \ insert w D₀) := by
        ext t
        by_cases h : t = w
        · subst h; simp [hwT, hwD]
        · simp [h]
      have hTs : ∀ t ∈ T' \ insert w D₀, t.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) := by
        intro t ht hf
        have ht' := Finset.mem_sdiff.1 ht
        exact ht'.2 (by rw [hthin (Finset.mem_coe.2 ht'.1) (Finset.mem_coe.2 hwT) hf]; exact Finset.mem_insert_self _ _)
      rw [hins] at hA
      have hE' : ∀ v ∈ S, v ≠ w → v ∉ T' \ insert w D₀ → EigT φ v (W v) (ψ v) := by
        intro v hv hvw hvT
        refine hE v hv ?_
        rw [hins]
        simp [hvw, hvT]
      by_cases hwS : w ∈ S
      · have hSs : ∀ v ∈ S, v ≠ w → v.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) :=
          fun v hv hvw hf => hvw (hS.inj (Finset.mem_coe.2 hv) (Finset.mem_coe.2 hwS) hf)
        obtain ⟨φ', hφ', hspan, hinv, hEig⟩ :=
          _root_.UpperTheory.V.Z.Sym.Al.exists_eigenvector_in_span_of_comp_eq_trivial hN L 2 _ π hπ w (hS.split w hwS) (W w) (ψ w) (hψ w hwS).1 (hψ w hwS).2 φ hφ hc
        have hk := spanKeep L 2 _ w φ φ' hspan
        refine ⟨φ', hφ', hk.1 π hπ hc, step S _ W w hSs hTs _ φ φ' hspan hA
          (fun x hx _ hJ g => hinv x hx (hJ hwS) g), fun v hv hvT => ?_⟩
        by_cases hvw : v = w
        · subst hvw; exact hEig
        · exact fun d hd => hk.2.2 v (hS.split v hv) (hSs v hv hvw) _ d _ (hE' v hv hvw hvT d hd)
      · have hSs : ∀ v ∈ S, v ≠ w → v.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) :=
          fun v hv _ => hsep w hwT hwS v hv
        obtain ⟨φ', hφ', hspan, hinv⟩ :=
          spanSph L 2 _ π hπ w (hun w (hsep w hwT hwS)) φ hφ hc
        have hk := spanKeep L 2 _ w φ φ' hspan
        refine ⟨φ', hφ', hk.1 π hπ hc, step S _ W w hSs hTs _ φ φ' hspan hA
          (fun x hx hK _ g => hinv x ⟨hx, hK⟩ g), fun v hv hvT => ?_⟩
        have hvw : v ≠ w := fun h => hwS (h ▸ hv)
        exact fun d hd => hk.2.2 v (hS.split v hv) (hSs v hv hvw) _ d _ (hE' v hv hvw hvT d hd)
  obtain ⟨φ, hφ, -, hA, hE⟩ := key T' subset_rfl
  refine ⟨e, φ, hφ, ⟨hA.left, hA.inf, fun u hu g => hA.level u ?_ g⟩, fun w hw => hE w hw (by simp)⟩
  exact Subgroup.mem_inf.2 ⟨hu, by simp⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TIsoOfFrob
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
theorem UpperTheory.V.Af.iso_of_frobenius_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.IsoOfFrob := by
  intro _ F Ω _ _ _ _ _ l _ ι n r r' hr hr' hs hs' hw
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix
section
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
private theorem iso_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    T x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap T _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply, f.2, hT]⟩ ⟨v, rfl⟩
private theorem iso_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    ρ g x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap (ρ g) _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, f.2 g v⟩
end
theorem UpperTheory.V.Af.local_comp_complex_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.LocCompC := by
  intro P E _ _ _ a π w
  refine ⟨(LocEx.exists_isLocComp P.litN.aut.fin E a π w).imp fun _ h => h.1, fun σ hσ => ?_⟩
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  obtain ⟨f, h0, hf⟩ := hσ
  change ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 = ⊤
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ (o : Op E a) (x : π.V),
      x ∈ (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1) →
      π.op o x ∈ ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 := by
    intro o x hx
    cases o with
    | fin k =>
      have h1 := iso_act σ.ρ (π.locRep w) (GeneralLinearGroup.map (pLoc E w) k) (iso_comm σ.ρ (π.locRep w)
        (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
        simp only [CuspSub.locRep, MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) hx)
      have e : π.locRep w (GeneralLinearGroup.map (pLoc E w) k)
          (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) x) = π.op (.fin k) x := by
        rw [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        rfl
      rwa [e] at h1
    | cpt k =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
        (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1
  rcases π.irred (Submodule.map π.V.subtype _) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h1 | h1
  · have h2 := hi (h1.trans (Submodule.map_bot _).symm)
    exact absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 (h2 ▸ le_iSup
      (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩))) h0
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPsFull
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Desc.W.principal_series_full_statement : _root_.UpperTheory.V.Z.Desc.W.PsFullAlt := by
  intro P L Ω _ _ _ _ _ l _ ι n w A h a ha τ ω hh ψ ph hs hω hp hinj
  have hv := fun i => ((Loc.ordCharIff P.aut.art h ι a ha (hh i) (ψ i)).2 (ω i) (hω i) (ph i)).1 (hp i)
  have key : ∀ i j, (∀ σ : Ine (F := L) A, ω i (a (ineIncl h σ)) = ω j (a (ineIncl h σ))) → i = j := fun i j e =>
    hinj (MonoidHom.ext fun σ => Units.ext (ι.injective (by rw [hv, hv, e])))
  refine (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient P _ n ω (fun i => (hω i).smooth) fun i j hij => ⟨fun e => hij (key i j fun σ => by rw [e]),
    fun e => hij (key i j fun σ => ?_)⟩).2 _ τ.ρ τ.irred hs
  have h1 := DFunLike.congr_fun (ha.absPow_comp 1) (ineIncl h σ)
  rw [Complex.ofReal_one, MonoidHom.comp_apply, GlobalTheory.WeilDeligne.unrChar_apply, deg_ineIncl] at h1
  rw [e, MonoidHom.mul_apply, h1]
  simp
end
end

