import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0850
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0144
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0067
import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.MkTauEmbInjective
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRanksDegreesAddWithMasses
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompAdds

theorem totallyComplex {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} (c : Coeff l) :
    IsTotallyComplex c.F := by
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  intro h
  exact GlobalTheory.CompHt.conj_comp_ne v.embedding (RingHom.ext fun a => by
    simpa [ComplexEmbedding.conjugate_coe_eq] using
      congrArg (fun f : c.F →+* ℂ => f a) (ComplexEmbedding.isReal_iff.1 h))

theorem pos_of_hasGram {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
    {N : (K →+* ℂ) → W → ℝ} (h : HasGram N) (hn : ∀ σ x, 0 ≤ N σ x)
    (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) {x : W} (hx : x ≠ 0) (σ : K →+* ℂ) : 0 < N σ x := by
  have e : N σ x = N (InfinitePlace.mk σ).embedding x := by
    rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · rw [h1]
    · have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun a => ComplexEmbedding.conjugate_coe_eq σ a
      rw [h1, this, hc]
  rw [e]
  exact lt_of_le_of_ne (hn _ _) fun h0 => hx (GlobalTheory.HSApp.HasGram_eq_zero h _ h0.symm)

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
  (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

section Basic

variable (Z : Comp Xo c) (G : WTZ D.host.E)

theorem normRes_nonneg (σ : c.F →+* ℂ) (f : cuspOn U Z G) : 0 ≤ normRes U V dict Z G σ f :=
  petAt_nonneg _ _ _ _ _ _ _

theorem normOn_nonneg (σ : c.F →+* ℂ) (f : cuspOn U Z G) : 0 ≤ normOn U (xiR D) V dict Z G σ f :=
  petAt_nonneg _ _ _ _ _ _ _

theorem normRes_conj (σ : c.F →+* ℂ) (f : cuspOn U Z G) :
    normRes U V dict Z G ((starRingEnd ℂ).comp σ) f = normRes U V dict Z G σ f :=
  congrArg (fun s => petAt (U s) (xiR D) (V s) (dict s) (muQ1 (V s)) G (f : Rul Xo c)) (GlobalTheory.CompHt.goodOf_conj σ)

theorem mass_conj (σ : c.F →+* ℂ) : mass U V dict Z ((starRingEnd ℂ).comp σ) = mass U V dict Z σ :=
  congrArg (fun s => (muQ1 (V s) (classesOver (V s) (dict s) (framesOn (U s) Z))).toReal) (GlobalTheory.CompHt.goodOf_conj σ)

theorem mass_nonneg (σ : c.F →+* ℂ) : 0 ≤ mass U V dict Z σ := ENNReal.toReal_nonneg

theorem normRes_zero (σ : c.F →+* ℂ) : normRes U V dict Z G σ 0 = 0 := by
  have a := petW_smul U (xiR D) V dict G σ 0 0
  simp only [zero_smul, map_zero, norm_zero, zero_mul] at a
  exact a

theorem normOn_zero (σ : c.F →+* ℂ) : normOn U (xiR D) V dict Z G σ 0 = 0 := by
  have a := petOn_smul U (xiR D) V dict Z G σ 0 0
  simp only [zero_smul, map_zero, norm_zero, zero_mul] at a
  exact a

theorem exists_normOn_eq (σ : c.F →+* ℂ) : ∃ k : ℝ, 0 ≤ k ∧
    ∀ f : cuspOn U Z G, normOn U (xiR D) V dict Z G σ f = k * normRes U V dict Z G σ f :=
  ⟨_, ENNReal.toReal_nonneg, fun f => GlobalTheory.HSApp.petAt_muOn (U (goodOf c σ)) (xiR D) (V (goodOf c σ))
    (dict (goodOf c σ)) Z G (Submodule.mem_inf.1 f.2).2⟩

theorem hasGram_normRes (h : HasGram (normOn U (xiR D) V dict Z G)) : HasGram (normRes U V dict Z G) := by
  by_cases h0 : ∃ f : cuspOn U Z G, f ≠ 0
  · obtain ⟨f, hf⟩ := h0
    choose k hk0 hk using fun σ => exists_normOn_eq U V dict Z G σ
    have hkpos : ∀ v : InfinitePlace c.F, 0 < k v.embedding := fun v => by
      refine lt_of_le_of_ne (hk0 _) fun h2 => hf (GlobalTheory.HSApp.HasGram_eq_zero h v ?_)
      rw [hk, ← h2, zero_mul]
    refine GlobalTheory.HSApp.hasGram_of_injective h LinearMap.id (fun _ _ h => h) (fun v => (k v.embedding)⁻¹)
      (fun v => inv_pos.2 (hkpos v)) fun v x => ?_
    rw [LinearMap.id_apply, hk, ← mul_assoc, inv_mul_cancel₀ (hkpos v).ne', one_mul]
  · push_neg at h0
    refine GlobalTheory.HSApp.hasGram_of_injective h LinearMap.id (fun _ _ h => h) (fun _ => 1) (fun _ => one_pos)
      fun v x => ?_
    rw [h0 x, LinearMap.id_apply, one_mul, normRes_zero, normOn_zero]

def sub : Submodule c.F (cuspW Xo c U G) := (cuspOn U Z G).comap (cuspW Xo c U G).subtype

def toOn : sub U Z G →ₗ[c.F] cuspOn U Z G :=
  LinearMap.codRestrict (cuspOn U Z G) ((cuspW Xo c U G).subtype ∘ₗ (sub U Z G).subtype) fun x => x.2

theorem toOn_injective : Function.Injective (toOn U Z G) := fun a b h =>
  Subtype.ext (Subtype.ext (congrArg (fun y : cuspOn U Z G => (y : Rul Xo c)) h))

theorem hasGram_sub (h : HasGram (normRes U V dict Z G)) :
    HasGram (fun σ (x : sub U Z G) => normW U (xiR D) V dict G σ x) :=
  GlobalTheory.HSApp.hasGram_of_injective h (toOn U Z G) (toOn_injective U Z G) (fun _ => 1) (fun _ => one_pos)
    fun _ _ => (one_mul _).symm

theorem span_partLat_le : Submodule.span c.F (partLat U Z G : Set (cuspW Xo c U G)) ≤ sub U Z G :=
  Submodule.span_le.2 (by rintro _ ⟨g, _, rfl⟩; exact g.2)

end Basic

variable {U V dict} {G : WTZ D.host.E}

theorem sub_indep (hS : Splits U G) : iSupIndep (fun Z => sub U Z G) := by
  intro Z
  refine Disjoint.mono_right (iSup₂_le fun j hj =>
    Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ Z) => cuspOn U j G) j hj)) ?_
  rw [disjoint_iff]
  show Submodule.comap (cuspW Xo c U G).subtype (cuspOn U Z G) ⊓
    Submodule.comap (cuspW Xo c U G).subtype (⨆ j, ⨆ (_ : j ≠ Z), cuspOn U j G) = ⊥
  rw [← Submodule.comap_inf, disjoint_iff.1 (hS.2.1.1 Z), Submodule.comap_bot, Submodule.ker_subtype]

theorem sub_iSup (hS : Splits U G) : ⨆ Z, sub U Z G = ⊤ := by
  apply Submodule.map_injective_of_injective (cuspW Xo c U G).injective_subtype
  rw [Submodule.map_iSup, Submodule.map_subtype_top]
  simp only [sub, Submodule.map_comap_subtype]
  rw [iSup_congr fun Z => inf_eq_right.2 (cuspOn_le U Z G)]
  exact hS.2.1.2

theorem pyth [Fintype (Comp Xo c)] (hO : Orthogonal U V dict G) (σ : c.F →+* ℂ) (f : ∀ Z, sub U Z G) :
    normW U (xiR D) V dict G σ (∑ Z, (f Z : cuspW Xo c U G)) ^ 2 =
      ∑ Z, normW U (xiR D) V dict G σ (f Z) ^ 2 := by
  have h := (hO σ).1 (fun Z => toOn U Z G (f Z))
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at h
  unfold normW
  rw [Submodule.coe_sum]
  exact h

theorem goodW_of (hS : Splits U G) (hO : Orthogonal U V dict G) (h : ∀ Z, GoodOn U (xiR D) V dict Z G) :
    GoodW U (xiR D) V dict G := by
  classical
  haveI : Finite (Comp Xo c) := CompFin.finite_comp Xo c
  letI := Fintype.ofFinite (Comp Xo c)
  refine ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.OrthSumGram.orth_sum_hasGram c.F (cuspW Xo c U G) (Comp Xo c) (normW U (xiR D) V dict G)
      (fun Z => sub U Z G) (fun σ x => petAt_nonneg _ _ _ _ _ _ _) (sub_indep hS) (sub_iSup hS)
      (fun Z => hasGram_sub U V dict Z G (hasGram_normRes U V dict Z G (h Z).1)) (pyth hO)
  · rw [← hS.2.2.2]
    exact Submodule.fg_iSup _ fun Z => (h Z).2.1.map _
  · rw [eq_top_iff, ← sub_iSup hS]
    refine iSup_le fun Z y hy => ?_
    have h1 : toOn U Z G ⟨y, hy⟩ ∈ Submodule.span c.F (latOn U Z G : Set (cuspOn U Z G)) :=
      by rw [(h Z).2.2]; exact Submodule.mem_top
    have h3 : Submodule.span c.F (latOn U Z G : Set (cuspOn U Z G)) ≤
        (Submodule.span c.F (latW U G : Set (cuspW Xo c U G))).comap (Submodule.inclusion (cuspOn_le U Z G)) :=
      Submodule.span_le.2 fun g hg => Submodule.subset_span ((mem_latOn U).1 hg)
    exact h3 h1

theorem normOn_eq_of_mass (hO : Orthogonal U V dict G) (Z : Comp Xo c) (σ : c.F →+* ℂ)
    (hm : 0 < mass U V dict Z σ) (f : cuspOn U Z G) :
    normOn U (xiR D) V dict Z G σ f = (Real.sqrt (mass U V dict Z σ))⁻¹ * normRes U V dict Z G σ f := by
  have h1 := (hO σ).2 Z f
  have hs := Real.sqrt_pos.2 hm
  have h2 : normRes U V dict Z G σ f = Real.sqrt (mass U V dict Z σ) * normOn U (xiR D) V dict Z G σ f := by
    rw [← sq_eq_sq₀ (normRes_nonneg U V dict Z G σ f) (mul_nonneg hs.le (normOn_nonneg U V dict Z G σ f)),
      mul_pow, Real.sq_sqrt hm.le]
    exact h1
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

theorem mass_pos (hO : Orthogonal U V dict G) (Z : Comp Xo c) (hR : HasGram (normRes U V dict Z G))
    (hr : rankOn U Z G ≠ 0) (σ : c.F →+* ℂ) : 0 < mass U V dict Z σ := by
  have hne : latOn U Z G ≠ ⊥ := fun h0 => hr (by
    rw [show rankOn U Z G = Module.finrank c.F (Submodule.span c.F ((latOn U Z G : Submodule _ _) : Set (cuspOn U Z G)))
      from rfl, h0, Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot])
  obtain ⟨f, -, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hp := pos_of_hasGram hR (normRes_nonneg U V dict Z G) (normRes_conj U V dict Z G) hf σ
  have h1 := (hO σ).2 Z f
  refine lt_of_le_of_ne (mass_nonneg U V dict Z σ) fun h0 => ?_
  rw [← h0, zero_mul] at h1
  exact hp.ne' ((pow_eq_zero_iff two_ne_zero).1 h1)

theorem degRes_zero (Z : Comp Xo c) (hr : rankOn U Z G = 0) : degRes U V dict Z G = 0 := by
  unfold degRes GlobalTheory.AllWt.deg
  unfold rankOn at hr
  rw [hr, Nat.cast_zero, zero_mul]

theorem degOn_zero (Z : Comp Xo c) (hr : rankOn U Z G = 0) : degOn U (xiR D) V dict Z G = 0 := by
  unfold degOn GlobalTheory.AllWt.deg
  unfold rankOn at hr
  rw [hr, Nat.cast_zero, zero_mul]

theorem degRes_eq [IsTotallyComplex c.F] (hO : Orthogonal U V dict G) (Z : Comp Xo c)
    (hR : HasGram (normRes U V dict Z G)) (hfg : (latOn U Z G).FG) :
    degRes U V dict Z G = degOn U (xiR D) V dict Z G - (rankOn U Z G : ℝ) / 2 *
      ((∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) / (Module.finrank ℚ c.F : ℝ)) := by
  by_cases hr : rankOn U Z G = 0
  · rw [degRes_zero Z hr, degOn_zero Z hr, hr]; simp
  · have hm := mass_pos hO Z hR hr
    have hsc := (GlobalTheory.NormScale.deg_scale c.F (cuspOn U Z G) (normRes U V dict Z G)
      (normOn U (xiR D) V dict Z G) (fun σ => (Real.sqrt (mass U V dict Z σ))⁻¹) hR
      (fun σ => inv_pos.2 (Real.sqrt_pos.2 (hm σ)))
      (fun σ => congrArg (fun m => (Real.sqrt m)⁻¹) (mass_conj U V dict Z σ))
      (fun σ f => normOn_eq_of_mass hO Z σ (hm σ) f)).2 (latOn U Z G) hfg
    have hl : ∀ σ, Real.log (Real.sqrt (mass U V dict Z σ))⁻¹ = -(Real.log (mass U V dict Z σ) / 2) :=
      fun σ => by rw [Real.log_inv, Real.log_sqrt (mass_nonneg U V dict Z σ)]
    simp only [hl, Finset.sum_neg_distrib, ← Finset.sum_div] at hsc
    unfold degRes degOn rankOn
    rw [hsc]
    ring

theorem sums [IsTotallyComplex c.F] (hS : Splits U G) (hO : Orthogonal U V dict G) (hW : GoodW U (xiR D) V dict G)
    (hOn : ∀ Z, GoodOn U (xiR D) V dict Z G) :
    rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧ degW U (xiR D) V dict G = ∑ᶠ Z : Comp Xo c, degRes U V dict Z G := by
  haveI : Finite (Comp Xo c) := CompFin.finite_comp Xo c
  letI := Fintype.ofFinite (Comp Xo c)
  have hrd := fun Z => (GlobalTheory.RestrictNorm.restrict_deg c.F (cuspW Xo c U G) (cuspOn U Z G)
    (normW U (xiR D) V dict G) (Submodule.inclusion (cuspOn_le U Z G)) (Submodule.inclusion_injective _)
    hW.1).2 (latOn U Z G) (hOn Z).2.1
  obtain ⟨hs1, hs2⟩ := GlobalTheory.OrthRankDeg.rkK_deg_iSup c.F (cuspW Xo c U G) (Comp Xo c) (normW U (xiR D) V dict G)
    (fun Z => partLat U Z G) hW.1 (fun Z => (hOn Z).2.1.map _)
    (fun σ f hf => pyth hO σ (fun Z => ⟨f Z, span_partLat_le U Z G (hf Z)⟩))
  refine ⟨?_, ?_⟩
  · rw [finsum_eq_sum_of_fintype]
    unfold GlobalTheory.AllWt.rankW
    rw [← hS.2.2.2]
    exact hs1.trans (Finset.sum_congr rfl fun Z _ => (hrd Z).1)
  · rw [finsum_eq_sum_of_fintype]
    unfold GlobalTheory.AllWt.degW
    rw [← hS.2.2.2]
    exact hs2.trans (Finset.sum_congr rfl fun Z _ => (hrd Z).2)

theorem adds : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : WTZ D.host.E),
    Splits U G → Orthogonal U V dict G → Adds U V dict G := by
  intro D H Dw l Xo c r U V dict G hS hO
  haveI : Finite (Comp Xo c) := CompFin.finite_comp Xo c
  letI := Fintype.ofFinite (Comp Xo c)
  haveI : IsTotallyComplex c.F := totallyComplex c
  refine ⟨⟨fun h Z => GlobalTheory.HSApp.goodOn_of_goodW U (xiR D) V dict Z G h, goodW_of hS hO⟩, fun hW => ?_⟩
  have hOn : ∀ Z, GoodOn U (xiR D) V dict Z G := fun Z => GlobalTheory.HSApp.goodOn_of_goodW U (xiR D) V dict Z G hW
  have hRes : ∀ Z, HasGram (normRes U V dict Z G) := fun Z => hasGram_normRes U V dict Z G (hOn Z).1
  obtain ⟨hs1, hs2⟩ := sums hS hO hW hOn
  refine ⟨hRes, hs1, hs2, fun Z => mass_pos hO Z (hRes Z), ?_⟩
  rw [hs2]
  exact finsum_congr fun Z => degRes_eq hO Z (hRes Z) (hOn Z).2.1

end GlobalTheory.CompAdds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCmHostRootNeSelf
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.CovTop.WtRead

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [mul_self_nonneg H.rt0.re]

theorem exists_of_places (D : D7) (τ : D.host.E →+* ℂ) :
    ∃ t, DV.tauEmb D t = τ ∨ conjEmb (DV.tauEmb D t) = τ := by
  have hb : Function.Bijective fun t => InfinitePlace.mk (DV.tauEmb D t) :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨Formalism.L2.Geo.Rec.StarEmbeddingNorm.mk_tauEmb_injective D, (Formalism.L2.Geo.Rec.StarEmbeddingNorm.card_places D).symm⟩
  obtain ⟨t, ht⟩ := hb.2 (InfinitePlace.mk τ)
  refine ⟨t, ?_⟩
  rcases InfinitePlace.mk_eq_iff.1 ht with h | h
  · exact Or.inl h
  · right
    rw [← h]
    ext x
    simp [conjEmb, ComplexEmbedding.conjugate_coe_eq]

theorem tauEmb_bijective (D : D7) (Q : Par D) (hQ : Q.PinHost) :
    Function.Bijective (fun t : D.what₂.Tau => (⟨DV.tauEmb D t, hQ.2.2.2 t⟩ : Psi Q.H)) := by
  refine ⟨fun s t h => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val h), fun τ => ?_⟩
  obtain ⟨t, h | h⟩ := exists_of_places D τ.1
  · exact ⟨t, Subtype.ext h⟩
  · exfalso
    have h1 : conjEmb (DV.tauEmb D t) (Q.H.rt : D.host.E) = (starRingEnd ℂ) Q.H.rt0 := by
      simp only [conjEmb, RingHom.coe_comp, Function.comp_apply, hQ.2.2.2 t]
    exact conj_cmHostRoot_ne_self Q.H (h1.symm.trans ((congrArg (fun σ : D.host.E →+* ℂ => σ (Q.H.rt : D.host.E)) h).trans τ.2))

def tauPsi (D : D7) (Q : Par D) (hQ : Q.PinHost) : D.what₂.Tau ≃ Psi Q.H :=
  Equiv.ofBijective _ (tauEmb_bijective D Q hQ)

@[simp] theorem tauPsi_val (D : D7) (Q : Par D) (hQ : Q.PinHost) (t : D.what₂.Tau) :
    (tauPsi D Q hQ t).1 = DV.tauEmb D t := rfl

theorem sigW_add (D : D7) (i : Fin D.R.m) :
    (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by
  have := i.2
  unfold Ranks.sigW Ranks.r
  simp only
  omega

theorem laOf_big (D : D7) (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (t : D.what₂.Tau) (τ : Psi T.Q.H) (hτ : τ.1 = DV.tauEmb D t)
    (k : Fin ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q)) (a : Fin (D.R.sigW ((i : ℕ) + 1)).1)
    (ha : (a : ℕ) = k) :
    laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n τ k = (κ.aP t a : ℤ) + ((κ.n / 2 : ℕ) : ℤ) := by
  have hD := hT.pins.2.2.2 ((i : ℕ) + 1) ⟨by omega, i.2⟩
  have hk : (k : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p := by have := hD.1; have := a.2; omega
  simp only [laOf, weightOf, if_pos hk, hτ]
  rw [GlobalTheory.WeightExponents.wtA_tauEmb hT.pins.1, Formalism.L2.Pj.ext0, dif_pos (by omega)]
  have : (⟨(k : ℕ), by omega⟩ : Fin (D.R.sigW ((i : ℕ) + 1)).1) = a := Fin.ext ha.symm
  rw [this]

theorem laOf_small (D : D7) (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (t : D.what₂.Tau) (τ : Psi T.Q.H) (hτ : τ.1 = DV.tauEmb D t)
    (k : Fin ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q)) (a : Fin (D.R.sigW ((i : ℕ) + 1)).2)
    (ha : (a : ℕ) + k + 1 = D.R.r) :
    laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n τ k = -(κ.aM t a : ℤ) - ((κ.n / 2 : ℕ) : ℤ) := by
  have hD := hT.pins.2.2.2 ((i : ℕ) + 1) ⟨by omega, i.2⟩
  have hs := sigW_add D i
  have hp := hD.1
  have hq := hD.2.1
  have hk : ¬ (k : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p := by omega
  simp only [laOf, weightOf, if_neg hk, hτ]
  rw [GlobalTheory.Shares.WtDic.wtA_conj, Formalism.L2.Pj.ext0, dif_pos (by omega)]
  have : (⟨(T.Q.Dw ((i : ℕ) + 1)).q - 1 - ((k : ℕ) - (T.Q.Dw ((i : ℕ) + 1)).p), by omega⟩ :
      Fin (D.R.sigW ((i : ℕ) + 1)).2) = a := Fin.ext (by simp only; omega)
  rw [this]

theorem main : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 ∧ (T.Q.Dw ((i : ℕ) + 1)).q = (D.R.sigW ((i : ℕ) + 1)).2 ∧ Nat.card (Psi T.Q.H) = D.R.f ∧ dimFlag (T.Q.Dw ((i : ℕ) + 1)) = D.R.f * D.R.r.choose 2 ∧ Dom (wtA κ) κ.n ∧ ∃ e : D.what₂.Tau ≃ Psi T.Q.H, (∀ t, (e t).1 = DV.tauEmb D t) ∧ ∀ t (k : Fin ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q)), (∀ a : Fin (D.R.sigW ((i : ℕ) + 1)).1, (a : ℕ) = k → laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n (e t) k = (κ.aP t a : ℤ) + ((κ.n / 2 : ℕ) : ℤ)) ∧ (∀ a : Fin (D.R.sigW ((i : ℕ) + 1)).2, (a : ℕ) + k + 1 = D.R.r → |laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n (e t) k + (κ.aM t a : ℤ)| ≤ (κ.n : ℤ)) := by
  intro D T hT i κ
  have hP := hT.pins
  have hD := hP.2.2.2 ((i : ℕ) + 1) ⟨by omega, i.2⟩
  have hs := sigW_add D i
  have hcard : Fintype.card (Psi T.Q.H) = D.R.f :=
    (Fintype.card_congr (tauPsi D T.Q hP.1)).symm.trans (Formalism.MainNotions.Lnk.card_Tau D)
  refine ⟨hD.1, hD.2.1, ?_, ?_, Formalism.L2.Pj.dom_wtA κ, tauPsi D T.Q hP.1, fun t => rfl, fun t k => ⟨?_, ?_⟩⟩
  · rw [Nat.card_eq_fintype_card, hcard]
  · rw [dimFlag, Formalism.DegreeFormula.dimFl, hcard, hD.1, hD.2.1, hs, Nat.choose_two_right]
  · exact fun a ha => laOf_big D T hT i κ t _ rfl k a ha
  · intro a ha
    rw [laOf_small D T hT i κ t _ rfl k a ha]
    have h0 : (0 : ℤ) ≤ ((κ.n / 2 : ℕ) : ℤ) := Int.natCast_nonneg _
    have h1 : ((κ.n / 2 : ℕ) : ℤ) ≤ (κ.n : ℤ) := by exact_mod_cast Nat.div_le_self _ _
    rw [show -(κ.aM t a : ℤ) - ((κ.n / 2 : ℕ) : ℤ) + (κ.aM t a : ℤ) = -((κ.n / 2 : ℕ) : ℤ) by ring, abs_neg,
      abs_of_nonneg h0]
    exact h1

end GlobalTheory.CovTop.WtRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnReadingIntegerExponentSection
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReadCont

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem pow_succ_mem_secZ {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e) (m : ℕ) :
    g ^ (m + 1) ∈ secZ Xo c ((m + 1) • e) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_secZ ih hg

theorem differentiableOn_rdU_of_antitone {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (hU : IsUnf U)
    (hpq : 1 ≤ Dw.p + Dw.q) {e : Ix Dw → ℤ} (he0 : e none = 0)
    (hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j → e (some ⟨τ, j⟩) ≤ e (some ⟨τ, i⟩))
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (k : U.Comp) : DifferentiableOn ℂ (rdU U f k) (U.X k).dom := by
  intro x hx
  have ho : IsOpen (U.X k).dom := FourierCoefficientDomain.isOpen_dom _
  obtain ⟨n, hn, g, hg, hg0⟩ := GlobalTheory.TrueCx.FlatConst.exists_sec_four hpq (U.un k ⟨x, hx⟩)
  set M : ℕ := ∑ i : Ix Dw, (e i).natAbs with hMdef
  have hM : ∀ i, -(4 * ((M + 1 : ℕ) : ℤ)) ≤ e i := fun i => by
    have h1 : (e i).natAbs ≤ M := Finset.single_le_sum (f := fun i => (e i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    have h2 : -((e i).natAbs : ℤ) ≤ e i := by
      have := Int.natAbs_abs (e i); rw [← Int.abs_eq_natAbs]; exact neg_abs_le _
    have h3 : ((e i).natAbs : ℤ) ≤ M := by exact_mod_cast h1
    push_cast; linarith
  let a : (E →+* ℂ) × ℕ → ℕ := fun p =>
    if h : p.2 < Dw.mult p.1 then (4 * ((M + 1 : ℕ) : ℤ) + e (some ⟨p.1, ⟨p.2, h⟩⟩)).toNat else 0
  have hdom : Dom a ((M + 1) * n) := by
    refine ⟨fun τ i j hij => ?_, hn.mul_left _⟩
    show a (τ, j) ≤ a (τ, i)
    simp only [a]
    by_cases hj : j < Dw.mult τ
    · have hi : i < Dw.mult τ := lt_of_le_of_lt hij hj
      rw [dif_pos hj, dif_pos hi]
      exact Int.toNat_le_toNat (by linarith [hanti τ ⟨i, hi⟩ ⟨j, hj⟩ hij])
    · rw [dif_neg hj]; exact Nat.zero_le _
  have hgp := pow_succ_mem_secZ (Xo := Xo) (c := c) (by rw [secZ_nat]; exact hg) M
  have hgf : g ^ (M + 1) * f ∈ sec Xo c a ((M + 1) * n) := by
    rw [← secZ_nat]
    convert mul_mem_secZ hgp hf using 2
    funext i
    rcases i with _ | ⟨τ, i⟩
    · simp [ex, he0]
    · have hi := i.2
      rw [Pi.add_apply, Pi.smul_apply]
      simp only [ex, a, dif_pos hi, nsmul_eq_mul]
      rw [Int.toNat_of_nonneg (by linarith [hM (some ⟨τ, i⟩)])]
      push_cast
      ring
  have d1 := (hU.2.2.2.2.1 _ n ⟨fun _ _ _ _ => le_rfl, hn⟩ g hg k).1
  have d2 := (hU.2.2.2.2.1 _ _ hdom _ hgf k).1
  have hx0 : rdU U g k x ≠ 0 := by
    have : rdU U g k x = toC (evR Xo c g (U.un k ⟨x, hx⟩)) := dif_pos hx
    rwa [this]
  have a1 := d1.differentiableAt (ho.mem_nhds hx)
  have a2 := d2.differentiableAt (ho.mem_nhds hx)
  refine ((a2.mul ((a1.pow (M + 1)).inv (pow_ne_zero _ hx0))).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [a1.continuousAt.eventually_ne hx0] with y hy0
  have e1 : rdU U (g ^ (M + 1) * f) k y = rdU U g k y ^ (M + 1) * rdU U f k y := by
    rw [rdU_mul]
    have : ∀ m : ℕ, rdU U (g ^ (m + 1)) = rdU U g ^ (m + 1) := fun m => by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ g (m + 1), rdU_mul, ih, ← pow_succ]
    rw [this]; rfl
  rw [Pi.mul_apply, Pi.inv_apply, e1, Pi.pow_apply, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero _ hy0), one_mul]

end GlobalTheory.ReadCont

namespace GlobalTheory.ReadCont

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem continuousOn_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (e : Ix Dw → ℤ), e none = 0 → ∀ s ∈ secZ Xo c e, ∀ σ, GoodEmb c σ → ∀ k, ContinuousOn (rdU (U σ) s k) ((U σ).X k).dom := by
  intro E _ _ _ H Dw l Xo c r U x hL e he0 s hs σ hσ k
  by_cases hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j → e (some ⟨τ, j⟩) ≤ e (some ⟨τ, i⟩)
  · exact (differentiableOn_rdU_of_antitone (hL.unf σ hσ) hL.pos he0 hanti hs k).continuousOn
  · push_neg at hanti
    obtain ⟨τ, i, j, hij, hlt⟩ := hanti
    have hij' : i < j := lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)
    rw [GlobalTheory.T.integerExponentSection_eq_zero_of_increasing_flag E H Dw l Xo c e τ i j hij' hlt s hs, map_zero]
    exact continuousOn_const

end GlobalTheory.ReadCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportWeilDatumCmExtensionStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_transport_weil_datum_cm_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsContOn (adeleClass F) om := by
  first | exact @GlobalTheory.WeilContF.continuous_transportF | exact GlobalTheory.WeilContF.continuous_transportF | (intros; apply GlobalTheory.WeilContF.continuous_transportF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponentsStatement
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_supLattice_split_over_components : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ G : WTZ D.host.E, Splits U G := by
  first | exact @GlobalTheory.CuspSplit.splits | exact GlobalTheory.CuspSplit.splits | (intros; apply GlobalTheory.CuspSplit.splits <;> assumption)
end

