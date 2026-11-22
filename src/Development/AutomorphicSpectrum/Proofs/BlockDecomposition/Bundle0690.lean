import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0676
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0668
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0653
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0679
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0104
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0106
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0395
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0603
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0681
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0654

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelCharactersUnramified
section
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrLevChars

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ}
  {S : Subring (Fv F v ⊗[F] E)} {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem sigR_algebraMap (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  rw [Algebra.algebraMap_eq_smul_one, sigR_smul, map_one]

theorem smul_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {β : Fv F v} (hβ : β ∈ v.adicCompletionIntegers F)
    {x : Fv F v ⊗[F] E} (hx : x ∈ S) : β • x ∈ S := by
  have h1 : x ∈ Rv bs v := by
    rw [← hG.carrier]
    exact hx
  have h2 : β • x ∈ Rv bs v := fun k => by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hβ (h1 k)
  rw [← hG.carrier] at h2
  exact h2

theorem fixed_eq (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (a : S) (ha : σS a = a) :
    ∃ α : Fv F v, (a : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) α :=
  hG.fixed a (by rw [← hG.sig, ha])

theorem basis_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (i : Fin d) :
    Algebra.TensorProduct.basis (Fv F v) bs i ∈ S := by
  have h : Algebra.TensorProduct.basis (Fv F v) bs i ∈ Rv bs v := fun k => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← hG.carrier] at h
  exact h

theorem nontrivial_S (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) : Nontrivial S := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hG.quad.notUnit (isUnit_of_subsingleton _)

theorem card_eq_two (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) : d = 2 := by
  obtain ⟨u, hu, hb⟩ := hG.quad.basis
  have : Nontrivial S := nontrivial_S hG
  have : Nontrivial (Fv F v ⊗[F] E) := (Subtype.val_injective (p := fun x => x ∈ S)).nontrivial
  have hinj := (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective
  have hli : LinearIndependent (Fv F v) ![(1 : Fv F v ⊗[F] E), (u : Fv F v ⊗[F] E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have ht : t = 0 := by
      by_contra ht
      have e : (u : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (-(t⁻¹ * s)) := by
        have h3 : t • (u : Fv F v ⊗[F] E) = -(s • (1 : Fv F v ⊗[F] E)) := eq_neg_of_add_eq_zero_right h
        have h4 : (u : Fv F v ⊗[F] E) = t⁻¹ • (t • (u : Fv F v ⊗[F] E)) := by
          rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [h4, h3, Algebra.algebraMap_eq_smul_one, smul_neg, neg_smul, smul_smul]
      have hfix : σS u = u := Subtype.ext (by rw [hG.sig, e, sigR_algebraMap])
      rw [hfix, sub_self, isUnit_zero_iff] at hu
      exact zero_ne_one hu
    subst ht
    refine ⟨?_, rfl⟩
    rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one] at h
    exact hinj (by rw [h, map_zero])
  have hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range ![(1 : Fv F v ⊗[F] E), (u : Fv F v ⊗[F] E)]) := by
    rw [← (Algebra.TensorProduct.basis (Fv F v) bs).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, y, hx, hy, e⟩ := hb ⟨_, basis_mem hG i⟩
    obtain ⟨α, hα⟩ := fixed_eq hG x hx
    obtain ⟨β, hβ⟩ := fixed_eq hG y hy
    have e2 : Algebra.TensorProduct.basis (Fv F v) bs i =
        α • (1 : Fv F v ⊗[F] E) + β • (u : Fv F v ⊗[F] E) := by
      have e3 := congrArg Subtype.val e
      simp only [Subring.coe_add, Subring.coe_mul] at e3
      rw [e3, hα, hβ, Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [SetLike.mem_coe, e2]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  have h2 := Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Fv F v) bs)
  simpa using h2.symm.trans h1

theorem trace_algebraMap_eq (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (x : Fv F v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (algebraMap (Fv F v) (Fv F v ⊗[F] E) x) = 2 * x := by
  rw [Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis (Fv F v) bs), Fintype.card_fin,
    card_eq_two hG, two_nsmul, two_mul]

theorem psiF_compat (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (c : Fv F v) (k : ℕ) (a : Fv F v ⊗[F] E) :
    psiF ψv ϖ c (k + 1) (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * a) = psiF ψv ϖ c k a := by
  unfold psiF
  rw [← Algebra.smul_def, map_smul, smul_eq_mul, ← mul_assoc ((ϖ ^ (k + 1))⁻¹), pow_succ, mul_inv,
    mul_assoc (ϖ ^ k)⁻¹, inv_mul_cancel₀ hG.unif_ne, mul_one]

theorem mem_level_of_character_trivial (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (hc1 : ‖c‖ = 1) (a : S) (ha : σS a = a)
    (hb : ∀ b, σS b = b → hG.psiLev hc 1 (Ideal.Quotient.mk _ (a * b)) = 1) : a ∈ lev hG.pS 1 := by
  have h20 : (2 : Fv F v) ≠ 0 := by
    intro h
    have := hG.two
    rw [h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨α, hα⟩ := fixed_eq hG a ha
  have hαO : α ∈ v.adicCompletionIntegers F := by
    have h2 := hG.trace_mem a.2
    rw [hα, trace_algebraMap_eq hG] at h2
    have h3 := mul_mem hG.half_mem h2
    rwa [← mul_assoc, inv_mul_cancel₀ h20, one_mul] at h3
  have hkey : c * (ϖ⁻¹ * α) ∈ v.adicCompletionIntegers F := by
    refine (hG.psi_cond _).1 fun β hβ => ?_
    have hbS : algebraMap (Fv F v) (Fv F v ⊗[F] E) β ∈ S := by
      have h1 := smul_mem hG hβ (one_mem S)
      rwa [← Algebra.algebraMap_eq_smul_one] at h1
    have hfix : σS ⟨_, hbS⟩ = ⟨_, hbS⟩ := Subtype.ext (by rw [hG.sig]; exact sigR_algebraMap β)
    have h1 := hb _ hfix
    rw [hG.psiLev_mk] at h1
    have e : ((a * ⟨_, hbS⟩ : S) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (α * β) := by
      rw [Subring.coe_mul, hα, map_mul]
    rw [e] at h1
    unfold psiF at h1
    rw [trace_algebraMap_eq hG] at h1
    rw [← h1]
    congr 1
    have := hG.unif_ne
    field_simp
  have hγ : ϖ⁻¹ * α ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff] at hkey ⊢
    rw [norm_mul, hc1, one_mul] at hkey
    exact hkey
  have hgS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ⁻¹ * α) ∈ S := by
    have h1 := smul_mem hG hγ (one_mem S)
    rwa [← Algebra.algebraMap_eq_smul_one] at h1
  refine Ideal.mem_span_singleton'.2 ⟨⟨_, hgS⟩, Subtype.ext ?_⟩
  rw [pow_one, Subring.coe_mul, hα]
  show algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ⁻¹ * α) * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = _
  rw [← map_mul]
  congr 1
  have := hG.unif_ne
  field_simp

theorem levChars : PositivityTheory.SiegelWeilFormula.Gunr.LevChars := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG c hc hc1
  refine ⟨fun k a => ?_, fun a ha hb => mem_level_of_character_trivial hG hc hc1 a ha hb⟩
  rw [GoodLoc.psiLev_mk, GoodLoc.psiLev_mk]
  exact psiF_compat hG c k a

end GlobalTheory.CompanionTheory.GunrLevChars

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExhaustion
section
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrExhaust

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_pow_mul_mem {v : HeightOneSpectrum (𝓞 F)} {ϖ : Fv F v} (h : ‖ϖ‖ < 1) (c : Fv F v) :
    ∀ᶠ k : ℕ in atTop, ϖ ^ k * c ∈ v.adicCompletionIntegers F := by
  have h0 : Tendsto (fun k : ℕ => ‖ϖ‖ ^ k * ‖c‖) atTop (𝓝 (0 * ‖c‖)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h).mul_const _
  rw [zero_mul] at h0
  filter_upwards [h0.eventually (gt_mem_nhds one_pos)] with k hk
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff, norm_mul, norm_pow]
  exact hk.le

theorem eventually_smul_mem {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
    {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
    {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ} (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (x : Fv F v ⊗[F] E) :
    ∀ᶠ k : ℕ in atTop, ϖ ^ k • x ∈ S := by
  have h : ∀ᶠ k : ℕ in atTop, ∀ i, ϖ ^ k * (Algebra.TensorProduct.basis (Fv F v) bs).repr x i ∈
      v.adicCompletionIntegers F :=
    eventually_all.2 fun i => eventually_pow_mul_mem hG.unif_lt _
  filter_upwards [h] with k hk
  have hmem : ϖ ^ k • x ∈ (S : Set (Fv F v ⊗[F] E)) := by
    rw [hG.carrier]
    intro i
    simpa [map_smul] using hk i
  exact hmem

theorem exhaust : Exhaust := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG b
  have h : ∀ᶠ k : ℕ in atTop, ∀ a c, ϖ ^ k • (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c ∈ S :=
    eventually_all.2 fun a => eventually_all.2 fun c => eventually_smul_mem hG _
  obtain ⟨k, hk⟩ := h.exists
  have hX : PositivityTheory.PfSWUS.Loc.cT σS (Matrix.of fun a c => (⟨_, hk a c⟩ : S)) = Matrix.of fun a c => (⟨_, hk a c⟩ : S) := by
    ext a c
    have hb := b.2 a c
    simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
    rw [hG.sig]
    simp only [sigR_smul]
    exact congrArg _ hb
  refine ⟨k, _, hX, ?_⟩
  apply Subtype.ext
  funext a c
  show (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c = (ϖ ^ k)⁻¹ • ϖ ^ k • (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hG.unif_ne), one_smul]

end GlobalTheory.CompanionTheory.GunrExhaust

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDoubleIntegralIdentity
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.LFGInt2

theorem modulus_det_iwasawa_inv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (x : F) (a b : Fˣ) (κ : GL (Fin 2) F), κ ∈ GLnLocal.integralGL F 2 → (modulus ((Matrix.GeneralLinearGroup.det (Ad3.uni2 x * Ad3.dg2 a b * κ)⁻¹ : Fˣ) : F) : ℝ) = ((modulus (a : F) : ℝ) * (modulus (b : F) : ℝ))⁻¹ := by
  intro F _ _ _ _ x a b κ hκ
  have hκ1 : modulus ((Matrix.GeneralLinearGroup.det κ : Fˣ) : F) = 1 := by
    obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hκ
    have key : ∀ g : GL (Fin 2) F, (∀ i j, g i j ∈ 𝒪[F]) →
        modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ≤ 1 := by
      intro g hg
      rw [modulus_le_one_iff, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      exact sub_mem (mul_mem (hg 0 0) (hg 1 1)) (mul_mem (hg 0 1) (hg 1 0))
    have a' := key κ h1
    have b' := key κ⁻¹ h2
    rw [map_inv, Units.val_inv_eq_inv_val, modulus_inv] at b'
    have hpos := modulus_pos (Matrix.GeneralLinearGroup.det κ : Fˣ).ne_zero
    exact le_antisymm a' ((inv_le_one₀ hpos).1 b')
  have hd1 : Matrix.GeneralLinearGroup.det (Ad3.uni2 x) = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Ad3.uni2, Matrix.det_fin_two]
  have hd2 : Matrix.GeneralLinearGroup.det (Ad3.dg2 a b) = a * b := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Ad3.dg2, Matrix.det_fin_two]
  rw [map_inv, map_mul, map_mul, hd1, hd2, one_mul, Units.val_inv_eq_inv_val, modulus_inv, Units.val_mul,
    modulus_mul, hκ1, mul_one, Units.val_mul, modulus_mul]
  push_cast
  rfl

open Ad3 Ad3.LFS in

theorem gInt2 : Ad3.LFS.GInt2 := by
  intro F _ _ _ _ _ _ ψ hψ ν hν V' H W' hW' R
  classical
  obtain ⟨C, B, hCB⟩ := H.bound W' hW' (1 / 4) (by norm_num)
  set q : ℝ := (residueCard F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast (one_lt_residueCard (K := F))
  have hq0 : 0 < q := by linarith
  obtain ⟨L₀, hL₀⟩ := pow_unbounded_of_one_lt R hq
  set L : ℤ := (L₀ : ℤ) with hLdef
  have hRL : R ≤ q ^ L := by rw [hLdef, zpow_natCast]; exact hL₀.le
  haveI hμ : (hG ψ).IsHaarMeasure := by unfold hG; infer_instance
  haveI hinv : (hG ψ).IsInvInvariant := ⟨Measures.inv_eq_self_GL F 2 (hG ψ)⟩
  set Kμ : ℝ≥0∞ := hG ψ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) with hKμ
  have hKfin : Kμ ≠ ∞ := (GLnLocal.isCompact_integralGL F 2).measure_lt_top.ne
  set C₁ : ℝ := max C 0 with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  have hbound : ∀ (a : Fˣ), ∀ κ ∈ GLnLocal.integralGL F 2,
      ‖W' (dg2 a 1 * κ)‖ ≤ C₁ * (modulus (a : F) : ℝ) ^ (1 / 4 : ℝ) := by
    intro a κ hκ
    have h := (hCB a κ hκ).1
    rw [show (1 / 2 - 1 / 4 : ℝ) = 1 / 4 by norm_num] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hpsi : ∀ x g, W' (uni2 x * g) = (ψ x : ℂ) * W' g := H.psi W' hW'
  have hcen : ∀ (a : Fˣ) g, W' (dg2 a a * g) = W' g := by
    intro a g
    rw [H.cen W' hW']
    simp
  obtain ⟨U, hU⟩ := H.smooth W' hW'
  have hWc : Continuous W' := by
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨{x | g⁻¹ * x ∈ U}, U.isOpen.preimage (continuous_const.mul continuous_id), by simp [U.one_mem],
      fun x hx => ?_⟩
    have := hU g _ hx
    simpa using this
  have hval : Continuous fun k : GL (Fin 2) F => (k : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have hmod : Continuous fun x : F => (modulus x : ℝ) := NNReal.continuous_coe.comp continuous_modulus
  have hdet : Continuous fun k : GL (Fin 2) F => (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) := by
    have : Continuous fun k : GL (Fin 2) F => ((GeneralLinearGroup.det k : Fˣ) : F) := by
      simpa using hval.matrix_det
    exact hmod.comp this
  have homc : ∀ t : Fˣ, IsClosed (om R t : Set (GL (Fin 2) F)) := by
    intro t
    have e : (om R t : Set (GL (Fin 2) F)) = (⋂ i, ⋂ j, {k : GL (Fin 2) F | (modulus ((k : Matrix (Fin 2) (Fin 2) F) i j) : ℝ) ≤ R}) ∩
        ⋂ j, {k : GL (Fin 2) F | (modulus ((t : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) : ℝ) ≤ R} := by
      ext k
      simp [om]
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (hmod.comp (hval.matrix_elem i j)) continuous_const) (isClosed_iInter fun j =>
      isClosed_le (hmod.comp (continuous_const.mul ((hval.comp continuous_inv).matrix_elem 1 j))) continuous_const)
  set r : ℝ := q ^ (-(1 / 4) : ℝ) with hr
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)
  set D : ℝ := 1 - r with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hqL : 0 < q ^ L := zpow_pos hq0 L
  refine ⟨C₁ * q ^ L * ((q ^ L) ^ (1 / 4 : ℝ) / D) ^ 2 * Kμ.toReal, fun t₁ t₂ => ?_⟩
  set τ : ℝ := (modulus (t₂ : F) : ℝ) with hτdef
  have hτ : 0 < τ := by exact_mod_cast modulus_pos t₂.ne_zero
  set σ : ℝ := (modulus (t₁ : F) : ℝ) with hσdef
  have hσ : 0 < σ := by exact_mod_cast modulus_pos t₁.ne_zero
  set f : GL (Fin 2) F → ℝ := (om R t₂).indicator fun k =>
    ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => Set.indicator_nonneg (fun _ _ => by positivity) k
  have hfm : Measurable f := by
    refine Measurable.indicator (Continuous.measurable ?_) (homc t₂).measurableSet
    exact (hWc.comp (continuous_const.mul continuous_inv)).norm.mul
      (hdet.rpow_const fun _ => Or.inr (by norm_num))
  set A : ℝ := C₁ * (σ / τ) ^ (1 / 4 : ℝ) with hA
  have hA0 : 0 ≤ A := by positivity
  set T₁r : ℝ := (q ^ L) ^ (1 / 4 : ℝ) / D with hT₁r
  set T₂r : ℝ := (q ^ L / τ) ^ (1 / 4 : ℝ) / D with hT₂r
  have hT₁ : (∑' m : ℤ, (if m ≤ L then ENNReal.ofReal (q ^ ((m : ℝ) / 4)) else 0)) ≤ ENNReal.ofReal T₁r := by
    have h := GlobalTheory.T.geometric_sum_below_threshold q (1 / 4) (q ^ L) hq (by norm_num) hqL
    refine le_of_eq_of_le (tsum_congr fun m => ?_) h
    simp only [zpow_le_zpow_iff_right₀ hq]
    rw [show (m : ℝ) / 4 = 1 / 4 * (m : ℝ) by ring]
  have hT₂ : (∑' n : ℤ, (if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) else 0)) ≤ ENNReal.ofReal T₂r := by
    have h := GlobalTheory.T.geometric_sum_below_threshold q (1 / 4) (q ^ L / τ) hq (by norm_num) (div_pos hqL hτ)
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine le_of_eq_of_le (tsum_congr fun m => ?_) h
    simp only [Equiv.neg_apply, neg_neg, Int.cast_neg]
    have e : τ * q ^ m ≤ q ^ L ↔ q ^ m ≤ q ^ L / τ := by rw [le_div_iff₀ hτ, mul_comm]
    simp only [e]
    rw [show (m : ℝ) / 4 = 1 / 4 * (m : ℝ) by ring]
  set S : ℤ → ℤ → Set (GL (Fin 2) F) := fun m n => {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ q ^ (L - m) ∧
    ∃ κ ∈ GLnLocal.integralGL F 2, g = uni2 x * dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} with hS
  set Φ : GL (Fin 2) F → ℝ≥0∞ := fun g => ENNReal.ofReal (f g⁻¹) with hΦ
  have hcov : ∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L ∧ y ∈ S m n ∧
      Φ y ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) := by
    intro g hg
    have hom : g⁻¹ ∈ om R t₂ := by
      by_contra h
      exact hg (by simp [hΦ, hf, h])
    obtain ⟨x, m, n, κ, hκ, rfl⟩ := GlobalTheory.T.iwasawa_decomposition_gl_two_holds F g
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.iwasawa_coordinates_bounded_region F x m n L κ R t₂ hκ hRL hom
    refine ⟨m, n, h1, h2, h4, ⟨x, h3, κ, hκ, rfl⟩, ENNReal.ofReal_le_ofReal ?_⟩
    rw [hf, Set.indicator_of_mem hom, inv_inv]
    have hw := GlobalTheory.T.whittaker_iwasawa_growth_bound F ψ W' C₁ hpsi hcen hbound t₁ t₂ (unifUnit F ^ m) (unifUnit F ^ n) x κ hκ
    have hu : ∀ k : ℤ, (modulus (((unifUnit F ^ k : Fˣ)) : F) : ℝ) = q ^ (-(k : ℝ)) := by
      intro k
      rw [modulus_of_ne_zero (Units.ne_zero _), ord_unifUnit_zpow, NNReal.coe_zpow, NNReal.coe_natCast,
        ← Real.rpow_intCast]
      push_cast
      rfl
    have hM : (modulus ((t₁ * unifUnit F ^ m * (t₂ * unifUnit F ^ n)⁻¹ : Fˣ) : F) : ℝ) =
        (σ / τ) * q ^ ((n : ℝ) - m) := by
      rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mul, modulus_mul, modulus_mul,
        modulus_inv, modulus_mul]
      simp only [NNReal.coe_mul, NNReal.coe_inv]
      rw [hu, hu, ← hσdef, ← hτdef, sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_neg hq0.le (m : ℝ),
        Real.rpow_neg hq0.le (n : ℝ)]
      have := (Real.rpow_pos_of_pos hq0 (m : ℝ)).ne'
      have := (Real.rpow_pos_of_pos hq0 (n : ℝ)).ne'
      field_simp
    have hdetg := modulus_det_iwasawa_inv F x (unifUnit F ^ m) (unifUnit F ^ n) κ hκ
    rw [hM] at hw
    rw [hdetg, hu, hu, mul_inv, ← Real.rpow_neg hq0.le, ← Real.rpow_neg hq0.le, neg_neg, neg_neg,
      ← Real.rpow_add hq0, ← Real.rpow_mul hq0.le]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hq0.le] at hw
    have e1 : ((n : ℝ) - m) * (1 / 4) = ((n : ℝ) - m) / 4 := by ring
    have e2 : ((m : ℝ) + n) * (1 / 2) = ((m : ℝ) + n) / 2 := by ring
    rw [e1] at hw
    rw [e2, hA, mul_assoc C₁]
    exact mul_le_mul_of_nonneg_right hw (by positivity)
  have hmain := GlobalTheory.T.iwasawa_sum_measure_estimate (hG ψ) q A τ L Kμ _ _ S Φ hq hA0 hτ
    (fun m n => (GlobalTheory.T.iwasawa_region_measure_bound F (hG ψ) m n L).1.measurableSet) (fun m n hn => (GlobalTheory.T.iwasawa_region_measure_bound F (hG ψ) m n L).2 hn)
    hT₁ hT₂ hcov
  have hinvl : ∫⁻ k, ENNReal.ofReal (f k) ∂hG ψ = ∫⁻ g, Φ g ∂hG ψ :=
    ((Measure.measurePreserving_inv (hG ψ)).lintegral_comp hfm.ennreal_ofReal).symm
  set Rr : ℝ := C₁ * q ^ L * ((q ^ L) ^ (1 / 4 : ℝ) / D) ^ 2 * Kμ.toReal * σ ^ (1 / 4 : ℝ) * τ ^ (-(1 / 2) : ℝ) with hRr
  have hRr0 : 0 ≤ Rr := by positivity
  have hfin : ∫⁻ k, ENNReal.ofReal (f k) ∂hG ψ ≤ ENNReal.ofReal Rr := by
    rw [hinvl]
    refine hmain.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hKfin, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hw0 : 0 < τ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hτ _
    have hw2 : τ ^ (-(1 / 2) : ℝ) = ((τ ^ (1 / 4 : ℝ)) ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le, ← Real.rpow_neg hτ.le]
      norm_num
    rw [hRr, hA, hT₁r, hT₂r, hw2, Real.div_rpow hσ.le hτ.le, Real.div_rpow hqL.le hτ.le]
    field_simp
  refine ⟨⟨hfm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)]
    exact hfin.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hRr0 hfin

end GlobalTheory.CompanionTheory.LFGInt2
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorExtensionStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_conductor_extension : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ (v' : V') (A : ℂ), EvVal ν ψ T B v v' A ∧ A ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero | exact GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero | (intros; apply GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityPowerFormula
section
noncomputable section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.SiegLoc

namespace GlobalTheory.CompanionTheory.GunrNu

theorem card_range_pow {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (hR : IsUnrQuad R σ ϖ q ε) (k : ℕ) (d : R) (hd : σ d = d) :
    ∃ e : ℕ, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) =
      (q ^ 2) ^ e := by
  rcases Scaled.fixed_decomp hR k d hd with h0 | ⟨a₀, e, c, rfl, hc, hc1, rfl⟩
  · have hz : Ideal.Quotient.mk (lev ϖ k) d = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h0
    have hr : (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = {0} := by
      ext z
      simp [hz]
    exact ⟨0, by rw [hr]; simp⟩
  · exact ⟨e, by
      rw [Scaled.card_range_mul hR.reg (hR.fixLocal c hc hc1) e a₀,
        GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR e, pow_mul]⟩

theorem nuPow : PositivityTheory.SiegelWeilFormula.Gunr.NuPow := by
  intro R _ σ ϖ q ε hR n k B hB
  obtain ⟨h, hh, rfl⟩ := hB
  have hq := hR.one_lt
  have hfin : Finite (R ⧸ lev ϖ k) := Nat.finite_of_card_ne_zero (by
    rw [GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR k]
    exact pow_ne_zero _ (by omega))
  let _ : Fintype (R ⧸ lev ϖ k) := Fintype.ofFinite _
  obtain ⟨g, g', d, hgg, hgg', hd, hgd⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR n h hh
  choose eI hcard using fun i => card_range_pow hR k (d i) (hd i)
  have hnu : nuAt ϖ (red ϖ k h) = (q ^ 2) ^ (∑ i, eI i) := by
    rw [GlobalTheory.T.multiplicity_reduction_diagonal_prod R σ ϖ hR.fix_ϖ hR.inv k n h g g' d hgg hgg' hgd,
      Finset.prod_congr rfl (fun i _ => hcard i), Finset.prod_pow_eq_pow_sum]
  rw [hnu, Nat.log_pow (Nat.one_lt_pow (by norm_num) hq)]

end GlobalTheory.CompanionTheory.GunrNu

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellFunctionCompactSupportUnipotentStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_function_compact_support_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ f ∈ openFns d hd ρ, ∃ L : Subgroup (GL (Fin N) k), L ≤ unipU k d hd ∧ IsCompact (L : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L) ∧ ∀ g, f.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support | exact GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support | (intros; apply GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothingFundamentalDomainIntegralStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_fundamental_domain_integral : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) →
  ∫⁻ x in F, ‖sm ν β f x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Conc.sm_sq_mass_le | exact GlobalTheory.CompanionTheory.Conc.sm_sq_mass_le | (intros; apply GlobalTheory.CompanionTheory.Conc.sm_sq_mass_le <;> assumption)
end

