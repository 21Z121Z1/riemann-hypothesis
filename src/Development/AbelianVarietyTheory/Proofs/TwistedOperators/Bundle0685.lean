import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0672
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0637
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0671
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0660
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0514
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0673

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLift
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.HoweRealKer

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    simp
  intro hM
  apply hD
  rw [← Matrix.det_submatrix_equiv_self e.symm, ← hA', Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul]

theorem det_ne_zero_of_sig {E : Type} [Field E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) {r s : ℕ} (h : HasSig (J.map f) r s) : J.det ≠ 0 := by
  intro hJ
  apply det_ne_zero_of_hasSig h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero]

theorem det_ne_zero_of_sigI {E : Type} [Field E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) {r s : ℕ} (h : HasSig (Complex.I • J.map f) r s) : J.det ≠ 0 := by
  intro hJ
  apply det_ne_zero_of_hasSig h
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero, mul_zero]

theorem resEtaPow_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} {n m : ℕ}
    (h : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n)
    (h' : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ' m) :
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (χ / χ') (n + m) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem actsD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ℝ → ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) :
    ActsD (evI F) (fun t => T t) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) ((0 : SInf F κ) : _) := by
  intro r _ x
  have h0 : tens (evI F) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = 0 := by
    funext y; simp [tens]
  simp only [h0, map_zero, Pi.zero_apply]
  exact hasDerivAt_const 0 0

theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) :
    Acts (evI F) T ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) ((0 : SInf F κ) : _) := by
  intro r _
  have h0 : tens (evI F) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = 0 := by
    funext y; simp [tens]
  simp only [h0, map_zero]

theorem main : GlobalTheory.Published.HoweDualityReal → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hMt
  obtain ⟨ht, hr, -⟩ := hMt
  have w0 : InfinitePlace F := Classical.arbitrary _
  have hVdet : G.V.J.det ≠ 0 := det_ne_zero_of_sig _ _ (ht.geo.hV.sig w0)
  have hV'det : G.V'.J.det ≠ 0 := det_ne_zero_of_sig _ _ (ht.geo.hV'.sig w0)
  have hWdet : G.W.J.det ≠ 0 := det_ne_zero_of_sigI _ _ (ht.geo.hW.sig w0)
  have hresW : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (Xc.β / Xc.α) (a + a') :=
    resEtaPow_div ht.chars.resβ ht.chars.resα
  have hresW' : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (Xc.α / Xc.β) (a' + a) :=
    resEtaPow_div ht.chars.resα ht.chars.resβ
  rw [Nat.add_comm a' a] at hresW'
  have hHk := isHecke_div ht.chars.heckeβ ht.chars.heckeα
  have hHk' := isHecke_div ht.chars.heckeα ht.chars.heckeβ
  obtain ⟨hchain, hsum⟩ := hHD F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have L := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have L' := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ ht.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' ht.base.std
    ht.geo.hV'.herm hV'det ht.geo.hW.skew hWdet ht.chars.resα hresW' ht.chars.heckeα hHk' ht.weil' Bs.emb
    ht.geo.hV'.cartan ht.geo.hW.cartan
  have C := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have C' := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ ht.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' ht.base.std
    ht.geo.hV'.herm hV'det ht.geo.hW.skew hWdet ht.chars.resα hresW' ht.chars.heckeα hHk' ht.weil' Bs.emb
    ht.geo.hV'.cartan ht.geo.hW.cartan
  refine ⟨hchain, ?_⟩
  intro N hN hNP

  set P := G.M.Pol Bs.ψ Bs.emb with hPdef
  let K : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) := LinearMap.ker R.p ⊓ P
  have hK : GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om K := by
    refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
    · intro γ hγ g hg g₁ hg₁
      exact ⟨LinearMap.mem_ker.mpr (hr.quot.lie γ hγ g hg g₁ hg₁), hN.1 (hN.2.1 γ hγ g hg g₁ hg₁)⟩
    · intro k hk g hg g₁ hg₁
      refine ⟨?_, hN.1 (hN.2.2.1 k hk g hg g₁ hg₁)⟩
      show R.p (g₁ - g) = 0
      rw [map_sub, hr.quot.cpt k hk g hg g₁ hg₁, sub_self]
    · intro γ hγ g hg g₁ hg₁
      refine ⟨?_, (L γ hγ g hg.2).2 g₁ hg₁⟩
      have e := hr.lie γ hγ g hg.2 0 (Submodule.zero_mem _) g₁ 0 hg₁ (actsD_zero _)
        (by rw [LinearMap.mem_ker.mp hg.1, map_zero])
      show R.p g₁ = 0
      rw [e, map_zero]
    · intro k hk g hg g₁ hg₁
      refine ⟨?_, (C k hk g hg.2).2 g₁ hg₁⟩
      have e := hr.cpt k hk g hg.2 0 (Submodule.zero_mem _) g₁ 0 hg₁ (acts_zero _)
        (by rw [LinearMap.mem_ker.mp hg.1, map_zero])
      show R.p g₁ = 0
      rw [e, map_zero]
  have hKP : K ≠ P := by
    intro hKP
    haveI := hr.nontriv
    have hle : P ≤ LinearMap.ker R.p := hKP ▸ inf_le_left
    have hbot : P.map R.p = ⊥ := by
      rw [eq_bot_iff, Submodule.map_le_iff_le_comap]
      intro x hx
      simpa [Submodule.mem_comap] using hle hx
    exact bot_ne_top (hbot.symm.trans hr.quot.onto)

  have hirr := hr.irred (N.map R.p) ?_ ?_
  · rcases hirr with hbot | htop
    · intro f hf
      have : R.p f ∈ N.map R.p := Submodule.mem_map_of_mem hf
      rw [hbot] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exfalso
      apply hsum N K hN hK hNP hKP
      refine le_antisymm (sup_le hN.1 inf_le_right) ?_
      intro g hg
      have hpg : R.p g ∈ N.map R.p := htop ▸ Submodule.mem_top
      obtain ⟨n₀, hn₀, hpn⟩ := hpg
      have hk : g - n₀ ∈ K := ⟨show R.p (g - n₀) = 0 by rw [map_sub, hpn, sub_self], P.sub_mem hg (hN.1 hn₀)⟩
      have := Submodule.add_mem_sup hn₀ hk
      simpa using this
  · intro γ hγ g hg g₁ hg₁ hpg
    obtain ⟨n₀, hn₀, hpn⟩ := hpg
    have hg' : R.p g ∈ (G.M'.Pol Bs.ψ Bs.emb).map R.p' := hr.quot'.onto ▸ Submodule.mem_top
    obtain ⟨g', hg'P, hpg'⟩ := hg'
    obtain ⟨g₁', hg₁'⟩ := (L' γ hγ g' hg'P).1
    obtain ⟨n₁, hn₁⟩ := (L γ hγ n₀ (hN.1 hn₀)).1
    have e1 := hr.lie γ hγ g hg g' hg'P g₁ g₁' hg₁ hg₁' hpg'.symm
    have e2 := hr.lie γ hγ n₀ (hN.1 hn₀) g' hg'P n₁ g₁' hn₁ hg₁' (hpn.trans hpg'.symm)
    exact ⟨n₁, hN.2.2.2.1 γ hγ n₀ hn₀ n₁ hn₁, e2.trans e1.symm⟩
  · intro k hk g hg g₁ hg₁ hpg
    obtain ⟨n₀, hn₀, hpn⟩ := hpg
    have hg' : R.p g ∈ (G.M'.Pol Bs.ψ Bs.emb).map R.p' := hr.quot'.onto ▸ Submodule.mem_top
    obtain ⟨g', hg'P, hpg'⟩ := hg'
    obtain ⟨g₁', hg₁'⟩ := (C' k hk g' hg'P).1
    obtain ⟨n₁, hn₁⟩ := (C k hk n₀ (hN.1 hn₀)).1
    have e1 := hr.cpt k hk g hg g' hg'P g₁ g₁' hg₁ hg₁' hpg'.symm
    have e2 := hr.cpt k hk n₀ (hN.1 hn₀) g' hg'P n₁ g₁' hn₁ hg₁' (hpn.trans hpg'.symm)
    exact ⟨n₁, hN.2.2.2.2 k hk n₀ hn₀ n₁ hn₁, e2.trans e1.symm⟩

end GlobalTheory.HoweRealKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPai
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweRealSmall

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

private theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

private theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have e := RingHom.map_det τ J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

private theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

private theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

private theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

private theorem actsD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(T t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  simp only [e, map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

theorem howe_real_ker' : GlobalTheory.Published.HoweDualityReal →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM
  have hT := hM.triple
  have hg := hT.geo
  have hc := hT.chars
  have hR := hM.real
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have dV' : G.V'.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 1 (by rw [one_smul]; exact hg.hV'.sig w₀)
  have dW : G.W.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 Complex.I (hg.hW.sig w₀)
  have hres := resEta_div hc.resα hc.resβ (Nat.add_comm a a')
  have hhk := hecke_div hc.heckeα hc.heckeβ
  obtain ⟨hbdd, hsum⟩ := hHD F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hLie := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hCpt := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  refine ⟨hbdd, ?_⟩
  intro N hN hNe φ hφ
  set K : Submodule ℂ (SInf F (Fin a' × Fin (a + a'))) := LinearMap.ker R.p' ⊓ G.M'.Pol Bs.ψ Bs.emb with hKdef
  have hK : GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' K := by
    refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
    · intro γ hγ f hf f₁ hact
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hR.quot'.lie γ hγ f hf f₁ hact), hN.1 (hN.2.1 γ hγ f hf f₁ hact)⟩
    · intro k hk f hf f₁ hact
      refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, hN.1 (hN.2.2.1 k hk f hf f₁ hact)⟩
      rw [map_sub, hR.quot'.cpt k hk f hf f₁ hact, sub_self]
    · intro γ hγ f hf f₁ hact
      have hf' := Submodule.mem_inf.1 hf
      have hp := hR.lie γ hγ 0 (zero_mem _) f hf'.2 0 f₁
        (actsD_zero (fun t => om (1, γ (Multiplicative.ofAdd t)))) hact
        (by rw [map_zero]; exact (LinearMap.mem_ker.1 hf'.1).symm)
      rw [map_zero] at hp
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp.symm, (hLie γ hγ f hf'.2).2 f₁ hact⟩
    · intro k hk f hf f₁ hact
      have hf' := Submodule.mem_inf.1 hf
      have hp := hR.cpt k hk 0 (zero_mem _) f hf'.2 0 f₁ (acts_zero _) hact
        (by rw [map_zero]; exact (LinearMap.mem_ker.1 hf'.1).symm)
      rw [map_zero] at hp
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp.symm, (hCpt k hk f hf'.2).2 f₁ hact⟩
  have hKne : K ≠ G.M'.Pol Bs.ψ Bs.emb := by
    intro hKe
    have hbot : (G.M'.Pol Bs.ψ Bs.emb).map R.p' = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨f, hf, rfl⟩
      rw [← hKe] at hf
      exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 hf).1
    rw [hR.quot'.onto] at hbot
    haveI := hR.nontriv
    exact top_ne_bot hbot
  have hNK : N ⊔ K ≠ G.M'.Pol Bs.ψ Bs.emb := hsum N K hN hK hNe hKne
  rcases hR.irred (N.map R.p') (by
    intro γ hγ f hf f₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    obtain ⟨n₁, hactn⟩ := (hLie γ hγ n (hN.1 hn)).1
    rw [hR.lie γ hγ f hf n (hN.1 hn) f₁ n₁ hact hactn hpn.symm]
    exact Submodule.mem_map_of_mem (hN.2.2.2.1 γ hγ n hn n₁ hactn)) (by
    intro k hk f hf f₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    obtain ⟨n₁, hactn⟩ := (hCpt k hk n (hN.1 hn)).1
    rw [hR.cpt k hk f hf n (hN.1 hn) f₁ n₁ hact hactn hpn.symm]
    exact Submodule.mem_map_of_mem (hN.2.2.2.2 k hk n hn n₁ hactn)) with h0 | htop
  · have hmem : R.p' φ ∈ N.map R.p' := Submodule.mem_map_of_mem hφ
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  · exfalso
    apply hNK
    refine le_antisymm (sup_le hN.1 inf_le_right) ?_
    intro f hf
    have hm : R.p' f ∈ N.map R.p' := by rw [htop]; exact Submodule.mem_top
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hm
    have hk : f - n ∈ K :=
      Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hpn, sub_self]), sub_mem hf (hN.1 hn)⟩
    have := Submodule.add_mem_sup hn hk
    rwa [add_sub_cancel] at this

end GlobalTheory.HoweRealSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumPlacesUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.IdemSumSet

theorem subset_of_isIdemSum {D : D7} {e : Formalism.L2.Theta.AE D} {P P' : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : Formalism.IndefR.Datum.IsIdemSum e P) (h' : Formalism.IndefR.Datum.IsIdemSum e P') : P ⊆ P' := by
  intro w hw
  obtain ⟨⟨es, hes, he⟩, -⟩ := h
  obtain ⟨⟨fs, hfs, hf⟩, -⟩ := h'
  have hw' := hes w hw

  have hpick : es w * e = es w := by
    rw [he, Finset.mul_sum, Finset.sum_eq_single w]
    · exact hw'.1.1
    · intro v hv hvw
      exact (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ w v hw' (hes v hv)).2 (Ne.symm hvw)
    · intro hn
      exact absurd hw hn

  by_contra hout
  apply GlobalTheory.LevelPlaces.ne_zero_of_isIdemAt hw'
  rw [← hpick, hf, Finset.mul_sum]
  refine Finset.sum_eq_zero fun v hv => ?_
  refine (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ w v hw' (hfs v hv)).2 ?_
  rintro rfl
  exact hout hv

theorem places_eq_of_isIdemSum : ∀ (D : D7) (e : AE D) (P P' : Finset (Pl D.host.E)), IsIdemSum e P → IsIdemSum e P' → P = P' := by
  intro D e P P' h h'
  ext w
  exact ⟨fun hw => subset_of_isIdemSum h h' hw, fun hw => subset_of_isIdemSum h' h hw⟩

end GlobalTheory.IdemSumSet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRowFlagTiltUniqueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRowFlagTilt_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {j : ℕ} (hj : j < D.R.m)
    (δ δ' : GA D (G.V (.grid D.R.m j))), IsTilt G j δ → IsTilt G j δ' → δ = δ' := by
  first | exact @GlobalTheory.TiltUnique.tilt_unique | exact GlobalTheory.TiltUnique.tilt_unique | (intros; apply GlobalTheory.TiltUnique.tilt_unique <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorDownwardArrowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_fock_vector_downward_arrow : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (ρ : RealMatch W)
    (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m → ∀ {e : AE D}, IsIdemSum e (locPl G t) →
    ∀ {φ f : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ}, IsLocVec W (.mu t i j) e (vacOf ρ (.down t i j)) φ f →
    ∀ Q : PolF D (G.pT (.mu t i j)).rank (G.pS (.mu t i j)).rank,
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) (W.fock (.mu t i j) f Q) := by
  first | exact @GlobalTheory.DownFock.isThetaFunO_fock_down | exact GlobalTheory.DownFock.isThetaFunO_fock_down | (intros; apply GlobalTheory.DownFock.isThetaFunO_fock_down <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorRightwardArrowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_fock_vector_rightward_arrow : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} {W : G'.Weil}, W.Over R → ∀ (ρ : RealMatch W), RealMatch.Over R ρ → ∀ (t : T) (i j : ℕ), i < D.R.m → j ≤ D.R.m → ∀ e, IsIdemSum e (locPl G' t) → ∀ φ f, IsLocVec W (.chi i j) e (vacOf ρ (.right i j)) φ f → ∀ Q : PolF D (G'.pT (.chi i j)).rank (G'.pS (.chi i j)).rank, IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) (W.fock (.chi i j) f Q) := by
  first | exact @GlobalTheory.RowFock.isThetaFunO_fock_right | exact GlobalTheory.RowFock.isThetaFunO_fock_right | (intros; apply GlobalTheory.RowFock.isThetaFunO_fock_right <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTypeAtDualParIffStarIsTypeAtStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTypeAt_dualPar_iff_star_isTypeAt : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (P : SPar) (φ : GA D V → ℂ), IsTypeAt θ V τ (Formalism.IndefR.Mult.dualPar P) φ ↔ IsTypeAt θ V τ P fun g => star (φ g) := by
  first | exact @GlobalTheory.TypeConj.isTypeAt_dualPar_iff | exact GlobalTheory.TypeConj.isTypeAt_dualPar_iff | (intros; apply GlobalTheory.TypeConj.isTypeAt_dualPar_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedInvariantIntegralDoubleCosetCellSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedInvariantIntegral_doubleCoset_cellSum : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)), (∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧ (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) → ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ), (∀ β ∈ S, ∀ i, i ∉ l → b β i = 1) → (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q → (∀ h, (∀ i, i ∉ l → h i = 1) → q h ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) h) → NIter ρ μ q l 1 (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  first | exact @GlobalTheory.RowVal.niter_cellSum | exact GlobalTheory.RowVal.niter_cellSum | (intros; apply GlobalTheory.RowVal.niter_cellSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowMovedVacuumEqUnitMulChosenStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_moved_vacuum_eq_unit_mul_chosen : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ i : ℕ, i < D.R.m → ∃ κ : ℂˣ, ch.W.om (.chi i D.R.m) (ch.G.toPair (.chi i D.R.m) (ch.S.N.u (Pair.chi i D.R.m : Pair T).small).1 (ch.S.N.u (Pair.chi i D.R.m : Pair T).big).1) (ch.S.Z.vac (.chi i D.R.m)) = (κ : ℂ) • ch.rm.vX i D.R.m := by
  first | exact @GlobalTheory.RowVac.moved_vac_eq | exact GlobalTheory.RowVac.moved_vac_eq | (intros; apply GlobalTheory.RowVac.moved_vac_eq <;> assumption)
end

