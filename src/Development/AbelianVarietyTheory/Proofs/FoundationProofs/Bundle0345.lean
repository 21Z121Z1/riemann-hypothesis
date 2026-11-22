import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetModuleMaximalParabolicPrincipalSeriesTypeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfMemTwistedJacquetKernelUpperUnitriangula
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem eq_zero_of_mem_twKer_unipB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  intro k _ _ _ _ n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ψ V _ _ π hπ hψ hord v hv heig
  rcases GlobalTheory.T.orderedCharacterFamily_splits_or_constant_on_units k n ψ hord with ⟨r, hr0, hrn, hcut⟩ | ⟨χ, hχ, hag⟩
  swap
  · obtain ⟨hg, hth, -, -⟩ := GlobalTheory.T.principalSeriesType_data_depend_only_on_units k n ψ _ hag
    rw [hg, hth] at heig
    exact GlobalTheory.T.jacquetKernel_eigenvector_eq_zero_of_const_character k n χ V π hπ (hχ hψ) v hv heig
  obtain ⟨t, rfl⟩ : ∃ t, n = r + t := ⟨n - r, by omega⟩
  have ht : 0 < t := by omega
  set e := stdSum (rfl : r + t = r + t) with he
  set ψ₁ : Fin r → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd t i) with hψ₁
  set ψ₂ : Fin t → kˣ →* ℂˣ := fun i => ψ (Fin.natAdd r i) with hψ₂
  obtain ⟨ho₁, ho₂, hmem⟩ := GlobalTheory.T.blockDiagonal_principalSeriesCongruenceSubgroup_split k r t ψ hord hcut
  have hs₁ : ∀ i, IsSmoothChar (ψ₁ i) := fun i => hψ _
  have hs₂ : ∀ i, IsSmoothChar (ψ₂ i) := fun i => hψ _
  have one_grp : ∀ (m : ℕ) (φ : Fin m → kˣ →* ℂˣ), (1 : GL (Fin m) k) ∈ grp φ := by
    intro m φ
    refine ⟨(KO k (Fin m)).one_mem, fun i j hij => ?_⟩
    have h0 : ((1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j = 0 := by
      simp [Matrix.one_apply_ne (ne_of_lt hij)]
    rw [h0]
    exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
  let Q := twKer π (unipRad k (two e)) 1
  let ρ := jacU₂ e π
  have hρ : IsSmooth ρ := isSmooth_comp (isSmooth_jacU _ hπ) _ (continuous_leviTwo k)
  have hact : ∀ g w, ρ g (Q.mkQ w) = Q.mkQ (π (emb₂ k e g) w) := fun g w => rfl
  let P : Submodule ℂ V := (twKer (ρ.comp (MonoidHom.inl _ _)) (unipB k (Fin r)) 1 ⊔
      twKer (ρ.comp (MonoidHom.inr _ _)) (unipB k (Fin t)) 1).comap Q.mkQ
  have hP : twKer π (unipB k (Fin (r + t))) 1 ≤ P := by
    refine GlobalTheory.T.twistedJacquetKernel_twoBlock_unipotent_le_stages k r t V π P ?_ ?_ ?_
    · intro w hw
      refine Submodule.mem_comap.2 ?_
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero Q).2 hw]
      exact zero_mem _
    · intro u hu w
      refine Submodule.mem_comap.2 ?_
      refine Submodule.mem_sup_left (Submodule.subset_span ⟨⟨u, hu⟩, Q.mkQ w, ?_⟩)
      simp only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]
      rfl
    · intro u hu w
      refine Submodule.mem_comap.2 ?_
      refine Submodule.mem_sup_right (Submodule.subset_span ⟨⟨u, hu⟩, Q.mkQ w, ?_⟩)
      simp only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]
      rfl
  have hx := hP hv
  have hzero : Q.mkQ v = 0 := by
    refine GlobalTheory.T.twistedJacquet_survival_product_of_two_groups (GL (Fin r) k) (GL (Fin t) k) _ ρ hρ (unipB k (Fin r)) (unipB k (Fin t))
      (grp ψ₁) (grp ψ₂) (theta ψ₁) (theta ψ₂)
      (fun W _ _ σ hσ w hw hwe => ih r (by omega) ψ₁ W σ hσ hs₁ ho₁ w hw hwe)
      (fun W _ _ σ hσ w hw hwe => ih t (by omega) ψ₂ W σ hσ hs₂ ho₂ w hw hwe)
      (Q.mkQ v) hx ?_ ?_
    · intro a ha
      have hm : emb₂ k e (a, 1) ∈ grp ψ := (hmem a 1).2 ⟨ha, one_grp _ _⟩
      have hth := GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal k r t ψ hord a ha 1 (one_grp _ _)
      rw [(GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k t ψ₂ hs₂).1, mul_one] at hth
      show ρ (a, 1) (Q.mkQ v) = _
      rw [hact, heig _ hm, map_smul]
      exact congrArg (· • Q.mkQ v) hth
    · intro b hb
      have hm : emb₂ k e (1, b) ∈ grp ψ := (hmem 1 b).2 ⟨one_grp _ _, hb⟩
      have hth := GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal k r t ψ hord 1 (one_grp _ _) b hb
      rw [(GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k r ψ₁ hs₁).1, one_mul] at hth
      show ρ (1, b) (Q.mkQ v) = _
      rw [hact, heig _ hm, map_smul]
      exact congrArg (· • Q.mkQ v) hth
  have hvQ : v ∈ Q := (Submodule.Quotient.mk_eq_zero Q).1 hzero
  exact GlobalTheory.T.jacquetModule_maximalParabolic_principalSeriesTypeEigen k r t ψ V π hπ hψ hord hcut v hvQ heig

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaInertPlace
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

noncomputable section
namespace GlobalTheory.InertIwasawaGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_trace_one_loc {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) :
    ∃ τ ∈ intLoc F E v, τ + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ τ = 1 := by
  have hu := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.InertChart.exists_conj_sub_unit h hw
  have hσ := GlobalTheory.LFun.InertChart.conj_conj h
  have h0 : σ (x : E) - x ≠ 0 := by
    intro e; rw [e, map_zero] at hx; exact zero_ne_one hx
  set t : E := σ x / (σ x - x) with ht
  have hsum : t + σ t = 1 := by
    rw [ht, map_div₀, map_sub, hσ, ← neg_sub (σ (x : E)) x, div_neg, ← sub_eq_add_neg, ← sub_div, div_self h0]
  refine ⟨(1 : Fv F v) ⊗ₜ[F] t, ?_, ?_⟩
  · rw [GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hu, GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]
    have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    change Valued.v (algebraMap E (w.adicCompletion E) t) ≤ 1
    rw [hval, ht, map_div₀, hx, div_one]
    exact w.valuation_le_one (RingOfIntegers.mapRingHom (σ : E →+* E) x)
  · change (1 : Fv F v) ⊗ₜ[F] t + 1 ⊗ₜ[F] σ t = 1
    rw [← TensorProduct.tmul_add, hsum]; rfl

open GlobalTheory.LFun GlobalTheory.InertIwasawa in

theorem hasIwasawa_of_inertAt {σ : E →ₐ[F] E} (hC : IsCMExt F E σ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hL : IsSelfDualAt σ J L v) : HasIwasawa σ Q (KFin σ Q L v) := fun g => by
  have h := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨τ, hτO, hτ⟩ := exists_trace_one_loc hC hw
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have eQ : JR (F := F) (Fv F v) Q = dblGram finSumFinEquiv (JR (Fv F v) J) := hQ ▸ JR_dblGram _ J
  obtain ⟨k, h1, h2, h3⟩ := exists_stab finSumFinEquiv (intLoc F E v)
    (hasFrames_of_equiv _ (w.adicCompletionIntegers E) (InertChart.complEquiv hw h) (InertChart.mem_intLoc_iff hw h))
    (σ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (fun _ => sigR_mem_intLoc σ) (sigR_invol (InertChart.conj_conj hC))
    hτO hτ
    (J := JR (Fv F v) J) (by ext i j; exact congrArg (fun x => (1 : Fv F v) ⊗ₜ[F] x) (hJ.1 i j))
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_JR hJ.2)) (Λ := latLoc F L v)
    (fun y => Submodule.ext_iff.1 hL y) (ha v) (g := matHom _ σ Q g) (eQ ▸ g.2)
  let κ : GLoc σ Q v := ⟨k, (eQ ▸ h1 : k ∈ Formalism.UG.UJ _ (JR (Fv F v) Q))⟩
  have hκ : κ ∈ KFin σ Q L v := by
    change k ∈ Formalism.UG.stabGL _
    rwa [latLoc_sumLat]
  exact ⟨⟨g * κ, h3⟩, κ⁻¹, inv_mem hκ, (mul_inv_cancel_right g κ).symm⟩

theorem ioH_mem_siegel_mul_KFin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)),
    IsSelfDualAt σ J L v → ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ g : GLoc σ J v,
      ∃ p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J), ∃ k ∈ KFin σ (dblGram finSumFinEquiv J) L v,
        ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v hL P hP g
  exact hasIwasawa_of_inertAt h hJ rfl (w := P) hP hL _

end GlobalTheory.InertIwasawaGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaSplitPlace
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

namespace GlobalTheory.GraphIwSplit

theorem isHermND_dblGram {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : IsHermND σ (dblGram finSumFinEquiv J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
    simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;> simp [hJ.1]
  · rw [dblGram, det_blkMat]
    exact mul_ne_zero hJ.2 (by rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by simp)) hJ.2)

theorem graph_iwasawa_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), IsSelfDualAt σ J L v → Nonempty (E →ₐ[F] Fv F v) → ∀ g : GLoc σ J v, ∃ p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J), ∃ k ∈ KFin σ (dblGram finSumFinEquiv J) L v, ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v hL ⟨τ⟩ g
  exact GlobalTheory.Core.Rk.IwSplit.hasIwasawa_of_algHom h rfl hJ (isHermND_dblGram σ hJ) τ L hL _

end GlobalTheory.GraphIwSplit
end

