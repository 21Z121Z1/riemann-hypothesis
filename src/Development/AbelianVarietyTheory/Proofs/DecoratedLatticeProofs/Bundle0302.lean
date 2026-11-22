import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0064
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0288
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CexpTwoPiINegInvNatSmulAddStar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0246
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsCombAt
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.CombAt

theorem exists_isCombAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)
    (Ξ : Matrix Y Y' k → ℂ) : ∃ c : WO S T →₀ ℂ, p.IsCombAt ψ FS FT c Ξ := by
  by_cases h : ∃ Φ : SB (Matrix Y Y' k), Φ.1 = Ξ
  · obtain ⟨Φ, hΦ⟩ := h
    obtain ⟨O, hO, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
    have hne : O ≠ 0 := by
      rintro rfl
      simp at hO0
    obtain ⟨c, h1, h2⟩ := GlobalTheory.LocComb.exists_comb D k p Y Y' S T FS FT ψ hψ O Φ hne
    refine ⟨c, h1, fun Tm hT Φ₀ Φ' h₀ h' => ?_⟩
    obtain rfl : Φ' = Φ := Subtype.ext (h'.trans hΦ.symm)
    obtain rfl : Φ₀ = O := Subtype.ext (h₀.trans hO.symm)
    exact h2 Tm hT
  · exact ⟨0, by simp, fun Tm _ Φ₀ Φ _ h' => (h ⟨Φ, h'⟩).elim⟩

theorem exists_cg : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (q : GlobalTheory.FinPl.SplitPt D k) (s : ℕ) (S : SymData k s D.R.k) (FX : ∀ j, j ≤ s + 1 → GlobalTheory.LocMod.Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)) (FM : GlobalTheory.LocMod.Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)), IsStdChar D d.c.ψ (-1) → ∃ cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ j c (H : j + 1 + c = s), (ofSplit q).IsCombAt d.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j) ((S.T (Fin D.R.t)).entry S.ψ ν j c H 1 1)) ∧ (ofSplit q).IsCombAt d.c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s) (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))) ∧ (ofSplit q).IsCombAt d.c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1)) ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t)))) := by
  intro D u d k _ _ _ _ _ _ ν q s S FX FM hψ
  obtain ⟨c₁, h₁⟩ := exists_isCombAt (ofSplit q) hψ (FX s (by omega)) (FX (s + 1) le_rfl)
    (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t)))
  obtain ⟨c₂, h₂⟩ := exists_isCombAt (ofSplit q) hψ (FX (s + 1) le_rfl) FM
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))
  have key : ∀ j, ∃ c : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ,
      (∀ c' (H : j + 1 + c' = s), (ofSplit q).IsCombAt d.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) c
        ((S.T (Fin D.R.t)).entry S.ψ ν j c' H 1 1)) ∧ (j = s → HEq c c₁) ∧ (j = s + 1 → HEq c c₂) := by
    intro j
    by_cases hj : j < s
    · obtain ⟨c', H⟩ : ∃ c', j + 1 + c' = s := ⟨s - j - 1, by omega⟩
      obtain ⟨c, hc⟩ := exists_isCombAt (ofSplit q) hψ (FX j (by omega)) (FX (j + 1) (by omega))
        ((S.T (Fin D.R.t)).entry S.ψ ν j c' H 1 1)
      refine ⟨c, fun c'' H' => ?_, fun h => by omega, fun h => by omega⟩
      obtain rfl : c'' = c' := by omega
      exact hc
    · by_cases h1 : j = s
      · subst h1
        exact ⟨c₁, fun c' H => by omega, fun _ => HEq.rfl, fun h => by omega⟩
      · by_cases h2 : j = s + 1
        · subst h2
          exact ⟨c₂, fun c' H => by omega, fun h => by omega, fun _ => HEq.rfl⟩
        · exact ⟨0, fun c' H => by omega, fun h => (h1 h).elim, fun h => (h2 h).elim⟩
  choose cg k1 k2 k3 using key
  refine ⟨cg, k1, ?_, ?_⟩
  · rw [eq_of_heq (k2 s rfl)]; exact h₁
  · rw [eq_of_heq (k3 (s + 1) rfl)]; exact h₂

end GlobalTheory.LocMod.CombAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRatOfSameOrb
section
open NumberField IsDedekindDomain Matrix ValuativeRel Formalism.L2.Col
open scoped Classical

namespace GlobalTheory.QPl.RatOrb
open GlobalTheory.StepData GlobalTheory.SplitWeil GlobalTheory.TwBridge.Lev GlobalTheory.TwBridge.LevOrb

theorem image_val_mem_nhds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {B : Type} [Fintype B] [DecidableEq B] {S : Set (GL B k)} (hS : IsOpen S) {h : GL B k} (hh : h ∈ S) :
    Units.val '' S ∈ nhds h.val := by
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hS
  have hd : h.val.det ≠ 0 := h.det_ne_zero
  have hc : ContinuousAt (Inv.inv : Matrix B B k → Matrix B B k) h.val := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  have hG : ContinuousAt (fun N : Matrix B B k => (N, MulOpposite.op N⁻¹)) h.val :=
    continuousAt_id.prodMk (MulOpposite.continuous_op.continuousAt.comp hc)
  have key : ∀ u : GL B k, Units.embedProduct _ u = (u.val, MulOpposite.op u.val⁻¹) := fun u => by
    rw [Units.embedProduct_apply, Matrix.coe_units_inv]
  have h1 := hG.preimage_mem_nhds (hW.mem_nhds (by rw [← key]; exact hh))
  have h2 : {N : Matrix B B k | N.det ≠ 0} ∈ nhds h.val :=
    (isOpen_ne.preimage (continuous_id.matrix_det)).mem_nhds hd
  filter_upwards [h1, h2] with N hN1 hN2
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero N hN2, ?_, rfl⟩
  rw [Set.mem_preimage, key]
  exact hN1

theorem exists_rat_of_sameOrb : ∀ {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P (qOf P) ι ϖ → ∀ {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (e : A ≃ Fin n) (Jl : Subgroup (GL (A ⊕ Fin 0) k)), IsOpen (Jl : Set (GL (A ⊕ Fin 0) k)) → Jl ≤ GlobalTheory.SplitWeil.KO k (A ⊕ Fin 0) → ∀ (M : ℕ) (c : (A → k) ⧸ GlobalTheory.StepData.box A (ϖ ^ M)) (y₀ : Sp E n), GlobalTheory.QPl.SameOrb Jl (GlobalTheory.StepData.box A (ϖ ^ M)) c (Submodule.Quotient.mk fun a => ι (y₀ (e a))) → ∃ r ∈ GLint E n P, ∃ g ∈ Jl, g.val.toBlocks₁₁ = GlobalTheory.SymBridge.toLoc ι e e r.toLinearMap ∧ ∀ y : Sp E n, ((qOf P : E) ^ M)⁻¹ • (r.symm y - y₀) ∈ stdAt E n P → c = Submodule.Quotient.mk fun a => ι (y (e a)) := by
  intro E k _ _ _ _ _ _ _ P ι ϖ hc A _ _ n e Jl hJo hJ M c y₀
  rintro ⟨g₀, hg₀, y₁, rfl, hy⟩
  rw [Submodule.Quotient.eq] at hy
  let e' : A ⊕ Fin 0 ≃ Fin n := (Equiv.sumEmpty A (Fin 0)).trans e
  have he : ∀ a, e' (.inl a) = e a := fun a => rfl
  have h0 : (g₀⁻¹).val.toBlocks₁₁ *ᵥ (fun a => ι (y₀ (e a))) - y₁ ∈ box A (ϖ ^ M) := by
    have := neg_mem (GlobalTheory.TwBridge.LevOrb.mulVec_mem_box (hJ (inv_mem hg₀)) _ hy)
    rwa [mulVec_sub, mulVec_mulVec, ← CoupStab.toBlocks₁₁_mul, Units.inv_mul, CoupStab.toBlocks₁₁_one, one_mulVec,
      neg_sub] at this
  have hU2 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k |
      N.toBlocks₁₁ *ᵥ (fun a => ι (y₀ (e a))) - y₁ ∈ box A (ϖ ^ M)} := by
    refine (CoupStab.isOpen_box (ϖ ^ M)).preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k =>
      N.toBlocks₁₁ *ᵥ (fun a => ι (y₀ (e a))) - y₁) ?_
    have hb : Continuous fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => N.toBlocks₁₁ :=
      continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inl i) (Sum.inl j)
    exact (hb.matrix_mulVec continuous_const).sub continuous_const
  obtain ⟨U, hU, hUo, hUm⟩ := mem_nhds_iff.1 (image_val_mem_nhds hJo (inv_mem hg₀))
  obtain ⟨M₀, ⟨a1, a2⟩, -⟩ := exists_approx ι hc.dense (g₀⁻¹).val (hUo.inter hU2) ⟨hUm, h0⟩
  obtain ⟨g, hg, ev⟩ := hU a1
  obtain ⟨r, hr⟩ := exists_phi ι e' M₀ g ev
  refine ⟨r, (GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO P ι hc.int e' r).2 ?_, g, hg, ?_, fun y hy' => ?_⟩
  · rw [show GlobalTheory.VolBridge.locHom ι e' r = phi ι e' r from Units.ext rfl, hr]
    exact hJ hg
  · rw [← hr]
    rfl
  · have h1 := GlobalTheory.TwBridge.LevOrb.mulVec_mem_box (hJ hg) _ ((mem_box_iff hc e M _).2 hy')
    rw [Set.mem_setOf_eq, ← ev] at a2
    rw [← hr, phi_mulVec e e' he] at h1 a2
    rw [eq_comm, Submodule.Quotient.eq]
    convert add_mem h1 a2 using 1
    funext a
    simp

end GlobalTheory.QPl.RatOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBesUnscaledDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Unscaled

variable {D : D7}

def rescale {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (μ : D.host.E) (hμ : μ ≠ 0) : HypDec S S₀ ρ where
  e := μ • d.e
  e' := (star μ)⁻¹ • d.e'
  i₀ := d.i₀
  ee := by simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, d.ee, smul_zero]
  e'e' := by simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, d.e'e', smul_zero]
  e'e := by
    simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, d.e'e, smul_smul, star_inv₀, star_star,
      mul_inv_cancel₀ hμ, one_smul]
  iso := d.iso
  i₀e := by simp only [Matrix.mul_smul, d.i₀e, smul_zero]
  i₀e' := by simp only [Matrix.mul_smul, d.i₀e', smul_zero]
  rank_add := d.rank_add

end GlobalTheory.Core.Mi.Unscaled

namespace GlobalTheory.Core.Mi

open GlobalTheory.Core.SBesEx GlobalTheory.Core.Mi.Unscaled in

theorem exists_sBes_scaled_dual : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀), IdE X → IsStdChar D ψ (-1) → ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∀ (μ : D.host.E) (vA : Vol (D.sp.X 0)), μ ≠ 0 → ∃ B : SBes X h u ψ (D.sp.X 0), B.Adapted tr.wt ∧ B.vA = vA ∧ (∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) ∧ (∀ k (a : Fin D.R.rS), B.d.e k a = μ * lam ^ (D.R.rS - (a : ℕ)) * X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) ∧ ∀ k (a : Fin D.R.rS), B.d.e' k a = (star (μ * lam ^ (D.R.rS - (a : ℕ))))⁻¹ * X.ιE (X.fR a (Fin.cast (rank_eq X h) k)) := by
  intro D X h u ψ F₀ tr hE hψ
  obtain ⟨lam, hlam, hP⟩ := GlobalTheory.Core.Mi.tiepsi_sign D X h u ψ hE hψ
  have hg : ((X.B.g : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.Pf.modulus_g_ne_zero X)
  have hl0 : lam ≠ 0 := by
    rcases hlam with hl | hl <;> rw [hl]
    · exact hg
    · exact neg_ne_zero.2 hg
  refine ⟨lam, hlam, fun μ vA hμ => ?_⟩
  obtain ⟨L, t, ht, hL1, hz0, hLg⟩ := GlobalTheory.RankOneLine.exists_line D X u
  obtain ⟨⟨V₀, o⟩⟩ := GlobalTheory.OrthSumExists.exists_orthDec D (D.sp.X 0) L
  obtain ⟨d₀, hde, hde', hdi⟩ := GlobalTheory.Core.SBesEx.exists_hypDec D X h u F₀ tr t lam ht hl0 (GlobalTheory.Core.SBesEx.cY_isom D X h hE)
    (GlobalTheory.Core.Mi.transported_frame_gram_orth D X u F₀ tr) L hL1 hLg V₀ o
  have hcard : Fintype.card (Fin L.rank) = 1 := by rw [Fintype.card_fin, hL1]
  have hz₀ : d₀.i₀ *ᵥ vecB o (zeta L) = t • cY X h (X.zu u) := by
    rw [vecB, Matrix.mulVec_mulVec, hdi, i0M, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, o.qA_iB, o.qB_iB,
      Matrix.mul_zero, zero_add, Matrix.mul_one]
    funext k
    simp only [Matrix.mulVec, dotProduct, zM, zeta, mul_one, Finset.sum_const, Finset.card_univ, hcard, one_smul,
      Pi.smul_apply, smul_eq_mul]
  have hline₀ : IsLineVec L (zeta L) := by
    refine ⟨hL1, ?_⟩
    simp only [zeta, hLg, dotProduct, Matrix.mulVec, Pi.star_apply, star_one, one_mul, mul_one, Finset.sum_const,
      Finset.card_univ, hcard, one_smul]
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 ht) ht) hz0
  have ht' : μ * t⁻¹ ≠ 0 := mul_ne_zero hμ (inv_ne_zero ht)
  set d := rescale d₀ (μ * t⁻¹) ht' with hd
  set ζ : Fin L.rank → D.host.E := (μ * t⁻¹) • zeta L with hζ
  have hline : IsLineVec L ζ := by
    refine ⟨hline₀.1, ?_⟩
    rw [hζ, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    exact mul_ne_zero (star_ne_zero.2 ht') (mul_ne_zero ht' hline₀.2)
  have hde1 : d.e = eM X h μ lam := by
    funext k a
    show ((μ * t⁻¹) • d₀.e) k a = _
    rw [hde]
    simp only [Matrix.smul_apply, eM, scl, smul_eq_mul]
    field_simp
  have hde1' : d.e' = e'M X h μ lam := by
    funext k a
    show ((star (μ * t⁻¹))⁻¹ • d₀.e') k a = _
    rw [hde']
    simp only [Matrix.smul_apply, e'M, scl, smul_eq_mul, star_mul', star_inv₀, inv_inv, mul_inv]
    have hst : star t ≠ 0 := star_ne_zero.2 ht
    field_simp
  have hz : d.i₀ *ᵥ vecB o ζ = μ • cY X h (X.zu u) := by
    show d₀.i₀ *ᵥ (o.iB *ᵥ ((μ * t⁻¹) • zeta L)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← vecB, hz₀, smul_smul, inv_mul_cancel_right₀ ht]
  refine ⟨SBes.mk V₀ L d o ζ hline (GlobalTheory.Unf.DefCpt.coCpt_X_zero D) vA
    (GlobalTheory.Unf.Inhab.nonempty_volN d).some (GlobalTheory.T.mem_flagUnipotentRadical_iff_secondModel D X h u μ lam hμ hl0 hE V₀ d hde1)
    (GlobalTheory.T.range_besselAnisotropicEmbedding_eq_secondModelSubgroup D X h u μ lam hμ hl0 hE V₀ L d o ζ hline hde1 hde1' hz)
    (hP μ hμ V₀ L d o ζ hde1 hde1' hz), ?_, rfl, ?_, ?_, ?_⟩
  · intro k j
    show (d₀.i₀ * o.iA) k j = _
    rw [hdi, i0M, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, o.qA_iA, o.qB_iA, Matrix.mul_zero, add_zero,
      Matrix.mul_one]
    rfl
  · intro k
    show (d.i₀ *ᵥ vecB o ζ) k = _
    rw [hz]
    rfl
  · intro k a
    show d.e k a = _
    rw [hde1]
    rfl
  · intro k a
    show d.e' k a = _
    rw [hde1']
    rfl

theorem exists_sBes_unscaled_dual : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀), IdE X → IsStdChar D ψ (-1) → ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∃ B : SBes X h u ψ (D.sp.X 0), B.Adapted tr.wt ∧ (∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) ∧ (∀ k (a : Fin D.R.rS), B.d.e k a = lam ^ (D.R.rS - (a : ℕ)) * X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) ∧ ∀ k (a : Fin D.R.rS), B.d.e' k a = (star (lam ^ (D.R.rS - (a : ℕ))))⁻¹ * X.ιE (X.fR a (Fin.cast (rank_eq X h) k)) := by
  intro D X h u ψ F₀ tr hE hψ
  obtain ⟨lam, hlam, hB⟩ := exists_sBes_scaled_dual D X h u ψ F₀ tr hE hψ
  obtain ⟨B, hA, -, hz, he, he'⟩ := hB 1 (GlobalTheory.Unf.Inhab.nonempty_vol _).some one_ne_zero
  simp only [one_mul] at hz he he'
  exact ⟨lam, hlam, B, hA, hz, he, he'⟩

theorem exists_sBes_unscaled : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀), IdE X → IsStdChar D ψ (-1) → ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∃ B : SBes X h u ψ (D.sp.X 0), B.Adapted tr.wt ∧ (∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) ∧ ∀ k (a : Fin D.R.rS), B.d.e k a = lam ^ (D.R.rS - (a : ℕ)) * X.ιE (X.eR a (Fin.cast (rank_eq X h) k)) := by
  intro D X h u ψ F₀ tr hE hψ
  obtain ⟨lam, hlam, B, hA, hz, he, -⟩ := exists_sBes_unscaled_dual D X h u ψ F₀ tr hE hψ
  exact ⟨lam, hlam, B, hA, hz, he⟩

end GlobalTheory.Core.Mi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitWeightRealCenterActionFockMonomial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CenFockWt

theorem central_wt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ wt : (FVar D T.rank S.rank →₀ ℕ) → GA D S → ℂ, (∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖wt α z‖ = 1 ∧ ∀ c : WO S T →₀ ℂ, IsFinComb c → k.om (z, 1) (pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) = wt α z • pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) ∧ ∀ χ : GA D S → ℂ, {α | ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z}.Finite := by
  intro D ψ θ hθ S T x y hx hy k hk
  classical
  obtain ⟨χS, χT, hW⟩ := hk.weil
  have hstd : IsStdChar D ψ (-1) := hk.vac.1
  have hvth : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_realCentre_character_on_definiteVacuum D ψ θ hθ S T x y hx hy k hk
  set ζ : GA D S → D.what₂.Tau → ℂ := fun z τ =>
    if h : 0 < S.rank then compAt θ τ (Formalism.L2.Theta.mt S z) ⟨0, h⟩ ⟨0, h⟩ else 1 with hζdef
  set μ : GA D S → D.what₂.Tau → ℂ := fun z τ => if (x.s τ = 1 ↔ y.s τ = 1) then (ζ z τ)⁻¹ else ζ z τ with hμdef
  set deg : D.what₂.Tau → (FVar D T.rank S.rank →₀ ℕ) → ℕ := fun τ α => ∑ v ∈ α.support with v.1 = τ, α v with hdeg
  have hζ : ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ,
      ‖ζ z τ‖ = 1 ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ z τ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
    intro z hz hzc τ
    obtain ⟨ζ', h1, h2⟩ := GlobalTheory.T.realComponent_central_definiteUnitary_eq_unit_scalar D θ hθ S x hx z hz hzc τ
    by_cases h : 0 < S.rank
    · have e : ζ z τ = ζ' := by
        simp only [hζdef, dif_pos h, h2, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rw [e]; exact ⟨h1, h2⟩
    · have e : ζ z τ = 1 := by simp only [hζdef, dif_neg h]
      refine ⟨by rw [e, norm_one], ?_⟩
      ext i
      exact absurd i.2 (by omega)
  have hμ : ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ, ‖μ z τ‖ = 1 := by
    intro z hz hzc τ
    simp only [hμdef]
    split_ifs
    · rw [norm_inv, (hζ z hz hzc τ).1, inv_one]
    · exact (hζ z hz hzc τ).1
  have hT1 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have comb_smul : ∀ (cc : WO S T →₀ ℂ) (a : ℂ) (g : WO S T → ℂ), comb ψ S T cc (a • g) = a • comb ψ S T cc g := by
    intro cc a g
    unfold comb
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have : heisO ψ S T u (a • g) = a • heisO ψ S T u g := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, smul_comm]
  refine ⟨fun α z => c z * ∏ τ, μ z τ ^ deg τ α, ?_, ?_⟩
  · intro α z hz hzc
    refine ⟨?_, ?_⟩
    · rw [norm_mul, (hc z hz hzc).1, one_mul, norm_prod]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [norm_pow, hμ z hz hzc τ, one_pow]
    · intro cc hcc
      set F := pureTensorO ψ θ S T x.s y.s x.B y.B with hF
      have hcomb : ∀ g, comb ψ S T cc g = ∑ i : Fin cc.support.card,
          cc (cc.support.equivFin.symm i) • heisO ψ S T (cc.support.equivFin.symm i) g := by
        intro g
        unfold comb
        rw [← Finset.sum_coe_sort]
        exact (Equiv.sum_comp cc.support.equivFin.symm (fun u => cc u • heisO ψ S T u g)).symm
      have key1 : ∀ g, IsThetaFunO ψ S T g → ∀ P, F (comb ψ S T cc g) P = comb ψ S T cc (F g P) := by
        intro g hg P
        rw [hcomb, hcomb]
        exact (GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D ψ θ S T hstd hθ x.s y.s x.B y.B g hg cc.support.card _ _
          (fun i => hcc _ (Finset.coe_mem _)) P).1.symm
      have hop := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT k.om hW hθ x.s x.s x.B (fun τ => ζ z τ • x.B τ)
        y.s y.s y.B y.B z 1
        (fun τ => by rw [(hζ z hz hzc τ).2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [hT1, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [(hζ z hz hzc τ).2, Matrix.smul_mul, Matrix.one_mul])
        (fun τ => by rw [hT1, Matrix.one_mul]) k.vac hvth (MvPolynomial.monomial α 1)
      rw [key1 k.vac hvth, GlobalTheory.T.weilOperator_sourceRealPoint_commute_heisenbergComb D ψ S T χS χT k.om hW z hz cc hcc _ hop.1, hop.2, (hc z hz hzc).2,
        GlobalTheory.FiniteFock.pureTensorO_smul,
        GlobalTheory.T.pureTensorFock_unitScaledBasis_monomial D ψ θ hstd hθ S T x y hx hy k.vac hvth (ζ z) (fun τ => (hζ z hz hzc τ).1) α,
        smul_smul, comb_smul]
  · intro χ
    by_cases hne : ∃ α₀, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → c z * ∏ τ, μ z τ ^ deg τ α₀ = χ z
    · obtain ⟨α₀, hα₀⟩ := hne
      refine (GlobalTheory.T.finite_monomials_with_prescribed_placeDegree D T.rank S.rank (fun τ => deg τ α₀)).subset fun α hα τ => ?_
      show deg τ α = deg τ α₀
      by_cases hr : 0 < S.rank ∧ 0 < T.rank
      · obtain ⟨z, hz, hzc, h1, h2⟩ := GlobalTheory.T.exists_central_realPoint_unit_scalar_single_place D θ hθ S τ (Complex.exp Complex.I) (by simpa using Complex.norm_exp_ofReal_mul_I 1)
        have e := (hα z hz hzc).trans (hα₀ z hz hzc).symm
        have hc0 : c z ≠ 0 := by
          intro h0
          have := (hc z hz hzc).1
          rw [h0, norm_zero] at this
          exact zero_ne_one this
        have e2 := mul_left_cancel₀ hc0 e
        have hζρ : ∀ ρ, ρ ≠ τ → ζ z ρ = 1 := by
          intro ρ hρ
          simp only [hζdef, dif_pos hr.1, h2 ρ hρ, Matrix.one_apply_eq]
        have hζτ : ζ z τ = Complex.exp Complex.I := by
          simp only [hζdef, dif_pos hr.1, h1, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        have hμρ : ∀ ρ, ρ ≠ τ → μ z ρ = 1 := by
          intro ρ hρ
          simp only [hμdef, hζρ ρ hρ, inv_one, ite_self]
        rw [Finset.prod_eq_single τ (fun ρ _ hρ => by rw [hμρ ρ hρ, one_pow]) (by simp),
          Finset.prod_eq_single τ (fun ρ _ hρ => by rw [hμρ ρ hρ, one_pow]) (by simp)] at e2
        exact GlobalTheory.T.eq_of_pow_eq_pow_of_eq_exp_I_or_inv _ _ (μ z τ) (by
          simp only [hμdef, hζτ]
          split_ifs
          exacts [Or.inr rfl, Or.inl rfl]) e2
      · have hE : IsEmpty (FVar D T.rank S.rank) :=
          ⟨fun v => hr ⟨by have := v.2.2.2; omega, by have := v.2.1.2; omega⟩⟩
        simp only [hdeg, Finset.eq_empty_of_isEmpty α.support, Finset.eq_empty_of_isEmpty α₀.support,
          Finset.filter_empty, Finset.sum_empty]
    · refine Set.Finite.subset Set.finite_empty fun α hα => hne ⟨α, hα⟩

end GlobalTheory.CenFockWt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteElementsActFockVectorsThroughDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockFin

theorem pt_finite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T) (k : KerDat S T), x.Is → y.Is → k.Is ψ θ x y → ∀ P, IsThetaFunO ψ S T (k.pt ψ θ x y P) ∧ ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ p : ℂ, k.om (g, h) (comb ψ S T k.c k.vac) = p • comb ψ S T k.c k.vac → k.om (g, h) (k.pt ψ θ x y P) = p • k.pt ψ θ x y P := by
  intro D ψ θ hθ S T x y k _ _ hk P
  obtain ⟨χS, χT, hW⟩ := hk.weil
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hvac : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  have hc : IsThetaFunO ψ S T (comb ψ S T k.c k.vac) :=
    Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
      fun u hu => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hvac (hk.fin u hu))
  have hop : ∀ g ∈ GfC S, ∀ h ∈ GfC T,
      IsThetaFunO ψ S T (k.pt ψ θ x y P) ∧
        k.om (g, h) (k.pt ψ θ x y P) = pureTensorO ψ θ S T x.s y.s x.B y.B (k.om (g, h) (comb ψ S T k.c k.vac)) P :=
    fun g hg h hh => GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT k.om hW hθ x.s x.s x.B x.B y.s y.s y.B y.B g h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul]) _ hc P
  refine ⟨(hop 1 (one_mem _) 1 (one_mem _)).1, fun g hg h hh p hp => ?_⟩
  rw [(hop g hg h hh).2, hp, GlobalTheory.FiniteFock.pureTensorO_smul]
  rfl

end GlobalTheory.FockFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModel
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatBFLoc

theorem flatBF_of_laws : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatBF D := by
  intro D hFL hFLs hOm k _ _ _ _ _ _ p ν hν ψ ψk hψk ρ B J st s hs n n' _ _ _ _ c FA F₀ FV G₀ FW hco hbe hja Tm hTm
  obtain ⟨hcont, hne⟩ := (GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ st.weil.std).2.1 ψk hψk
  have hc : c = 2 * ρ := by have := hbe.1; omega
  let L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ) :=
    { toFun := fun Φ => flatBF st (Tm Φ)
      map_add' := fun Φ Φ' => by
        simp only [map_add]
        exact (GlobalTheory.T.besselToJacobiFlatSchwartz_linear D hFL ψ ρ B J st (Tm Φ) (Tm Φ') 1 (hTm.theta Φ) (hTm.theta Φ')).1
      map_smul' := fun a Φ => by
        simp only [map_smul, RingHom.id_apply]
        exact (GlobalTheory.T.besselToJacobiFlatSchwartz_linear D hFL ψ ρ B J st (Tm Φ) (Tm Φ) a (hTm.theta Φ) (hTm.theta Φ)).2 }
  obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.flatMap_fourierJacobi_factors_local_flat k ψk ν hcont hne hν n n' c ρ (WO B.V₀ J.W₀ → ℂ) L hc
    (GlobalTheory.T.localFlatMap_dualColumn_multiplicationLaws D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (GlobalTheory.T.flat_bessel_to_fourierJacobi_row_mul_laws D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (GlobalTheory.T.localFlatMap_freeEntry_translationLaws_besselToJacobi D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (GlobalTheory.T.besselFlatMap_local_unipotent_translation_law D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
  have hL : ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ := hL₀
  refine ⟨L₀, ⟨?_, ?_, ?_⟩, hL⟩
  · exact GlobalTheory.T.localFlatMap_factor_values_thetaFunctions D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL
  · exact GlobalTheory.T.localFlatMap_factor_intertwines_translations D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL
  · exact GlobalTheory.T.localFlatMap_factor_intertwines_multiplication D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL

end GlobalTheory.FlatBFLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarFiniteAdeleDisintegrationStabilizerCompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_finite_adele_disintegration_stabilizer_compact : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word), ∃ μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)), μSf.IsHaarMeasure ∧ SigmaFinite μSf ∧ ∃ c : ℝ, 0 < c ∧ ∀ φ : X.B.I.Gf → ENNReal, Measurable φ → (∀ x, φ x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x = s * X.xu u * k) → ∫⁻ x, φ x ∂X.B.μf = ENNReal.ofReal c * ∫⁻ t, ∫⁻ k in X.K2, φ (t.1 * X.xu u * k) ∂X.B.μf ∂μSf := by
  first | exact @GlobalTheory.SfinHaar.disint_finPart | exact GlobalTheory.SfinHaar.disint_finPart | (intros; apply GlobalTheory.SfinHaar.disint_finPart <;> assumption)
end

