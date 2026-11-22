import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0536
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsEqPureVacuumOfLatticeInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem invTwo_mem (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have h : evFin F v (⅟(2 : AF F)) * algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) = 1 := by
    rw [map_ofNat, map_ofNat, ← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hv : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F 2)) = 1 := by
    have := v.valuedAdicCompletion_eq_valuation' (K := F) (algebraMap (𝓞 F) F 2)
    rw [HeightOneSpectrum.valuation_of_algebraMap, (HeightOneSpectrum.intValuation_eq_one_iff).2 h2] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h' := congrArg (Valued.v : v.adicCompletion F → _) h
  rw [map_mul, map_one, hv, mul_one] at h'
  exact h'.le

private theorem smul_mem_lat {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : HeightOneSpectrum (𝓞 F)) {c : AF F}
    (hc : evFin F v c ∈ v.adicCompletionIntegers F) {γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)}
    (hγ : γ ∈ latAtV X W v) : c • γ ∈ latAtV X W v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨c * a, fun u hu => ?_, ?_, x, hx, y, hy, smul_smul _ _ _⟩
    · rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]; exact mul_mem hc hav
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg z _ h => rw [smul_neg]; exact neg_mem h

private theorem hTens_half {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n d : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (t : E →ₐ[F] Fv F v) (JA : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E))
    (JB : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) {γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)}
    (hγ : At (evFin F v) γ) (ht : γ.map (piW t) = 0) :
    GlobalTheory.WeilM.hTens (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) JA JB γ γ = 0 := by
  have h0 := GlobalTheory.SwapAtPlace.one_sub_smul hγ
  rw [sub_smul, one_smul, sub_eq_zero] at h0
  have ht' : ∀ i j, piW t (γ i j) = 0 := fun i j => congrFun (congrFun ht i) j
  have hσ : (t.comp σ).comp σ = t := GlobalTheory.AdelicU.comp_conj_conj h t
  unfold GlobalTheory.WeilM.hTens
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ =>
    Finset.sum_eq_zero fun l _ => ?_
  have h3 : GlobalTheory.LatVac.liftV v (1 : Fv F v) • γ i j = γ i j := (congrFun (congrFun h0 i) j).symm
  refine GlobalTheory.SwapAtPlace.eq_zero_of_piW h t ?_ ?_ ?_
  · rw [← smul_mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, h3]
  · rw [map_mul, map_mul, map_mul, ht', zero_mul, zero_mul, zero_mul]
  · rw [map_mul, GlobalTheory.SplitDict.piW_cA, hσ, ht', mul_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.exists_eq_pure_vacuum_of_lattice_invariant :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
        (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
        W.IsSkew σ B r' s' → M.IsGood B.ψ →
        ∀ Ψ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), (∀ v, ∀ γ ∈ latAtV X W v, M.co.rho B.ψ (2 • γ) Ψ = Ψ) →
        (∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v), ∀ γ ∈ latAtV X W v, γ.map (piW t) = 0 → M.co.rho B.ψ γ Ψ = Ψ) →
        ∃ g : SInf F (Fin n × Fin d), Ψ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hG Ψ hΨ h2 hh
  have hstd := hB.std
  obtain ⟨f, hf⟩ := GlobalTheory.T.adelicSchwartz_eq_pureTensor_of_finite_slices M.vac (fun v => (hG.vac v).2.1) hG.std Ψ hΨ fun v y hy => by
    let gen : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) :=
      {γ | (∃ γ' ∈ latAtV X W v, γ = 2 • γ') ∨ (γ ∈ latAtV X W v ∧ ∃ t : E →ₐ[F] Fv F v, γ.map (piW t) = 0)}
    have hsub : ∀ γ ∈ gen, γ ∈ latAtV X W v := by
      rintro γ (⟨γ', h, rfl⟩ | ⟨h, -⟩)
      · exact nsmul_mem h 2
      · exact h
    have hgen : latAtV X W v ≤ AddSubgroup.closure gen := by
      intro γ hγ
      by_cases hv : ∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w
      · haveI := hB.unram
        obtain ⟨t⟩ := GlobalTheory.SplitDict.nonempty_emb hB.cm v hv
        obtain ⟨γ₁, h₁, γ₂, h₂, rfl, e₁, e₂⟩ := GlobalTheory.T.tensorLatticeAtFinitePlace_eq_sum_splitPlace_parts hB.cm X W v t γ hγ
        exact add_mem (AddSubgroup.subset_closure (.inr ⟨h₁, _, e₁⟩)) (AddSubgroup.subset_closure (.inr ⟨h₂, _, e₂⟩))
      · obtain ⟨w, hw⟩ := not_forall_not.1 hv
        refine AddSubgroup.subset_closure (.inl ⟨⅟(2 : AF F) • γ, smul_mem_lat X W v (invTwo_mem v (hB.inert v w hw).1) hγ, ?_⟩)
        rw [two_nsmul, ← add_smul, invOf_two_add_invOf_two, one_smul]
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat hW.lat
    obtain ⟨a, ha⟩ := GlobalTheory.T.schroedinger_fixed_functions_proportional_of_selfDual v (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.VacAny.continuous_psiV hstd.1 v)
      (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v) (GlobalTheory.LatVac.locCo M.co v '' gen)
      ((latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v)) c
      (by rw [← AddMonoidHom.map_closure]; exact AddSubgroup.map_mono hgen) hc0
      (GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ _ (fun γ hγ => GlobalTheory.VacLine.at_latAtV hγ)
        (GlobalTheory.T.heisenbergLattice_selfDual_every_finitePlace F E σ B n d X W r s r' s' hB hX hW v))
      (by rintro _ ⟨γ, hγ, rfl⟩; exact hc γ hγ) (M.vac v)
      (fun ξ => Ψ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        refine GlobalTheory.BigDat.schr_eq_of_acts _ _ (GlobalTheory.VacLine.at_latAtV (hsub γ hγ)) (hG.vac v).1 ?_
        obtain ⟨-, -, θ, -, hθ⟩ := hG.vac v
        have h1 := hθ γ (hsub γ hγ)
        have h3 : B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)
            (inclR (F := F) (AF F) (θ : E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F W.J) γ γ) = 1 := by
          rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨hγ, t, ht⟩
          · exact GlobalTheory.BigDat.VacFix.psi_double _ B X W _ _ _ _ hB hX hW v θ γ' hγ'
          · unfold GlobalTheory.WeilM.symp
            rw [hTens_half hB.cm t _ _ (GlobalTheory.VacLine.at_latAtV hγ) ht, mul_zero, map_zero, mul_zero,
              AddChar.map_zero_eq_one]
        rwa [h3, one_smul] at h1)
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        refine GlobalTheory.BigDat.schr_slice _ _ (GlobalTheory.VacLine.at_latAtV (hsub γ hγ)) ?_ hy
        rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨hγ, t, ht⟩
        · exact h2 v γ' hγ'
        · exact hh v t γ hγ ht) (hG.vac v).2.1
    exact ⟨a, congrFun ha⟩
  exact ⟨f, hf⟩
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsMaxCompactEqFrameGramSplitBasis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_maxCompact_eq_frame_gram_splitBasis :
    ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (β : GL (Fin S.rank) (Lev.EAf D)),
        IsSelfDualC S Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : Pl D.host.F) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
        (b : GL (Fin S.rank) (Fv D.host.F v)), IsSplitBasis τ (GlobalTheory.TripleSpaceW.conjSub Λ) b →
        ∃ g ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) (Fin S.rank),
          g.val = (β.val.map (GlobalTheory.BotMatch.evW τ))ᵀ * (S.gram.map τ)ᵀ * b.val := by
  intro D S Λ β hΛ hβ v τ b hb
  have hJ := GlobalTheory.Doubling.isHermND_gram S
  have hL := GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hΛ v
  have h1 := GlobalTheory.FlipMatch.RowChart.isSplitBasis_conj τ
    (GlobalTheory.FlipMatch.RowChart.isFrameAt_loc hβ (splitPrime τ))
  have e : ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      splitLat (t.comp D.sp.cm.sig) (GlobalTheory.TripleSpaceW.conjSub Λ) = splitLat t Λ := fun t => by
    refine le_antisymm (GlobalTheory.FlipMatch.RowChart.splitLat_le fun x hx => ⟨star x, hx, fun i => rfl⟩)
      (GlobalTheory.FlipMatch.RowChart.splitLat_le fun x hx => ⟨star x, ?_, fun i => ?_⟩)
    · rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hx
    · change t (x i) = t (star (star (x i)))
      rw [star_star]
  have e2 := e (τ.comp D.sp.cm.sig)
  rw [comp_conj_conj (isCMExt_host D)] at e2
  set β' := GeneralLinearGroup.map (complEquiv τ (splitPrime_under τ)).symm.toRingHom (loc (splitPrime τ) β) with hβ'
  have hv : β'.val = β.val.map (GlobalTheory.BotMatch.evW τ) := rfl
  have h2 : IsSplitBasis τ Λ β' := fun u => by rw [← e τ]; exact h1 u
  have h3 : IsSplitBasis (τ.comp D.sp.cm.sig) Λ b := fun u => by rw [← e2]; exact hb u
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : GL (Fin S.rank) (Fv D.host.F v), g₀.val = b.valᵀ * S.gram.map τ * β'.val :=
    ⟨dualConj 1 b⁻¹ * splitGram hJ τ * β', by
      rw [Units.val_mul, Units.val_mul, dualConj_one_val, inv_inv, splitGram_val]⟩
  obtain ⟨k1, k2⟩ := GlobalTheory.FlipMatch.RowChart.pairing_int (isCMExt_host D) hJ hL h2 h3 hg₀
  refine ⟨dualConj 1 g₀⁻¹, ?_, ?_⟩
  · rw [← (GLint_eq_KO_and_princ_eq_KOne v S.rank).1, mem_GLint_iff, ← map_inv, dualConj_one_val, dualConj_one_val,
      inv_inv]
    exact ⟨fun i j => k1 j i, fun i j => k2 j i⟩
  · rw [dualConj_one_val, inv_inv, hg₀, hv, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsSplitIdempotentMulEqOfPiWEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_splitIdempotent_mul_eq_of_piW_eq_zero :
    ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.E →ₐ[D.host.F] Fv D.host.F v),
        ∃ a : AE D, IsSplitIdem D a ∧ ∀ z : AE D, At (evFin D.host.F v) z → piW t z = 0 → a * z = z := by
  intro D v t
  refine ⟨GlobalTheory.EmbChart.idem (t.comp D.sp.cm.sig), GlobalTheory.EmbChart.isSplitIdem_idem _, fun z hz h0 => ?_⟩
  have h1 : (1 - GlobalTheory.EmbChart.atPlace v (1 : Fv D.host.F v)) • z = 0 :=
    hz _ (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero, Algebra.smul_def] at h1
  have h2 : z = GlobalTheory.EmbChart.tensAt D.host.E v (1 * GlobalTheory.AdelicU.compFin D.host.F D.host.E v z) :=
    h1.trans (GlobalTheory.EmbChart.tensAt_mul_right v 1 z)
  have h3 : GlobalTheory.AdelicU.splitIdem (GlobalTheory.AdelicU.isCMExt_host D) t * GlobalTheory.AdelicU.compFin D.host.F D.host.E v z = 0 :=
    (GlobalTheory.AdelicU.splitProj_eq_zero_iff _ t _).1 h0
  rw [GlobalTheory.EmbChart.idem_mul, GlobalTheory.AdelicU.splitIdem_comp, sub_mul, h3, sub_zero]
  exact h2.symm
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.IdempotentSumFixesIffHalfEl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section

open GlobalTheory.StdFrames (cpt comp_toAd)
open GlobalTheory.LFun (complMap)
open GlobalTheory.AdelicU (splitPrime_under)

variable {D : D7}

private theorem ext_cpt {a b : AE D} (h1 : infPart D a = infPart D b)
    (h2 : ∀ Q, cpt (D := D) Q (toEAf D a) = cpt (D := D) Q (toEAf D b)) : a = b :=
  (comp_toAd D).ext' h1 h2

private theorem cpt_base {Q : HeightOneSpectrum (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : Q.under (𝓞 D.host.F) = v) (u : AF D.host.F) :
    cpt (D := D) Q (toEAf D (algebraMap _ (AE D) u)) = complMap h (evFin D.host.F v u) := by
  subst h
  exact (comp_toAd D).base u Q

private theorem cpt_split {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : AE D) :
    cpt (D := D) (splitPrime τ) (toEAf D z) = complMap (splitPrime_under τ) (piW τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x =>
    have e1 : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap _ (AE D) a * incA D x := by
      change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have e2 : piW τ (a ⊗ₜ[D.host.F] x : AE D) = evFin D.host.F v a * τ x := rfl
    have e3 : cpt (D := D) (splitPrime τ) (toEAf D (incA D x)) = algebraMap _ _ x :=
      congrArg (fun s => s (splitPrime τ)) ((comp_toAd D).inc x)
    rw [e2, e1, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, cpt_base (splitPrime_under τ), e3,
      GlobalTheory.LFun.SplitTie.complMap_apply_emb]

private theorem piW_comp {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : AE D) :
    piW (τ.comp D.sp.cm.sig) z = piW τ (cA D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

private theorem first_half {e₀ : AE D} {S : Finset (HeightOneSpectrum (𝓞 D.host.E))} (he : IsIdemSum e₀ S)
    (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (hP : ∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) (ht : ∀ v : P, splitPrime (t v) ∈ S) (z : AE D) :
    e₀ * z = z ↔ HalfEl P (fun v => (t v).comp D.sp.cm.sig) z := by
  obtain ⟨e0, e1, e2⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  have one : ∀ {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ ∈ S →
      piW τ e₀ = 1 := fun τ h =>
    (complMap (splitPrime_under τ)).injective (by rw [← cpt_split, e1 _ h, RingHom.map_one])
  constructor
  · intro hz
    refine ⟨fun u hu => ?_, fun v => ?_⟩
    · have h0 : algebraMap _ (AE D) u * e₀ = 0 := by
        refine ext_cpt (by rw [RingHom.map_mul, e0, mul_zero, RingHom.map_zero]) fun Q => ?_
        rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_zero, RingHom.map_zero]
        by_cases hQ : Q ∈ S
        · rw [cpt_base rfl, hu _ ((hP _).2 ⟨Q, hQ, rfl⟩), RingHom.map_zero, zero_mul]
        · rw [e2 Q hQ, mul_zero]
      rw [Algebra.smul_def, ← hz, ← mul_assoc]
      exact (congrArg (· * z) h0).trans (zero_mul z)
    · have h0 := congrArg (piW (t v)) he.2
      rw [RingHom.map_mul, one _ (ht v), one_mul, RingHom.map_zero, ← piW_comp] at h0
      change piW ((t v).comp D.sp.cm.sig) z = 0
      rw [← hz, RingHom.map_mul, h0, zero_mul]
  · rintro ⟨h1, h2⟩
    have h1' : ∀ u : AF D.host.F, (∀ v ∈ P, evFin D.host.F v u = 0) → algebraMap _ (AE D) u * z = 0 :=
      fun u hu => (Algebra.smul_def u z).symm.trans (h1 u hu)
    refine ext_cpt ?_ fun Q => ?_
    · have h3 := congrArg (infPart D) (h1' ((1, 0) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) fun v _ => rfl)
      have h4 : infPart D (algebraMap (AF D.host.F) (AE D) ((1, 0) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) = 1 := rfl
      rw [RingHom.map_mul, h4, one_mul, RingHom.map_zero] at h3
      rw [RingHom.map_mul, h3, mul_zero]
    · rw [RingHom.map_mul, RingHom.map_mul]
      by_cases hQ : Q ∈ S
      · rw [e1 Q hQ, one_mul]
      rw [e2 Q hQ, zero_mul, eq_comm]
      by_cases hv : Q.under (𝓞 D.host.F) ∈ P
      · have hm : Q.asIdeal ∈ (Q.under (𝓞 D.host.F)).asIdeal.primesOver (𝓞 D.host.E) := ⟨Q.isPrime, ⟨rfl⟩⟩
        rw [GlobalTheory.AdelicU.primesOver_eq_split (GlobalTheory.AdelicU.isCMExt_host D) (t ⟨_, hv⟩)] at hm
        rcases hm with e | e
        · exact absurd ((HeightOneSpectrum.ext e : Q = _) ▸ ht ⟨_, hv⟩) hQ
        · have h5 := cpt_split ((t ⟨_, hv⟩).comp D.sp.cm.sig) z
          rw [h2 ⟨_, hv⟩, RingHom.map_zero] at h5
          have e' : Q = splitPrime ((t ⟨_, hv⟩).comp D.sp.cm.sig) := HeightOneSpectrum.ext e
          generalize splitPrime ((t ⟨_, hv⟩).comp D.sp.cm.sig) = Q' at h5 e'
          subst e'
          exact h5
      · let u : AF D.host.F := ((0, singleV D.host.F (Q.under (𝓞 D.host.F)) 1) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
        have h3 := congrArg (fun y => cpt (D := D) Q (toEAf D y)) (h1' u fun v hv' =>
          Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F)
            (fun e : v = Q.under (𝓞 D.host.F) => hv (e ▸ hv')) 1)
        have h4 : evFin D.host.F (Q.under (𝓞 D.host.F)) u = 1 :=
          Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) (Q.under (𝓞 D.host.F)) 1
        simp only [RingHom.map_mul, RingHom.map_zero] at h3
        rwa [cpt_base rfl, h4, RingHom.map_one, one_mul] at h3

private theorem cA_smul (u : AF D.host.F) (z : AE D) : cA D (u • z) = u • cA D z := by
  rw [Algebra.smul_def, Algebra.smul_def, RingHom.map_mul, GlobalTheory.IdemSupport.cA_algebraMap]

end

theorem UpperTheory.idempotentSum_fixes_iff_halfEl :
    ∀ (D : D7) (e₀ : AE D) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e₀ S →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) → (∀ v : P, splitPrime (t v) ∈ S) →
        (∀ z : AE D, e₀ * z = z ↔ HalfEl P (fun v => (t v).comp D.sp.cm.sig) z) ∧ ∀ z : AE D, cA D e₀ * z = z ↔ HalfEl P t z := by
  intro D e₀ S he P t hP ht
  refine ⟨first_half he P t hP ht, fun z => ?_⟩
  have hc : ∀ y : AE D, cA D (cA D y) = y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [RingHom.map_add, hx, hy]
    | tmul a x => exact congrArg (fun s => a ⊗ₜ[D.host.F] s) (star_star x)
  have hi : Function.Injective (cA D) := Function.LeftInverse.injective hc
  have h := first_half he P t hP ht (cA D z)
  rw [← hi.eq_iff, RingHom.map_mul, hc] at h
  refine h.trans (and_congr (forall_congr' fun u => imp_congr_right fun _ => ?_) (forall_congr' fun v => ?_))
  · change u • cA D z = 0 ↔ u • z = 0
    rw [← cA_smul, ← hi.eq_iff, hc, RingHom.map_zero]
  · change piW ((t v).comp D.sp.cm.sig) (cA D z) = 0 ↔ _
    rw [piW_comp, hc]
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.LocalCharConductorLeOfHeckeExponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.localChar_conductor_le_of_heckeExponent :
    ∀ (D : D7) (ν : (AE D)ˣ →* Circle) (νH : Formalism.L2.Host.HChar D.host.E), ChrEq ν νH →
        ∀ (v : Pl D.host.F) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (c : ℕ), GlobalTheory.CMVal.ExpAt νH (splitPrime τ) c →
        GlobalTheory.SplitFlip.CondLE (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) c (chrW ν τ) ∧ (¬ GlobalTheory.LFun.UnrAt ν (splitPrime τ) → 1 ≤ c) := by
  intro D ν νH h v τ c hc
  refine ⟨fun x hx => ?_, fun hn => ?_⟩
  · have h1 : Valued.v (x : Fv D.host.F v) = 1 := (GlobalTheory.FlipMatch.isEquiv_Fv v).eq_one_iff_eq_one.1 hx.1
    have h2 : Valued.v ((x : Fv D.host.F v) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
      refine ((GlobalTheory.FlipMatch.isEquiv_Fv v _ _).1 hx.2).trans_eq ?_
      rw [Units.val_pow_eq_pow_val, map_pow, GlobalTheory.ChrWUnif.valued_unifAt, ← WithZero.exp_nsmul]
      simp
    have h3 := (hc c).2 le_rfl (Units.map (complMap (splitPrime_under τ)).toMonoidHom x)
      ((SplitTie.valued_complMap τ (splitPrime_under τ) _).trans h1) (by
        refine le_of_eq_of_le ?_ h2
        rw [← SplitTie.valued_complMap τ (splitPrime_under τ), RingHom.map_sub, RingHom.map_one]
        rfl)
    rw [← locChar_eq_of_chrEq h] at h3
    exact h3
  · by_contra h0
    apply hn
    rw [unrAt_iff_of_chrEq h]
    intro x hx
    refine (hc 0).2 (by omega) x hx ?_
    rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact Valuation.map_sub_le _ (le_of_eq hx) (le_of_eq (map_one _))
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.PtOSgnMemLatAtVIffMemLatO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ptO_eq {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) (x : Matrix (Fin n) (Fin S.rank) (AE D))
    (p : Fin S.rank) (q : Fin d) : ptO S.gram e x p q = GlobalTheory.BigDat.divG S x (e q) p := rfl

private noncomputable def ptH {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) :
    Matrix (Fin n) (Fin S.rank) (AE D) →+ Matrix (Fin S.rank) (Fin d) (AE D) :=
  AddMonoidHom.mk' (ptO S.gram e) fun x y => by
    ext p q
    rw [Matrix.add_apply, ptO_eq, ptO_eq, ptO_eq, GlobalTheory.BigDat.divG, Matrix.add_mul]
    rfl

private theorem ptO_inj {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) {x y : Matrix (Fin n) (Fin S.rank) (AE D)}
    (h : ptO S.gram e x = ptO S.gram e y) : x = y := by
  have h1 : GlobalTheory.BigDat.divG S x = GlobalTheory.BigDat.divG S y := by
    ext q p
    obtain ⟨q, rfl⟩ := e.surjective q
    rw [← ptO_eq, ← ptO_eq, h]
  rw [← GlobalTheory.BigDat.mulG_divG S x, h1, GlobalTheory.BigDat.mulG_divG]

private theorem ptO_gen {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) (β : AF D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin n → D.host.E) :
    ptO S.gram e (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (fun q => a * t (e q))) := by
  ext p q
  refine (ptO_eq S e _ p q).trans ((GlobalTheory.BigDat.divG_gen S β a s t (e q) p).trans ?_)
  rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, mul_comm]
  rfl

private theorem at_eq_pairA {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {b : AF F}
    (hb : At (evFin F v) b) (hi : evFin F v b ∈ v.adicCompletionIntegers F) : ∃ α ∈ intAf F, b = pairA F 0 α := by
  refine ⟨GlobalTheory.AdelicU.singleFin v (evFin F v b), fun w => ?_, GlobalTheory.VacAny.eq_atPlace_of_at v b hb⟩
  by_cases h : w = v
  · subst h
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
    exact hi
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne h]
    exact zero_mem _

private theorem finiteRing_sq_sub_mul_sq_eq_of_card {D : D7} (S X : HSp D) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E))
    (hL : IsLat e Vs Ws ΛS ΛX) :
    (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (x : WO S X), ptO S.gram e x ∈ latAtV Vs Ws v → x ∈ (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True)) ∧
        ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : AF D.host.F), At (evFin D.host.F v) a →
          evFin D.host.F v a ∈ v.adicCompletionIntegers D.host.F → ∀ x ∈ (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True), a • ptO S.gram e x ∈ latAtV Vs Ws v := by
  refine ⟨fun v x hx => ?_, fun v b hb hi x hx => ?_⟩
  · have key : latAtV Vs Ws v ≤ (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E))
        fun _ => True).map (ptH S e) := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨b, hb, hi, x, hx, y, hy, rfl⟩
      obtain ⟨α, hα, rfl⟩ := at_eq_pairA hb hi
      have h1 : (1 : D.host.E) ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
          ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) := by
        rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ GlobalTheory.SkewLat.DualPair.AA_ne]
        exact FractionalIdeal.one_mem_one _
      have h2 : ∀ z ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
          ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)),
          pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x (z • y)) ∈
            (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True).map (ptH S e) := by
        intro z hz
        refine Submodule.mul_induction_on hz (fun a ha c hc => ?_) (fun z z' hz hz' => ?_)
        · refine ⟨_, AddSubgroup.subset_closure ⟨α, hα, fun _ h => (h trivial).elim, a, ha, star x, (hL.1 x).1 hx,
            c • fun k => y (e.symm k), (hL.2 y).1 hy c hc, rfl⟩, ?_⟩
          refine (ptO_gen S e _ a _ _).trans ?_
          rw [star_star]
          congr 3
          funext q
          simp only [Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply, mul_assoc]
        · have h3 : pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x ((z + z') • y)) =
              pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x (z • y)) +
              pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x (z' • y)) := by
            refine Matrix.ext fun p q => ?_
            rw [Matrix.add_apply, GlobalTheory.BigDat.smul_incM_apply, GlobalTheory.BigDat.smul_incM_apply, GlobalTheory.BigDat.smul_incM_apply,
              ← TensorProduct.tmul_add]
            simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add]
          rw [h3]
          exact add_mem hz hz'
      have h4 := h2 1 h1
      rwa [one_smul] at h4
    obtain ⟨x', hx', h⟩ := key hx
    rwa [← ptO_inj S e h]
  · refine GlobalTheory.BigDat.map_mem_of_closure ((DistribMulAction.toAddMonoidHom _ b).comp (ptH S e)) ?_ hx
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine (congrArg (fun z => b • z ∈ latAtV Vs Ws v) (ptO_gen S e (pairA _ 0 α) a s t)).mpr ?_
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨_, ?_, ?_, _, (hL.1 _).2 (by rw [star_star]; exact hs), _, (hL.2 _).2 ?_, rfl⟩
    · intro u hu
      rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u, hb u hu, zero_mul]
    · rw [map_mul]
      exact mul_mem hi (hα v)
    · simp only [Equiv.apply_symm_apply]
      exact GlobalTheory.BigDat.smul_mem_scLat_of_mem ha ht

theorem UpperTheory.ptO_sgn_mem_latAtV_iff_mem_latO :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)),
        IsLat e Vs Ws ΛS ΛX →
        (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (x : WO (sgn ε S) X), ptO (sgn ε S).gram e x ∈ latAtV Vs Ws v → x ∈ (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True)) ∧
        ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : AF D.host.F), At (evFin D.host.F v) a →
          evFin D.host.F v a ∈ v.adicCompletionIntegers D.host.F → ∀ x ∈ (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True), a • ptO (sgn ε S).gram e x ∈ latAtV Vs Ws v := by
  intro D ψ ε S X d e Bs Vs Ws M _ ΛS ΛX hL
  exact finiteRing_sq_sub_mul_sq_eq_of_card (sgn ε S) X e Vs Ws ΛS ΛX hL
end

