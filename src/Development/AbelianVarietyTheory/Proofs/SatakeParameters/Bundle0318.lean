import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0310
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0315
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0312
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0893
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
import Formalism.SharpRestriction.GlobalSchurBounds.Joints

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformizerBlockEqDiagonalPowMulIntegralGL
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.DiagUnifFactor

theorem getD_pattern (k m i : ℕ) :
    (List.replicate k (1 : ℤ) ++ List.replicate m 0).getD i 0 = if i < k then 1 else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2 h2
  · simp [List.getElem?_replicate, h2]
  · simp at h1; omega
  · simp at h1; omega
  · simp [List.getElem?_replicate]
    split_ifs <;> rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ)
    (ϖ π : v.adicCompletion F), Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v π = WithZero.exp (-1 : ℤ) →
    ∃ T ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), Formalism.UG.diagJ n ϖ k =
      Matrix.diagonal (fun i : Fin n => π ^ ((List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0).getD i.1 0)) *
        (T : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro F _ _ v n k ϖ π hϖ hπ
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπ; exact WithZero.zero_ne_coe hπ
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hu : Valued.v (ϖ / π) = 1 := by
    rw [map_div₀, hϖ, hπ, div_self (WithZero.coe_ne_zero)]
  have hu' : Valued.v (π / ϖ) = 1 := by
    rw [map_div₀, hϖ, hπ, div_self (WithZero.coe_ne_zero)]
  let d : Fin n → v.adicCompletion F := fun i => if (i : ℕ) < k then ϖ / π else 1
  let d' : Fin n → v.adicCompletion F := fun i => if (i : ℕ) < k then π / ϖ else 1
  have hdd' : Matrix.diagonal d * Matrix.diagonal d' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; simp only [d, d']
    split_ifs
    · rw [div_mul_div_comm, mul_comm ϖ π, div_self (mul_ne_zero hπ0 hϖ0)]
    · exact one_mul 1
  have hd'd : Matrix.diagonal d' * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; simp only [d, d']
    split_ifs
    · rw [div_mul_div_comm, mul_comm π ϖ, div_self (mul_ne_zero hϖ0 hπ0)]
    · exact one_mul 1
  let T : GL (Fin n) (v.adicCompletion F) := ⟨Matrix.diagonal d, Matrix.diagonal d', hdd', hd'd⟩
  have hmem : ∀ (e : Fin n → v.adicCompletion F), (∀ i, Valued.v (e i) ≤ 1) →
      ∀ a b, Matrix.diagonal e a b ∈ Formalism.UG.Ov F v := by
    intro e he a b
    show Matrix.diagonal e a b ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hab : a = b
    · subst hab; rw [Matrix.diagonal_apply_eq]; exact he a
    · rw [Matrix.diagonal_apply_ne _ hab, map_zero]; exact zero_le'
  have hle : ∀ (x : v.adicCompletion F), Valued.v x = 1 → ∀ i : Fin n,
      Valued.v (if (i : ℕ) < k then x else 1) ≤ 1 := by
    intro x hx i; split_ifs
    · exact hx.le
    · rw [map_one]
  refine ⟨T, ?_, ?_⟩
  · have inj : Function.Injective ((Formalism.UG.Ov F v).subtype.mapMatrix (m := Fin n)) :=
      fun A B h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
    let A : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v) := fun i j => ⟨Matrix.diagonal d i j, hmem d (hle _ hu) i j⟩
    let B : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v) := fun i j => ⟨Matrix.diagonal d' i j, hmem d' (hle _ hu') i j⟩
    have hA : (Formalism.UG.Ov F v).subtype.mapMatrix A = Matrix.diagonal d := rfl
    have hB : (Formalism.UG.Ov F v).subtype.mapMatrix B = Matrix.diagonal d' := rfl
    refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, hA, hB, map_one, hdd']
    · rw [map_mul, hA, hB, map_one, hd'd]
  · show Matrix.diagonal _ = _ * Matrix.diagonal d
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [getD_pattern]
    simp only [d]
    split_ifs
    · rw [zpow_one, mul_div_cancel₀ _ hπ0]
    · rw [zpow_zero, one_mul]

end GlobalTheory.DiagUnifFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetSupportAtSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocEigAgree

theorem main : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (Q Q' : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite → (∀ σ σ', IsLocS (P.H.av.S i Q) sp σ → IsLocS (P.H.av.S i Q') sp σ' → GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ') → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → ∀ F' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q'), F' ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F' ≠ 0 → ∀ c c' : ℂ, NG.heckeD (P.M.loc i).J Ds F = c • F → NG.heckeD (P.M.loc i).J Ds F' = c' • F' → c = c' := by
  intro _hAF hL D P i Q Q' sp hJ Ds hDs hbi hfin hcls F hF hFT hF0 F' hF' hF'T hF'0 c c' hc hc'
  classical

  have hK : ∀ f ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ,
      ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ f = f := by
    intro f hf κ hκ
    obtain ⟨h1, h2⟩ := hJ κ hκ.2
    have hJκ : κ ∈ (P.M.loc i).J := h1.2 hκ.1
    have e := hf.2 ⟨κ, hJκ⟩
    rw [h2 hJκ] at e
    simpa using e
  have hJU : ∀ x ∈ Ds, ∀ x' ∈ Ds, (x⁻¹ * x' ∈ (P.M.loc i).J ↔ x⁻¹ * x' ∈ Umax D.host.E D.R.nV) :=
    fun x hx x' hx' => (hJ _ (GlobalTheory.HeckeScalarAll.trivOutside_mul (GlobalTheory.HeckeScalarAll.trivOutside_inv (hDs x hx))
      (hDs x' hx'))).1

  have hfinU : ((fun x : GAf D.host.E D.R.nV => (x : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV)) '' Ds).Finite := by
    let φ : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J → GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV := fun c =>
      if hc : ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c then (hc.choose : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV) else ((1 : GAf D.host.E D.R.nV) : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV)
    refine (hfin.image φ).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    have hc : ∃ y ∈ Ds, (y : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) := ⟨x, hx, rfl⟩
    refine ⟨(x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J), ⟨x, hx, rfl⟩, ?_⟩
    simp only [φ, dif_pos hc]
    have h1 := hc.choose_spec.2
    rw [QuotientGroup.eq] at h1
    exact QuotientGroup.eq.2 ((hJU _ hc.choose_spec.1 _ hx).1 h1)
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_reps (Umax D.host.E D.R.nV) Ds hfinU
  have hH : ∀ f : GAf D.host.E D.R.nV → (P.M.loc i).wt.W, (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ f = f) →
      NG.heckeD (P.M.loc i).J Ds f = ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ f := by
    intro f hf
    have hf' : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → NG.rt D.host.E D.R.nV κ f = f :=
      fun κ hκ ht => hf κ ⟨hκ, ht⟩
    have e1 : NG.heckeD (P.M.loc i).J Ds f = NG.heckeD (Umax D.host.E D.R.nV) Ds f := by
      funext g
      simp only [NG.heckeD]
      refine GlobalTheory.HeckeScalarAll.finsum_cosets_eq (P.M.loc i).J (Umax D.host.E D.R.nV) Ds (fun x => f (g * x)) hJU ?_
      intro x hx x' hx' hu
      have ht := GlobalTheory.HeckeScalarAll.trivOutside_mul (GlobalTheory.HeckeScalarAll.trivOutside_inv (hDs x hx)) (hDs x' hx')
      have h1 := congrFun (hf' _ hu ht) (g * x)
      simp only [NG.rt, LinearMap.coe_mk, AddHom.coe_mk] at h1
      rw [mul_assoc, mul_inv_cancel_left] at h1
      exact h1.symm
    rw [e1]
    exact GlobalTheory.HeckeScalarSph.heckeD_eq_sum (v := sp.v) hDs hR1 hR2 hf'

  obtain ⟨cX, hcX⟩ := GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) sp Ds hDs hbi R hR1 hR2
  obtain ⟨cX', hcX'⟩ := GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible D.host.E D.R.nV _ _ _ (P.H.av.irr i Q') sp Ds hDs hbi R hR1 hR2
  have hcI := GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) _ R cX hcX
  have hcI' := GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart D.host.E D.R.nV _ _ _ (P.H.av.irr i Q') _ R cX' hcX'
  have hc1 : c = cX := by
    have e1 := hc
    rw [hH F (hK F hFT), hcI F hF (hK F hFT)] at e1
    exact smul_left_injective ℂ hF0 e1.symm
  have hc2 : c' = cX' := by
    have e1 := hc'
    rw [hH F' (hK F' hF'T), hcI' F' hF' (hK F' hF'T)] at e1
    exact smul_left_injective ℂ hF'0 e1.symm
  rw [hc1, hc2]

  let π : NG.AutRep D.host.E D.R.nV := ⟨(P.M.loc i).wt, P.H.av.S i Q, P.H.av.irr i Q⟩
  let π' : NG.AutRep D.host.E D.R.nV := ⟨(P.M.loc i).wt, P.H.av.S i Q', P.H.av.irr i Q'⟩
  obtain ⟨σ, hσ⟩ := GlobalTheory.LocCompSplit.exists_isLocS π sp
  obtain ⟨σ', hσ'⟩ := GlobalTheory.LocCompSplit.exists_isLocS π' sp
  have hcl := hcls σ σ' hσ hσ'
  obtain ⟨E⟩ : Nonempty (σ.ρ.Equiv σ'.ρ) := by
    have h2 : σ.cl = σ'.cl := eq_of_heq (Sigma.mk.inj hcl).2
    exact GlobalTheory.SmGL.IrrRep.cl_eq_iff.1 h2
  have hσ0 := hσ
  obtain ⟨ι, T0, hι, hιc, hT0i, hT0S, hT0e⟩ := hσ
  obtain ⟨ι', T0', hι', hιc', hT0i', hT0S', hT0e'⟩ := hσ'
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique _ sp ι ι' hι hι' hιc hιc'
  obtain ⟨a, ha0, hafix⟩ := GlobalTheory.T.splitLocalComponent_has_fixedVector_of_isotypic D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) sp σ hσ0 ι hι hιc F hF hF0 (hK F hFT)
  have hT0H : ∀ v, T0 (∑ γ ∈ R, σ.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) v) =
      ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ (T0 v) := by
    intro v
    rw [map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hT0e γ (hDs γ (hR1 γ hγ)) v
  have hT0H' : ∀ v, T0' (∑ γ ∈ R, σ'.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) v) =
      ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ (T0' v) := by
    intro v
    rw [map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hT0e' γ (hDs γ (hR1 γ hγ)) v
  have hT0fix : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ (T0 a) = T0 a := by
    intro κ hκ
    rw [← hT0e κ hκ.2 a, hafix κ hκ]
  have hHa : ∑ γ ∈ R, σ.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) a = cX • a := by
    apply hT0i
    rw [hT0H, map_smul]
    exact hcX (T0 a) (hT0S a) hT0fix
  have hE : ∀ g v, E.toLinearEquiv (σ.ρ g v) = σ'.ρ g (E.toLinearEquiv v) := fun g v =>
    LinearMap.congr_fun (E.isIntertwining' g) v
  have ha'0 : E.toLinearEquiv a ≠ 0 := fun h => ha0 (E.toLinearEquiv.injective (by rw [h, map_zero]))
  have hHa' : ∑ γ ∈ R, σ'.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) (E.toLinearEquiv a) =
      cX • E.toLinearEquiv a := by
    simp only [← hE, ← map_sum, hHa, map_smul]
  have hT0fix' : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v,
      NG.rt D.host.E D.R.nV κ (T0' (E.toLinearEquiv a)) = T0' (E.toLinearEquiv a) := by
    intro κ hκ
    rw [← hT0e' κ hκ.2, ← hE, hafix κ hκ]
  have key := hcX' (T0' (E.toLinearEquiv a)) (hT0S' _) hT0fix'
  rw [← hT0H', hHa', map_smul] at key
  have hne : T0' (E.toLinearEquiv a) ≠ 0 := fun h => ha'0 (hT0i' (by rw [h, map_zero]))
  exact smul_left_injective ℂ hne key

end GlobalTheory.LocEigAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenGoodOfAdmissibilityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_good_of_admissibility : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.tieLab D → MtParTie D.nd D.naut D.ntypes → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → Formalism.MainNotions.SumRepresentations.adm5 D → GlobalTheory.NRows.GoodIdempotentFixesLocalisationForms D → GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector X → ∀ i, GlobalTheory.NJoin.EigGood X i := by
  first | exact @GlobalTheory.EigGoodTypes.main | exact GlobalTheory.EigGoodTypes.main | (intros; apply GlobalTheory.EigGoodTypes.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSectionSplitPlaceComponentMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.SplitComp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_integralSection_splitPlace_componentMap_cast {E : Type} [Field E] [NumberField E] [IsCMField E] (F1 : Subfield E)
    (hF : F1 = maximalRealSubfield E) (sp : SplitPlace E) :
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield E) → FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E,
      (∀ t, sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield E),
        sec t ∈ AddSubgroup.closure {y | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F1, ∃ x : 𝓞 E, y = a ⊗ₜ[F1] (x : E)}) ∧
      (∀ x ∈ AddSubgroup.closure {y | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F1, ∃ x : 𝓞 E, y = a ⊗ₜ[F1] (x : E)},
        sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield E)) ∧
      ∀ x : E, sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x)) = sp.i x := by
  classical
  subst hF
  have hc : ∀ (a : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (x : E),
      Formalism.IndefR.principalLevelFrame.tensCastR (rfl : maximalRealSubfield E = maximalRealSubfield E)
        (a ⊗ₜ[maximalRealSubfield E] x) = x ⊗ₜ[maximalRealSubfield E] a := fun a x => rfl
  have hp : ∀ (a : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (x : E),
      sp.proj (x ⊗ₜ[maximalRealSubfield E] a) = sp.i x * a sp.v := fun a x => rfl
  refine ⟨fun t => singleV (maximalRealSubfield E) sp.v t ⊗ₜ[maximalRealSubfield E] (1 : E), ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hc, hp, map_one, one_mul]
    exact RestrictedProduct.single_eq_same _ _ _
  · intro t ht
    apply AddSubgroup.subset_closure
    refine ⟨singleV (maximalRealSubfield E) sp.v t, ?_, 1, by simp⟩
    intro w
    show (singleV (maximalRealSubfield E) sp.v t) w ∈ _
    by_cases h : w = sp.v
    · subst h
      have e : (singleV (maximalRealSubfield E) sp.v t) sp.v = t := RestrictedProduct.single_eq_same _ _ _
      rw [e]
      exact ht
    · have e : (singleV (maximalRealSubfield E) sp.v t) w = 0 := RestrictedProduct.single_eq_of_ne _ _ h
      rw [e]
      exact zero_mem _
  · intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, z, rfl⟩ := hy
      rw [hc, hp]
      refine mul_mem ?_ (ha sp.v)
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (sp.split_le_one z)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, map_add]
      exact add_mem hy hz
    | neg y _ hy =>
      rw [map_neg, map_neg]
      exact neg_mem hy
  · intro x
    rw [hc, hp]
    show sp.i x * 1 = sp.i x
    exact mul_one _

theorem proj_tensCast_section : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) ∧
      (∀ x ∈ Formalism.L2.Theta.intAE D,
        sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) ∧
      ∀ x : D.host.E, sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x))) = sp.i x := by
  intro D sp hF
  obtain ⟨sec, h1, h2, h3, h4⟩ := exists_integralSection_splitPlace_componentMap_cast D.host.F hF sp
  refine ⟨sec, h1, h2, h3, fun x => ?_⟩
  have e : Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
    simp [Formalism.L2.Theta.finPart, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
  rw [e]
  exact h4 x

end GlobalTheory.SplitComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsModelOfMem
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst

noncomputable section

namespace GlobalTheory.AboveLRes

theorem exists_model_of_mem {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ} (T : FinExt l)
    (ρ : Γ →* GL (Fin a) (Om l))
    (hρ : ∀ g i k, ((ρ g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ T.1) :
    ∃ ρ' : Γ →* GL (Fin a) ↥T.1, mapRep (algebraMap ↥T.1 (Om l)) ρ' = ρ := by
  let f : GL (Fin a) ↥T.1 →* GL (Fin a) (Om l) := Units.map ((algebraMap ↥T.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥T.1 →+* Matrix (Fin a) (Fin a) (Om l)).toMonoidHom
  have hmi : Function.Injective ((algebraMap ↥T.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥T.1 → _) :=
    Matrix.map_injective (algebraMap ↥T.1 (Om l)).injective
  have hf : Function.Injective f := Units.map_injective hmi
  let lift : Γ → Matrix (Fin a) (Fin a) ↥T.1 := fun g => Matrix.of fun i k => ⟨_, hρ g i k⟩
  have hlift : ∀ g, (algebraMap ↥T.1 (Om l)).mapMatrix (lift g) = ((ρ g : GL (Fin a) (Om l)) : Matrix _ _ _) :=
    fun g => by ext i k; rfl
  have hm : ∀ g, ρ g ∈ f.range := by
    intro g
    refine ⟨⟨lift g, lift g⁻¹, hmi ?_, hmi ?_⟩, Units.ext (hlift g)⟩
    · rw [map_mul, hlift, hlift, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    · rw [map_mul, hlift, hlift, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  refine ⟨(MonoidHom.ofInjective hf).symm.toMonoidHom.comp (ρ.codRestrict f.range hm), ?_⟩
  exact MonoidHom.ext fun g => MonoidHom.apply_ofInjective_symm hf ⟨ρ g, hm g⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes

theorem exists_decRes_eq {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L]
    [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω} (σ : ↥(Dec (F := K) A))
    (hσ : ∀ x : L, (σ : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x) :
    ∃ σ' : ↥(Dec (F := L) A), decRes A σ' = σ := by
  let τ : G L Ω := { (σ : G K Ω).toRingEquiv with commutes' := hσ }
  have hτ : τ ∈ Dec (F := L) A := by
    have hg := mem_Dec.mp σ.2
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    conv_rhs => rw [← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  exact ⟨⟨τ, hτ⟩, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes

open GlobalTheory.AboveL in

theorem exists_model_dec {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) {l : ℕ}
    [Fact l.Prime] {a : ℕ} (r : G K Ω →* GL (Fin a) (Om l)) (LL' B : FinExt l)
    (r' : ↥(Dec (F := L) A) →* GL (Fin a) ↥LL'.1)
    (hm' : mapRep (algebraMap ↥LL'.1 (Om l)) r' = (resTo L r).comp (Dec (F := L) A).subtype) :
    ∃ (T : FinExt l) (r₁ : ↥(Dec (F := K) A) →* GL (Fin a) ↥T.1), B.1 ≤ T.1 ∧
      mapRep (algebraMap ↥T.1 (Om l)) r₁ = r.comp (Dec (F := K) A).subtype := by
  let M : IntermediateField K Ω := (IsScalarTower.toAlgHom K L Ω).fieldRange
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : FiniteDimensional K M :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L Ω)).toLinearEquiv.finiteDimensional
  haveI : Finite (G K Ω ⧸ M.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.fixingSubgroup_isOpen
  haveI : M.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set H : Subgroup ↥(Dec (F := K) A) := M.fixingSubgroup.subgroupOf (Dec (F := K) A) with hH
  haveI : Finite (↥(Dec (F := K) A) ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  set S : Set (Om l) := Set.range fun x : (↥(Dec (F := K) A) ⧸ H) × Fin a × Fin a =>
    ((r (x.1.out : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) x.2.1 x.2.2 with hS
  have hSf : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  obtain ⟨T, hT⟩ : ∃ T : FinExt l, T.1 = IntermediateField.adjoin ℚ_[l] S ⊔ LL'.1 ⊔ B.1 :=
    ⟨supExt (supExt ⟨_, hSf⟩ LL') B, rfl⟩
  have hET : IntermediateField.adjoin ℚ_[l] S ≤ T.1 := hT ▸ le_sup_left.trans le_sup_left
  have hLT : LL'.1 ≤ T.1 := hT ▸ le_sup_right.trans le_sup_left
  have hBT : B.1 ≤ T.1 := hT ▸ le_sup_right
  have hfix : ∀ σ : ↥(Dec (F := K) A), σ ∈ H → ∀ i k,
      ((r (σ : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ LL'.1 := by
    intro σ hσ i k
    have hσ' : ∀ x : L, (σ : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x := fun x =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_subgroupOf.1 hσ) _ ⟨x, rfl⟩
    obtain ⟨τ, hτ⟩ := exists_decRes_eq σ hσ'
    have e1 : (r (σ : G K Ω)) = ((resTo L r).comp (Dec (F := L) A).subtype) τ := by
      rw [← hτ]; rfl
    rw [e1, ← hm']
    exact ((r' τ : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1) i k |>.2
  have hent : ∀ (g : ↥(Dec (F := K) A)) i k,
      (((r.comp (Dec (F := K) A).subtype) g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ T.1 := by
    intro g i k
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    have hg : g = (QuotientGroup.mk g : ↥(Dec (F := K) A) ⧸ H).out * ((h⁻¹ : H) : ↥(Dec (F := K) A)) := by
      rw [hh, Subgroup.coe_inv, mul_inv_cancel_right]
    rw [MonoidHom.comp_apply, hg, map_mul, map_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun m _ => mul_mem (hET (IntermediateField.subset_adjoin _ _ ⟨⟨_, i, m⟩, rfl⟩)) ?_
    exact hLT (hfix _ (h⁻¹).2 m k)
  obtain ⟨r₁, hr₁⟩ := exists_model_of_mem T _ hent
  exact ⟨T, r₁, hBT, hr₁⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes

open GlobalTheory.AboveL in

theorem isPstAt_of_resTo : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Om l)), Continuous r → ∀ (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → IsPstAt P Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) → IsPstAt P Bw (r.comp (Dec (F := K) A).subtype) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A l _ P AI hT a r hr O O' _ _ _ _ _ _ Bw Bw' hj hj' hL
  have hcL : Continuous fun g : ↥(Dec (F := L) A) =>
      ((((resTo L r).comp (Dec (F := L) A).subtype) g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) :=
    Units.continuous_val.comp ((hr.comp (UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω)).comp continuous_subtype_val)
  obtain ⟨LL', r', hm', hV'⟩ := hL
  obtain ⟨T, r₁, hBT, hr₁⟩ := exists_model_dec A r LL' Bw.LL r' hm'.2

  obtain ⟨S'', Bw'', hjj, hTS, hle⟩ := exists_bridge (L := L) Bw hj T
  have hj'' : GlobalTheory.Pst.Induces Bw'' := fun x => by rw [hjj]; exact hj x
  obtain ⟨LL₃, r₃, hm₃, hV₃⟩ := GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge l P AI hT L Ω A O' _ Bw' Bw'' hj' hj'' a _
    hcL ⟨LL', r', hm', hV'⟩
  have h1 : Bw''.LL.1 ≤ (supExt Bw''.LL LL₃).1 := le_sup_left
  have h3 : LL₃.1 ≤ (supExt Bw''.LL LL₃).1 := le_sup_right
  have hTT : T.1 ≤ (supExt Bw''.LL LL₃).1 := hTS.trans h1
  have hr₁' : mapRep (algebraMap ↥(supExt Bw''.LL LL₃).1 (Om l))
      (mapRep (IntermediateField.inclusion hTT).toRingHom r₁) = r.comp (Dec (F := K) A).subtype := by
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hmL : IsModel Bw'' ((resTo L r).comp (Dec (F := L) A).subtype) (supExt Bw''.LL LL₃)
      ((mapRep (IntermediateField.inclusion hTT).toRingHom r₁).comp (decRes A)) := by
    refine ⟨h1, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f (decRes A g) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁'
  have hm₃' : IsModel Bw'' ((resTo L r).comp (Dec (F := L) A).subtype) (supExt Bw''.LL LL₃)
      (mapRep (IntermediateField.inclusion h3).toRingHom r₃) := by
    refine ⟨hm₃.1.trans h3, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := L) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hm₃.2
  have heq := IsModel.unique Bw'' _ hm₃' hmL
  have hp := GlobalTheory.PstExt.isPst_enlarge P Bw'' h3 r₃ hV₃
  rw [heq, repE_decRes Bw Bw'' hjj hle] at hp
  exact ⟨_, _, ⟨hBT.trans hTT, hr₁'⟩, (GlobalTheory.PstLaws.isPst_resTo_iff P _ hle).1 hp⟩

end GlobalTheory.AboveLRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGoodStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_place_split_of_tieLab : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ sp : SplitPlace D.host.E, sp.w = w ∧ (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) := by
  first | exact @GlobalTheory.OffBad.offbad | exact GlobalTheory.OffBad.offbad | (intros; apply GlobalTheory.OffBad.offbad <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryAutColumnFieldOfStandardUnitaryMatrStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAut_columnField_of_standard_unitary_matrix : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {n : ℕ} (G : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E) * (G : Matrix (Fin n) (Fin n) D.host.E) = 1 → ∃ g : UF X.E n, seamGL s g.1 = G := by
  first | exact @GlobalTheory.TwU.UnitaryFrom.exists_uf_seamGL_eq | exact GlobalTheory.TwU.UnitaryFrom.exists_uf_seamGL_eq | (intros; apply GlobalTheory.TwU.UnitaryFrom.exists_uf_seamGL_eq <;> assumption)
end

