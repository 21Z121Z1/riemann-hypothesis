import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.ArchBaseChangeOfHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ContinuousAT
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
import GroundTheory.AutomorphicForms.AnisotropicHeight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import GroundTheory.AutomorphicForms.Bundle0016
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfAdmissibility
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0781
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0635
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0735
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0439
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0398
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0407
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0787
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0758
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0776
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNormalisedOfDualIsConj
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.OneExDatum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev sConj (x : HeightOneSpectrum (𝓞 E)) :
    GL (Fin n) ((GlobalTheory.ThetaSatake.cw x).adicCompletion E) →* GL (Fin n) (x.adicCompletion E) :=
  GeneralLinearGroup.map (n := Fin n) (conjLoc (IsCMField.complexConj E).toRingEquiv x)

theorem exists_equiv_of_dualIsConj {π : CuspSub E n} (hd : GlobalTheory.ContraPair.DualIsConj π) (x : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin n) ((GlobalTheory.ThetaSatake.cw x).adicCompletion E)))
    (τ : SmIrr (GL (Fin n) (x.adicCompletion E))) (hσ : π.IsLocComp (GlobalTheory.ThetaSatake.cw x) σ)
    (ha : IsAdmissible σ.ρ) (hτ : π.IsLocComp x τ) :
    ∃ T : σ.V ≃ₗ[ℂ] τ.V, ∀ g v, τ.ρ (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc x) n g) (T v) = T (σ.ρ g v) := by
  obtain ⟨B, -, hB, hfinB, -, -⟩ := hd
  obtain ⟨f, f0, hf⟩ := hτ
  have hs : Continuous (sConj (n := n) x) :=
    Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ x).1)
  let τ' : SmIrr (GL (Fin n) ((GlobalTheory.ThetaSatake.cw x).adicCompletion E)) :=
    { V := τ.V, ρ := MonoidHom.comp τ.ρ (sConj x), smooth := fun v => (τ.smooth v).preimage hs
      irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (GlobalTheory.ConjPairLoc.map_conjLoc_surjective x) τ.irred }
  have hσ' := ((cuspSub_iff π).2.1 _ σ).2 hσ
  let β : π.V →ₗ[ℂ] τ.V →ₗ[ℂ] ℂ := B.compl₂ f
  have hβ : β ≠ 0 := fun h => f0 (LinearMap.ext fun v =>
    hB (f v) fun φ => LinearMap.congr_fun (LinearMap.congr_fun h φ) v)
  obtain ⟨F, hF⟩ := GlobalTheory.LocDual.exists_comp_ne_zero π.V π.stable π.irred _ σ hσ' β hβ
  let P : σ.V →ₗ[ℂ] τ.V →ₗ[ℂ] ℂ := β ∘ₗ F.1.codRestrict π.V F.2.1
  have hP : ∀ g u v, P (σ.ρ g u) (τ'.ρ g v) = P u v := fun g u v => by
    have e1 : F.1.codRestrict π.V F.2.1 (σ.ρ g u) =
        π.op (.fin (locGL E n _ g)) (F.1.codRestrict π.V F.2.1 u) := Subtype.ext (F.2.2 g u)
    have e2 : f (τ'.ρ g v) = π.op (GlobalTheory.ContraPair.conjOp (.fin (locGL E n _ g))) (f v) := by
      change f (τ.ρ (sConj x g) v) = π.op (.fin (GeneralLinearGroup.map _ (locGL E n _ g))) (f v)
      rw [GlobalTheory.ConjPairLoc.conjFin_locGL, hf, CuspSub.locRep_eq]
    change B (F.1.codRestrict π.V F.2.1 (σ.ρ g u)) (f (τ'.ρ g v)) = B (F.1.codRestrict π.V F.2.1 u) (f v)
    rw [e1, e2, hfinB]
  have hirr : (GlobalTheory.SmGL.contra σ.ρ).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis _ n) ha σ.irred
  let e₁ := (GlobalTheory.InvPairing.pairMap σ.ρ τ'.smooth P hP).ofBijective
    (GlobalTheory.InvPairing.pairMap_bijective σ.ρ τ'.smooth P hP hF τ'.irred hirr)
  obtain ⟨e₂⟩ := GlobalTheory.GelfandKazhdan.equiv_contra _ n σ.V σ.ρ ha σ.irred
  let e : σ.V ≃ₗ[ℂ] τ.V := (e₂.trans e₁.symm).toLinearEquiv
  have he : ∀ g v, e (σ.ρ g v) = τ.ρ (sConj x (invT n _ g)) (e v) := fun g v => by
    have h := GlobalTheory.ConjPairLoc.equiv_apply (e₂.trans e₁.symm) (invT n _ g) v
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose n _ (invT n _ g) = g := Units.ext (Matrix.transpose_transpose _)
    rw [MonoidHom.comp_apply, h1] at h
    exact h
  refine ⟨e, fun g v => ?_⟩
  rw [he]
  congr 2
  exact Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

theorem eq_cw_of_conjPl {w u : HeightOneSpectrum (𝓞 E)} (h : ConjPl w u) : u = GlobalTheory.ThetaSatake.cw w := by
  obtain ⟨h1, h2⟩ := h
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w).1 h1.symm with e | e
  · subst e
    rcases h2 with h2 | h2
    · exact absurd rfl h2
    · exact (GlobalTheory.BCT.LocMem.conjSrc_eq_of_not_split _ h2).symm
  · exact eq_conjSrc e

end GlobalTheory.CompanionTheory.OneExDatum

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub
section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.CompanionTheory.CTSmooth
open PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.PExpFin

namespace GlobalTheory.CompanionTheory.HullExp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

def trans (r : ℕ) (s : ℝ) : Module.End ℂ (GA E N → ℂ) where
  toFun f g := f (aT E N r s * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem trans_pow (r : ℕ) (s : ℝ) (i : ℕ) (f : GA E N → ℂ) :
    (trans r s ^ i) f = fun g => f (aT E N r (s * i) * g) := by
  induction i generalizing f with
  | zero =>
    funext g
    simp [aT_zero]
  | succ i ih =>
    funext g
    rw [pow_succ, Module.End.mul_apply, ih]
    change f (aT E N r s * (aT E N r (s * i) * g)) = _
    rw [← mul_assoc, ← aT_add]
    congr 3
    push_cast
    ring

theorem kl_iff {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} :
    Kl r s p F ↔ aeval (trans (E := E) (N := N) r s) p F = 0 := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, trans_pow]
  constructor
  · intro h
    funext g
    simpa [Finset.sum_apply] using h g
  · intro h g
    simpa [Finset.sum_apply] using congrFun h g

theorem kl_mul_left {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) (q : ℂ[X]) :
    Kl r s (q * p) F := by
  rw [kl_iff] at h ⊢
  rw [map_mul, Module.End.mul_apply, h, map_zero]

theorem lo_fin {φ : Sm E N} (h : LO φ) (k : GL (Fin N) (Af E)) : LO (act (.fin k) φ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ ?_⟩
  · change φ.1 (ratGL E N γ * g * finGL E N k) = φ.1 (g * finGL E N k)
    rw [mul_assoc, h.1]
  · have hc : Continuous fun u : GL (Fin N) (Af E) => k⁻¹ * u * k := by fun_prop
    have hm : {u | finRep E N u φ = φ} ∈ nhds (k⁻¹ * 1 * k) := by
      have : k⁻¹ * 1 * k = 1 := by group
      rw [this]
      exact h.2.mem_nhds (by simp)
    refine Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds hm) fun u hu => ?_
    have hu' : finRep E N (k⁻¹ * u * k) φ = φ := hu
    change finRep E N u (finRep E N k φ) = finRep E N k φ
    conv_rhs => rw [← hu']
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group

theorem lo_cpt {φ : Sm E N} (h : LO φ) (k : Kinf E N) : LO (act (.cpt k) φ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.2.mem_nhds (by simp)) fun u hu => ?_)⟩
  · change φ.1 (ratGL E N γ * g * infGL E N (Unitary.toUnits k)) = φ.1 (g * infGL E N (Unitary.toUnits k))
    rw [mul_assoc, h.1]
  · have hu' : finRep E N u φ = φ := hu
    apply Subtype.ext
    funext g
    change φ.1 (g * finGL E N u * infGL E N (Unitary.toUnits k)) = φ.1 (g * infGL E N (Unitary.toUnits k))
    have e : φ.1 (g * infGL E N (Unitary.toUnits k) * finGL E N u) = φ.1 (g * infGL E N (Unitary.toUnits k)) :=
      congrArg (fun ψ : Sm E N => ψ.1 (g * infGL E N (Unitary.toUnits k))) hu'
    rw [← e, mul_assoc, mul_assoc, infGL_comm]

theorem lo_act {φ : Sm E N} (h : LO φ) (o : Op E N) : LO (act o φ) := by
  cases o with
  | fin k => exact lo_fin h k
  | cpt k => exact lo_cpt h k
  | lie X => exact lo_lie h X

theorem lo_add {φ ψ : Sm E N} (h : LO φ) (h' : LO ψ) : LO (φ + ψ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
    ((h.2.inter h'.2).mem_nhds ⟨by simp, by simp⟩) fun k hk => ?_)⟩
  · change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [h.1, h'.1]
  · have h1 : finRep E N k φ = φ := hk.1
    have h2 : finRep E N k ψ = ψ := hk.2
    change finRep E N k (φ + ψ) = φ + ψ
    rw [map_add, h1, h2]

theorem lo_smul {φ : Sm E N} (h : LO φ) (c : ℂ) : LO (c • φ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.2.mem_nhds (by simp)) fun k hk => ?_)⟩
  · change c * φ.1 _ = c * φ.1 _
    rw [h.1]
  · have h1 : finRep E N k φ = φ := hk
    change finRep E N k (c • φ) = c • φ
    rw [map_smul, h1]

theorem lo_zero : LO (0 : Sm E N) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  have : {k | finRep E N k (0 : Sm E N) = 0} = Set.univ := Set.eq_univ_of_forall fun k => map_zero _
  rw [this]
  exact isOpen_univ

section CT

variable {r : ℕ} [MeasurableSpace (BlockIx N r → Ad E)] [BorelSpace (BlockIx N r → Ad E)]
  (μ : Measure (BlockIx N r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx N r → Ad E))

theorem ct_add_lo (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) {φ ψ : Sm E N} (hφ : LO φ) (hψ : LO ψ) :
    PositivityTheory.Affgl.CT.ct μ 𝓕 (φ + ψ).1 = PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 + PositivityTheory.Affgl.CT.ct μ 𝓕 ψ.1 := by
  funext g
  exact integral_add (GlobalTheory.CompanionTheory.CTFin.Central.integrable_unip_mul μ 𝓕 h𝓕 hφ.1 hφ.2 g)
    (GlobalTheory.CompanionTheory.CTFin.Central.integrable_unip_mul μ 𝓕 h𝓕 hψ.1 hψ.2 g)

theorem kl_act_lo (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) {s : ℝ} {p : ℂ[X]} {φ : Sm E N}
    (hφ : LO φ) (h : Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1)) (o : Op E N) :
    Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 (act o φ).1) := by
  cases o with
  | fin k =>
    have e : PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.fin k) φ).1 = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (g * finGL E N k) := by
      funext g
      exact congrArg (fun f : (BlockIx N r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ)
        (funext fun x => congrArg φ.1 (mul_assoc _ _ _))
    rw [e]
    exact kl_right h _
  | cpt k =>
    have e : PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.cpt k) φ).1 =
        fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (g * infGL E N (Unitary.toUnits k)) := by
      funext g
      exact congrArg (fun f : (BlockIx N r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ)
        (funext fun x => congrArg φ.1 (mul_assoc _ _ _))
    rw [e]
    exact kl_right h _
  | lie X =>
    obtain ⟨F, hF1, hF2⟩ := ct_smooth E N r φ hφ.1 hφ.2 μ 𝓕 inferInstance h𝓕
    have e1 : F.1 = PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 := funext hF1
    have e2 : (lie E N X F).1 = PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.lie X) φ).1 := funext (hF2 X)
    rw [← e2]
    exact kl_lie (e1 ▸ h) X

end CT

def bdSub (r : ℕ) (ρ : ℝ) : Submodule ℂ (Sm E N) where
  carrier := {φ | LO φ ∧ ∃ p : ℂ[X], p.Monic ∧ (∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp ρ) ∧ ∀ F, IsCT r φ.1 F → Kl r 1 p F}
  add_mem' := by
    rintro φ ψ ⟨hφ, p, hp, hpz, hpk⟩ ⟨hψ, q, hq, hqz, hqk⟩
    refine ⟨lo_add hφ hψ, p * q, hp.mul hq, fun z hz => ?_, ?_⟩
    · exact (Polynomial.root_mul.1 hz).elim (hpz z) (hqz z)
    · rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
      let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
      have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
      have _ := hμ
      rw [ct_add_lo μ 𝓕 h𝓕 hφ hψ]
      refine (klSub r 1 (p * q)).add_mem ?_ ?_
      · rw [mul_comm]
        exact kl_mul_left (hpk _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩) q
      · exact kl_mul_left (hqk _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩) p
  zero_mem' := by
    refine ⟨lo_zero, 1, monic_one, fun z hz => ?_, ?_⟩
    · simp [Polynomial.IsRoot] at hz
    · rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
      let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
      have : PositivityTheory.Affgl.CT.ct μ 𝓕 (0 : Sm E N).1 = 0 := by
        funext g
        simp [PositivityTheory.Affgl.CT.ct]
      rw [this]
      exact (klSub r 1 1).zero_mem
  smul_mem' := by
    rintro c φ ⟨hφ, p, hp, hpz, hpk⟩
    refine ⟨lo_smul hφ c, p, hp, hpz, ?_⟩
    rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
    let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
    rw [ct_smul]
    exact (klSub r 1 p).smul_mem c (hpk _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩)

theorem isStable_bdSub (r : ℕ) (ρ : ℝ) : IsStable (bdSub (E := E) (N := N) r ρ) := by
  rintro o φ ⟨hφ, p, hp, hpz, hpk⟩
  refine ⟨lo_act hφ o, p, hp, hpz, ?_⟩
  rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
  let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  have _ := hμ
  exact kl_act_lo μ 𝓕 h𝓕 hφ (hpk _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩) o

theorem re_le_of_mem {r : ℕ} {ρ : ℝ} {φ : Sm E N} (hφ : φ ∈ bdSub (E := E) (N := N) r ρ) {c : ℂ}
    (hc : c ∈ Exp r φ.1) : c.re ≤ ρ := by
  obtain ⟨-, p, -, hpz, hpk⟩ := hφ
  obtain ⟨F₀, hCT, F, hF, hF0, hFe⟩ := hc
  have hroot := kl_eigen (kl_span (hpk _ hCT) hF) hF0 hFe
  have := hpz _ hroot
  simpa [Complex.norm_exp] using this

theorem mem_bdSub {r : ℕ} (hr : 0 < r) (hrN : r < N) {ρ : ℝ} {φ : Sm E N} (hφ : IsAutForm φ)
    (hρ : ∀ c ∈ Exp r φ.1, c.re ≤ ρ) : φ ∈ bdSub (E := E) (N := N) r ρ := by
  obtain ⟨-, -, -, hDct⟩ := dict_holds E N
  obtain ⟨hct, huniq⟩ := hDct φ hφ r hr hrN
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    let _ : MeasurableSpace (BlockIx N r → Ad E) := _root_.borel _
    have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
    obtain ⟨μ, 𝓕, hμ, h𝓕, e⟩ := hct
    obtain ⟨F, hF, -⟩ := ct_smooth E N r φ hφ.left hφ.level μ 𝓕 hμ h𝓕
    have e2 : An.ctn r φ.1 = F.1 := e.trans (funext fun g => (hF g).symm)
    intro g
    rw [e2]
    exact PDich.continuous_aT F r g
  obtain ⟨p, hp, hk, hroot⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) (fun u v => aT_add r u v) hcont
    (finTr_holds E N φ hφ r hr hrN _ hct)
  have hk' : Kl r 1 p (An.ctn r φ.1) := fun g => by
    simpa only [one_mul] using hk g
  refine ⟨⟨hφ.left, hφ.level⟩, p, hp, fun z hz => ?_, fun F hF => ?_⟩
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroot z hz
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (hρ c ⟨_, hct, F, hF, hF0, hFe⟩)
  · obtain ⟨a, -, rfl⟩ := huniq F hF
    exact (klSub r 1 p).smul_mem a hk'

end GlobalTheory.CompanionTheory.HullExp

open GlobalTheory.CompanionTheory.HullExp in

theorem GlobalTheory.CompanionTheory.HullExp.hullNonPos : PositivityTheory.Rg.BcB.E.E3.HullNonPos := by
  intro E _ _ _ N S hS φ hφ r hr hrN c hc
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have key : ∀ ψ ∈ S, ψ ∈ bdSub (E := E) (N := N) r (An.rho E N r) := fun ψ hψ =>
    mem_bdSub hr hrN (hS ψ hψ).1 fun c' hc' => by
      have := (hS ψ hψ).2 r hr hrN c' hc'
      rw [pE, sub_nonpos, div_le_iff₀ hd] at this
      rw [An.rho]
      linarith
  have hmem : φ ∈ bdSub (E := E) (N := N) r (An.rho E N r) :=
    (Submodule.mem_sInf.1 hφ) _ ⟨key, isStable_bdSub r _⟩
  have := re_le_of_mem hmem hc
  rw [pE, sub_nonpos, div_le_iff₀ hd]
  rw [An.rho] at this
  linarith

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LambdaInvolutionNeg
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusAdj

theorem conj_one_add {R : Type} [Ring R] (U A D Di : R) (h1 : D * Di = 1) (h2 : Di * D = 1) :
    D * (1 + (U - 1) * A) * Di = 1 + (D * U * Di - 1) * (D * A * Di) := by
  have k : D * U * Di * (D * A * Di) = D * (U * A) * Di := by
    calc D * U * Di * (D * A * Di) = D * U * (Di * D) * A * Di := by simp only [mul_assoc]
      _ = D * (U * A) * Di := by rw [h2]; simp only [mul_one, mul_assoc]
  calc D * (1 + (U - 1) * A) * Di = D * Di + (D * (U * A) * Di - D * A * Di) := by noncomm_ring
    _ = 1 + (D * U * Di * (D * A * Di) - D * A * Di) := by rw [h1, k]
    _ = 1 + (D * U * Di - 1) * (D * A * Di) := by noncomm_ring

theorem map_det_adj {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (A u t D Di : Matrix (Fin n) (Fin n) R)
    (h1 : D * Di = 1) (h2 : Di * D = 1) (hS : D * (u.map σ)ᵀ * Di = t) :
    σ (1 + A * (u - 1)).det = (1 + (t - 1) * (D * (A.map σ)ᵀ * Di)).det := by
  have e1 : (σ.mapMatrix (1 + A * (u - 1)))ᵀ = 1 + ((u.map σ)ᵀ - 1) * (A.map σ)ᵀ := by
    rw [map_add, map_mul, map_sub, map_one, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one]
    rfl
  have e2 : (D * (1 + ((u.map σ)ᵀ - 1) * (A.map σ)ᵀ) * Di).det = (1 + ((u.map σ)ᵀ - 1) * (A.map σ)ᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm D.det, mul_assoc, ← Matrix.det_mul, h1, Matrix.det_one, mul_one]
  rw [RingHom.map_det, ← Matrix.det_transpose, e1, ← e2, conj_one_add _ _ _ _ h1 h2, hS]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem rm_one : rm (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem adj_rm (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E) :
    rm d.val * ((rm e).map (conjAd E))ᵀ * rm (d⁻¹ : GL (Fin n) E).val = rm (sg d e) := by
  have h : ((rm e).map (conjAd E))ᵀ = rm (e.map (conjE E))ᵀ := by
    ext i j
    simp [rm, conjAd_algebraMap]
    rfl
  rw [h, sg, rm_mul, rm_mul]

theorem adj_inv (d : GL (Fin n) E) (t : GA E n) (ht : t ∈ adCent d) :
    rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ * rm (d⁻¹ : GL (Fin n) E).val = t.val := by
  have h : t⁻¹ * ratGL E n d * thetaA E n t = ratGL E n d := ht
  have hv : (t⁻¹ : GA E n).val * rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ = rm d.val :=
    congrArg Units.val h
  have h1 : rm d.val * rm (d⁻¹ : GL (Fin n) E).val = 1 := by
    rw [← rm_mul, Units.mul_inv, rm_one]
  calc rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ * rm (d⁻¹ : GL (Fin n) E).val
      = t.val * ((t⁻¹ : GA E n).val * rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ) *
          rm (d⁻¹ : GL (Fin n) E).val := by
        simp only [← mul_assoc, Units.mul_inv, one_mul]
    _ = t.val := by rw [hv, mul_assoc, h1, mul_one]

theorem chi_sg (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E) (t : GA E n) (ht : t ∈ adCent d)
    (hc : t.val * rm (sg d e) = rm (sg d e) * t.val) : chi (sg d e) t = conjAd E (chi e t⁻¹) := by
  have h1 : rm d.val * rm (d⁻¹ : GL (Fin n) E).val = 1 := by
    rw [← rm_mul, Units.mul_inv, rm_one]
  have h2 : rm (d⁻¹ : GL (Fin n) E).val * rm d.val = 1 := by
    rw [← rm_mul, Units.inv_mul, rm_one]
  have hcom : (t.val - 1) * rm (sg d e) = rm (sg d e) * (t.val - 1) := by
    rw [sub_mul, mul_sub, hc, one_mul, mul_one]
  rw [chi, chi, map_det_adj (conjAd E) (rm e) _ t.val _ _ h1 h2 (adj_inv d t ht), adj_rm, hcom]

theorem lam_sg (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E)
    (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t : GA E n) (ht : t ∈ adCent d)
    (h1 : t.val * rm e = rm e * t.val) (h2 : t.val * rm (sg d e) = rm (sg d e) * t.val) :
    lam (sg d e) t = - lam e t := by
  rw [← lam_inv e he t h1, lam, lam, chi_sg d e t ht h2]
  exact GlobalTheory.CompanionTheory.DegPairingProof.logAbs_conj GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces _

end GlobalTheory.CompanionTheory.TorusAdj

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankEquivariantFunctionalsCongr
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.StdSubTop

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem segmentRepresentation : GlobalTheory.Published.SegmentRepresentation :=
  GlobalTheory.T.unique_irreducible_sub_length_two (GlobalTheory.T.segment_length_two_irreducible_sub GlobalTheory.T.segment_length_two_reducible)

end GlobalTheory.CompanionTheory.StdSubTop

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateIsometry
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem rt_mem_l2Sub_and_inner_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : GA E N) (x y : Sm E N) (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hy : y ∈ squareIntegrableSmoothSubmoduleGL μ) :
    rt E N g x ∈ squareIntegrableSmoothSubmoduleGL μ ∧ ⟪l2Map μ (rt E N g x), l2Map μ (rt E N g y)⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
  have key : ∀ z : Sm E N, ∀ hz : z ∈ squareIntegrableSmoothSubmoduleGL μ, ∃ h' : rt E N g z ∈ squareIntegrableSmoothSubmoduleGL μ,
      l2Map μ (rt E N g z) = R (latticeGL E N) μ g (l2Map μ z) := by
    intro z hz
    have h' : rt E N g z ∈ squareIntegrableSmoothSubmoduleGL μ := ((mem_l2Sub μ).1 hz).mul_right g
    refine ⟨h', ?_⟩
    rw [l2Map_apply μ h', l2Map_apply μ hz, right_translate_toL2]
    rfl
  obtain ⟨hx', ex⟩ := key x hx
  obtain ⟨hy', ey⟩ := key y hy
  refine ⟨hx', ?_⟩
  let U : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
    ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  rw [ex, ey]
  exact U.inner_map_map _ _

end GlobalTheory.CompanionTheory.FinDiscOrth
end
end

