import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0225
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0227
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0167
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0301
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0237
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0238

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterAtInertPlaceOfSpherical
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG

noncomputable section

namespace GlobalTheory.SatExists

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : TrivOutside {v} (1 : GAf L n) := by
  intro v' _
  show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v') = 1
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem trivOutside_mul {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x y : GAf L n}
    (hx : TrivOutside {v} x) (hy : TrivOutside {v} y) : TrivOutside {v} (x * y) := by
  intro v' hv'
  show (((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1
  rw [Units.val_mul, Matrix.map_mul, hx v' hv', hy v' hv', Matrix.one_mul]

theorem trivOutside_inv {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x : GAf L n}
    (hx : TrivOutside {v} x) : TrivOutside {v} x⁻¹ := by
  intro v' hv'
  have e : (((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') *
      ((x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1 := by
    rw [← Matrix.map_mul]
    have : ((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hx v' hv', Matrix.mul_one] at e

theorem exists_satAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  intro L _ _ _ n π v w _ hsph Dv
  obtain ⟨f₀, hf₀S, hf₀0, hf₀K⟩ := hsph
  obtain ⟨-, N, hN, hNf⟩ := π.irrS.1.le hf₀S
  let U : Subgroup (GAf L n) :=
    Subgroup.closure ({κ | NG.Cong L n N κ} ∪ {κ | κ ∈ Umax L n ∧ TrivOutside {v} κ})
  have hUmax : U ≤ Umax L n := (Subgroup.closure_le _).2 (by
    rintro κ (hκ | hκ)
    · exact hκ.1
    · exact hκ.1)
  have hUv : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n) := fun κ hκ =>
    ⟨fun h => hUmax h, fun h => Subgroup.subset_closure (Or.inr ⟨h, hκ⟩)⟩
  have hCU : ∀ κ, NG.Cong L n N κ → κ ∈ U := fun κ hκ => Subgroup.subset_closure (Or.inl hκ)
  have hf₀U : ∀ κ ∈ U, NG.rt L n κ f₀ = f₀ := by
    intro κ hκ
    induction hκ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact funext fun g => hNf x hx g
      · exact hf₀K x hx.1 hx.2
    | one => exact funext fun g => by change f₀ (g * 1) = f₀ g; rw [mul_one]
    | mul x y _ _ hx hy =>
      refine funext fun g => ?_
      change f₀ (g * (x * y)) = f₀ g
      have h1 : f₀ (g * x * y) = f₀ (g * x) := congrFun hy (g * x)
      have h2 : f₀ (g * x) = f₀ g := congrFun hx g
      rw [← mul_assoc, h1, h2]
    | inv x _ hx =>
      refine funext fun g => ?_
      change f₀ (g * x⁻¹) = f₀ g
      have h1 : f₀ (g * x⁻¹ * x) = f₀ (g * x⁻¹) := congrFun hx (g * x⁻¹)
      rw [← h1, inv_mul_cancel_right]
  have hdec : ∀ u ∈ U, ∃ a b : GAf L n, u = a * b ∧ a ∈ U ∧ TrivOutside {v} a ∧ b ∈ U ∧
      ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨a, b, e, ha, hat, hb, hc⟩ := GlobalTheory.T.congruence_element_decompose L n v N x hx
        exact ⟨a, b, e, (hUv a hat).2 ha, hat, hCU b hb, hc⟩
      · exact ⟨x, 1, (mul_one x).symm, Subgroup.subset_closure (Or.inr hx), hx.2, one_mem _,
          fun y _ => by rw [mul_one, one_mul]⟩
    | one => exact ⟨1, 1, (mul_one 1).symm, one_mem _, trivOutside_one v, one_mem _,
        fun y _ => by rw [mul_one, one_mul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl, ha, hat, hb, hbc⟩ := hx
      obtain ⟨a', b', rfl, ha', hat', hb', hbc'⟩ := hy
      refine ⟨a * a', b * b', ?_, mul_mem ha ha', trivOutside_mul hat hat', mul_mem hb hb', fun z hz => ?_⟩
      · simp only [mul_assoc]
        rw [← mul_assoc b a', ← hbc a' hat', mul_assoc]
      · rw [← mul_assoc, hbc z hz, mul_assoc, hbc' z hz, ← mul_assoc]
    | inv x _ hx =>
      obtain ⟨a, b, rfl, ha, hat, hb, hbc⟩ := hx
      refine ⟨a⁻¹, b⁻¹, ?_, inv_mem ha, trivOutside_inv hat, inv_mem hb, fun z hz => ?_⟩
      · rw [mul_inv_rev, eq_mul_inv_iff_mul_eq, mul_assoc, hbc a⁻¹ (trivOutside_inv hat), inv_mul_cancel_left]
      · rw [mul_inv_eq_iff_eq_mul, mul_assoc, hbc z hz, inv_mul_cancel_left]
  let V : Submodule ℂ (GAf L n → π.W) :=
    { carrier := {f | f ∈ π.S ∧ ∀ κ ∈ U, NG.rt L n κ f = f}
      zero_mem' := ⟨π.S.zero_mem, fun κ _ => map_zero _⟩
      add_mem' := fun ha hb => ⟨π.S.add_mem ha.1 hb.1, fun κ hκ => by rw [map_add, ha.2 κ hκ, hb.2 κ hκ]⟩
      smul_mem' := fun c f hf => ⟨π.S.smul_mem c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩ }
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  haveI : FiniteDimensional ℂ V := by
    have := GlobalTheory.AlgFormsFin.fixedForms_finite L n π.ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hN
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n π.ρ N) ?_
    rintro f ⟨hfS, hfU⟩
    exact ⟨(π.irrS.1.le hfS).1, fun κ hκ g => congrFun (hfU κ (hCU κ hκ)) g⟩
  have hf₀V : f₀ ∈ V := ⟨hf₀S, hf₀U⟩
  haveI : Nontrivial V := ⟨⟨⟨f₀, hf₀V⟩, 0, fun e => hf₀0 (congrArg Subtype.val e)⟩⟩
  let T : Hecke ℂ (KU Dv.σw n) → Module.End ℂ V := fun h =>
    { toFun := fun f => ⟨heckeFunI L n U Dv h.1 f.1,
        GlobalTheory.T.inertHeckeOperator_preserves_rightTranslationStable L n v w Dv U hUv π.W π.S π.irrS.1.stable h.1 h.2 f.1 f.2.1,
        GlobalTheory.T.inertHeckeOperator_preserves_levelInvariants L n v w Dv U hUv hdec π.W h.1 h.2 f.1 f.2.2⟩
      map_add' := fun f f' => Subtype.ext ((GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 1 f.1 f'.1).2.2.1)
      map_smul' := fun c f => Subtype.ext ((GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 c f.1 f.1).2.2.2) }
  have hT : ∀ h (f : V), ((T h f : V) : GAf L n → π.W) = heckeFunI L n U Dv h.1 f.1 := fun _ _ => rfl
  have hcomm : ∀ a b, T a * T b = T b * T a := fun a b => LinearMap.ext fun f => Subtype.ext (by
    change heckeFunI L n U Dv a.1 (heckeFunI L n U Dv b.1 f.1) = heckeFunI L n U Dv b.1 (heckeFunI L n U Dv a.1 f.1)
    rw [← GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution L n v w Dv U hUv π.W a.1 a.2 b.1 b.2 f.1 f.2.2,
      ← GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution L n v w Dv U hUv π.W b.1 b.2 a.1 a.2 f.1 f.2.2,
      GlobalTheory.UnitarySwap.heckeCommU _ Dv.ϖ Dv.σw _ n ℂ Dv.unram a.1 a.2 b.1 b.2])
  obtain ⟨f, hf0, hμ⟩ := GlobalTheory.exists_common_eigenvector_of_commute T hcomm
  choose μ hμ using hμ
  have ev : ∀ h : Hecke ℂ (KU Dv.σw n), heckeFunI L n U Dv h.1 f.1 = μ h • f.1 := fun h =>
    congrArg Subtype.val (hμ h)
  have hf'0 : (f : GAf L n → π.W) ≠ 0 := fun e => hf0 (Subtype.ext e)
  have inj := smul_left_injective ℂ hf'0
  let l : Hecke ℂ (KU Dv.σw n) →ₗ[ℂ] ℂ :=
    { toFun := μ
      map_add' := fun h h' => inj (by
        change μ (h + h') • f.1 = (μ h + μ h') • f.1
        rw [← ev, add_smul, ← ev, ← ev]
        exact (GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h'.1 h'.2 1 f.1 f.1).1)
      map_smul' := fun c h => inj (by
        change μ (c • h) • f.1 = (c * μ h) • f.1
        rw [← ev, mul_smul, ← ev]
        exact (GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 c f.1 f.1).2.1) }
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.SatCompare.exists_satU_eq Dv.unram l
    (inj (by
      change μ _ • f.1 = (1 : ℂ) • f.1
      rw [← ev, one_smul]
      exact GlobalTheory.T.inertHeckeOperator_sphericalUnit_eq_id L n v w Dv U hUv π.W f.1 f.2.2))
    (fun h h' => inj (by
      change μ _ • f.1 = (μ h * μ h') • f.1
      rw [← ev]
      change heckeFunI L n U Dv (conv (KU Dv.σw n) h.1 h'.1) f.1 = _
      rw [GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution L n v w Dv U hUv π.W h.1 h.2 h'.1 h'.2 f.1 f.2.2, ev h',
        (GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 (μ h') f.1 f.1).2.2.2, ev h, smul_smul, mul_comm]))
  refine ⟨fun i => (α i : ℂ), f.1, f.2.1, hf'0, U, f.2.2, hUv, fun h hh => ?_⟩
  rw [ev ⟨h, hh⟩]
  congr 1
  exact hα ⟨h, hh⟩

end GlobalTheory.SatExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrueReadingWithLaws
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TrueReading

open GlobalTheory.WeilDeligne GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in

theorem readAt_exists (hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7)
    (P : Pin hL D) (hR : ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) (i : D.nd.Loc)
    (s : SplitPlace D.host.E) :
    ∃ X : ReadAt P.T i s.w, X.rc = rcAt hL D s.w ∧
      (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → IsLocS (P.rep σ).S s (X.row σ).toIrrRep) ∧
      (∀ Q, IsLocS (n := D.R.nV) (P.H.av.S i Q) s (X.rep Q).toIrrRep) ∧
      (∀ j : Fin D.R.m, j.1 + 1 = D.nd.j i → IsComp (P.tp.tup (D.nd.mu i) j) s.w X.mu) ∧
      IsComp P.cf.eta s.w X.eta := by
  classical
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have HR := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 s.w)
  have hlaws : RecLaws (rcAt hL D s.w) := HR.recLaws
  have hrow : ∀ σ, ∃ τ : Irr (s.w.adicCompletion D.host.E) D.R.r,
      D.what₂.isot (D.nd.j i) σ ≠ ⊥ → IsLocS (P.rep σ).S s τ.toIrrRep := by
    intro σ
    by_cases hσ : D.what₂.isot (D.nd.j i) σ ≠ ⊥
    · obtain ⟨τ, hτ⟩ := GlobalTheory.T.isotypic_row_local_split_exists D P.rep (D.nd.j i) (hR i).some σ hσ s
      exact ⟨Irr.ofIrrRep τ, fun _ => hτ⟩
    · exact ⟨default, fun h => absurd h hσ⟩
  choose row hrow using hrow
  have hrep : ∀ Q : D.naut.AV i, ∃ τ : Irr (s.w.adicCompletion D.host.E) (D.R.r + D.R.t),
      IsLocS (n := D.R.nV) (P.H.av.S i Q) s τ.toIrrRep := by
    intro Q
    obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i Q) s
    exact ⟨Irr.ofIrrRep τ, hτ⟩
  choose rep hrep using hrep
  have hjr := D.nd.j_range i
  let j0 : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj0 : j0.1 + 1 = D.nd.j i := by simp only [j0]; omega
  have hmuC := P.chr.muC i j0 hj0
  obtain ⟨μ, hμ, -, hμu⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E (P.tp.tup (D.nd.mu i) j0) s.w
  have hμU : GlobalTheory.SmGL.IsUnitaryChar μ := hμu (hmuC ▸ (P.chr.e1 (D.naut.muC i)).2)
  have hμP : IsComp (P.chr.e1 (D.naut.muC i)).1 s.w μ := hmuC ▸ hμ
  have eμ := GlobalTheory.T.rank_one_local_component_det hAF hL D P (D.naut.muC i) s.w μ hμP
  obtain ⟨η, hη, -, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E P.cf.eta⁻¹ s.w
  have hηP : IsComp (P.chr.e1 D.naut.etaTinv).1 s.w η := P.chr.etaTinv ▸ hη
  have eη := GlobalTheory.T.rank_one_local_component_det hAF hL D P D.naut.etaTinv s.w η hηP
  have hun : GlobalTheory.SplitWeil.IsUnram η := by
    have := (hlaws.sph 1 (Irr.ofDet 1 η hηP.1)).1
      (by rw [← eη]; exact (P.T.unr s.w _).1 (D.naut.etaTinv_def s.w).1)
    intro x hx
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 this
    have hI : (fun _ : Fin 1 => x) ∈ torusO (s.w.adicCompletion D.host.E) (Fin 1) := fun _ => hx
    have h2 := hv ⟨_, iwahori_le_KO _ _ (diagT_mem_iwahori hI)⟩
    have h3 : Matrix.GeneralLinearGroup.det (diagT (s.w.adicCompletion D.host.E) (Fin 1) fun _ => x) = x := by
      ext; simp [val_diagT]
    have h4 : (η x : ℂ) * (show ℂ from v) = (show ℂ from v) := by
      have h5 : detRep (Fin 1) η (diagT (s.w.adicCompletion D.host.E) (Fin 1) fun _ => x) v = (show ℂ from v) := by
        exact h2.trans (by simp)
      have h6 := (ofChar_apply (detChar (Fin 1) η) (diagT (s.w.adicCompletion D.host.E) (Fin 1) fun _ => x)
        (show ℂ from v)).symm.trans h5
      rw [detChar_apply, h3] at h6
      exact h6
    ext
    exact (mul_eq_right₀ hv0).1 h4
  refine ⟨⟨rcAt hL D s.w, row, rep, μ, η⁻¹, ⟨hμ.1, hμU⟩, ⟨hηP.1.inv, fun x hx => by simp [hun x hx]⟩,
    fun σ hσ => (P.row i).1 σ s _ (hrow σ hσ), fun Q => ?_, fun c hc => ?_, fun c hc => ?_⟩,
    rfl, hrow, hrep, fun j hj => ?_, ⟨hη.1.inv, fun x => ?_⟩⟩
  · rw [D.nbc.embAV_loc, P.H.emb]
    exact P.au _ _ _ _ s _ (hrep Q)
  · rw [eμ]; exact ((hlaws.iso 1 c (Irr.ofDet 1 μ hμP.1)).2 hc).symm
  · rw [inv_inv] at hc
    rw [eη]; exact ((hlaws.iso 1 c (Irr.ofDet 1 η hηP.1)).2 hc).symm
  · have : j = j0 := Fin.ext (by simp only [j0]; omega)
    subst this
    exact hμ
  · rw [MonoidHom.inv_apply, hη.2 x]
    exact inv_inv _

set_option maxHeartbeats 1000000 in

theorem exists_true_reading : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D),
    (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) →
    ∃ S : Reading P.T, IsTrue P S ∧ Laws S ∧ SuppLaws S := by
  intro hAF hL D P hR
  classical
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have hex : ∀ w : PlE D.host, IsSplitPl D.host w → ∃ s : SplitPlace D.host.E, s.w = w := by
    intro w hw
    obtain ⟨w', hw'⟩ := GlobalTheory.ToricFactor.exists_isConjPl w
    obtain ⟨s, -, hs, -⟩ :=
      GlobalTheory.SplitConjPlace.splitEx_all D w' (GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl hw hw')
    exact ⟨s, GlobalTheory.ToricFactor.isConjPl_unique hs (GlobalTheory.ToricFactor.isConjPl_symm hw')⟩
  have key : ∀ i (w : PlE D.host), IsSplitPl D.host w → ∃ X : ReadAt P.T i w, X.rc = rcAt hL D w ∧
      ∀ (s : SplitPlace D.host.E), s.w = w → ∀ Y : ReadAt P.T i s.w, HEq Y X →
        (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → IsLocS (P.rep σ).S s (Y.row σ).toIrrRep) ∧
        (∀ Q, IsLocS (n := D.R.nV) (P.H.av.S i Q) s (Y.rep Q).toIrrRep) ∧
        (∀ j : Fin D.R.m, j.1 + 1 = D.nd.j i → IsComp (P.tp.tup (D.nd.mu i) j) s.w Y.mu) ∧
        IsComp P.cf.eta s.w Y.eta := by
    intro i w hw
    obtain ⟨s₀, rfl⟩ := hex w hw
    obtain ⟨X, h1, h2⟩ := GlobalTheory.TrueReading.readAt_exists hAF hL D P hR i s₀
    refine ⟨X, h1, fun s hs Y hY => ?_⟩
    obtain rfl := GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq D.host.E s s₀ hs
    obtain rfl := eq_of_heq hY
    exact h2
  choose S hS using key
  refine ⟨S, ⟨fun i w hw => (hS i w hw).1, fun i s hw σ hσ => ((hS i s.w hw).2 s rfl _ HEq.rfl).1 σ hσ,
    fun i s hw Q => ((hS i s.w hw).2 s rfl _ HEq.rfl).2.1 Q,
    fun i w hw j hj => ?_, fun i w hw => ?_⟩, fun i w hw => ?_, fun i w hw => ?_⟩
  · obtain ⟨s, rfl⟩ := hex w hw
    exact ((hS i s.w hw).2 s rfl _ HEq.rfl).2.2.1 j hj
  · obtain ⟨s, rfl⟩ := hex w hw
    exact ((hS i s.w hw).2 s rfl _ HEq.rfl).2.2.2
  · rw [(hS i w hw).1]
    exact (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)).recLaws
  · rw [(hS i w hw).1]
    exact GlobalTheory.LocLanglands.IsRec.recSupp (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w))

end GlobalTheory.TrueReading
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsLast
section
namespace GlobalTheory.TransportLemma

theorem transport {V : Type} [AddCommGroup V] [Module ℂ V] [DecidableEq V] (T : V ≃+ V)
    {Λ₁ Λ₂ M₁ M₂ : AddSubgroup V} {S : Finset V}
    (hS : Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S)
    (h₁ : ∀ x : V, (T : V → V) x ∈ M₁ ↔ x ∈ Λ₁)
    (h₂ : ∀ x : V, (T : V → V) x ∈ M₂ ↔ x ∈ Λ₂) :
    Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → V) S) := by
  obtain ⟨hmem, hinj, hcov⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact (h₂ s).mpr (hmem s hs)
  · intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have h : (T : V → V) (s - t) ∈ M₁ := by
      rw [map_sub]; exact hxy
    rw [hinj s hs t ht ((h₁ _).mp h)]
  · intro y hy
    have hy' : T.symm y ∈ Λ₂ := (h₂ _).mp (by simpa using hy)
    obtain ⟨s, hs, hd⟩ := hcov _ hy'
    refine ⟨(T : V → V) s, Finset.mem_image_of_mem _ hs, ?_⟩
    have h : (T : V → V) (T.symm y - s) ∈ M₁ := (h₁ _).mpr hd
    rw [map_sub] at h
    simpa using h

theorem main : ∀ {V : Type} [inst : AddCommGroup V] [Module ℂ V] [inst_2 : DecidableEq V] (T : V ≃+ V) {Λ₁ Λ₂ M₁ M₂ : AddSubgroup V} {S : Finset V}, Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S → (∀ (x : V), (T : V → V) x ∈ M₁ ↔ x ∈ Λ₁) → (∀ (x : V), (T : V → V) x ∈ M₂ ↔ x ∈ Λ₂) → Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → V) S) :=
  @transport

end GlobalTheory.TransportLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectors
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigLocal

open GlobalTheory.PRep

theorem exists_trivOutside_map_loc {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L)
    (h : GL (Fin n) (s.w.adicCompletion L)) :
    ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h := by
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
  refine ⟨x, hx, ?_⟩
  rw [e]
  ext i j
  simp

def twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (θ : G → ℂ) (h1 : θ 1 = 1) (hm : ∀ a b, θ (a * b) = θ a * θ b) : Representation ℂ G V where
  toFun g := (θ g)⁻¹ • ρ g
  map_one' := by simp [h1]
  map_mul' a b := by
    rw [hm, map_mul, mul_inv, smul_mul_smul_comm]

theorem exists_eigen_of_sum {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθU : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b)
    (T : ι → V →ₗ[ℂ] W) (y : ι → V) (hf0 : ∑ i, T i (y i) ≠ 0)
    (hinv : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ v : V, v ≠ 0 ∧ ∀ h ∈ K, ρ h v = θ h • v :=
  _root_.GlobalTheory.ExistsEigenvector.exists_eigenvector hρ hK hU h1 θ hθU hmul T y hf0 hinv
set_option maxHeartbeats 1000000 in

theorem exists_eigen_local : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ), K ≤ KO (s.w.adicCompletion L) (Fin n) → (∀ h ∈ KOne (s.w.adicCompletion L) (Fin n), h ∈ K ∧ θ h = 1) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∃ y : σ.V, y ≠ 0 ∧ ∀ h ∈ K, σ.ρ h y = θ h • y := by
  intro L _ _ _ n a S hS s σ hloc c hc hci K θ hK hKOne f hf hf0 hθ
  classical
  have hrt : ∀ h ∈ K, ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h ∧ NG.rt L n x f = θ h • f := by
    intro h hh
    obtain ⟨x, hx, e⟩ := exists_trivOutside_map_loc n s c h
    exact ⟨x, hx, e, by rw [hθ x hx (e ▸ hh), e]⟩
  have hmul : ∀ k ∈ K, ∀ k' ∈ K, θ (k * k') = θ k * θ k' := by
    intro k hk k' hk'
    obtain ⟨x, hx, e, hfx⟩ := hrt k hk
    obtain ⟨x', hx', e', hfx'⟩ := hrt k' hk'
    have hxx : TrivOutside {s.v} (x * x') := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hx'
    have e2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (x * x')) = k * k' := by
      rw [map_mul, map_mul, e, e']
    have h2 := hθ (x * x') hxx (e2 ▸ mul_mem hk hk')
    rw [e2] at h2
    have h3 : NG.rt L n (x * x') f = NG.rt L n x (NG.rt L n x' f) := by
      funext g; simp [NG.rt, mul_assoc]
    rw [h3, hfx', map_smul, hfx, smul_smul] at h2
    have h4 : (θ (k * k') - θ k' * θ k) • f = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · rw [sub_eq_zero.1 h5, mul_comm]
    · exact absurd h5 hf0
  have hmem := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n a S hS s σ hloc c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨F, hF, hFsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  choose y hy using fun i => LinearMap.mem_range.1 (hF i)
  have hsum : ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y j.1) = f := by
    rw [← hFsum, Finsupp.sum, ← Finset.sum_attach F.support]
    exact Finset.sum_congr rfl fun j _ => hy j.1
  have hKo : IsOpen (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    Subgroup.isOpen_mono (fun h hh => (hKOne h hh).1) GlobalTheory.StepData.isOpen_KOne
  have hKc : IsCompact (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) hK
  refine exists_eigen_of_sum σ.smooth hKc GlobalTheory.StepData.isOpen_KOne (one_mem _) θ
    (fun g hg _ => (hKOne g hg).2) hmul (fun j : F.support => (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)))
    (fun j => y j.1) (by rw [hsum]; exact hf0) ?_
  intro k hk
  obtain ⟨x, hx, e, hfx⟩ := hrt k hk
  subst e
  have hj : ∀ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
      (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (y j.1)) =
      NG.rt L n x ((j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y j.1)) := fun j => j.1.2.2 x hx (y j.1)
  rw [Finset.sum_congr rfl fun j _ => hj j, ← map_sum, hsum, hfx]

end GlobalTheory.EigLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLengthStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInductionTensorProduct_hasFiniteLength : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (e : (Σ a, Fin (d a)) ≃ Fin n), HasFiniteLength (multiProd e fun a => (σ a).π) := by
  first | exact @GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength | exact GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength | (intros; apply GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalDoubleCosetSumScalarIrreducibleFixedStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalDoubleCosetSum_scalar_irreducible_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  first | exact @GlobalTheory.HeckeScalarDC.dc_scalar | exact GlobalTheory.HeckeScalarDC.dc_scalar | (intros; apply GlobalTheory.HeckeScalarDC.dc_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalTwistOfBlockTypeVectorStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_twist_of_blockTypeVector : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (π₁ : Irr k r) (π₂ : Irr k t) (v : π.V), IsSmoothChar χ → IsTame χ → (∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α)) → Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) → v ≠ 0 → IsBlockVec χ π.π v → IsSpherical (twist π₂.π (detChar (Fin t) χ⁻¹)) := by
  first | exact @GlobalTheory.BlockSph.sph_of_isBlockVec | exact GlobalTheory.BlockSph.sph_of_isBlockVec | (intros; apply GlobalTheory.BlockSph.sph_of_isBlockVec <;> assumption)
end

