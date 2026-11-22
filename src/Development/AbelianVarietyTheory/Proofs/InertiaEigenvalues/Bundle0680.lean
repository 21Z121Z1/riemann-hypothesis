import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0667
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0109
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0152
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0149
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0671

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankBlochKatoGAddELeFAddF
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoDef.Count

theorem finrank_blochKato_g_add_e_le_f_add_f_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → finrank ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ') ≤ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ') := by
  intro l _ P AI hT K V _ _ _ _ _ _ _ ρ V' _ _ _ _ _ _ _ ρ' m hc hc' hdR hdR' hdual
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module ℤ_[l] V' := Module.compHom V' (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hO := GlobalTheory.Published.BlochKato.goodO_padicInt (l := l)
  have hTD := CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate
  have hEC := CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler
  let A : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V, ρ := ρ, cont := hc }
  let A' : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V', ρ := ρ', cont := hc' }
  have hdual' : IsDual1 (P.PD K) ρ' ρ m.flip := by
    obtain ⟨h1, h2, h3, h4⟩ := hdual
    refine ⟨fun g y x => ?_, fun y hy => h3 y hy, fun x hx => h2 x hx, h4.symm⟩
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  obtain ⟨hfin, -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A A' m hdual
  obtain ⟨hfin', -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A' A m.flip hdual'
  haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ) := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A hfin
  haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ') := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A' hfin'
  obtain ⟨β, hβ, -, hr⟩ : ∃ β : ↥(continuousCocycles ρ) →ₗ[ℚ_[l]] ↥(continuousCocycles ρ') →ₗ[ℚ_[l]] ℚ_[l],
      (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL ρ' m a.1 b.1)) ∧
      (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 ρ' :=
    GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles hTD l P K ℚ_[l] ℤ_[l] hO A A' m hdual
  have hann : ∀ a ∈ continuousCocycles ρ, (a ∈ finiteCocycles (P.PD K) ρ ↔
      ∀ b ∈ finiteCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m a b)) :=
    (GlobalTheory.T.blochKato_exact_annihilators_periodDatum hTD hEC l P AI hT K ℚ_[l] ℤ_[l] hO A A' m hdR hdual).1
  have horth := GlobalTheory.T.de_rham_cocycle_dimension_compare l P AI hT K V ρ V' ρ' m hc hc' hdR' hdual
  have hg : geometricCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  have he : crystallineCocycles (P.PD K) ρ' ≤ continuousCocycles ρ' := fun _ h => h.1
  have hf : finiteCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  have hf' : finiteCocycles (P.PD K) ρ' ≤ continuousCocycles ρ' := fun _ h => h.1
  have hBf : B1 ρ' ≤ finiteCocycles (P.PD K) ρ' := GlobalTheory.BlochKatoAnn.B1_le_Z1f (P.PD K) A'
  have hBe : B1 ρ' ≤ crystallineCocycles (P.PD K) ρ' := by
    intro c hcB
    refine ⟨hf' (hBf hcB), ?_⟩
    obtain ⟨x, rfl⟩ := hcB
    refine ⟨x ⊗ₜ[ℚ_[l]] 1, ?_, fun g => ?_⟩
    · simp [φVB]
    · simp [cob, actVB, sub_tmul]
  have key := GlobalTheory.HyodoDef.PairLin.finrank_add_le β
    ((geometricCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype) ((finiteCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype)
    ((crystallineCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype) ((finiteCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype)
    (fun b hb => ⟨hBe ((hr b).1 hb), hBf ((hr b).1 hb)⟩)
    (fun a ha b hb => (hβ a b).2 (horth a.1 ha b.1 hb))
    (fun a => by
      rw [Submodule.mem_comap, Submodule.subtype_apply, hann a.1 a.2]
      constructor
      · intro h b hb
        exact (hβ a b).2 (h b.1 hb)
      · intro h b hb
        exact (hβ a ⟨b, hf' hb⟩).1 (h ⟨b, hf' hb⟩ hb))
  rwa [(Submodule.comapSubtypeEquivOfLe hg).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe he).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hf).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hf').finrank_eq] at key

end GlobalTheory.HyodoDef.Count
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinReciprocityMapUnique
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.ArtinUniq

variable {E : Type} [Field E] [NumberField E]

theorem eq_one_of_unit_unif {B : Type} [Group B] (v : HeightOneSpectrum (𝓞 E)) (f : (v.adicCompletion E)ˣ →* B)
    (hu : ∀ x, IsUnitAt v x → f x = 1) (hp : ∀ x, IsUnifAt v x → f x = 1) (x : (v.adicCompletion E)ˣ) : f x = 1 := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E v
  have hv : Valued.v ((π : E) : v.adicCompletion E) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hπ0 : ((π : E) : v.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  let p : (v.adicCompletion E)ˣ := Units.mk0 _ hπ0
  have hpv : Valued.v (p : v.adicCompletion E) = WithZero.exp (-1) := hv
  have hfp : f p = 1 := hp p hpv
  have key : ∀ n : ℤ, ∀ y : (v.adicCompletion E)ˣ, Valued.v (y : v.adicCompletion E) = WithZero.exp n → f y = 1 := by
    intro n
    induction n using Int.induction_on with
    | zero => exact fun y hy => hu y (by show Valued.v _ = 1; rw [hy, WithZero.exp_zero])
    | succ n ih =>
      intro y hy
      have h1 : f (y * p) = 1 := ih _ (by
        rw [Units.val_mul, map_mul, hy, hpv, ← WithZero.exp_add]
        congr 1
        ring)
      rwa [map_mul, hfp, mul_one] at h1
    | pred n ih =>
      intro y hy
      have h1 : f (y * p⁻¹) = 1 := ih _ (by
        rw [Units.val_mul, map_mul, hy, Units.val_inv_eq_inv_val, map_inv₀, hpv, ← WithZero.exp_neg,
          ← WithZero.exp_add]
        congr 1
        ring)
      rwa [map_mul, map_inv, hfp, inv_one, mul_one] at h1
  have h0 : Valued.v (x : v.adicCompletion E) ≠ 0 := by simp
  exact key _ x (WithZero.exp_log h0).symm

variable {Ω : Type} [Field Ω] [Algebra E Ω]

theorem unif_eq {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (ha' : IsGlobalArtin art')
    {B : Type} [Group B] (χ : Gab E Ω →* B) (v : HeightOneSpectrum (𝓞 E))
    (hu' : ∀ y, IsUnitAt v y → χ (art' (localIdele E v y)) = 1) (x : (v.adicCompletion E)ˣ) (hx : IsUnifAt v x) :
    χ (art (localIdele E v x)) = χ (art' (localIdele E v x)) := by
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω v
  obtain ⟨σ, hσ, e⟩ := (ha.frob v A hA _).mp ⟨x, hx, rfl⟩
  obtain ⟨y, hy, e'⟩ := (ha'.frob v A hA _).mpr ⟨σ, hσ, e⟩
  have hxy : IsUnitAt v (x * y⁻¹) := by
    show Valued.v _ = 1
    have hy0 : Valued.v (y : v.adicCompletion E) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hx, ← hy, mul_inv_cancel₀ hy0]
  have h2 : localIdele E v x = localIdele E v (x * y⁻¹) * localIdele E v y := by
    rw [← map_mul, inv_mul_cancel_right]
  conv_rhs => rw [h2, map_mul, map_mul, hu' _ hxy, one_mul, e']

end GlobalTheory.ArtinUniq

namespace GlobalTheory.ArtinUniq

variable {E : Type} [Field E] [NumberField E]

theorem eq_infPart {B : Type} [CommGroup B] (D : Ideles E →* B) (hD : IsOpen (D.ker : Set (Ideles E)))
    (hloc : ∀ v x, D (localIdele E v x) = 1) (x : Ideles E) :
    D x = D (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E x)) := by
  have hnhds : {z : Ideles E | D z = D x} ∈ nhds x := by
    have e : {z : Ideles E | D z = D x} = (fun z => x⁻¹ * z) ⁻¹' (D.ker : Set (Ideles E)) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
      rw [inv_mul_eq_one, eq_comm]
    rw [e]
    exact ((continuous_const.mul continuous_id).isOpen_preimage _ hD).mem_nhds (by simp)
  obtain ⟨T, hT⟩ := ((GlobalTheory.HeckeSplit.tendsto_truncIdele x).eventually hnhds).exists
  have h1 : ∀ v ∈ T, D (HeckeValGen.localIdele E v (GlobalTheory.HeckeSplit.finPart E v x)) = 1 := fun v _ => hloc v _
  rw [← show D (GlobalTheory.HeckeSplit.truncIdele x T) = D x from hT, GlobalTheory.HeckeSplit.truncIdele, map_mul, map_prod,
    Finset.prod_eq_one h1, mul_one]

theorem eq_one_of_local {B : Type} [CommGroup B] (D : Ideles E →* B) (hD : IsOpen (D.ker : Set (Ideles E)))
    (hdiag : ∀ k : Eˣ, D (diagUnits E k) = 1) (hinf : ∀ y ∈ infConn E, D y = 1)
    (hloc : ∀ v x, D (localIdele E v x) = 1) : D = 1 := by
  ext x
  rw [eq_infPart D hD hloc x, MonoidHom.one_apply]
  set y := GlobalTheory.HeckeSplit.infPart E x
  let C := Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ
  have hopen : IsOpen ((fun z => y⁻¹ * z) ⁻¹' (C : Set (InfiniteAdeleRing E)ˣ)) :=
    (continuous_const.mul continuous_id).isOpen_preimage _ (isOpen_connectedComponentOfOne_inf E)
  obtain ⟨k, hk⟩ := (denseRange_units_inf E).exists_mem_open hopen ⟨y, by simp [C.one_mem]⟩
  set kinf : (InfiniteAdeleRing E)ˣ := Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k with hkinf
  have hk' : y⁻¹ * kinf ∈ C := hk
  have h1 : D (GlobalTheory.HeckeSplit.infIdele E kinf) = 1 := by
    have h := eq_infPart D hD hloc (diagUnits E k)
    have e : GlobalTheory.HeckeSplit.infPart E (diagUnits E k) = kinf := Units.ext rfl
    rw [e, hdiag k] at h
    exact h.symm
  have h2 : D (GlobalTheory.HeckeSplit.infIdele E (y⁻¹ * kinf)) = 1 := hinf _ ⟨_, hk', rfl⟩
  have e : y = kinf * (y⁻¹ * kinf)⁻¹ := by group
  rw [e, map_mul, map_inv, map_mul, map_inv, h1, h2, inv_one, mul_one]

end GlobalTheory.ArtinUniq

namespace GlobalTheory.ArtinUniq

theorem val_div_sub_one_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a c : K}
    (hc : c ≠ 0) {N m : ℕ} (hm : (WithZero.log (w.valuation K c)).natAbs ≤ m)
    (h : w.valuation K (a - c) ≤ WithZero.exp (-((N : ℤ) + m))) :
    w.valuation K (a / c - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have hv : w.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]
  refine h.trans (WithZero.exp_le_exp.mpr ?_)
  have : -(m : ℤ) ≤ WithZero.log (w.valuation K c) := by omega
  omega

theorem val_le_of_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {N N' : ℤ}
    (h : w.valuation K x ≤ WithZero.exp (-N)) (hN : N' ≤ N) : w.valuation K x ≤ WithZero.exp (-N') :=
  h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem globalArtin_unique : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (art art' : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art →
    GlobalTheory.HeckeGal.IsGlobalArtin art' → art = art' := by
  intro E Ω _ _ _ _ _ art art' ha ha'
  classical
  ext x
  rw [← div_eq_one]
  refine GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup E Ω _ fun U hU => ?_
  let χ : Gab E Ω →* Gab E Ω ⧸ U := QuotientGroup.mk' U
  have hker : ∀ a : Ideles E →* Gab E Ω, IsGlobalArtin a → IsOpen ((χ.comp a).ker : Set (Ideles E)) := by
    intro a h
    have e : ((χ.comp a).ker : Set (Ideles E)) = a ⁻¹' U := by
      ext y
      simp [χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [e]
    exact hU.preimage h.quot.continuous
  have hdiag : ∀ a : Ideles E →* Gab E Ω, IsGlobalArtin a → ∀ k : Eˣ, a (diagUnits E k) = 1 := by
    intro a h k
    have hk : diagUnits E k ∈ a.ker := by
      rw [h.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hinf : ∀ a : Ideles E →* Gab E Ω, IsGlobalArtin a → ∀ y ∈ infConn E, a y = 1 := by
    intro a h y hy
    have hk : y ∈ a.ker := by
      rw [h.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hy)
    exact hk
  let ψ : Ideles E →* Gab E Ω ⧸ U := χ.comp art
  let ψ' : Ideles E →* Gab E Ω ⧸ U := χ.comp art'
  let D : Ideles E →* Gab E Ω ⧸ U := ψ / ψ'
  let V : Subgroup (Ideles E) := ψ.ker ⊓ ψ'.ker
  have hV : IsOpen (V : Set (Ideles E)) := (hker art ha).inter (hker art' ha')
  have hDV : ∀ z ∈ V, D z = 1 := fun z hz => by
    show ψ z / ψ' z = 1
    rw [MonoidHom.mem_ker.mp hz.1, MonoidHom.mem_ker.mp hz.2, div_one]
  have hDo : IsOpen (D.ker : Set (Ideles E)) := Subgroup.isOpen_mono (fun z hz => hDV z hz) hV
  have hDd : ∀ k : Eˣ, D (diagUnits E k) = 1 := fun k => by
    show χ (art _) / χ (art' _) = 1
    rw [hdiag art ha, hdiag art' ha', map_one, div_one]
  have hDi : ∀ y ∈ infConn E, D y = 1 := fun y hy => by
    show χ (art _) / χ (art' _) = 1
    rw [hinf art ha y hy, hinf art' ha' y hy, map_one, div_one]
  obtain ⟨S, M, -, hSu, hSc⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr E V hV ∅

  have hgood : ∀ v ∉ S, ∀ z, D (localIdele E v z) = 1 := fun v hv z => by
    refine eq_one_of_unit_unif v (D.comp (localIdele E v)) (fun y hy => hDV _ (hSu v hv y hy)) (fun y hy => ?_) z
    show ψ _ / ψ' _ = 1
    rw [div_eq_one]
    exact unif_eq ha ha' χ v (fun y' hy' => MonoidHom.mem_ker.mp (hSu v hv y' hy').2) y hy

  have hbad : ∀ v ∈ S, ∀ z, D (localIdele E v z) = 1 := fun v hv z => by
    have ho : IsOpen ((D.comp (localIdele E v)).ker : Set (v.adicCompletion E)ˣ) :=
      hDo.preimage (GlobalTheory.Mem.UnrAe.continuous_localIdele v)
    have ho1 : IsOpen (((1 : (v.adicCompletion E)ˣ →* Gab E Ω ⧸ U)).ker : Set (v.adicCompletion E)ˣ) := by
      rw [MonoidHom.ker_one]
      exact isOpen_univ
    refine GlobalTheory.units_adicCompletion_hom_ext E v _ (D.comp (localIdele E v)) 1 ho ho1 (fun c => ?_) z
    rw [MonoidHom.one_apply, MonoidHom.comp_apply, ← locUnit_apply]
    let m : ℕ := (WithZero.log (v.valuation E (c : E))).natAbs
    obtain ⟨a, hap, hapos⟩ :=
      GlobalTheory.FinPlaceApproxPos.approxpos_target E S (fun u => if u = v then (c : E) else 1) (M + 1 + m)
    have haW : v.valuation E (a - c) ≤ WithZero.exp (-(((M + 1 : ℕ) : ℤ) + m)) := by
      have := hap v hv
      rw [if_pos rfl] at this
      exact val_le_of_le v this (by push_cast; omega)
    have hz : v.valuation E (a / c - 1) ≤ WithZero.exp (-((M + 1 : ℕ) : ℤ)) :=
      val_div_sub_one_le v c.ne_zero le_rfl haW
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_div, zero_sub, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hz
      push_cast at hz
      omega
    let au : Eˣ := Units.mk0 a ha0
    let q : Eˣ := au / c
    have hq : (q : E) = a / c := by simp [q, au]
    have hqV : locUnit E v q ∈ V := hSc v hv q (by rw [hq]; exact val_le_of_le v hz (by push_cast; omega))
    have hprod := GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos E _ D hDo hDd hDi au (fun φ => hapos φ) S
      (fun u hu => by rw [locUnit_apply]; exact hgood u hu _)
    rw [Finset.prod_eq_single_of_mem v hv (fun u hu hne => hDV _ (hSc u hu au (by
      have := hap u hu
      rw [if_neg hne] at this
      exact val_le_of_le u this (by push_cast; omega))))] at hprod
    have e : au = c * q := by simp [q]
    rw [e, map_mul, map_mul, hDV _ hqV, mul_one] at hprod
    exact hprod
  have hD : D = 1 := eq_one_of_local D hDo hDd hDi fun v z => by
    by_cases hv : v ∈ S
    · exact hbad v hv z
    · exact hgood v hv z
  have h1 : χ (art x / art' x) = 1 := by
    rw [_root_.map_div]
    exact DFunLike.congr_fun hD x
  exact (QuotientGroup.eq_one_iff _).mp h1

end GlobalTheory.ArtinUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratedLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1f_generated_lattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) [IsTopologicalAddGroup T.V], FiniteCohomologyGeneratorsBound (P.PD K) T.L := by
  first | exact @GlobalTheory.H1fGeneration.h1fGen_tied | exact GlobalTheory.H1fGeneration.h1fGen_tied | (intros; apply GlobalTheory.H1fGeneration.h1fGen_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramifiedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1fGeneratorBoundAll_loc : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBoundAll D.loc := by
  first | exact @GlobalTheory.GenCountUnram.admGenL_all | exact GlobalTheory.GenCountUnram.admGenL_all | (intros; apply GlobalTheory.GenCountUnram.admGenL_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fKsOntoUpToPow
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.RightExactKs

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem h1fKs_onto_up_to_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), Function.Surjective π.f → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → ∀ κ₂ ∈ H1fIntegralCyclotomicLayer W T₂, ∃ (c : ℕ), ∃ κ₁ ∈ H1fIntegralCyclotomicLayer W T₁, (resHom π W.GKs).H1map κ₁ = (l ^ c : ℕ) • κ₂ := by
  intro D HW l _ K s LL h W T₁ T₂ π hπ h₁ h₂ κ₂ hκ₂
  refine (Submodule.mem_map.1 hκ₂).elim fun c₂ hc => ?_
  have hf : ((c₂ : _) : ↥W.GKs → T₂.V) ∈ BlochKatoCocyclesSubgroup ((D.loc l).PD K) W.GKs T₂ := hc.1.2
  refine hf.2.elim fun x hx => ?_
  refine (lift_cocycle (D.loc l) (D.locA l) (D.locT l) h.2.2.1 W ((HW l).W_s K s LL h)
    T₁ T₂ π hπ h₁ h₂ c₂ κ₂ hc.2 x hx).elim fun n hn => hn.elim fun c₁ hn =>
      hn.elim fun κ₁ hn => ?_
  refine ⟨n, κ₁, Submodule.mem_map.2 ⟨c₁, ⟨c₁.2, ?_⟩, hn.1⟩, hn.2.2⟩
  exact ⟨mem_continuousCocycles_restrictLattice T₁ W.GKs c₁, hn.2.1⟩

end GlobalTheory.NL.RightExactKs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasStringOfLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.LiftInjProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hasString_of_lift (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (ok : Pl D.host.E → Prop)
    (h1 : UnrCorr R i t fun w => ¬ ok w) (h1' : UnrCorr R i t ok)
    (h2 : ParamsEx R i t) (h3 : DownEig R i t) {h} (hh : GlobalTheory.Hk3.IsOpsV R i t h) {s : Sys D} {y} (hy : IsEigV R i t h s y)
    (h0 : R.thF i t y ≠ 0) : HasString R i t s := by
  obtain ⟨c, hc⟩ := h3 h hh s
  obtain ⟨B, hB⟩ := h2.1 h hh s y hy (fun e => h0 (by rw [e, map_zero]))
  obtain ⟨B', hB', hb⟩ := h2.2 c ((Submodule.ne_bot_iff _).2 ⟨_, hc y hy, h0⟩)
  refine ⟨B, hB, fun w hw => ⟨(B' w).map (fun a : ℂˣ => ((a * valV R i t w * (valW R i t w)⁻¹ : ℂˣ) : ℂ)), ?_, fun a ha => ?_⟩⟩
  · by_cases hw' : ok w
    · exact h1' h hh s c y hy h0 (hc y hy) B B' hB hB' w hw hw'
    · exact h1 h hh s c y hy h0 (hc y hy) B B' hB hB' w hw hw'
  obtain ⟨b, hb', rfl⟩ := Multiset.mem_map.1 ha
  have e1 : ‖(valV R i t w : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
  have e2 : ‖(valW R i t w : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
  simpa [e1, e2] using hb w hw b hb'

theorem liftInj_of_typeNZ : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → (∀ i, TypeNZ R i A.μ0 ∧ DownEig R i A.μ0 ∧ UnrCorr R i A.μ0 (fun w => ¬ IsConjPl w w) ∧ UnrCorr R i A.μ0 (fun w => IsConjPl w w) ∧ ParamsEx R i A.μ0) → GlobalTheory.LiftRows.LiftInj R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ hZ
  intro i h hops s x y hx hy hxne hyG hy0
  obtain ⟨hT, hDE, hU1, hU2, hPE⟩ := hZ i
  have hF : R.thF i A.μ0 x ≠ 0 := by
    intro h0
    apply hxne
    apply (hG.core.models.HW i (sg0 D A)).1
    rw [hG.core.thP.thG i A.μ0 x, h0, map_zero, map_zero]
  exact hT h hops s (hasString_of_lift R i A.μ0 (fun w => IsConjPl w w) hU1 hU2 hPE hDE hops hx hF) y hy hyG hy0

end GlobalTheory.LiftInjProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerAlt
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace GlobalTheory.DepthZeroWildInertiaEigenvalues

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.PRep ValuativeRel in

theorem main : GlobalTheory.Published.DepthZeroWild := by
  intro E Ω _ _ _ _ _ A w h rc ⟨a, ha, ε, _, H⟩ n σ _ ⟨v, hv, hfix⟩ t ht hw
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  obtain ⟨e⟩ := GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ
  have h1 : fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1)) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨e.toLinearEquiv.symm v, ?_, fun h0 => hv (e.toLinearEquiv.symm.map_eq_zero_iff.1 h0)⟩
    have key : ∀ κ ∈ KOne (w.adicCompletion E) (Fin n), σ.cl.rep.ρ κ (e.toLinearEquiv.symm v) = e.toLinearEquiv.symm v := by
      rintro _ ⟨g, hg, rfl⟩
      apply e.toLinearEquiv.injective
      have hi := LinearMap.congr_fun (e.isIntertwining' (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation (w.adicCompletion E)).integer) _) g)) (e.toLinearEquiv.symm v)
      refine hi.trans ?_
      have e3 : e.toLinearMap (e.toLinearEquiv.symm v) = v := e.toLinearEquiv.apply_symm_apply v
      rw [LinearMap.comp_apply, e3, LinearEquiv.apply_symm_apply]
      refine hfix _ fun i j => ?_
      rw [← he.lt_one_iff_lt_one]
      have hg' := congrArg (fun x : GL (Fin n) _ => x.val i j) (MonoidHom.mem_ker.1 hg)
      have hm : IsLocalRing.residue _ ((g.val - 1) i j) = 0 := by
        simp only [Matrix.sub_apply, map_sub, sub_eq_zero]
        refine hg'.trans ?_
        simp [Matrix.one_apply, apply_ite]
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hm
      convert hm using 2
      simp [Matrix.one_apply, apply_ite]
      split_ifs <;> rfl
    intro κ
    simpa using key κ κ.2
  obtain ⟨m, b, hb, hb'⟩ := (H.depth _).1 h1
  have hd := H.dim (cls σ)
  rw [← hb] at hd ⊢
  rw [WD.lpDim_mk] at hd
  have hW : Formalism.MainNotions.BlochKatoReduction.IsWild A ((ineIncl h ⟨t, ht⟩ : Weil h) : G E Ω) := by
    refine ⟨ht, fun y hy => ?_⟩
    have h2 := hw y hy
    have h0 : A.valuation y ≠ 0 := by simpa using hy
    have e2 : t y / y - 1 = (t y - y) / y := by field_simp
    rw [e2, map_div₀, div_lt_one₀ (zero_lt_iff.mpr h0)] at h2
    exact h2
  rw [WD.inePol_of_mem_Ine _ ht, WD.charPol_mk, hb' _ hW, LinearMap.charpoly_one, hd]

end GlobalTheory.DepthZeroWildInertiaEigenvalues

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationTwistMultisegment
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL

theorem isL_map_tw_of_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
    IsL 𝔪 x.rep → IsL (𝔪.map fun Δ => Δ.tw χ hχ) (x.tw χ hχ).rep := by
  intro k _ _ _ _ _ 𝔪 x χ hχ h
  exact (h.tw χ hχ).of_equiv (x.twEquiv χ hχ)

end GlobalTheory.LocGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableOfInvertiblePeriodMatrixSemistableRiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemistable_of_invertible_periodMatrix_semistableRing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (Q : GL n (Bst P)), (∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P)) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → IsSst P ρ := by
  first | exact @GlobalTheory.PMon.isSst_of_periodMatrix | exact GlobalTheory.PMon.isSst_of_periodMatrix | (intros; apply GlobalTheory.PMon.isSst_of_periodMatrix <;> assumption)
end

