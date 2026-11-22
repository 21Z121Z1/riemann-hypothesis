import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0898
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0002
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0027
import Development.DiscreteGroups.GlobalIrreducibility.ActKEEqSelfLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0424
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0043
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0892
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0921
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0904
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0903
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0993
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0792
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameUniformizerPower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtAdicCompletion
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.UnitaryReadS
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0838
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0712
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ArtinTr
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL

theorem GlobalTheory.LocLanglands.artin_transport_m : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (c : Ω ≃+* Ω) (j : E →+* E) (i : w.adicCompletion E ≃+* w'.adicCompletion E), (∀ z, c z ∈ A' ↔ z ∈ A) → (∀ x, c (algebraMap E Ω x) = algebraMap E Ω (j x)) → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E _ (j x)) → ∀ {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}, Laws a ha ε (ParLaws.locRec hL h) → ∀ {a' : Weil h' →* (w'.adicCompletion E)ˣ} {ha' : IsLocalArtin h' a'} {ε' : EpsFamily A'}, Laws a' ha' ε' (ParLaws.locRec hL h') → ∀ (ξ : (w'.adicCompletion E)ˣ →* ℂˣ), IsSmoothChar ξ → ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, c ((σ : G E Ω) z) = (σ' : G E Ω) (c z)) → ξ (Units.map i.toRingHom.toMonoidHom (a σ)) = ξ (a' σ') := by
  intro hL E Ω _ _ _ _ _ A A' w w' h h' c j i hcA hcj hi hij a ha ε H a' ha' ε' H' ξ hξ σ σ' hσ
  set iU : (w.adicCompletion E)ˣ →* (w'.adicCompletion E)ˣ := Units.map i.toRingHom.toMonoidHom with hiU
  have hcont : Continuous iU := Units.continuous_map hi
  have hs : IsSmoothChar (ξ.comp iU) := hξ.comp iU hcont
  obtain ⟨b, b', hb, hb', -, hρ⟩ := UpperTheory.One.M.Old.field hL
    (ParLaws.isRec_locRec hL h) (ParLaws.isRec_locRec hL h') c j i hcA hcj hi hij 1
    (IrrRep.det (Fin 1) (ξ.comp iU) hs) (IrrRep.det (Fin 1) ξ hξ) (LinearEquiv.refl ℂ ℂ) (by
      intro g v
      have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom g) =
          iU (Matrix.GeneralLinearGroup.det g) := by
        ext
        simp [hiU, RingHom.map_det]
      show (LinearEquiv.refl ℂ ℂ) ((ξ.comp iU (Matrix.GeneralLinearGroup.det g) : ℂ) • v) = _
      show _ = ((ξ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom g)) : ℂ) • v)
      rw [hd]
      rfl) (UpperTheory.One.M.good_ofChar _ hs)
  have e1 : WD.mk b = WD.lpOfChar h ((ξ.comp iU).comp a) (ha.smooth hs) := hb.trans (H.one _ hs)
  have e2 : WD.mk b' = WD.lpOfChar h' (ξ.comp a') (ha'.smooth hξ) := hb'.trans (H'.one _ hξ)
  have k := congrFun (congrArg (fun f : Module.End ℂ (Fin 1 → ℂ) => f (fun _ => 1)) (hρ σ σ' hσ)) 0
  simp only [b.rho_apply_of_mk_eq_lpOfChar _ _ e1, b'.rho_apply_of_mk_eq_lpOfChar _ _ e2] at k
  simp at k
  exact Units.ext (by simpa [hiU] using k)

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ClassMapD
section
section
noncomputable section
namespace GlobalTheory.SerSys
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
variable {g : ℕ} [Fact g.Prime]

def IsClassMapD {LP : Type*} (dim : LP → ℕ) (rc : ∀ n, QRep g n → LP) : Prop :=
  ∀ n (π : QRep g n), IrrSm π → dim (rc n π) = n ∧ ∀ π' : QRep g n, IrrSm π' → fixK1 π'.ρ ≠ ⊥ → (rc n π = rc n π' ↔ Nonempty (π ≅ π'))

end GlobalTheory.SerSys
end
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M

end UpperTheory.One.M
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.TypeRec GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end DiscreteGroups.sglob.DzType.Rt
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace GlobalTheory.LabPin
open GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end GlobalTheory.LabPin
namespace GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.LabPin
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.DzValue
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace DiscreteGroups.sglob.DzType.Rt
open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.DepthZeroRankOneLabel
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem value_at_gen_m [IsTotallyComplex E] (H : DiscreteGroups.sglob.DzType.DepthZeroInertiaBig) {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {ε : EpsFamily A} (hε : IsDeligneEps ε) {rc : IrrGL (w.adicCompletion E) → WD h} (hl : Laws a ha ε rc)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : GlobalTheory.GLq.LabelDatum g) (t : G E Ω) (ht : t ∈ Ine (F := E) A)
    (hT : TameCoupled A κ t L.gen) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ)
    (htm : GlobalTheory.SplitWeil.IsTame μ) (n : ℕ) (hn : n.Coprime g)
    (hgen : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (n : ZMod g) = L.gen 1) (x : (w.adicCompletion E)ˣ)
    (hx : valuation (w.adicCompletion E) ((x : w.adicCompletion E) - (n : w.adicCompletion E)) < 1) :
    μ (a (ineIncl h ⟨t, ht⟩)) = μ x := by
  haveI : IsLocalHom (PadicInt.toZMod (p := g)) := IsLocalHom.of_surjective _ (ZMod.ringHom_surjective _)
  let u₀ : (ZMod g)ˣ := ZMod.unitOfCoprime n hn
  have hu₀ : IsUnit ((n : ℕ) : ℤ_[g]) := isUnit_of_map_unit (PadicInt.toZMod (p := g)) _ (by
    rw [map_natCast]; exact u₀.isUnit)
  obtain ⟨θ, hθ⟩ := exists_red i hi hw μ htm
  obtain ⟨P, hP, e⟩ := GlobalTheory.Published.DepthZeroModel.exists_label L θ u₀ (by rw [ZMod.coe_unitOfCoprime]; exact hgen)
  have h1 := H E Ω g A w h rc (UpperTheory.One.M.Old.close hε hl) i hi κ L t ht hT 1 (Or.inl rfl) (GlobalTheory.SmGL.IrrRep.det (Fin 1) μ hμ)
    (IrrGL.isCusp_ofChar μ hμ) _ P hP (inflates_units i θ μ hμ hθ)
  have h2 : rc (cls (GlobalTheory.SmGL.IrrRep.det (Fin 1) μ hμ)) = _ := hl.one μ hμ
  rw [h2, e, WD.inePol_of_mem_Ine _ ht, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd] at h1
  have h3 := congrArg (fun p => p.coeff 0) h1
  have h4 : μ (a (ineIncl h ⟨t, ht⟩)) = θ u₀ := Units.ext (by simpa using h3)
  have h5 : u₀ = Units.map (PadicInt.toZMod (p := g)).toMonoidHom hu₀.unit := Units.ext (by simp [u₀])
  rw [h4, h5, hθ]

  set y : (w.adicCompletion E)ˣ :=
    Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom hu₀.unit) with hy
  have hyn : (y : w.adicCompletion E) = n := by simp [hy]
  have hyi : valuation (w.adicCompletion E) ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
    have e4 : ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        i (((hu₀.unit⁻¹ : ℤ_[g]ˣ) : ℤ_[g]) : ℚ_[g]) := by
      rw [hy, ← map_inv, ← map_inv]; rfl
    rw [e4]; exact val_int_le i hi _
  have h6 : μ (x * y⁻¹) = 1 := htm _ (by
    have e3 : ((x * y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        ((x : w.adicCompletion E) - n) * ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
      rw [← hyn, sub_mul, Units.mul_inv]; simp
    rw [e3, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hx hyi)
  rw [map_mul, map_inv, mul_inv_eq_one] at h6
  exact h6.symm

end DiscreteGroups.sglob.DzType.Rt
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Imports
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.One.M.New.field {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h}
    (_hL : RecTExists) {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    {rc' : IrrGL (w'.adicCompletion E') → WD h'} (H : IsRecT h rc) (H' : IsRecT h' rc') : UpperTheory.One.M.FieldG rc rc' :=
  UpperTheory.One.M.fieldGT E Ω A w h E' Ω' A' w' h' rc rc' H H'
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.IsQgOfOver
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.One.M.isQg_of_over (D : D7) (k : Fin 2) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    UpperTheory.One.M.IsQg (w.adicCompletion D.host.E) := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have key : Function.Surjective (Formalism.BasicNotions.Examples₂.LocF.emb w (D.host.g k) hw) := by
    refine GlobalTheory.TypeRec.Model.emb_surjective _ _ _ (fun h => ?_)
      (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw)
    have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (D.host.g_prime k).ne_zero
    have hs := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
      (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard (D.host.g_prime k) (D.nd.g_split k)).2
    have := hs w.asIdeal (by rw [← sq, Ideal.dvd_span_singleton]; exact h)
    exact w.isPrime.ne_top (Ideal.isUnit_iff.1 this)
  exact ⟨_, this, RingEquiv.ofBijective _ ⟨RingHom.injective _, key⟩, Formalism.BasicNotions.Examples₂.LocF.emb_cont _ _ hw⟩

end

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroLoc

end GlobalTheory.DepthZeroLoc
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroTame

end GlobalTheory.DepthZeroTame
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Pointwise
namespace GlobalTheory.DepthZeroType

end GlobalTheory.DepthZeroType
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.PairLiftH
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.SplitPairLift

namespace UpperTheory.One.M

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def RepGood {T : WDTie N A} (S : Reading T) : Prop := ∀ i w hw P, GoodI ((S i w hw).rep P)

end UpperTheory.One.M
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RankOne
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroRankOneLabel
open ValuativeRel
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
variable (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
end GlobalTheory.DepthZeroRankOneLabel
namespace GlobalTheory.DepthZeroRankOneLabel
open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end GlobalTheory.DepthZeroRankOneLabel
namespace GlobalTheory.DepthZeroRankOneLabel
open GlobalTheory.TameRes
end GlobalTheory.DepthZeroRankOneLabel
namespace GlobalTheory.DepthZeroRankOneLabel
end GlobalTheory.DepthZeroRankOneLabel

open GlobalTheory.WeilDeligne in
theorem GlobalTheory.DepthZeroRankOneLabel.wild_trivial_m (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ) (hT : GlobalTheory.SplitWeil.IsTame μ)
    (a : Weil (D.nd.plOm.2 (D.naut.plGw k v)) →* ((D.naut.plGw k v).adicCompletion D.host.E)ˣ)
    (ha : GlobalTheory.LocLanglands.IsLocalArtin (D.nd.plOm.2 (D.naut.plGw k v)) a)
    (ε : GlobalTheory.LocLanglands.EpsFamily (D.nd.plOm.1 (D.naut.plGw k v)))
    (rc : GlobalTheory.LocGL.IrrGL ((D.naut.plGw k v).adicCompletion D.host.E) → WD (D.nd.plOm.2 (D.naut.plGw k v)))
    (hl : GlobalTheory.LocLanglands.Laws a ha ε rc) :
    ∀ σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)),
      (σ : G D.host.E D.nd.Om) ∈ Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) → (μ.comp a) σ = 1 := by
  have htame := GlobalTheory.SerSys.LabDepth.tame_of_isTameWD (UpperTheory.One.M.Old.depth hl (GlobalTheory.LocGL.IrrGL.ofChar μ hμ) (UpperTheory.One.M.good_ofChar μ hμ) (by
    refine GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv
      (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep (Irr.ofDet 1 μ hμ).toIrrRep).some.symm ?_
    refine (Submodule.ne_bot_iff _).2 ⟨(show (Irr.ofDet 1 μ hμ).V from (1 : ℂ)), GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_,
      (one_ne_zero : (1 : ℂ) ≠ 0)⟩
    have hu' : u ∈ GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin 1) := hu
    have h1 := GlobalTheory.StepData.mem_KOne.1 hu' 0 0
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at h1
    have h2 : μ (Matrix.GeneralLinearGroup.det u) = 1 := hT _ (by
      have e : ((Matrix.GeneralLinearGroup.det u : (_)ˣ) : (D.naut.plGw k v).adicCompletion D.host.E) = u.val 0 0 := by
        simp [Matrix.det_fin_one]
      rw [e]; exact h1)
    change (GlobalTheory.SmGL.detRep (Fin 1) μ) u (1 : ℂ) = (1 : ℂ)
    simp [GlobalTheory.SmGL.detRep, h2]))
  rw [hl.one, WD.lpOfChar, WD.tame_mk] at htame
  intro σ hσ
  have h2 := LinearMap.congr_fun (htame σ hσ) (fun _ => 1)
  have h3 := congrFun h2 0
  simpa using h3

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RowTame
section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands

theorem tame_locRec_m {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hL : GlobalTheory.Published.LocalLanglandsGL) (h : IsPlaceOver A w) {n : ℕ}
    (τ : IrrRep (GL (Fin n) (w.adicCompletion E)))
    (hf : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n)) ≠ ⊥)
    (hq : UpperTheory.One.M.IsQg (w.adicCompletion E)) :
    (GlobalTheory.CuspRep.ParLaws.locRec hL h (cls τ)).tame := by
  obtain ⟨_, _, _, -, H⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL h
  have hx : GlobalTheory.PRep.fixed (cls τ).rep (GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin (cls τ).1)) ≠ ⊥ :=
    GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep τ).some.symm hf
  obtain ⟨m, b, hb, hw⟩ := haveI := UpperTheory.One.M.charZero_compl w; UpperTheory.One.M.Old.depth H _ (UpperTheory.One.M.good_of_fixed hq _ hx) hx
  rw [← hb, GlobalTheory.WeilDeligne.WD.tame_mk]
  intro g hg
  refine hw g ⟨GlobalTheory.WeilDeligne.Wild_le_Ine hg, fun x hx0 => ?_⟩
  have h1 := hg x hx0
  have e : ((g : G E Ω) x - x) = ((g : G E Ω) x / x - 1) * x := by field_simp
  rw [e, map_mul]
  have h2 : (0 : _) < A.valuation x := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff _).2 hx0
  calc A.valuation ((g : G E Ω) x / x - 1) * A.valuation x < 1 * A.valuation x := by
        exact mul_lt_mul_of_pos_right h1 h2
    _ = A.valuation x := one_mul _

end Loc
end GlobalTheory.RowPar
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)

theorem parOf_tame_m (σ : D.what₂.FT) (s : SplitPlace D.host.E) (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hτ : IsLocS (rep σ).S s τ)
    (hf : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion D.host.E) (Fin D.R.r)) ≠ ⊥)
    (hq : UpperTheory.One.M.IsQg (s.w.adicCompletion D.host.E)) :
    (parOf hL D rep σ s.w).tame := by
  rw [parOf_eq hL D rep σ s τ hτ]
  exact tame_locRec_m hL _ τ hf hq

end Loc
end GlobalTheory.RowPar
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
end Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_rowWD_rowTrue_m : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), RowDepth D rep →
    ∃ Rw : RowWD D, RowTrue hL D rep Rw.par Rw.sat := by
  intro hL D rep hD
  refine ⟨⟨parOf hL D rep, fun σ => satOf (rep σ).S, parOf_dim hL D rep, fun σ k v => ?_⟩, ?_, ?_⟩
  · obtain ⟨s, τ, hs, hl, hf⟩ := hD σ k v
    obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
    have hq : UpperTheory.One.M.IsQg ((D.naut.plGw k v).adicCompletion D.host.E) := ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩
    rw [← hs] at hq ⊢
    exact parOf_tame_m hL D rep σ s τ hl hf hq
  · intro σ s τ hτ
    exact parOf_eq hL D rep σ s τ hτ
  · intro σ v w hO Dv hα
    exact satOf_spec (rep σ).S v w hO Dv hα

end GlobalTheory.RowPar
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.UnitaryReadTrue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC GlobalTheory.UnitaryReadTrue
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.One.M

theorem noSplit (D : D7) (w : PlE D.host) (v) (hw : ¬ IsSplitPl D.host w) (hv : NG.OverPl w v) : NoSplit D.host.E v := by
  intro s hs
  by_cases e : s.w = w
  · exact hw (e ▸ GlobalTheory.SplitPlaceConj.isSplitPl_w D s)
  · refine not_isSplitAt D w hw ⟨s.w, e, HeightOneSpectrum.ext ?_⟩
    exact s.w_under.trans ((congrArg HeightOneSpectrum.asIdeal hs).trans hv.symm)

end UpperTheory.One.M
end
end

