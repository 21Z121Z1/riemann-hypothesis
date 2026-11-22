import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0002
import Formalism.SatakeDualWeyl.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped InnerProductSpace TensorProduct
open Matrix

namespace Formalism.L2.SG.RowDict

section Conj

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

def conjL : Lp ℂ 2 μ ≃ₗᵢ⋆[ℂ] Lp ℂ 2 μ where
  toFun := star
  invFun := star
  map_add' f g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_add f g, Lp.coeFn_add (star f) (star g), Lp.coeFn_star f,
      Lp.coeFn_star g] with x h1 h2 h3 h4 h5
    rw [h1, h3, Pi.star_apply, h2, Pi.add_apply, Pi.add_apply, h4, h5, Pi.star_apply, Pi.star_apply, star_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f, Lp.coeFn_smul ((starRingEnd ℂ) c) (star f),
      Lp.coeFn_star f] with x h1 h2 h3 h4
    rw [h1, h3, Pi.star_apply, h2, Pi.smul_apply, Pi.smul_apply, h4, Pi.star_apply, smul_eq_mul, smul_eq_mul,
      star_mul', starRingEnd_apply]
  left_inv f := star_star f
  right_inv f := star_star f
  norm_map' f := by
    show ‖star f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f), eLpNorm_star]

theorem conjL_apply (f : Lp ℂ 2 μ) : conjL μ f = star f := rfl

end Conj

section Good

variable {D : D7} (X : HidaSetting D)

def wLat (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E) :=
  Submodule.span (𝓞 X.B.I.E) {z | ∃ a : 𝓞 X.B.I.E, (∃ b ∈ w.asIdeal, X.ιE (a : X.B.I.E) = (b : D.host.E)) ∧
    ∃ y ∈ X.B.I.L, z = (a : X.B.I.E) • y}

abbrev wLf (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (IntAf X.B.I.F X.B.I.E) (Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
  lamAf (F := X.B.I.F) (wLat X w)

def IsRedBasis (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (b : Fin D.R.r → (Fin X.B.I.n → X.B.I.E)) :
    Prop :=
  (∀ i, b i ∈ X.B.I.L) ∧ ∀ y ∈ X.B.I.L, ∃ c : Fin D.R.r → ℤ, y - ∑ i, (c i : X.B.I.E) • b i ∈ wLat X w

def RedMat (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (g : ℕ) (x : X.B.I.Gf)
    (M : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)) : Prop :=
  ∃ b, IsRedBasis X w b ∧ ∀ i, X.B.I.fmat x *ᵥ incl X.B.I (b i) -
    ∑ j, (((M j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (b j) ∈ wLf X w

def GoodAt (x : X.B.I.Gf) (γ : G0g D.nd) : Prop :=
  ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
    RedMat X (D.naut.plGw kv.1 kv.2) (D.host.g kv.1) x ((γ kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))

open Classical in

def eg (x : X.B.I.Gf) : ℂ :=
  if h : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ then
    D.ntypes.e0.coeff (Classical.choose h.2) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ)
  else 0

def RedExists : Prop := ∀ x ∈ X.B.I.Kset, ∃ γ : G0g D.nd, GoodAt X x γ

def EgWellDef : Prop :=
  ∀ x (γ γ' : G0g D.nd), GoodAt X x γ → GoodAt X x γ' → D.ntypes.e0.coeff γ = D.ntypes.e0.coeff γ'

def IdempotentRealFixed (D : D7) : Prop := ∀ γ : G0g D.nd, star (D.ntypes.e0.coeff γ) = D.ntypes.e0.coeff γ

structure GoodOp where
  Rg : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund
  Rg_spec : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eg X) Rg

end Good

section Rows

open Formalism.L2.SG.ProjRows

variable {D : D7} (X : HidaSetting D)

abbrev L2X : Type := X.B.I.L2 X.B.μf X.B.fund

abbrev muX : Measure X.B.I.GA := (X.B.I.muA X.B.μf).restrict X.B.fund

def goodSub (G : GoodOp X) : Submodule ℂ (L2X X) :=
  HHX X ⊓ LinearMap.ker ((G.Rg : L2X X →ₗ[ℂ] L2X X) - LinearMap.id)

def EEC (G : GoodOp X) : Submodule ℂ (L2X X) :=
  (goodSub X G).comap (conjL (muX X)).toLinearEquiv.toLinearMap

theorem mem_EEC (G : GoodOp X) (F : L2X X) : F ∈ EEC X G ↔ star F ∈ goodSub X G := Iff.rfl

def conjHH (G : GoodOp X) : EEC X G →ₗᵢ⋆[ℂ] HHX X where
  toFun F := ⟨star (F : L2X X), ((mem_EEC X G F).1 F.2).1⟩
  map_add' F F' := Subtype.ext (by
    show star ((F : L2X X) + F') = star (F : L2X X) + star (F' : L2X X)
    exact (conjL (muX X)).map_add _ _)
  map_smul' c F := Subtype.ext (by
    show star (c • (F : L2X X)) = (starRingEnd ℂ c) • star (F : L2X X)
    exact (conjL (muX X)).map_smulₛₗ c _)
  norm_map' F := by
    show ‖star (F : L2X X)‖ = ‖(F : L2X X)‖
    exact (conjL (muX X)).norm_map _

theorem conjHH_apply (G : GoodOp X) (F : EEC X G) : ((conjHH X G F : HHX X) : L2X X) = star (F : L2X X) := rfl

end Rows

def IsConjOnto {E W H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (s : E → H) (c : W →ₗᵢ⋆[ℂ] H) : Prop :=
  ∃ j : E ≃ₗᵢ[ℂ] W, ∀ F, s F = c (j F)

section Comparison₂

open Formalism.L2.SG.ProjRows

variable {D : D7} (X : HidaSetting D)

def RowDictTie (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) : Prop :=
  IsConjOnto (fun F : D.what₂.EE => ι (D.sEE F)) (conjHH X G)

theorem finiteDimensional_HHX (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) : FiniteDimensional ℂ (HHX X) := LinearEquiv.finiteDimensional ι.toLinearEquiv

theorem dall_eq (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) : D.what₂.Dall = Module.finrank ℂ (HHX X) := by
  rw [← D.s_HH]
  exact ι.toLinearEquiv.finrank_eq

theorem drows_eq {G : GoodOp X} {ι : D.s.HH ≃ₗᵢ[ℂ] HHX X} (h : RowDictTie X G ι) :
    D.what₂.Drows = Module.finrank ℂ (EEC X G) := by
  obtain ⟨j, -⟩ := h
  rw [← j.toLinearEquiv.finrank_eq, Module.finrank_eq_card_basis D.what₂.onb.toBasis, Fintype.card_fin]

theorem range_sEE {G : GoodOp X} {ι : D.s.HH ≃ₗᵢ[ℂ] HHX X} (h : RowDictTie X G ι) (y : HHX X) :
    (y : L2X X) ∈ goodSub X G ↔ ∃ F : D.what₂.EE, ι (D.sEE F) = y := by
  obtain ⟨j, hj⟩ := h
  have hj' : ∀ F, ι (D.sEE F) = conjHH X G (j F) := hj
  constructor
  · intro hy
    have hmem : star (y : L2X X) ∈ EEC X G := by
      rw [mem_EEC, star_star]; exact hy
    refine ⟨j.symm ⟨star (y : L2X X), hmem⟩, ?_⟩
    rw [hj', LinearIsometryEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [conjHH_apply]
    exact star_star _
  · rintro ⟨F, rfl⟩
    rw [hj', conjHH_apply]
    exact (mem_EEC X G _).1 (j F).2

def EEB (G : GoodOp X) : Submodule ℂ (L2X X) :=
  (HHX X).comap (conjL (muX X)).toLinearEquiv.toLinearMap ⊓ LinearMap.ker ((G.Rg : L2X X →ₗ[ℂ] L2X X) - LinearMap.id)

def RgReal (G : GoodOp X) : Prop := ∀ φ : L2X X, star (G.Rg φ) = G.Rg (star φ)

theorem eec_eq_eeb (G : GoodOp X) (h : RgReal X G) : EEC X G = EEB X G := by
  ext F
  rw [mem_EEC]
  simp only [EEB, goodSub, Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker]
  refine and_congr Iff.rfl ?_
  simp only [LinearMap.sub_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe, sub_eq_zero]
  rw [← h]
  exact star_inj

theorem D_eq_of (hB : Formalism.L2.SG.RowsDef.RowsBij) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X)
    (hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v)) (hIrr : ∀ v, IsIrredOn (UJset (X.B.I.ε v)) (X.B.σ v))
    (hF : ∀ v, IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)))
    (hw : ∀ v, ‖X.B.w v‖ = 1)
    (hint : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v)
      (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v))) (Formalism.REAL.muG (X.B.I.ε v))) :
    X.B.D = D.what₂.Dall := by
  rw [dall_eq X ι]
  exact (Formalism.L2.SG.RowsDef.RowsAut.D_eq_finrank_HH hB X.B _ hU hIrr hF hw hint X.Rph X.Rph_spec).1

theorem D_eq_holds (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X)
    (hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v)) (hIrr : ∀ v, IsIrredOn (UJset (X.B.I.ε v)) (X.B.σ v))
    (hF : ∀ v, IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)))
    (hw : ∀ v, ‖X.B.w v‖ = 1)
    (hint : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v)
      (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v))) (Formalism.REAL.muG (X.B.I.ε v))) :
    X.B.D = D.what₂.Dall :=
  D_eq_of X Formalism.L2.SG.Closed.RowsBij_holds ι hU hIrr hF hw hint

def DstarAgree : Prop :=
  Formalism.MainNotions.StandardLattice.DstarD D =
    X.B.I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) X.B.μf X.B.fund X.B.e

theorem dstar_iff (hT : AutTie D X.B X.pl) : D.what₂.Dstar = Formalism.MainNotions.StandardLattice.DstarD D ↔ DstarAgree X := by
  rw [hT.Dstar_eq, DstarAgree, eq_comm]

end Comparison₂

end Formalism.L2.SG.RowDict
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SettingExistsAdapted
section
noncomputable section

open scoped TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

set_option linter.dupNamespace false

namespace Formalism.L2.SG.SettingExistsAdapted

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def toHostF (X : HidaSetting D) (a : X.B.I.F) : D.host.F :=
  ⟨X.ιE (algebraMap X.B.I.F X.B.I.E a), (X.ιE_F _).2 ⟨a, rfl⟩⟩

def SplitPin (X : HidaSetting D) : Prop :=
  ∀ (p : HeightOneSpectrum (𝓞 D.host.F))
    (sp : Formalism.MainNotions.S.Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Formalism.MainNotions.S.Loc.resChar p)),
    (D.s.atP p).split = some sp →
    ∃ (v : HeightOneSpectrum (𝓞 X.B.I.F)) (φ : v.adicCompletion X.B.I.F ≃+* (D.s.atP p).Fp)
      (c : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F →+* (D.s.atP p).Ep),
      Continuous φ ∧
      (∀ a : X.B.I.F, φ (algebraMap X.B.I.F (v.adicCompletion X.B.I.F) a) = (D.s.atP p).ιF (toHostF X a)) ∧
      (∀ x : X.B.I.E, c (x ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) = (D.s.atP p).ιE (X.ιE x)) ∧
      (∀ a : v.adicCompletion X.B.I.F,
        c ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] a) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (φ a)) ∧
      sp.e (c (Formalism.UG.prV (E := X.B.I.E) v X.ew)) = (1, 0)

variable (D)

def RescaleStep3 : Prop :=
  ∀ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I), X.MeasTie hb →
    ∃ (mg : Formalism.L2.SG.Measures.MeasG X.B.I.cm.sig X.B.I.J D.R.rS) (hg : mg.IsTextNorm)
      (mw : ∀ u, Formalism.L2.SG.Measures.MeasW X.B.I.cm.sig X.B.I.J
        (⟨fun a => crdOf X.B.I X.ιE X.bas (X.eX a), fun a => crdOf X.B.I X.ιE X.bas (X.fY a),
          crdOf X.B.I X.ιE X.bas (X.zu u)⟩ : Formalism.L2.SG.Sub.Frame X.B.I.E X.B.I.n D.R.rS))
      (hw : ∀ u, (mw u).IsTextNorm),
      (Formalism.L2.SG.SettingExistsMeasured.withMeas X mg hg mw hw).MeasTie hb ∧
      ∃ ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧
        Formalism.L2.SG.LocVol.IsStdChar ψ ∧
        Formalism.L2.SG.MassDataConc.MeasCompatψ (Formalism.L2.SG.SettingExistsMeasured.withMeas X mg hg mw hw) ψ ∧
        ∀ w, Formalism.L2.SG.LocVol.LocCompatX (Formalism.L2.SG.SettingExistsMeasured.withMeas X mg hg mw hw) ψ w

def TransportExists3 (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∃ X : HidaSetting D, ∃ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    X.MeasTie hb ∧ Formalism.L2.SG.WuDecay.WuDecay X ∧
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
    ∃ hK : X.LevelSubgroupCharacter, ∀ u, ∃ Tr : Formalism.L2.SG.ColDict.Transport X u (F u), Formalism.L2.SG.ColDict.LevelMatch X Tr hK

def SettingExistsAdapted (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∃ X : HidaSetting D, ∃ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    ∃ ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ,
    X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧
    Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧
    Formalism.L2.SG.WuDecay.WuDecay X ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
    (∃ θ : ℝ, ∃ C : Formalism.L2.SG.LocWSOf.Choice X θ, Formalism.L2.SG.LocWSOf.WuBessel C) ∧
    ∃ hK : X.LevelSubgroupCharacter, ∀ u, ∃ Tr : Formalism.L2.SG.ColDict.Transport X u (F u), Formalism.L2.SG.ColDict.LevelMatch X Tr hK

def WuBesselStep : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ X : HidaSetting D, ∃ θ : ℝ, ∃ C : Formalism.L2.SG.LocWSOf.Choice X θ, Formalism.L2.SG.LocWSOf.WuBessel C

end Formalism.L2.SG.SettingExistsAdapted

namespace Formalism.L2.SG.SettingExistsAdapted

open Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.ColDict Matrix
open scoped InnerProductSpace

variable {D : D7}

def WittX (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  (∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y) ∧ (∀ a, wt (X.eX a) = D.sp.hypE a) ∧
    (∀ a, wt (X.fY a) = D.sp.hypF a) ∧ wt (X.zu u) = D.zmOf u

def IsAdeleIso (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) : Prop :=
  (∀ x : X.B.I.E, ιA (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x) =
    Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (X.ιE x)) ∧
  ∀ a, a ∈ IntAf X.B.I.F X.B.I.E ↔ ιA a ∈ IntAf D.host.F D.host.E

def LatMatchH (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u)
    (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  ∀ x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F,
    (h0⁻¹).1.1 *ᵥ x ∈
      Formalism.UG.latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
        (Formalism.UG.tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Formalism.UG.intOE D.host.E)
          (Formalism.UG.intAd D.host.F)) F.cls0.lev.Lb ↔
    (∑ j, ιA.symm (x j) • qA X wt j) ∈ X.B.I.Lf

def LevelKH (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u)
    (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y →
    (h ∈ Ku X u hK ↔ ((h0⁻¹ * y * h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
      F.cls0.lev.U) ∧
    ∀ (hk : h ∈ Ku X u hK) (hy : ((h0⁻¹ * y * h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
        F.cls0.lev.U),
      ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = ((F.cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ)

def JOK (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ)) : Prop :=
  (∀ s ∈ Hinf X u, ∀ (ξ : X.Vpi u) (y y' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)),
    Formalism.L2.Forms.IsTr (sTil X wt s) y' y → J (X.piU u s ξ) y = J ξ y') ∧
  (∀ ξ, J ξ ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
    (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0)) ∧
  ∀ (c : (D.mem u).C.cls 0) (ξ η : X.Vpi u),
    (D.fm u).ipV 0 c (fun z => J ξ (F.val0.eY z))
      (fun z => J η (F.val0.eY z)) = ⟪η, ξ⟫_ℂ

variable (D)

def RefExistsS : Prop :=
  ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D), ∃ Rf : ReferenceFrame A L, ∀ (P : AdditiveCharacterData A) (Xu : TransportData A L Rf) (Bu : AutomorphicBundle A P Rf)
    (Pi : RepresentationData A L) (Mu : MuBlocks A L) (Wb : WBlk A L Bu Pi Mu) (Mb : MBlk A L), SplitPin (mk A L P Rf Xu Bu Pi Mu Wb Mb)

def WittExists : Prop := ∀ (X : HidaSetting D) (u : D.what₂.Word), ∃ wt, WittX X u wt

def AdeleIsoExists : Prop := ∀ X : HidaSetting D, ∃ ιA, IsAdeleIso X ιA

def GenusMatch (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) ιA, WittX X u wt → IsAdeleIso X ιA →
    ∃ h0, LatMatchH X u (F u) wt ιA h0

def LevelConj (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) ιA h0, WittX X u wt → IsAdeleIso X ιA →
    LatMatchH X u (F u) wt ιA h0 →
    ∃ h0', LatMatchH X u (F u) wt ιA h0' ∧ LevelKH X u (F u) wt ιA h0' (Formalism.L2.SG.Closed.level_subgroup_is_group X)

def HcExists (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) ιA h0, WittX X u wt → IsAdeleIso X ιA →
    ∀ c : (D.mem u).C.cls 0, ∃ h : Hfin X u,
      RepF X wt ιA (h : X.B.I.Gf) ((F u).cls0.y c * h0⁻¹)

def JExists (F : ∀ u, Formalism.L2.Forms.Forms0 D u) : Prop :=
  ∀ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt →
    ∃ J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ), JOK X u (F u) wt J

theorem transport_of (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (h1 : WittExists D) (h2 : AdeleIsoExists D)
    (h0g : GenusMatch D F) (h3 : LevelConj D F) (h4 : HcExists D F) (h5 : JExists D F) (X : HidaSetting D)
    (u : D.what₂.Word) :
    ∃ Tr : Transport X u (F u), LevelMatch X Tr (Formalism.L2.SG.Closed.level_subgroup_is_group X) := by
  obtain ⟨wt, hw⟩ := h1 X u
  obtain ⟨ιA, hι⟩ := h2 X
  obtain ⟨g0, hg0⟩ := h0g X u wt ιA hw hι
  obtain ⟨h0, hL, hK⟩ := h3 X u wt ιA g0 hw hι hg0
  choose hcf hcr using h4 X u wt ιA h0 hw hι
  obtain ⟨J, hJ1, hJ2, hJ3⟩ := h5 X u wt hw
  exact ⟨⟨wt, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, ιA, hι.1, hι.2, h0, hcf, hcr, J, hJ1, hJ2, hJ3⟩, hL, hK⟩

end Formalism.L2.SG.SettingExistsAdapted
end
end

