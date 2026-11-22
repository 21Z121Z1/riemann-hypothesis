import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.HaarIdx
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevVol

variable {D : D7}

theorem mul_set_eq_comap (V : HSp D) (U : Subgroup (GA D V)) (hU : U ≤ GfC V) :
    {g : GA D V | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} =
      (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) := by
  ext g
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨k, hk, κ, hκ, rfl⟩
    have e : GlobalTheory.AutMult.toFin V (k * κ) = ⟨κ, hU hκ⟩ := by
      rw [map_mul, GlobalTheory.AutMult.toFin_coe_inf (⟨k, hk⟩ : GinfC V), one_mul]
      exact GlobalTheory.AutMult.toFin_coe (⟨κ, hU hκ⟩ : GfC V)
    rw [e]
    exact hκ
  · intro h
    exact ⟨_, (GlobalTheory.AutMult.toInf V g).2, _, h, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩

theorem volLev_mul_relIndex : ∀ (D : D7) (V : HSp D) (v : GlobalTheory.Unf.Vol V) (U U' : Subgroup (GA D V)), U ≤ U' → U' ≤ GfC V →
    IsCompact (U' : Set (GA D V)) → IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) →
    volLev v U * (U.relIndex U' : ℝ) = volLev v U' := by
  intro D V v U U' hle hU' _ hopn
  obtain ⟨i1, -, -, -, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  haveI := i1
  haveI := i5
  haveI := v.haar
  have hU : U ≤ GfC V := hle.trans hU'
  set A := (U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) with hA
  set A' := (U'.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) with hA'
  have hAA : A ≤ A' := Subgroup.comap_mono (fun x hx => Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hx)))
  have hAo : IsOpen (A : Set (GA D V)) := hopn.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have key := MassDataLevelSSteps.toReal_eq_relIndex_mul_of_open v.μ A A' hAA hAo
  have hsurj : Function.Surjective (GlobalTheory.AutMult.toFin V) := fun y => ⟨y, GlobalTheory.AutMult.toFin_coe y⟩
  have hidx : A.relIndex A' = U.relIndex U' := by
    rw [hA, Subgroup.relIndex_comap, hA', Subgroup.map_comap_eq_self_of_surjective hsurj,
      Subgroup.relIndex_subgroupOf hU']
  unfold GlobalTheory.SeeSaw.volLev
  rw [mul_set_eq_comap V U hU, mul_set_eq_comap V U' hU', ← hA, ← hA', key, hidx, mul_comm]

end GlobalTheory.LevVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStageYValidStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chain_stage_Y_valid : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → (GlobalTheory.BaseChain.stageY W j).Is (GlobalTheory.BaseChain.com W) j := by
  first | exact @GlobalTheory.BaseChain.stageY_is | exact GlobalTheory.BaseChain.stageY_is | (intros; apply GlobalTheory.BaseChain.stageY_is <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelLineVectorPrimitiveRowLatticeNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.SZ

variable {D : D7}

theorem cY_eq_repr (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (y : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h y = (X.bas.reindex (finCongr (rank_eq X h)).symm).repr y := by
  funext k
  simp [GlobalTheory.Core.SBesEx.cY, HidaSetting.crd, crdOf, Module.Basis.repr_reindex]

theorem sum_bas_mem_iff (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (ιE : I.E ≃+* D.host.E)
    (hId : ∀ x : I.E, HEq (ιE x) x) (hn : (D.sp.Y 0).rank = I.n) (bas : Module.Basis (Fin I.n) D.host.E (VS D).V)
    (hL : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0) (v : Fin (D.sp.Y 0).rank → D.host.E) :
    (∑ k, v k • bas (Fin.cast hn k)) ∈ (VS D).L0 ↔ (∑ k, v k • (VS D).frame k) ∈ (VS D).L0 := by
  subst hI
  have h2 : ∀ i, ιE (v i) = v i := fun i => eq_of_heq (hId _)
  rw [← Formalism.L2.SG.InstExistsPf.mem_Lv]
  refine Iff.trans ?_ (hL v).symm
  apply iff_of_eq
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 i]
  rfl

theorem cY_mem_latS_iff (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : GlobalTheory.Core.Mi.IdE X)
    (y : (VS D).V) : GlobalTheory.Core.SBesEx.cY X h y ∈ latS D ↔ y ∈ (VS D).L0 := by
  have hs := sum_bas_mem_iff X.B.I h X.ιE hId (rank_eq X h) X.bas X.L_eq (GlobalTheory.Core.SBesEx.cY X h y)
  have hy : (∑ k, GlobalTheory.Core.SBesEx.cY X h y k • X.bas (Fin.cast (rank_eq X h) k)) = y := by
    rw [cY_eq_repr]
    conv_rhs => rw [← (X.bas.reindex (finCongr (rank_eq X h)).symm).sum_repr y]
    simp
  rw [hy] at hs
  rw [hs]
  simp only [latS, Formalism.L2.Herm.crdLat, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Formalism.L2.Herm.crd]
  constructor
  · rintro ⟨w, hw, hwe⟩
    have : w = ∑ k, GlobalTheory.Core.SBesEx.cY X h y k • (VS D).frame k := by
      rw [← hwe]; exact ((VS D).frame.sum_equivFun w).symm
    rw [← this]; exact hw
  · intro hw
    exact ⟨_, hw, by
      rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]⟩

theorem cY_smul (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (c : D.host.E) (y : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h (c • y) = c • GlobalTheory.Core.SBesEx.cY X h y := by
  rw [cY_eq_repr, cY_eq_repr, map_smul, Finsupp.coe_smul]

end GlobalTheory.Core.Mi.LatMatch.SZ

namespace GlobalTheory.Core.Mi.LatMatch.SZ

variable {D : D7}

theorem smul_zu_mem_iff (X : HidaSetting D) (u : D.what₂.Word) (c : D.host.E) :
    c • X.zu u ∈ (VS D).L0 ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  constructor
  · intro hc
    have hfix := (X.Fu_fixed u).2.2.2.2
    apply hfix c
    have hz : (X.Fu u).z = X.zu u := X.flagZVector u
    show c • (X.Fu u).z ∈ _
    rw [hz]
    have horth : c • X.zu u ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu u).X := by
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [map_smulₛₗ, ← hz, (X.Fu u).z_orth a, smul_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [LinearMap.map_smulₛₗ₂, hx, smul_zero]
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hc, horth⟩), horth⟩
  · rintro ⟨o, rfl⟩
    have hz : X.zu u ∈ (VS D).L0 := by
      rw [X.Lam_split]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.zu_Lb u))
    have := (VS D).L0.smul_mem o hz
    simpa [algebraMap_smul] using this

theorem quad {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n D.host.E) (G : Matrix m m D.host.E) (x : n → D.host.E) :
    star x ⬝ᵥ (Mᴴ * G * M) *ᵥ x = star (M *ᵥ x) ⬝ᵥ G *ᵥ (M *ᵥ x) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end GlobalTheory.Core.Mi.LatMatch.SZ

open GlobalTheory.Core.Mi.LatMatch.SZ in

theorem GlobalTheory.Core.Mi.LatMatch.sz_tied : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → (∀ t : D.host.E, t • vecB B.o B.ζ ∈ coreLat B.d (latS D) ↔ μ * t ∈ (1 : FI D)) ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(μ * star μ * (((D.mem u).A.T : ℕ) : D.host.E)) ∧ vecB B.o B.ζ ≠ 0 := by
  intro D X h u ψ A B μ lam hId hF
  have hz : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY X h (X.zu u) := hF.z
  refine ⟨fun t => ?_, ?_, ?_⟩
  · rw [mem_coreLat, Matrix.mulVec_smul, hz, smul_smul, ← cY_smul, cY_mem_latS_iff X h hId, smul_zu_mem_iff,
      FractionalIdeal.mem_one_iff, mul_comm]
  · rw [← B.o.isoB, quad, ← B.d.iso, quad]
    change star (B.d.i₀ *ᵥ vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = _
    rw [hz, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct,
      GlobalTheory.Core.SBesEx.cY_isom D X h hId, X.zu_norm]
    simp only [smul_eq_mul]
    ring
  · intro h0
    apply B.line.2
    rw [← B.o.isoB, quad]
    change star (vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (vecB B.o B.ζ) = 0
    rw [h0]
    simp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliser
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FinPl.OrbitCoset

variable {D : D7}

theorem mem_congGrp_iff' (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ (mt V g).map (Ideal.Quotient.mk I) = 1 := by
  unfold congGrp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  rfl

theorem matrixTransform_wittCoreEmbedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (h : GA D S₀) :
    mt S (d.emb0 h) = d.jX ⬝ d.pX + d.j0 ⬝ mt S₀ h ⬝ d.p0 + d.jY ⬝ d.pY := by
  conv_lhs => rw [← Matrix.mul_one (mt S (d.emb0 h)), ← d.sum_eq_one]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclY]

theorem wittCoreEmbedding_mem_supportedSubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {h : GA D S₀}
    (hh : h ∈ grpAt S₀ P) : d.emb0 h ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff'] at hh ⊢
  have hadd : ∀ A B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (A + B).map (Ideal.Quotient.mk (idAt D P)) =
      A.map (Ideal.Quotient.mk (idAt D P)) + B.map (Ideal.Quotient.mk (idAt D P)) :=
    fun A B => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add A B
  have key : (mt S (d.emb0 h)).map (Ideal.Quotient.mk (idAt D P)) =
      (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY).map (Ideal.Quotient.mk (idAt D P)) := by
    rw [matrixTransform_wittCoreEmbedding]; simp only [hadd, Matrix.map_mul, hh, Matrix.mul_one]
  rw [key, d.sum_eq_one]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem emb_mem_grpAt' {S A B : HSp D} (o : OrthDec S A B) {P : Pl D → Prop} {a : GA D A} (ha : a ∈ grpAt A P) :
    o.emb (a, 1) ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff'] at ha ⊢
  have hadd : ∀ M N : Matrix (Fin S.rank) (Fin S.rank) (AE D), (M + N).map (Ideal.Quotient.mk (idAt D P)) =
      M.map (Ideal.Quotient.mk (idAt D P)) + N.map (Ideal.Quotient.mk (idAt D P)) :=
    fun M N => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add M N
  have key : (mt S (o.emb (a, 1))).map (Ideal.Quotient.mk (idAt D P)) =
      (o.jA ⬝ o.pA + o.jB ⬝ o.pB).map (Ideal.Quotient.mk (idAt D P)) := by
    rw [o.mt_emb, mt_one]; simp only [hadd, Matrix.map_mul, ha, Matrix.mul_one]
  rw [key, o.sum_eq_one]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem inK_mul' {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a b : GA D S} (ha : InK S L P a) (hb : InK S L P b) :
    InK S L P (a * b) := by
  refine ⟨mul_mem ha.1 hb.1, fun y hy => ?_⟩
  have hy' : ∀ i, (mt S b *ᵥ y) i ∈ idAt D P := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  rw [mt_mul, ← Matrix.mulVec_mulVec, ← ha.2 _ hy', hb.2 y hy]

end GlobalTheory.FinPl.OrbitCoset

namespace GlobalTheory.FinPl.OrbitCoset

theorem orbit_coset : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ) (L : Lat B.V) (L₀ : Lat B.V₀) (v : Pl D), MonoAt B.d L L₀ v →
    ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ a ∈ grpAt B.A (· = v), ∀ κ₀, InK B.V₀ L₀ (· = v) κ₀ → ∀ κ,
    InK B.V L (· = v) κ → ∃ r ∈ besGrp B.d B.o, r ∈ grpAt B.V (· = v) ∧ ∃ κ', InK B.V L (· = v) κ' ∧
      n * B.d.emb0 (B.o.emb (a, 1) * κ₀) * κ = r * κ' := by
  intro D σ B L L₀ v hM n hn hnv a ha κ₀ hκ₀ κ hκ
  refine ⟨n * embA B.d B.o a, mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨a, rfl⟩),
    mul_mem hnv (wittCoreEmbedding_mem_supportedSubgroup B.d _ (emb_mem_grpAt' B.o ha)), B.d.emb0 κ₀ * κ,
    inK_mul' ⟨wittCoreEmbedding_mem_supportedSubgroup B.d _ hκ₀.1, (carriesLattice_wittEmbedding_iff_core D B.V B.V₀ σ B.d L L₀ v κ₀ hM).2 hκ₀.2⟩ hκ, ?_⟩
  rw [map_mul, embA_apply]
  group

end GlobalTheory.FinPl.OrbitCoset

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterLocalUnitaryGroupFinitePlaceScalar
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.CenterLocU

open Matrix Formalism.UG

section Gen

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem cT_add' (σ : A →+* A) (M N : Matrix n n A) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

theorem cT_sub' (σ : A →+* A) (M N : Matrix n n A) : cT σ (M - N) = cT σ M - cT σ N := by
  ext i j; simp [cT]

theorem cT_smul' (σ : A →+* A) (c : A) (M : Matrix n n A) : cT σ (c • M) = σ c • cT σ M := by
  ext i j; simp [cT]

theorem cT_cT' (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (M : Matrix n n A) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem cayley_unitary (σ : A →+* A) (J B V : Matrix n n A) (s : A) (hs : σ s = s)
    (hB : cT σ B * J + J * B = 0) (hV1 : (s • (1 : Matrix n n A) - B) * V = 1) :
    cT σ ((s • (1 : Matrix n n A) + B) * V) * J * ((s • (1 : Matrix n n A) + B) * V) = J := by
  set S : Matrix n n A := s • (1 : Matrix n n A) with hSdef
  have hS : cT σ S = S := by rw [hSdef, cT_smul', cT_one, hs]
  have hc : ∀ M : Matrix n n A, S * M = M * S := fun M => by
    rw [hSdef, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have key : cT σ (S + B) * J * (S + B) = cT σ (S - B) * J * (S - B) := by
    rw [cT_add', cT_sub', hS]
    have e1 : (S + cT σ B) * J * (S + B) - (S - cT σ B) * J * (S - B)
        = (S * J * B + cT σ B * J * S) + (S * J * B + cT σ B * J * S) := by noncomm_ring
    have e2 : S * J * B + cT σ B * J * S = 0 := by
      rw [Matrix.mul_assoc (cT σ B) J S, ← hc J, ← Matrix.mul_assoc, ← hc (cT σ B),
        Matrix.mul_assoc S J B, Matrix.mul_assoc S (cT σ B) J, ← Matrix.mul_add, add_comm, hB, Matrix.mul_zero]
    rw [e2, add_zero] at e1
    exact sub_eq_zero.1 e1
  calc cT σ ((S + B) * V) * J * ((S + B) * V) = cT σ V * (cT σ (S + B) * J * (S + B)) * V := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT σ V * (cT σ (S - B) * J * (S - B)) * V := by rw [key]
    _ = cT σ ((S - B) * V) * J * ((S - B) * V) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hV1, cT_one, Matrix.one_mul, Matrix.mul_one]

theorem comm_of_comm_cayley (g B V : Matrix n n A) (s : A) (h2s : IsUnit (2 * s))
    (hV1 : (s • (1 : Matrix n n A) - B) * V = 1) (hV2 : V * (s • (1 : Matrix n n A) - B) = 1)
    (hg : g * ((s • (1 : Matrix n n A) + B) * V) = ((s • (1 : Matrix n n A) + B) * V) * g) :
    g * B = B * g := by
  have e : s • (1 : Matrix n n A) + B = (2 * s) • (1 : Matrix n n A) - (s • (1 : Matrix n n A) - B) := by
    rw [two_mul, add_smul]; abel
  rw [e, Matrix.sub_mul, hV1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_left_inj] at hg
  have hgV : g * V = V * g := by
    have := congrArg (fun M => (↑h2s.unit⁻¹ : A) • M) hg
    simp only [smul_smul, IsUnit.val_inv_mul, one_smul] at this
    exact this
  have hU : (s • (1 : Matrix n n A) - B) * g = g * (s • (1 : Matrix n n A) - B) := by
    calc (s • (1 : Matrix n n A) - B) * g
        = (s • (1 : Matrix n n A) - B) * g * (V * (s • (1 : Matrix n n A) - B)) := by rw [hV2, Matrix.mul_one]
      _ = (s • (1 : Matrix n n A) - B) * (g * V) * (s • (1 : Matrix n n A) - B) := by simp only [Matrix.mul_assoc]
      _ = (s • (1 : Matrix n n A) - B) * (V * g) * (s • (1 : Matrix n n A) - B) := by rw [hgV]
      _ = ((s • (1 : Matrix n n A) - B) * V) * g * (s • (1 : Matrix n n A) - B) := by simp only [Matrix.mul_assoc]
      _ = g * (s • (1 : Matrix n n A) - B) := by rw [hV1, Matrix.one_mul]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    sub_right_inj] at hU
  exact hU.symm

theorem comm_of_comm_skew (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n A) (hJ : cT σ J = J)
    (hJu : IsUnit J.det) (h2 : IsUnit (2 : A)) (δ : A) (hδ : IsUnit δ) (hδσ : σ δ = -δ)
    (g : Matrix n n A) (hg : ∀ B : Matrix n n A, cT σ B * J + J * B = 0 → g * B = B * g)
    (M : Matrix n n A) : g * M = M * g := by
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJu
  have hJJ' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJi : J⁻¹ = cT σ J⁻¹ := Matrix.inv_eq_left_inv (by
    have := cT_mul σ J J⁻¹
    rw [hJ, hJJ, cT_one] at this
    exact this.symm)
  have hsk : ∀ X : Matrix n n A, cT σ X = -X → g * (J⁻¹ * X) = (J⁻¹ * X) * g := fun X hX => hg _ (by
    rw [cT_mul, hX, ← hJi, neg_mul, ← neg_mul, Matrix.mul_assoc, hJJ', Matrix.mul_one, ← Matrix.mul_assoc, hJJ,
      Matrix.one_mul, neg_add_cancel])
  set Y := J * M
  have h1 := hsk (Y - cT σ Y) (by rw [cT_sub', cT_cT' σ hσ, neg_sub])
  have h2' := hsk (δ • (Y + cT σ Y)) (by rw [cT_smul', cT_add', cT_cT' σ hσ, hδσ, neg_smul, add_comm])
  have e : (2 : A) • M = J⁻¹ * (Y - cT σ Y) + (↑hδ.unit⁻¹ : A) • (J⁻¹ * (δ • (Y + cT σ Y))) := by
    rw [Matrix.mul_smul, smul_smul, IsUnit.val_inv_mul, one_smul, ← Matrix.mul_add,
      sub_add_add_cancel, ← two_smul A Y, Matrix.mul_smul, ← Matrix.mul_assoc, hJJ', Matrix.one_mul]
  have h3 : g * ((2 : A) • M) = ((2 : A) • M) * g := by
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h1, h2']
  rw [Matrix.mul_smul, Matrix.smul_mul] at h3
  have := congrArg (fun N => (↑h2.unit⁻¹ : A) • N) h3
  simp only [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  exact this

theorem exists_nat_isUnit_sub (K : Type) [Field K] [CharZero K] [Algebra K A] [FiniteDimensional K A]
    (B : Matrix n n A) : ∃ m : ℕ, m ≠ 0 ∧ IsUnit ((m : A) • (1 : Matrix n n A) - B) := by
  let L : Module.End K (n → A) := (Matrix.mulVecLin B).restrictScalars K
  have hfin : {m : ℕ | L.HasEigenvalue (m : K)}.Finite :=
    (Module.End.finite_hasEigenvalue L).preimage Nat.cast_injective.injOn
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, by omega, ?_⟩
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  let T : Module.End K (n → A) :=
    (Matrix.mulVecLin (((N + 1 : ℕ) : A) • (1 : Matrix n n A) - B)).restrictScalars K
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hT : (((N + 1 : ℕ) : A) • (1 : Matrix n n A) - B) *ᵥ x = 0 := hx
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hT
    have hev : L.HasEigenvalue ((N + 1 : ℕ) : K) := by
      refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ⟨?_, hx0⟩
      rw [Module.End.mem_eigenspace_iff]
      show B *ᵥ x = ((N + 1 : ℕ) : K) • x
      rw [← hT, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    have := hN hev
    omega
  exact LinearMap.injective_iff_surjective.1 hinj

end Gen

end GlobalTheory.CenterLocU

namespace GlobalTheory.CenterLocU
open Matrix Formalism.UG

section Gen2

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem scalar_of_comm_UJ (K : Type) [Field K] [CharZero K] [Algebra K A] [FiniteDimensional K A]
    (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n A) (hJ : cT σ J = J) (hJu : IsUnit J.det)
    (δ : A) (hδ : IsUnit δ) (hδσ : σ δ = -δ) (g : Matrix n n A)
    (hg : ∀ h ∈ UJ σ J, g * (h : Matrix n n A) = (h : Matrix n n A) * g) :
    ∃ c : A, g = c • (1 : Matrix n n A) := by
  have h2 : IsUnit (2 : A) := by
    have : (2 : A) = algebraMap K A 2 := (map_ofNat (algebraMap K A) 2).symm
    rw [this]; exact (IsUnit.mk0 (2 : K) two_ne_zero).map _
  have hskew : ∀ B : Matrix n n A, cT σ B * J + J * B = 0 → g * B = B * g := by
    intro B hB
    obtain ⟨m, hm, hU⟩ := exists_nat_isUnit_sub K B
    have hUd := (Matrix.isUnit_iff_isUnit_det _).1 hU
    have hV1 : ((m : A) • (1 : Matrix n n A) - B) * ((m : A) • (1 : Matrix n n A) - B)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hUd
    have hV2 : ((m : A) • (1 : Matrix n n A) - B)⁻¹ * ((m : A) • (1 : Matrix n n A) - B) = 1 :=
      Matrix.nonsing_inv_mul _ hUd
    have hC := cayley_unitary σ J B _ (m : A) (map_natCast σ m) hB hV1
    have hWC : (J⁻¹ * cT σ (((m : A) • (1 : Matrix n n A) + B) * ((m : A) • (1 : Matrix n n A) - B)⁻¹) * J) *
        (((m : A) • (1 : Matrix n n A) + B) * ((m : A) • (1 : Matrix n n A) - B)⁻¹) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ _), hC, Matrix.nonsing_inv_mul J hJu]
    let Cu : GL n A := ⟨_, _, mul_eq_one_comm.1 hWC, hWC⟩
    have hCm : Cu ∈ UJ σ J := hC
    have h2m : IsUnit (2 * (m : A)) := by
      have : (2 * (m : A)) = algebraMap K A (2 * m) := by rw [map_mul, map_ofNat, map_natCast]
      rw [this]; exact (IsUnit.mk0 _ (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 hm))).map _
    exact comm_of_comm_cayley g B _ (m : A) h2m hV1 hV2 (hg Cu hCm)
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := g)
    (fun i j _ => (comm_of_comm_skew σ hσ J hJ hJu h2 δ hδ hδσ g hskew _).symm)
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

end Gen2

end GlobalTheory.CenterLocU

namespace GlobalTheory.CenterLocU

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_anti (D : D7) : ∃ e : D.host.E, D.sp.cm.sig e = -e ∧ e ≠ 0 := by
  have hx : ∃ x : D.host.E, x ∉ Set.range (algebraMap D.host.F D.host.E) := by
    by_contra h
    push_neg at h
    have htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ :=
      eq_top_iff.2 fun x _ => Algebra.mem_bot.2 (h x)
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
    rw [D.sp.cm.deg2] at this
    norm_num at this
  obtain ⟨x, hx⟩ := hx
  refine ⟨x - star x, ?_, ?_⟩
  · show star (x - star x) = -(x - star x)
    rw [star_sub, star_star, neg_sub]
  · intro h0
    exact hx (RingHom.mem_range.1 ((D.sp.cm.fixed x).1 (sub_eq_zero.1 h0).symm))

theorem center_scalar_loc : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)) (g : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v), g ∈ Subgroup.center (GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) → ∃ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig V.gram g).1 = c • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
  intro D V v g hg
  have hσ : ∀ x : D.host.E, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  obtain ⟨e, he, he0⟩ := exists_anti D
  have hJ : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv D.host.F v) D.sp.cm.sig) (JR (Fv D.host.F v) V.gram) =
      JR (Fv D.host.F v) V.gram := by
    ext i j
    exact congrArg (inclR (Fv D.host.F v)) (V.herm.eq (V.frame j) (V.frame i))
  have hδσ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv D.host.F v) D.sp.cm.sig (inclR (Fv D.host.F v) e) =
      -inclR (Fv D.host.F v) e := by
    show inclR (Fv D.host.F v) (D.sp.cm.sig e) = _
    exact (congrArg _ he).trans (map_neg _ _)
  have hgc : ∀ h ∈ Formalism.UG.UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv D.host.F v) D.sp.cm.sig) (JR (Fv D.host.F v) V.gram),
      ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig V.gram g).1) * (h : Matrix (Fin V.rank) (Fin V.rank) _) =
        (h : Matrix (Fin V.rank) (Fin V.rank) _) * ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig V.gram g).1) := by
    intro h hh
    let h' : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v := ⟨h, hh⟩
    have e1 := congrArg (fun x => (GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig V.gram x).1)
      (Subgroup.mem_center_iff.1 hg h')
    simp only [map_mul, Units.val_mul] at e1
    exact e1.symm
  exact scalar_of_comm_UJ (Fv D.host.F v)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv D.host.F v) D.sp.cm.sig) (GlobalTheory.Doubling.sigR_invol hσ)
    (JR (Fv D.host.F v) V.gram) hJ
    (GlobalTheory.Doubling.isUnit_det_JR (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero)
    (inclR (Fv D.host.F v) e) ((isUnit_iff_ne_zero.2 he0).map _) hδσ
    ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig V.gram g).1) hgc

end GlobalTheory.CenterLocU
end
end

