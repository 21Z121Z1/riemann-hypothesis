import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0338
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RangeBesselAnisotropicEmbeddingEqSecondModelSubg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

noncomputable section

namespace GlobalTheory.Core.SBesLevi

variable {D : D7}

theorem bridge_fix (D : D7) (g : GA D (D.sp.Y 0)) (x : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E) :
    (mt (D.sp.Y 0) g *ᵥ (fun k => incA D (x k)) = fun k => incA D (x k)) ↔
    ((∀ v, uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) *ᵥ rv (Formalism.L2.SG.InstExistsPf.instOf D) v x = rv (Formalism.L2.SG.InstExistsPf.instOf D) v x) ∧
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ incl (Formalism.L2.SG.InstExistsPf.instOf D) x = incl (Formalism.L2.SG.InstExistsPf.instOf D) x) := by
  have hb := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  have hb1 : ∀ v, uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) = ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) g v :=
    fun v => (hb.1 v).trans (congrArg (fun q => ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) q v) key)
  have hb2 : (Formalism.IndefR.RationalEmbedding.inst D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) g :=
    hb.2.trans (congrArg (fun q => ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) q) key)
  have hdet : ∀ v, IsUnit ((Formalism.L2.SG.InstExistsPf.instOf D).P v).det :=
    fun v => (Matrix.isUnit_iff_isUnit_det _).1 ((Formalism.L2.SG.InstExistsPf.instOf D).P_unit v)
  have hinf : ∀ v, (uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) *ᵥ rv (Formalism.L2.SG.InstExistsPf.instOf D) v x = rv (Formalism.L2.SG.InstExistsPf.instOf D) v x) ↔
      ∀ i, thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) =
        thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v (incA D (x i)) := by
    intro v
    have hθ : (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g).map (thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v) *ᵥ
        (fun i => (Formalism.L2.SG.InstExistsPf.instOf D).φ v (x i)) =
        fun i => thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) := by
      funext i
      refine Eq.trans ?_ (RingHom.map_mulVec (thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v) (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g) (fun k => incA D (x k)) i).symm
      congr 1
      funext k
      exact (GlobalTheory.Core.SBesFlagTie.thetaV_incA v (x k)).symm
    have hφ : (fun i => (Formalism.L2.SG.InstExistsPf.instOf D).φ v (x i)) =
        fun i => thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v (incA D (x i)) :=
      funext fun i => (GlobalTheory.Core.SBesFlagTie.thetaV_incA v (x i)).symm
    rw [hb1 v]
    unfold ofHAInf rv
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet v), Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hθ, hφ]
    constructor
    · intro h i
      have := congrArg (fun w => (Formalism.L2.SG.InstExistsPf.instOf D).P v *ᵥ w) h
      simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet v), Matrix.one_mulVec] at this
      exact congrFun this i
    · intro h
      rw [funext h]
  have hfin : ((Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ incl (Formalism.L2.SG.InstExistsPf.instOf D) x =
      incl (Formalism.L2.SG.InstExistsPf.instOf D) x) ↔
      ∀ i, tauF (Formalism.L2.SG.InstExistsPf.instOf D) ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) =
        tauF (Formalism.L2.SG.InstExistsPf.instOf D) (incA D (x i)) := by
    have hτ : (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g).map (tauF (Formalism.L2.SG.InstExistsPf.instOf D)) *ᵥ
        incl (Formalism.L2.SG.InstExistsPf.instOf D) x =
        fun i => tauF (Formalism.L2.SG.InstExistsPf.instOf D) ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) := by
      funext i
      refine Eq.trans ?_ (RingHom.map_mulVec (tauF (Formalism.L2.SG.InstExistsPf.instOf D)) (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g) (fun k => incA D (x k)) i).symm
      congr 1
      funext k
      exact (GlobalTheory.Core.SBesFlagTie.tauF_incA (x k)).symm
    have hi : incl (Formalism.L2.SG.InstExistsPf.instOf D) x = fun i => tauF (Formalism.L2.SG.InstExistsPf.instOf D) (incA D (x i)) :=
      funext fun i => (GlobalTheory.Core.SBesFlagTie.tauF_incA (x i)).symm
    have e1 := hb2
    unfold ofHAFin at e1
    change (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = _ at e1
    rw [e1, hτ, hi]
    exact funext_iff
  rw [hfin, forall_congr' hinf]
  change ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) = fun k => incA D (x k)) ↔ _
  constructor
  · intro h
    exact ⟨fun v i => by rw [congrFun h i], fun i => by rw [congrFun h i]⟩
  · rintro ⟨h1, h2⟩
    funext i
    have := Formalism.L2.SG.Pf.TT_ext (Formalism.L2.SG.InstExistsPf.instOf D)
      ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i - (show AF (Formalism.L2.SG.InstExistsPf.instOf D).F ⊗[(Formalism.L2.SG.InstExistsPf.instOf D).F] (Formalism.L2.SG.InstExistsPf.instOf D).E from incA D (x i)))
      (fun v => by rw [map_sub, h1 v i, sub_self]) (by rw [map_sub, h2 i, sub_self])
    exact sub_eq_zero.1 this

theorem transport_fix (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n) (S : Set (Fin I.n → I.E))
    (s : (Formalism.L2.SG.InstExistsPf.instOf D).GA) :
    ((castGA hI.symm s).1 ∈ Formalism.L2.SG.PoincareInHH.HinfS I S ∧ (castGA hI.symm s).2 ∈ Formalism.L2.SG.PoincareInHH.HfinS I S) ↔
    ∀ p ∈ S, (∀ v, uMat (s.1 v) *ᵥ rv (Formalism.L2.SG.InstExistsPf.instOf D) v (fun k => ιE (p (Fin.cast hr k))) =
        rv (Formalism.L2.SG.InstExistsPf.instOf D) v (fun k => ιE (p (Fin.cast hr k)))) ∧
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat s.2 *ᵥ incl (Formalism.L2.SG.InstExistsPf.instOf D) (fun k => ιE (p (Fin.cast hr k))) =
        incl (Formalism.L2.SG.InstExistsPf.instOf D) (fun k => ιE (p (Fin.cast hr k))) := by
  generalize hI.symm = e
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hv : ∀ p : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E,
      (fun k : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n => ιE (p (Fin.cast hr k))) = p := fun p => funext fun k => by rw [hid]; rfl
  rw [GlobalTheory.Core.SBesFlagTie.castGA_self]
  change ((∀ v, ∀ x ∈ S, uMat (s.1 v) *ᵥ rv _ v x = rv _ v x) ∧ (∀ y ∈ S, _)) ↔ _
  constructor
  · rintro ⟨h1, h2⟩ p hp
    rw [hv p]
    exact ⟨fun v => h1 v p hp, h2 p hp⟩
  · intro H
    refine ⟨fun v p hp => ?_, fun p hp => ?_⟩
    · have := (H p hp).1 v
      rw [hv p] at this
      exact this
    · have := (H p hp).2
      rw [hv p] at this
      exact this

theorem fix_smul {S : HSp D} (g : GA D S) {c : D.host.E} (hc : c ≠ 0) (y : Fin S.rank → D.host.E) :
    (mt S g *ᵥ (fun k => incA D ((c • y) k)) = fun k => incA D ((c • y) k)) ↔
      (mt S g *ᵥ (fun k => incA D (y k)) = fun k => incA D (y k)) := by
  have hs : (fun k => incA D ((c • y) k)) = incA D c • fun k => incA D (y k) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  have hu : IsUnit (incA D c) := (IsUnit.mk0 c hc).map (incA D)
  rw [hs, Matrix.mulVec_smul]
  exact hu.smul_left_cancel

theorem fix_cols {S : HSp D} (g : GA D S) {ρ : ℕ} (e : Matrix (Fin S.rank) (Fin ρ) D.host.E) :
    mt S g ⬝ rat e = rat e ↔ ∀ a, (mt S g *ᵥ (fun k => incA D (e k a)) = fun k => incA D (e k a)) := by
  constructor
  · intro h a
    funext k
    exact congrFun (congrFun h k) a
  · intro h
    funext k a
    exact congrFun (h a) k

theorem rat_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    (fun k => incA D ((M *ᵥ w) k)) = rat M *ᵥ fun k => incA D (w k) := by
  funext k
  exact RingHom.map_mulVec (incA D) M w k

theorem range_embA_iff {S V₀ A L : HSp D} {ρ : ℕ} (d : HypDec S V₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) (g : GA D S) :
    g ∈ (embA d o).range ↔ (mt S g ⬝ d.jX = d.jX ∧ mt S g ⬝ d.jY = d.jY ∧
      (mt S g *ᵥ (fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k)) = fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k))) := by
  have hw : (fun k => incA D (vecB o ζ k)) = o.jB *ᵥ fun k => incA D (ζ k) := rat_mulVec o.iB ζ
  rw [rat_mulVec d.i₀ (vecB o ζ)]
  change _ ↔ (_ ∧ _ ∧ mt S g *ᵥ (d.j0 *ᵥ _) = d.j0 *ᵥ _)
  constructor
  · rintro ⟨a, rfl⟩
    change mt S (d.emb0 (o.emb (a, 1))) ⬝ d.jX = d.jX ∧ mt S (d.emb0 (o.emb (a, 1))) ⬝ d.jY = d.jY ∧
      mt S (d.emb0 (o.emb (a, 1))) *ᵥ (d.j0 *ᵥ _) = d.j0 *ᵥ _
    refine ⟨d.wittDecomp_anisotropicEmbedding_inclX _, d.wittDecomp_anisotropicEmbedding_inclY _, ?_⟩
    rw [Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec (M := mt V₀ _), o.emb_jB,
      MixModel.mt_one, Matrix.mul_one]
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨b, rfl⟩ := GlobalTheory.T.exists_levi_preimage_of_fix_isotropic_frames d g h1 h2
    have hb : (mt V₀ b *ᵥ fun k => incA D (vecB o ζ k)) = fun k => incA D (vecB o ζ k) := by
      rw [Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec] at h3
      have := congrArg (fun w => d.p0 *ᵥ w) h3
      simp only [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec] at this
      simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, d.p0_j0, Matrix.one_mul] using this
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_orthogonalComplement_preimage_of_fix_line o ζ hζ b hb
    exact ⟨a, by rw [← ha]; rfl⟩

theorem range_embA_eq_H : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → IdE X → ∀ (V₀ L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ (D.sp.X 0) L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → d.e = GlobalTheory.Core.SBesEx.eM X h t lam → d.e' = GlobalTheory.Core.SBesEx.e'M X h t lam → d.i₀ *ᵥ vecB o ζ = t • GlobalTheory.Core.SBesEx.cY X h (X.zu u) → ∀ g, g ∈ (embA d o).range ↔ (iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u := by
  intro D X h u t lam ht hl hId V₀ L d o ζ hζ he he' hz g
  have hsc : ∀ a, GlobalTheory.Core.SBesEx.scl t lam a ≠ 0 := fun a => mul_ne_zero ht (pow_ne_zero _ hl)
  have hR : ((iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u) ↔
      ∀ p ∈ fixSet X u, (mt (D.sp.Y 0) g *ᵥ (fun k => incA D (X.ιE (p (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (p (Fin.cast (rank_eq X h) k)))) :=
    (transport_fix D X.B.I X.ιE hId h (rank_eq X h) (fixSet X u) (Formalism.IndefR.RationalEmbedding.iota D g)).trans
      (forall₂_congr fun p _ => (bridge_fix D g _).symm)
  rw [range_embA_iff d o ζ hζ g, hR, HypDec.jX, HypDec.jY, fix_cols, fix_cols]
  change _ ↔ ∀ p ∈ Set.range X.eR ∪ Set.range X.fR ∪ {X.zR u}, _
  have hE : ∀ a, (fun k => d.e k a) = GlobalTheory.Core.SBesEx.scl t lam a • GlobalTheory.Core.SBesEx.cY X h (X.eX a) := by
    intro a; funext k; rw [he]; rfl
  have hE' : ∀ a, (fun k => d.e' k a) = (star (GlobalTheory.Core.SBesEx.scl t lam a))⁻¹ • GlobalTheory.Core.SBesEx.cY X h (X.fY a) := by
    intro a; funext k; rw [he']; rfl
  have hA : ∀ a, ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (d.e k a)) = fun k => incA D (d.e k a)) ↔
      ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (X.ιE (X.eR a (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (X.eR a (Fin.cast (rank_eq X h) k)))) := fun a => by
    have := fix_smul g (hsc a) (GlobalTheory.Core.SBesEx.cY X h (X.eX a))
    rw [← hE a] at this
    exact this
  have hB : ∀ a, ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (d.e' k a)) = fun k => incA D (d.e' k a)) ↔
      ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (X.ιE (X.fR a (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (X.fR a (Fin.cast (rank_eq X h) k)))) := fun a => by
    have := fix_smul g (inv_ne_zero (star_ne_zero.2 (hsc a))) (GlobalTheory.Core.SBesEx.cY X h (X.fY a))
    rw [← hE' a] at this
    exact this
  have hC : ((mt (D.sp.Y 0) g *ᵥ fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k)) = fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k)) ↔
      ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (X.ιE (X.zR u (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (X.zR u (Fin.cast (rank_eq X h) k)))) := by
    have := fix_smul g ht (GlobalTheory.Core.SBesEx.cY X h (X.zu u))
    rw [← hz] at this
    exact this
  simp only [hA, hB, hC]
  constructor
  · rintro ⟨h1, h2, h3⟩ p hp
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact h1 a
    · exact h2 a
    · rw [Set.mem_singleton_iff] at hp
      subst hp
      exact h3
  · intro H
    exact ⟨fun a => H _ (Or.inl (Or.inl ⟨a, rfl⟩)), fun a => H _ (Or.inl (Or.inr ⟨a, rfl⟩)), H _ (Or.inr rfl)⟩

end GlobalTheory.Core.SBesLevi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerIntertwinerSliceRestrictionPlaceMode
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem restrModel_isPlaceModel : ∀ (D : D7) {m n m' n' m'' n'' : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (BS : Mx D m n → Mx D m n → AF D.host.F) (hsS : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (BA : Mx D m' n' → Mx D m' n' → AF D.host.F) (hsA : Mx D m' n' → (Mx D m' n' → ℂ) → (Mx D m' n' → ℂ)) (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (e : AE D) (ΛS : AddSubgroup (Mx D m n)) (ΛA : AddSubgroup (Mx D m' n')) (h : Mx D m'' n'' → ℂ) (f₀ : Mx D m n → ℂ) (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)), IsPlaceModel ψ BS hsS e ΛS 1 f₀ T' → (∀ a F w y, hsS (r.symm (a, 0)) F (r.symm (w, y)) = hsA a (fun w' => F (r.symm (w', y))) w) → (∀ t a, BS t (r.symm (a, 0)) = BA (r t).1 a) → (∀ a, IsHalf e a → IsHalf e (r.symm (a, 0))) → (∀ a, IsHalf (cA D e) a → IsHalf (cA D e) (r.symm (a, 0))) → (∀ Φ, IsSBHalf e ΛA Φ → IsSBHalf e ΛS (fun t => Φ (r t).1 * h (r t).2)) → halfInd e ΛS = (fun t => halfInd e ΛA (r t).1 * h (r t).2) → ∀ y, IsPlaceModel ψ BA hsA e ΛA 1 (fun w => f₀ (r.symm (w, y))) (GlobalTheory.FinPl.ExtZero.restrModel r h T' y) := by
  intro D m n m' n' m'' n'' ψ BS hsS BA hsA r e ΛS ΛA h f₀ T' hT hcomp hB hhalf hhalfc hSB hInd y
  refine ⟨?_, ?_, ?_⟩
  · intro Φ hΦ x hx
    funext w
    rw [restrModel_apply]
    have hfun : (fun t => (fun t => Φ (t + x)) (r t).1 * h (r t).2) =
        fun t => (fun t => Φ (r t).1 * h (r t).2) (t + r.symm (x, 0)) := by
      funext t
      simp only [map_add, AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero]
    rw [hfun, hT.trans _ (hSB Φ hΦ) _ (hhalf x hx), hcomp]
    rfl
  · intro Φ hΦ y' hy'
    funext w
    rw [restrModel_apply]
    have hfun : (fun t => (fun t => ψ (BA t y') * Φ t) (r t).1 * h (r t).2) =
        fun t => ψ (BS t (r.symm (y', 0))) * (fun t => Φ (r t).1 * h (r t).2) t := by
      funext t
      simp only [hB, mul_assoc]
    rw [hfun, hT.modul _ (hSB Φ hΦ) _ (hhalfc y' hy'), hcomp]
    rfl
  · funext w
    rw [restrModel_apply]
    have hfun : (fun t => ((1 : ℂ) • halfInd e ΛA) (r t).1 * h (r t).2) = (1 : ℂ) • halfInd e ΛS := by
      rw [hInd]; funext t; simp
    rw [hfun, hT.vac]

end GlobalTheory.FinPl.ExtZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMulConjugateHalfCharacterSplitPlac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModSB

theorem continuous_pi_hO_up {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (y : WO S T) :
    Continuous fun t : Matrix Y Y' k => p.π (hO S T (p.up FS FT t) y) := by
  have h : (fun t : Matrix Y Y' k => p.π (hO S T (p.up FS FT t) y)) = fun t =>
      ∑ a, ∑ b, ∑ c, ∑ d, p.π (incA D (S.gram⁻¹ a b)) * p.π (cA D (y c b)) * p.π (incA D (T.gram c d)) *
        (FT.β * t * FS.γ) d a := by
    funext t
    unfold hO
    simp only [map_sum, map_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [GlobalTheory.LocMod.Place.up, Matrix.map_apply, p.π_ι]
  rw [h]
  have hm : Continuous fun t : Matrix Y Y' k => FT.β * t * FS.γ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ =>
    continuous_finset_sum _ fun d _ => continuous_const.mul (hm.matrix_elem d a)

theorem mul_char_mem_SB : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (y : WO S T), IsHalf (cA D p.e) y → ∀ Φ ∈ SB (Matrix Y Y' k), (fun t => ψ (symplO S T (p.up FS FT t) y) * Φ t) ∈ SB (Matrix Y Y' k) := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT y hy Φ hΦ
  obtain ⟨⟨ψk, hk⟩, hc, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  have hcont := (hc ψk hk).1
  have heq : (fun t => ψ (symplO S T (p.up FS FT t) y) * Φ t) =
      fun t => ((ψk (p.π (hO S T (p.up FS FT t) y)) : Circle) : ℂ) * Φ t := by
    funext t
    rw [GlobalTheory.LocSympl.psi_sympl_up p FS FT ψ ψk hk t y]
  rw [heq]
  have hl : IsLocallyConstant (fun t : Matrix Y Y' k => ((ψk (p.π (hO S T (p.up FS FT t) y)) : Circle) : ℂ)) :=
    ((GlobalTheory.IrredSB.char_isLocallyConstant ψk hcont).comp_continuous (continuous_pi_hO_up p FS FT y)).comp
      (fun z : Circle => (z : ℂ))
  exact ⟨hl.mul hΦ.1, HasCompactSupport.mul_left hΦ.2⟩

end GlobalTheory.ModSB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlacesStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalParameterBound_nonsplit_places : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ D : D7, ParamBoundOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.Core.Rk.ParamInert.paramBoundOn_nonsplit | exact GlobalTheory.Core.Rk.ParamInert.paramBoundOn_nonsplit | (intros; apply GlobalTheory.Core.Rk.ParamInert.paramBoundOn_nonsplit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSchwartzBruhatActsAsSupportedCombinatiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceSchwartzBruhat_acts_as_supported_combination : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ Ψ ∈ SB (Matrix n n' k), ∃ c : WO S T →₀ ℂ, CombAt (· = p.v) c ∧ ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 f₀ Tm → Tm (extFun α β Ψ) = comb ψ S T c f₀ := by
  first | exact @GlobalTheory.FinPl.CombProof.extFun_comb | exact GlobalTheory.FinPl.CombProof.extFun_comb | (intros; apply GlobalTheory.FinPl.CombProof.extFun_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitWeilPhiInnerProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

theorem phiQ_ip : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ), r ≤ a → r ≤ b → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.ip ν (phiQ (a := a) (b := b) v r mu) (phiQ (a := a) (b := b) v r mu) = (((GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {y | ∀ i j, Valued.v (y i j) ≤ 1}).toReal * (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (b - r)))⁻¹) : ℝ) : ℂ) ∧ phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  intro D PP v φ hP a b r hra hrb ξ mu hL ν hν
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  refine ⟨?_, GlobalTheory.T.twistPlaceChainStepDatum_mem_schwartzBruhat D PP v φ hP a b r ξ mu hL⟩
  have h1 := GlobalTheory.T.twistPlaceChainStepDatum_mul_conj_eq_indicator D PP v φ hP a b r ξ mu hL
  have h3 := GlobalTheory.T.measurableSet_twistPlaceChainStepDatumMatrixSupport D v a b r
  obtain ⟨e1, e2⟩ := GlobalTheory.T.twistPlaceChainStepDatumSupport_eq_valuative D v a b r
  have h4 := GlobalTheory.T.matrixMeasure_topBlock_integralGL_maxIdeal (Fv D.host.F v) ν hν a b r hra hrb
  rw [← e1, ← e2, (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hP).2] at h4
  unfold GlobalTheory.SplitWeil.ip
  simp_rw [h1]
  rw [integral_indicator_const _ h3, Measure.real, h4, zinv]
  simp

end GlobalTheory.NrmVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIffStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardUnitaryChart_mem_rational_iff : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g, g ∈ GQ (dblSp A) ↔ κ g ∈ GF D A.rank := by
  first | exact @GlobalTheory.StdUnn.chart_mem_GF_iff | exact GlobalTheory.StdUnn.chart_mem_GF_iff | (intros; apply GlobalTheory.StdUnn.chart_mem_GF_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartSiegelLeviDetEqStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardUnitaryChart_siegelLeviDet_eq : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (p : siegel A) (a : GL (Fin A.rank) (AE D)), blkA (mat (κ p)) = a.1 → aP A p = Matrix.GeneralLinearGroup.det a := by
  first | exact @GlobalTheory.StdUnn.chart_aP_eq_det | exact GlobalTheory.StdUnn.chart_aP_eq_det | (intros; apply GlobalTheory.StdUnn.chart_aP_eq_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamsTrivialBoundRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ChainOnto.parBound_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LevFacts D → ParBound D := by
  intro hCRD D _hLF c hc j hj s hs u B hB
  obtain ⟨hu0, hpar⟩ := hB
  have hex : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s.V → ℂ := fun g => conj (PiLocalization₂.val u v g) with hfdef
  have hPF : ParFun c s (PiLocalization₂.val u v) B := hpar v hv
  have h3 : GlobalTheory.LFun.IsParamFunV s.V c.S f B := ((GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs).2 f B).1 hPF
  obtain ⟨h4a, _, _⟩ := GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators hCRD D c hc j hj s hs
  obtain ⟨hcont, ⟨C, hC⟩, hinv, hlev⟩ := h4a u v
  obtain ⟨_, hsph, _⟩ := GlobalTheory.T.thetaChainStage_level_spherical_off_set D c hc j hj s hs
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  have hf0 : f ≠ 0 := by
    intro h0
    apply hv
    funext g
    have := congrFun h0 g
    simpa [hfdef] using this
  have hlev' : ∀ k ∈ levS s.V s.β s.L, ∀ g, f (g * k) = conj (Lev.levChi s.V s.β s.L k) * f g := by
    intro k hk g
    simp only [hfdef, hlev k hk g, map_mul]
  obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S hsph B
  obtain ⟨B', hB', hbd⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D s.V _ _ c.S hsph f hfmem hf0 hlev' a (fun P d R hR => ha f h3 P d R hR)
  intro w hw
  rw [GlobalTheory.LFun.IsParamVecOff.unique h3 hB' hw]
  exact hbd w hw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillingImpliesVanishingStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_killing_implies_vanishing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W : HSp D) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ (m : Measure (GA D A)) (mW : Measure (GA D W)), m.IsHaarMeasure → mW.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omh m u → (∀ φ', IsThetaFunO ψ (dblSp A) W φ' → ∀ g, ThetaPairConv omh mW φ' 1 g) → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → GlobalTheory.Eis.dblInt A χ⁻¹ m (thetaInt omh mW φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  first | exact @GlobalTheory.Core.Rk.Aniso.dblInt_thetaInt_eq_zero | exact GlobalTheory.Core.Rk.Aniso.dblInt_thetaInt_eq_zero | (intros; apply GlobalTheory.Core.Rk.Aniso.dblInt_thetaInt_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeParahoricEntriesEqColumnDataStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrime_parahoricEntries_eq_columnData : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → EntryAgree Ch sel mu cst σ₀ P ι s W ν L := by
  first | exact @GlobalTheory.EntryAtTwist.entryAgree | exact GlobalTheory.EntryAtTwist.entryAgree | (intros; apply GlobalTheory.EntryAtTwist.entryAgree <;> assumption)
end

