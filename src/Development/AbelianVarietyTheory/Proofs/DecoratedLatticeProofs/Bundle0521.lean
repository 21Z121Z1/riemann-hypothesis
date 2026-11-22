import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0500
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0486
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0511
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdditiveCharacterCongruenceInvariance
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

noncomputable section

namespace GlobalTheory.FamTraceChiColSide

theorem psi_unif_mul_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S : GlobalTheory.SymChain.SymData k s κ) (d e : k) (hv : valuation k (d - e) < 1) :
    (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * e) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * d) : ℂ) := by
  have hsplit : ((S.ϖ⁻¹ : kˣ) : k) * d = ((S.ϖ⁻¹ : kˣ) : k) * e + ((S.ϖ⁻¹ : kˣ) : k) * (d - e) := by ring
  have h1 : S.ψ (((S.ϖ⁻¹ : kˣ) : k) * (d - e)) = 1 := by
    refine (S.cond 1).2 le_rfl _ ?_
    have hle := (S.unif _).1 hv
    have hϖ : valuation k ((S.ϖ : kˣ) : k) ≠ 0 := by simp
    rw [map_one, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    calc (valuation k ((S.ϖ : kˣ) : k))⁻¹ * valuation k (d - e)
        ≤ (valuation k ((S.ϖ : kˣ) : k))⁻¹ * valuation k ((S.ϖ : kˣ) : k) := by gcongr
      _ = 1 := inv_mul_cancel₀ hϖ
  rw [hsplit, AddChar.map_add_eq_mul, h1, mul_one]

theorem colLam_eq_psi_superSum : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (F0 W u).cls0.lev.U → ∀ (i : Fin a.n) g, GlobalTheory.FamTrace.IsMatrixInFrameOfXZero (a.G i) κ g → GlobalTheory.FamTraceChiCol.colLam (F0 W u) ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)) (y : GL _ _) = ((a.G i).S.ψ ((((a.G i).S.ϖ⁻¹ : (a.G i).kˣ) : (a.G i).k) * ∑ p : Fin (I.rec7 l Z).R.k, ∑ q : Fin (I.rec7 l Z).R.k, if q.val = p.val + 1 then g.val (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl q)) else 0) : ℂ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ y hy hyU i g hg
  obtain ⟨j, h, z, w, hw, hv, hcol⟩ := GlobalTheory.T.true_geometry_final_twist W hW u a ha hat row col hc κ hκ y hy hyU i g hg
  rw [hcol, ← GlobalTheory.T.true_geometry_psi_value W hW u a ha hat row col hc i j h z w hw]
  exact psi_unif_mul_congr _ _ _ hv

end GlobalTheory.FamTraceChiColSide

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllTrueFamilyGeometry
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.XGeoStd.exists_xgeo : GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ u : B.Word, ∃ (a : XGeo (I.rec7 l Z)) (c₀ : ℕ → ℂ), (∀ j, j ≤ B.R.m → (a.x j).Is) ∧ GlobalTheory.AdForm.PinX I l Z (pk W).ψ (pk W).θ a.x a.vac c₀ ∧ a.bT = 1 ∧ (∀ r s, (a.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) ∧ a.LT = (pk W).ΛX ∧ IsLineVec a.Lz a.ζ₀ ∧ star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) ∧ GlobalTheory.AdForm.IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((a.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) ∧ (∀ r, vecB (a.oT B.R.m rfl) a.ζ₀ r = (show Fin (B.R.N B.R.m) → (I.rec7 l Z).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl) r)) ∧ (∀ n (h : n = B.R.m) x, ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) ∧ ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → ∃ s : LocX a (pk W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  open GlobalTheory.XGeoStd GlobalTheory.AdForm.LiveModel GlobalTheory.AdForm.PinInhab GlobalTheory.MixModel GlobalTheory.Mem in (
    intro hSA B X I l Z L hT Gi Gl Kc Yd cX ex W hW u
    have hI : I.Ok := hW.tr.ok
    obtain ⟨hP⟩ := hW.tr.pins
    have hψ : IsStdChar (I.rec7 l Z) (pk W).ψ (-1) := W.Q.stdChar
    have hθ : IsInfFam (pk W).θ := W.Q.charW.base.models.inf
    choose vac hvac using exists_vac (l := l) (Z := Z) hI hψ hθ
    choose c hc using fun i hi => GlobalTheory.T.exists_const_movedVacuum_all_tuples hSA I hI hP l Z _ _ hψ hθ i hi (vac i) (hvac i)
    refine ⟨xgeo l Z hI vac u (pk W).ΛX, fun j => if h : j + 1 ≤ B.R.m then c j h else 1,
      fun j _ => stdSp_is ((I.rec7 l Z).sp.X_sig _) (gram_X hI j),
      ⟨hψ, hθ, fun j _ => ⟨rfl, rfl, fun z => ?_⟩, fun j _ => hvac j, fun j hj => ?_⟩, rfl, fun r s => by
      show (if ((s : ℕ) = r) then (1 : (I.rec7 l Z).host.E) else 0) = if (r : ℕ) = s then 1 else 0
      by_cases h : (r : ℕ) = s
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (fun h' => h h'.symm), if_neg h], rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← lat_X hI j]; exact Iff.rfl
    · rw [dif_pos hj]; exact hc j hj

    case refine_3 => exact isLineVec_zeta l Z u
    case refine_4 => exact norm_zeta l Z u

    case refine_5 => exact isEmbTop_topDec (gram_X hI _) (gram_X' hI) hP.iX _
    case refine_6 =>
      intro r
      have h0 := rk_top (I.rec7 l Z)
      have h2 := Formalism.L2.Forms.rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl
      change (∑ _i : Fin 1, (if (I.rec7 l Z).sp.X'.rank = (r : ℕ) then (1 : (I.rec7 l Z).host.E) else 0) *
        piE I l Z u) = if (r : ℕ) + 1 = B.R.N B.R.m then piE I l Z u else 0
      rw [Fin.sum_univ_one]
      have hr := r.2
      have e : ((I.rec7 l Z).sp.X'.rank = (r : ℕ)) ↔ ((r : ℕ) + 1 = B.R.N B.R.m) := by
        change _ ↔ (r : ℕ) + 1 = (I.rec7 l Z).R.N (I.rec7 l Z).R.m
        constructor <;> intro h <;> omega
      by_cases h : (I.rec7 l Z).sp.X'.rank = (r : ℕ)
      · rw [if_pos h, if_pos (e.1 h), one_mul]
      · rw [if_neg h, if_neg (fun h' => h (e.2 h')), zero_mul]

    case refine_7 =>
      intro n h x
      refine ⟨GlobalTheory.PlaceModel.latFrame _, GlobalTheory.PlaceModel.isSelfDualC_latFrame _, ?_⟩
      have e : (pk W).ΛX = GlobalTheory.PlaceModel.latFrame (I.rec7 l Z).sp.X' := eq_latFrame_of_isSDFrame W.Q.charW.base.lev.βX
      show GlobalTheory.FinPl.OrthAt (oTop l Z hI n h) (GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X n)) (pk W).ΛX _ x
      rw [e]
      exact GlobalTheory.XGeoStd.orthAt_oTop hI n h x
    case refine_8 =>
      intro PP hPP
      obtain ⟨k, _, _, _, _, _, _, q, h1, h2, h3, h4⟩ := GlobalTheory.XGeoPlace.exists_place W hW u PP hPP
      exact GlobalTheory.T.true_family_vacuum_data W hW u vac PP k q h1 h2 h3 h4

  )
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BcPrVMemLevelVLOfMoves
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem prV_toEAf_eq_swap (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (a : AE D) :
    Formalism.UG.prV (E := D.host.E) v (Formalism.IndefR.Datum.toEAf D a) =
      GlobalTheory.StabConjIndex.swap v (GlobalTheory.AdelicU.compFin D.host.F D.host.E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

set_option maxHeartbeats 1000000 in

theorem bc_prV_mem_levelVL_of_moves : ∀ (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) (L : GlobalTheory.FinPl.Lat S)
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), L.FG →
    (∀ x : Fin n → D.host.E, x ∈ Λ ↔ (fun i => x (finCongr hn i)) ∈ L) →
    ∀ (κ : GA D S) (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    GlobalTheory.AdForm.finM S hn κ = g.1 → ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    GlobalTheory.FinPl.Moves S κ L L (· = v) →
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g ∈
      Formalism.UG.levelVL (Formalism.L2.Forms.sigD D) (S.gram.reindex (finCongr hn) (finCongr hn)) v Λ := by
  intro D S n hn L Λ hL hΛ κ g hg v hm
  subst hn
  have hΛL : Λ = L := by
    ext x; rw [hΛ x]; rfl
  subst hΛL
  have h1 := (GlobalTheory.StMoves.moves_iff_stabLoc S Λ hL v κ).1 hm
  have h2 := GlobalTheory.StabConjIndex.map_stabLoc (Formalism.L2.Forms.sigD D) S.gram v Λ
  have h3 : GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram v (GlobalTheory.AdelicU.proj _ S.gram v κ) ∈
      Formalism.UG.levelVL (Formalism.L2.Forms.sigD D) S.gram v Λ := h2 ▸ ⟨_, h1, rfl⟩
  have hgram : (S.gram.reindex (finCongr (rfl : S.rank = S.rank)) (finCongr rfl)) = S.gram := by
    ext i j; simp
  have hp := GlobalTheory.AdelicU.matHom_proj (Formalism.L2.Forms.sigD D) S.gram v κ
  have hE : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g =
      GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram v (GlobalTheory.AdelicU.proj _ S.gram v κ) := by
    ext i j
    have hij := congrFun (congrFun hg i) j
    have e1 : (GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram v (GlobalTheory.AdelicU.proj _ S.gram v κ)).val i j =
        GlobalTheory.StabConjIndex.swap v ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) (Formalism.L2.Forms.sigD D) S.gram
          (GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram v κ)).val i j) := rfl
    rw [e1, hp]
    show Formalism.UG.prV v (g.1 i j) = GlobalTheory.StabConjIndex.swap v (GlobalTheory.AdelicU.compFin _ _ v _)
    rw [← hij]
    exact prV_toEAf_eq_swap D v _
  rw [hgram, hE]
  exact h3

theorem levelVL_eq_of_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {Lb Λ : Submodule (𝓞 E) (Fin n → E)} {T : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} (hT : (T : 𝓞 F) ∉ v.asIdeal)
    (h1 : ∀ x ∈ Lb, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2 : ∀ j, (Pi.single j (T : E) : Fin n → E) ∈ Lb)
    (h1' : ∀ x ∈ Λ, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2' : ∀ j, (Pi.single j (T : E) : Fin n → E) ∈ Λ) :
    Formalism.UG.levelVL σ J v Lb = Formalism.UG.levelVL σ J v Λ := by
  have e1 := GlobalTheory.Mem.Col2.ChartLevel.latS_eq_std hT h1 h2
  have e2 := GlobalTheory.Mem.Col2.ChartLevel.latS_eq_std hT h1' h2'
  unfold Formalism.UG.levelVL
  exact congrArg _ (e1.trans e2.symm)

end GlobalTheory.FamTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatWeilRepresentationCoresStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToJacobiFlat_weilRepresentation_cores : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ radX J.d, ∀ h', flatBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ)) := by
  first | exact @GlobalTheory.Unf.FlatCommBF.flatBF_om | exact GlobalTheory.Unf.FlatCommBF.flatBF_om | (intros; apply GlobalTheory.Unf.FlatCommBF.flatBF_om <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfEachPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriesLatticeCompletion_of_each_place : ∀ {D : D7} (S : HSp D) (g : GA D S) (L M : GlobalTheory.FinPl.Lat S) (Q : Finset (GlobalTheory.FinPl.Pl D)), (∀ v ∈ Q, GlobalTheory.FinPl.Moves S g L M (· = v)) → GlobalTheory.FinPl.Moves S g L M (· ∈ Q) := by
  first | exact @GlobalTheory.FinPl.MovesPl.moves_of_places | exact GlobalTheory.FinPl.MovesPl.moves_of_places | (intros; apply GlobalTheory.FinPl.MovesPl.moves_of_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterMtEqSmulOne
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.CenterScalar
open Matrix Polynomial

variable {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]

theorem eval_charpolyRev_eq (M : Matrix n n E) (z : E) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm z]

theorem cT_smul (σ : E →+* E) (c : E) (M : Matrix n n E) :
    Formalism.UG.cT σ (c • M) = σ c • Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_add (σ : E →+* E) (M N : Matrix n n E) :
    Formalism.UG.cT σ (M + N) = Formalism.UG.cT σ M + Formalism.UG.cT σ N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_sub (σ : E →+* E) (M N : Matrix n n E) :
    Formalism.UG.cT σ (M - N) = Formalism.UG.cT σ M - Formalism.UG.cT σ N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_cT (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (M : Matrix n n E) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cayley_unitary (σ : E →+* E) (J X : Matrix n n E) (t : E) (ht : σ t = t)
    (hX : Formalism.UG.cT σ X * J + J * X = 0) (hA : (1 - t • X).det ≠ 0) :
    Formalism.UG.cT σ ((2 : E) • (1 - t • X)⁻¹ - 1) * J * ((2 : E) • (1 - t • X)⁻¹ - 1) = J := by
  set A : Matrix n n E := 1 - t • X with hAdef
  set P : Matrix n n E := A⁻¹
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have hAP : A * P = 1 := Matrix.mul_nonsing_inv A hu
  have hPA : P * A = 1 := Matrix.nonsing_inv_mul A hu
  set g : Matrix n n E := (2 : E) • P - 1
  have hgA : g * A = 1 + t • X := by
    rw [Matrix.sub_mul, Matrix.smul_mul, hPA, Matrix.one_mul, hAdef, two_smul]
    abel
  have hcA : Formalism.UG.cT σ A = 1 - t • Formalism.UG.cT σ X := by
    rw [hAdef, cT_sub, cT_smul, Formalism.UG.cT_one, ht]
  have hcPA : Formalism.UG.cT σ P * Formalism.UG.cT σ A = 1 := by
    rw [← Formalism.UG.cT_mul, hAP, Formalism.UG.cT_one]
  have hY : Formalism.UG.cT σ X * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
  have key : Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A = Formalism.UG.cT σ A * J * A := by
    have e1 : Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A = Formalism.UG.cT σ (g * A) * J * (g * A) := by
      rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    rw [e1, hgA, hcA, cT_add, cT_smul, Formalism.UG.cT_one, ht]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hY]
    rw [hAdef]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul]
    module
  calc Formalism.UG.cT σ g * J * g
      = (Formalism.UG.cT σ P * Formalism.UG.cT σ A) * (Formalism.UG.cT σ g * J * g) * (A * P) := by
        rw [hcPA, hAP, Matrix.one_mul, Matrix.mul_one]
    _ = Formalism.UG.cT σ P * (Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A) * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ P * (Formalism.UG.cT σ A * J * A) * P := by rw [key]
    _ = (Formalism.UG.cT σ P * Formalism.UG.cT σ A) * J * (A * P) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [hcPA, hAP, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.CenterScalar

namespace GlobalTheory.CenterScalar
open Matrix Polynomial

variable {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]
variable {R : Type} [CommRing R] (ι : E →+* R)

theorem map_smulE (c : E) (M : Matrix n n E) : (c • M).map ι = ι c • M.map ι := by
  ext i j; simp

theorem map_subE (M N : Matrix n n E) : (M - N).map ι = M.map ι - N.map ι := by
  ext i j; simp

theorem map_addE (M N : Matrix n n E) : (M + N).map ι = M.map ι + N.map ι := by
  ext i j; simp

theorem map_oneE : (1 : Matrix n n E).map ι = 1 := Matrix.map_one _ (map_zero ι) (map_one ι)

theorem map_mulE (M N : Matrix n n E) : (M * N).map ι = M.map ι * N.map ι := Matrix.map_mul

theorem commute_skew (σ : E →+* E) (J : Matrix n n E) (hF : {t : E | σ t = t}.Infinite) (h2 : (2 : E) ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g : Matrix n n E, Formalism.UG.cT σ g * J * g = J → Commute Z (g.map ι))
    (X : Matrix n n E) (hX : Formalism.UG.cT σ X * J + J * X = 0) : Commute Z (X.map ι) := by
  classical
  have hp : X.charpolyRev ≠ 0 := by
    intro h
    have := Matrix.eval_charpolyRev (M := X)
    rw [h, Polynomial.eval_zero] at this
    exact zero_ne_one this
  obtain ⟨t, ht, hts⟩ := hF.exists_notMem_finset (insert 0 X.charpolyRev.roots.toFinset)
  have ht0 : t ≠ 0 := fun e => hts (by simp [e])
  have hdet : (1 - t • X).det ≠ 0 := by
    intro e
    apply hts
    rw [Finset.mem_insert, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot, eval_charpolyRev_eq]
    exact Or.inr e
  have hg := hZ _ (cayley_unitary σ J X t ht hX hdet)
  set A : Matrix n n E := 1 - t • X with hAdef
  set P : Matrix n n E := A⁻¹
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  have hAP : A * P = 1 := Matrix.mul_nonsing_inv A hu
  have hPA : P * A = 1 := Matrix.nonsing_inv_mul A hu
  have hP : Commute Z (P.map ι) := by
    have h1 : Commute Z (((2 : E) • P - 1).map ι + 1) := hg.add_right (Commute.one_right Z)
    rw [map_subE, map_smulE, map_oneE, sub_add_cancel] at h1
    have h3 := h1.smul_right (ι (2 : E)⁻¹)
    rwa [smul_smul, ← map_mul, inv_mul_cancel₀ h2, map_one, one_smul] at h3
  have hA : Commute Z (A.map ι) := by
    let u : (Matrix n n R)ˣ := ⟨P.map ι, A.map ι, by rw [← map_mulE, hPA, map_oneE], by rw [← map_mulE, hAP, map_oneE]⟩
    exact Commute.units_inv_right (u := u) hP
  have h4 : Commute Z (ι t • X.map ι) := by
    have := (Commute.one_right Z).sub_right hA
    rwa [hAdef, map_subE, map_oneE, map_smulE, sub_sub_cancel] at this
  have h5 := h4.smul_right (ι t⁻¹)
  rwa [smul_smul, ← map_mul, inv_mul_cancel₀ ht0, map_one, one_smul] at h5

theorem commute_all (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n E) (hJh : Formalism.UG.cT σ J = J)
    (hJ : J.det ≠ 0) (ξ : E) (hξ : σ ξ = -ξ) (hξ0 : ξ ≠ 0)
    (hF : {t : E | σ t = t}.Infinite) (h2 : (2 : E) ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g : Matrix n n E, Formalism.UG.cT σ g * J * g = J → Commute Z (g.map ι))
    (M : Matrix n n E) : Commute Z (M.map ι) := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ
  have hJJi : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have hJiJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have hcJi : Formalism.UG.cT σ J⁻¹ * J = 1 := by
    calc Formalism.UG.cT σ J⁻¹ * J = Formalism.UG.cT σ J⁻¹ * Formalism.UG.cT σ J := by rw [hJh]
      _ = 1 := by rw [← Formalism.UG.cT_mul, hJJi, Formalism.UG.cT_one]
  have skew : ∀ K : Matrix n n E, Formalism.UG.cT σ K = -K → Commute Z ((J⁻¹ * K).map ι) := by
    intro K hK
    refine commute_skew ι σ J hF h2 Z hZ _ ?_
    rw [Formalism.UG.cT_mul, hK, Matrix.mul_assoc, hcJi, ← Matrix.mul_assoc, hJJi]
    simp
  set K := J * M
  have hK1 : Formalism.UG.cT σ (K - Formalism.UG.cT σ K) = -(K - Formalism.UG.cT σ K) := by
    rw [cT_sub, cT_cT σ hσ]; abel
  have hK2 : Formalism.UG.cT σ (ξ • (K + Formalism.UG.cT σ K)) = -(ξ • (K + Formalism.UG.cT σ K)) := by
    rw [cT_smul, cT_add, cT_cT σ hσ, hξ, neg_smul, add_comm (Formalism.UG.cT σ K)]
  have c1 := skew _ hK1
  have c2 := (skew _ hK2).smul_right (ι ξ⁻¹)
  have c3 := (c1.add_right c2).smul_right (ι (2 : E)⁻¹)
  have e : M = (2 : E)⁻¹ • (J⁻¹ * (K - Formalism.UG.cT σ K) + ξ⁻¹ • (J⁻¹ * (ξ • (K + Formalism.UG.cT σ K)))) := by
    rw [Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hξ0, one_smul, ← Matrix.mul_add, sub_add_add_cancel,
      ← two_smul E K, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h2, one_smul, ← Matrix.mul_assoc, hJiJ,
      Matrix.one_mul]
  rw [e, map_smulE, map_addE, map_smulE]
  exact c3

theorem eq_smul_one (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n E) (hJh : Formalism.UG.cT σ J = J)
    (hJ : J.det ≠ 0) (ξ : E) (hξ : σ ξ = -ξ) (hξ0 : ξ ≠ 0)
    (hF : {t : E | σ t = t}.Infinite) (h2 : (2 : E) ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g : Matrix n n E, Formalism.UG.cT σ g * J * g = J → Commute Z (g.map ι)) :
    ∃ c : R, Z = c • (1 : Matrix n n R) := by
  have hs : Z ∈ Set.range (Matrix.scalar n) := by
    refine Matrix.mem_range_scalar_of_commute_single fun i j _ => ?_
    have := (commute_all ι σ hσ J hJh hJ ξ hξ hξ0 hF h2 Z hZ (Matrix.single i j 1)).symm
    have e : (Matrix.single i j (1 : E)).map ι = Matrix.single i j 1 := by
      ext a b; simp [Matrix.single_apply]
    rwa [e] at this
  obtain ⟨c, hc⟩ := hs
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

end GlobalTheory.CenterScalar

namespace GlobalTheory.CenterScalar
open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_skew (D : D7) : ∃ ξ : D.host.E,
    (D.sp.cm.sig : D.host.E →+* D.host.E) ξ = -ξ ∧ ξ ≠ 0 := by
  obtain ⟨e, he⟩ : ∃ e : D.host.E, e ∉ (algebraMap D.host.F D.host.E).range := by
    by_contra h
    push_neg at h
    have htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
      ext x
      simp only [Algebra.mem_bot, Algebra.mem_top, iff_true]
      exact h x
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
    rw [D.sp.cm.deg2] at h1
    norm_num at h1
  refine ⟨e - star e, ?_, ?_⟩
  · change star (e - star e) = -(e - star e)
    rw [star_sub, star_star, neg_sub]
  · intro h0
    apply he
    exact (D.sp.cm.fixed e).1 (sub_eq_zero.1 h0).symm

theorem fixed_infinite (D : D7) :
    {t : D.host.E | (D.sp.cm.sig : D.host.E →+* D.host.E) t = t}.Infinite := by
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (algebraMap D.host.F D.host.E).injective)
  rintro _ ⟨a, rfl⟩
  exact D.sp.cm.sig.commutes a

theorem center_mt_eq_smul_one : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (z : GA D V), z ∈ Subgroup.center (GA D V) →
    ∃ c : AE D, Formalism.L2.Theta.mt V z = c • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  intro D V z hz
  obtain ⟨ξ, hξ, hξ0⟩ := exists_skew D
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)
  have hσ : ∀ x, σ (σ x) = x := fun x => star_star x
  have hJh : Formalism.UG.cT σ V.gram = V.gram := Matrix.ext fun i j => V.herm.eq (V.frame j) (V.frame i)
  refine eq_smul_one (incA D) σ hσ V.gram hJh (Formalism.L2.Theta.gram_det_ne V) ξ hξ hξ0 (fixed_infinite D)
    two_ne_zero _ ?_
  intro g hg
  have hdet : IsUnit g.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => Formalism.L2.Theta.gram_det_ne V ?_
    have := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  let gG : GL (Fin V.rank) D.host.E := Matrix.nonsingInvUnit g hdet
  have hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g.map (incA D)) = (Formalism.UG.cT σ g).map (incA D) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR, σ]
  have hmem : Formalism.UG.bc (incA D) gG ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g.map (incA D)) * (V.gram.map (incA D)) * g.map (incA D) =
      V.gram.map (incA D)
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  let w : GA D V := ⟨Formalism.UG.bc (incA D) gG, hmem⟩
  have hw : Formalism.L2.Theta.mt V w = g.map (incA D) := rfl
  have hzw : w * z = z * w := Subgroup.mem_center_iff.1 hz w
  have e1 : Formalism.L2.Theta.mt V (w * z) = Formalism.L2.Theta.mt V w * Formalism.L2.Theta.mt V z := by
    simp [Formalism.L2.Theta.mt, map_mul]
  have e2 : Formalism.L2.Theta.mt V (z * w) = Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V w := by
    simp [Formalism.L2.Theta.mt, map_mul]
  rw [← hw]
  change Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V w = Formalism.L2.Theta.mt V w * Formalism.L2.Theta.mt V z
  rw [← e1, ← e2, hzw]

end GlobalTheory.CenterScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilCoefficientFockVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_weilCoefficient_fockVectors : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → ∀ Q₁ Q₂, Continuous fun g : GA D (Wc D i) => l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) := by
  first | exact @GlobalTheory.LiftCoefCont.continuous_l2_weil_action_ptAt | exact GlobalTheory.LiftCoefCont.continuous_l2_weil_action_ptAt | (intros; apply GlobalTheory.LiftCoefCont.continuous_l2_weil_action_ptAt <;> assumption)
end

