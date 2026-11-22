import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePsiBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0498
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1927
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1929
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1928

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGoodFormValuesMemScaledDualWeylLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormFinVal

open GlobalTheory.CoefModel
open scoped TensorProduct

section Lat

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

private theorem nabAt_map (emb : ι → E →+* K) (lam : ι → DomWeight n) (γ : GL (Fin n) E) (M : Submodule (𝓞 E) (Fin n → E))
    (x : VV K lam) (hx : x ∈ nabAt emb lam M) :
    rhoV emb lam γ x ∈ nabAt emb lam (M.map ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E))) := by
  unfold nabAt
  simp_rw [tauLatG E K ι n emb]
  exact (Formalism.L2.Col.nabK_gLat lam _ (embGL emb γ)).ge ⟨x, hx, rfl⟩

omit [NumberField K] in
private theorem invTr_invTr (B : GL (Fin n) K) : inside₂ K n (inside₂ K n B) = B := by
  apply Units.ext
  simp [inside₂]

private theorem isBasisAt_of_dualFr (w : HeightOneSpectrum (𝓞 K)) {M : Submodule (𝓞 K) (Fin n → K)}
    (hM : Submodule.IsLattice K M) {B : GL (Fin n) K} (hB : IsBasisAt w (dualFr M) B) : IsBasisAt w M (inside₂ K n B) := by
  obtain ⟨B₀, h₀⟩ := GlobalTheory.LatBasisAt.basisAtEx K n M hM w
  have h1 : IsBasisAt w (colLat (inside₂ K n B₀)) B :=
    Eq.trans (Eq.symm (GlobalTheory.DualWeylDual.isBasisAt_dualFr w hM.fg h₀)) hB
  have h2 := GlobalTheory.DualWeylDual.isBasisAt_dualFr w (Submodule.fg_span (Set.finite_range _)) h1
  rw [show Submodule.span (𝓞 K) _ = colLat (inside₂ K n B₀) from rfl, GlobalTheory.DualWeylDual.dualFr_colLat, invTr_invTr] at h2
  exact Eq.trans h₀ h2

private theorem funEquiv_nabK (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K))
    (hM : ∀ τ, Submodule.IsLattice K (M τ)) (F : VV K lam) (hF : F ∈ nabK lam M) :
    funEquiv lam F ∈ nabK (fun τ => (lam τ).dual) fun τ => dualFr (M τ) := by
  have hF' : F.1 ∈ transLat lam (nabStd K lam) M := hF
  show (funEquiv lam F).1 ∈ transLat _ (nabStd K _) _
  simp only [transLat, Submodule.mem_iInf] at hF' ⊢
  intro w B hB
  obtain ⟨s, hs, h⟩ := hF' w (invTrK B) fun τ => isBasisAt_of_dualFr w (hM τ) (hB τ)
  refine ⟨s, hs, ?_⟩
  have h1 := (funEquiv_mem_nabStd lam ((s : K) • rhoK lam (invTrK B)⁻¹ F)).1 h
  have e : invTrK (invTrK B)⁻¹ = B⁻¹ := by
    rw [map_inv]
    exact congrArg (·⁻¹) (funext fun τ => invTr_invTr (B τ))
  rw [map_smul, funEquiv_rhoK, e] at h1
  exact h1

private theorem funEquiv_mapVV {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) (F : VV K lam) :
    funEquiv lam (mapVV φ lam F) = mapVV φ _ (funEquiv lam F) :=
  ((isFunForm_iff_eq lam _ _).1 (GlobalTheory.BrRat.isFunForm_map φ lam (isFunForm_funEquiv lam F))).symm

end Lat

section Ad

variable {D : D7}

private theorem mem_hLat (V : HSp D) (g : Bridge.Gf V) (x : Fin V.rank → D.host.E) :
    x ∈ Bridge.hLat V g ↔ (g.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
      GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  rw [← SetLike.mem_coe, GlobalTheory.RepsCompare.coe_hLat, ← GlobalTheory.RepsCompare.inv_mulVec_mem_iff]
  rfl

private theorem hLat_mul_lev {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (L : LevDat D.host.E ℂ V.rank) (h : Bridge.Gf V) (k : (levEnv V β L).J) :
    Bridge.hLat V (h * k) = Bridge.hLat V h := by
  have key : ∀ (h : Bridge.Gf V) (k : Bridge.Gf V), k ∈ (levEnv V β L).J → Bridge.hLat V h ≤ Bridge.hLat V (h * k) := by
    intro h k hk x hx
    rw [mem_hLat, ← GlobalTheory.PrincInLevel.eq_latC hβ] at hx ⊢
    have h1 := GlobalTheory.RepsCompare.mulVec_mem_hat hβ L (inv_mem hk) hx
    rw [Matrix.mulVec_mulVec, ← Units.val_mul] at h1
    rwa [Subgroup.coe_mul, _root_.mul_inv_rev]
  refine le_antisymm ?_ (key h k k.2)
  have := key (h * k) (k : Bridge.Gf V)⁻¹ (inv_mem k.2)
  rwa [mul_inv_cancel_right] at this

private theorem hLat_rat (V : HSp D) (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) (h : Bridge.Gf V) :
    Bridge.hLat V (Bridge.ratF V γ * h) = (Bridge.hLat V h).map (γE.1.mulVecLin.restrictScalars (𝓞 D.host.E)) := by
  let φ : D.host.E →+* Af D.host.F ⊗[D.host.F] D.host.E := inclR (F := D.host.F) (Af D.host.F)
  have e1 : (Bridge.ratF V γ).1 = Formalism.UG.bc φ γE := by
    show Formalism.UG.bc _ (matHom V γ.1) = _
    rw [show matHom V γ.1 = _ from hγ]
    apply Units.ext
    ext i j
    rfl
  have e2 : ∀ x : Fin V.rank → D.host.E, x ∈ Bridge.hLat V (Bridge.ratF V γ * h) ↔ (γE⁻¹).1 *ᵥ x ∈ Bridge.hLat V h := by
    intro x
    have e3 : (Formalism.UG.bc φ γE⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) =
        fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] ((γE⁻¹).1 *ᵥ x) i := by
      funext i
      exact (RingHom.map_mulVec φ (γE⁻¹).1 x i).symm
    rw [mem_hLat, mem_hLat, Subgroup.coe_mul, _root_.mul_inv_rev, e1, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv, e3]
  ext x
  rw [e2]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    show γE.1 *ᵥ ((γE⁻¹).1 *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rintro ⟨z, hz, rfl⟩
    show (γE⁻¹).1 *ᵥ (γE.1 *ᵥ z) ∈ _
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

private theorem globLat_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (g : GA D V) :
    Formalism.UG.CS.globLat (Lev.finE V g) Λ = Bridge.hLat V ((finHom V).rangeRestrict g) := by
  ext x
  rw [mem_hLat, ← GlobalTheory.PrincInLevel.eq_latC hβ]
  have e : ((Formalism.UG.bc (Lev.swapAE D) (finHom V g))⁻¹).1 *ᵥ
      (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) =
      fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E
        ((((finHom V g)⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) i) := by
    rw [← map_inv]
    funext i
    change _ = Lev.swapAE D _
    rw [RingHom.map_mulVec (Lev.swapAE D)]
    rfl
  change ((Formalism.UG.bc (Lev.swapAE D) (finHom V g))⁻¹).1 *ᵥ
    (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ _
  rw [e]
  constructor
  · intro hz
    have := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ hz
    simp only [AlgEquiv.symm_apply_apply] at this
    exact this
  · intro hz
    exact GlobalTheory.PrincInLevel.swap_mem_hatL Λ _ hz

private theorem ext_mem {V : HSp D} {C : Bridge.CoefDat D V} {S : CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)}
    {χ : J →* ℂˣ} {P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ} {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair del}
    (hc : Bridge.CoefTie V C P lam c0 pair (nabAt (labLL D) lam) del) (hm : Bridge.CoefMapTie V C c0 (rhoV (labLL D) lam))
    (hJ : ∀ h (k : J), Bridge.hLat V (h * k) = Bridge.hLat V h)
    (f : S.Forms) (hf : ∀ c, (f : S.Cl → S.V) c ∈ S.Nab c) (g : Bridge.Gf V) :
    ∃ (k : J) (u : VV D.what₂.LL lam), u ∈ nabAt (labLL D) lam (Bridge.hLat V g) ∧ P.extL f g = (χ k : ℂ) • c0 u := by
  obtain ⟨e, -, he, -, hN, -⟩ := hc
  obtain ⟨γE, hγ⟩ := GlobalTheory.RationalValues.exists_isRatMat (P.decG g)
  have h1 : e ((f : S.Cl → S.V) (P.decC g)) ∈ nabAt (labLL D) lam (Bridge.hLat V (P.y (P.decC g))) := by
    rw [← hN (P.decC g)]
    exact ⟨_, hf _, rfl⟩
  have e3 : Bridge.hLat V g = (Bridge.hLat V (P.y (P.decC g))).map
      ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVecLin.restrictScalars (𝓞 D.host.E)) :=
    (congrArg (Bridge.hLat V) (P.dec_spec g)).trans ((hJ _ _).trans (hLat_rat V _ γE hγ _))
  refine ⟨P.decK g, rhoV (labLL D) lam γE (e ((f : S.Cl → S.V) (P.decC g))), ?_, ?_⟩
  · exact (congrArg (nabAt (labLL D) lam) e3).ge (nabAt_map (labLL D) lam γE _ _ h1)
  · exact congrArg ((χ (P.decK g) : ℂ) • ·) ((congrArg (C.ρ (P.decG g)) (he _)).trans (hm.1 _ γE hγ _).symm)

private theorem inLat_value {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (Y : LSp D) (hY : Y = ⟨V, Λ⟩) (h : V.rank = Y.sp.rank) (lam : D.what₂.Tau → DomWeight V.rank)
    (lam' : D.what₂.Tau → DomWeight Y.sp.rank) (hw : ∀ τ a, (lam' τ).w (Fin.cast h a) = (lam τ).w a) (y : GfC Y.sp)
    (v : VV D.what₂.LL lam)
    (hv : v ∈ nabAt (labLL D) lam
      (Bridge.hLat V ((finHom V).rangeRestrict (cast (congrArg (fun X : LSp D => GA D X.sp) hY) y.1))))
    (U : VV ℂ lam')
    (hU : U.1 = MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast h) (Fin.cast h))) (MvPolynomial.map D.what₂.embLL v.1))
    (fr : GL (Fin Y.sp.rank) D.host.E) (w : PlL D) :
    InLat (fun τ => (lam' τ).dual) w 0
      ((Formalism.UG.CS.globLat (finG Y.sp y) Y.lat).comap (fr.1.mulVecLin.restrictScalars (𝓞 D.host.E)))
      (rhoVr (tauE D) _ fr⁻¹ (funOf lam' U)) := by
  subst hY
  have e : lam' = lam := funext fun τ => by
    have := hw τ
    generalize lam' τ = a at this
    generalize lam τ = b at this
    cases a
    cases b
    congr
    funext i
    exact this i
  subst e
  have hr : (Prod.map id (Prod.map (Fin.cast h) (Fin.cast h)) : D.what₂.Tau × Fin V.rank × Fin V.rank → _) = id := by
    funext x
    rfl
  rw [hr, MvPolynomial.rename_id_apply] at hU
  obtain rfl : U = mapVV D.what₂.embLL lam' v := Subtype.ext hU
  rw [(isFunForm_iff_eq _ _ _).1 ((SumModel.readOK lam').1 _), funEquiv_mapVV, TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.rhoVr_mapVV]
  refine TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.inLat_of_mem _ w ?_
  have e1 : Formalism.UG.CS.globLat (finG V y) Λ = Bridge.hLat V ((finHom V).rangeRestrict y.1) := globLat_eq hβ y.1
  have e2 := TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.comap_eq_map fr 1 (Bridge.hLat V ((finHom V).rangeRestrict y.1))
    (Formalism.UG.CS.globLat (finG V y) Λ) fun z => by rw [e1, Units.val_one, Matrix.one_mulVec]
  rw [mul_one] at e2
  refine e2 ▸ TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.nabAtr_map _ _ _ _ _ ?_
  exact funEquiv_nabK lam' _
    (fun τ => GlobalTheory.TauLat.tauLatLattice _ _ _ _ (labLL D) τ _ (GlobalTheory.RepsCompare.isLattice_hLat _ _)) v hv

end Ad

end GlobalTheory.FormFinVal

set_option maxHeartbeats 1600000 in
open GlobalTheory.FormFinVal in
theorem _root_.GlobalTheory.T.integralGoodForm_values_mem_scaledDualWeylLattice : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch _ _ => ∀ (t : _) (w : PlL D), ∀ x ∈ (A.fam.R t).Mt (A.fam.lvl F.P0 F.ψ0), ∀ y,
  InLat _ w 0 (latAt ch.S.toGridChoice (.grid 0 D.R.m) y) (rowVal ch.S.toGridChoice (ch.S.formC t (R.jX t (formOf F t x)) y)) := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ _ t w x hx y
  obtain ⟨gram, c₀, c₁, hT, hco⟩ := ch.S.co_is
  have hc := hS.core
  have hf : ∀ c : (A.MtildeCSD t).Cl, (formOf F t x).1 c ∈ (A.MtildeCSD t).Nab c := fun c => hx c (Set.mem_univ c)
  obtain ⟨k, u, hu, hv⟩ := ext_mem (hT.coefR t) hT.mapR (fun h k => hLat_mul_lev hc.lev.βX (R.datXt t) h k) (formOf F t x)
    hf (toXf y)
  have h0 := (congrFun (hc.models.jX t (formOf F t x)) (toXf y)).trans hv
  have i0 : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩
  obtain ⟨a, ha⟩ := GlobalTheory.FormCoef.typeX_mem R t D.what₂.embLL.fieldRange (GlobalTheory.RationalValues.chiVal_of_chiW R hc.grp.chiW)
    (GlobalTheory.RationalValues.xiR_mem R hc.lev hc.fam.pl_onto hc.fam.muVal hT.ok i0 t) k
  obtain ⟨n, hn, hak⟩ : ∃ n : ℕ, 0 < n ∧ (levEnv D.sp.X' R.βX (R.datXt t)).χ k ^ n = 1 :=
    isOfFinOrder_iff_pow_eq_one.1 (GlobalTheory.LevSplit.levFn_finOrd _ _ _)
  have hak' : a ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, ha, ← Units.val_pow_eq_pow_val, hak, map_one, Units.val_one])
  have hai : IsIntegral ℤ a := IsIntegral.of_pow hn (by rw [hak']; exact isIntegral_one)
  have h1 : (R.HX t).e (R.jX t (formOf F t x)) (toXf y) = c₀ (a • u) :=
    h0.trans (GlobalTheory.RationalValues.smul_eq_of c₀ ha rfl)
  have hw : ∀ τ a, (listedWt ch.G (.grid 0 D.R.m) τ).w (Fin.cast (rank_zero_m ch.G) a) =
      (Bridge.lamRdef (Ptw D) τ).w a := fun τ a => by
    change (wtOf _ (GlobalTheory.SignedHC.entries (parV D ch.sc.cGap 0 D.R.m τ))).w _ = _
    rw [parV_zero D ch.sc.cGap le_rfl τ]
    exact wtOf_entries_eq (rank_zero_m ch.G) (GlobalTheory.ForcedWeights.lamRForced D τ) a
  exact inLat_value hc.lev.βX (ch.G.node (.grid 0 D.R.m)) (colY_m _) (rank_zero_m ch.G) _ _ hw y (a • u)
    (Submodule.smul_mem _ (⟨a, hai⟩ : 𝓞 D.what₂.LL) hu) _ (by rw [SumChoice.formC, h1, hco]) _ w
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelHeisenbergOperatorsTranslationChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LinBarOps

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE At piW cA incM)

theorem linForm_eq {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) :
    l Y = ∑ k, ∑ j, Y k j * l (Matrix.single k j 1) := by
  conv_lhs => rw [Y.matrix_eq_sum_single]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

theorem sum_transpose_mul {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (g : Matrix m m K) (Y L : Matrix m n K) :
    ∑ k, ∑ j, (gᵀ * Y) k j * L k j = ∑ k, ∑ j, Y k j * (g * L) k j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ x, ∑ i, ∑ j, g i x * Y i j * L x j := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ j, g i x * Y i j * L x j := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ x, g i x * Y i j * L x j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.LinBarOps

namespace GlobalTheory.LinBarOps

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE At piW cA incM)

theorem at_hTens {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (x u : Matrix (Fin m) (Fin n) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * hTens (cA σ) (incM F JA) (incM F JB) x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

theorem heis_ops : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) ∧ GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ ≠ 1 ∧
    ∃ (wT : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁))
      (wM : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)),
    ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ) = fun Y => ι φ (Y + C)) ∧
      (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ) = fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l Y) * ι φ Y) ∧
      (∀ g C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ)) =
        fun Y => ι (S g φ) (Y + ((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * C)) ∧
      (∀ g l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ)) =
        fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l (g.valᵀ * Y)) * ι (S g φ) Y) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hT K hK S hSB h4
  have hcm : IsCMExt F E σ := hT.base.cm
  have hstd := hT.base.std
  refine ⟨GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 _, GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd _, ?_⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdV : Γ.V'.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hV'.sig w)
    have e : (Γ.V'.J.map (Bs.emb w).1).det = (Bs.emb w).1 Γ.V'.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : Γ.W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hW.sig w)
    have e : (Γ.W.J.map (Bs.emb w).1).det = (Bs.emb w).1 Γ.W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  set A := Γ.V'.J.map Bs.τ₁ with hAdef
  set B := Γ.W.J.map Bs.τ₁ with hBdef
  have hA : IsUnit A.det := by
    have e : A.det = (Bs.τ₁ : E →+* Fv F Bs.v₁) Γ.V'.J.det := (RingHom.map_det _ _).symm
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdV ((Bs.τ₁ : E →+* Fv F Bs.v₁).injective (by rw [map_zero]; exact h))
  have hB : IsUnit Bᵀ.det := by
    have e : B.det = (Bs.τ₁ : E →+* Fv F Bs.v₁) Γ.W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h => hdW ((Bs.τ₁ : E →+* Fv F Bs.v₁).injective (by rw [map_zero]; exact h))
  have hBm : IsUnit B.det := by rw [← Matrix.det_transpose]; exact hB
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)) =>
    GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm Bs.v₁ Bs.τ₁ P₀ P₁
  let Pm : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) :=
    fun C => -(A⁻¹ * C * (Bᵀ)⁻¹)
  let Lm : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) →
      Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) := fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hcoP : ∀ C, -(A * (U 0 (Pm C)).map (piW (Bs.τ₁.comp σ)) * Bᵀ) = C := by
    intro C
    rw [hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have hsymp : ∀ x u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F Bs.v₁) x → x.map (piW Bs.τ₁) = 0 →
      u.map (piW (Bs.τ₁.comp σ)) = 0 →
      Bs.ψ (symp (R := AF F) (cA σ) (-1) (incM F Γ.V'.J) (incM F Γ.W.J) x u) =
        GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁
          (-(∑ k, ∑ j, (-(A * x.map (piW (Bs.τ₁.comp σ)) * Bᵀ)) k j * u.map (piW Bs.τ₁) k j)) := by
    intro x u hx hx0 hu1
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm Bs.v₁ Bs.τ₁ _ (at_hTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
      GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm Bs.τ₁ Γ.V'.J Γ.W.J hT.geo.hV'.herm hT.geo.hW.skew x u hx0 hu1]
    rfl
  refine ⟨fun C => GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (U 0 (Pm C)),
    fun l => GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (U (-Lm l) 0), ?_⟩
  intro ι hι
  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinBar at hL
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have htr := hL.trans
  have hmu := hL.mult
  have hK' : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)),
      actAB (cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) u = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u := by
    intro g u
    simp [actAB, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat]
  have hKat : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F Bs.v₁) u →
      At (evFin F Bs.v₁) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u) := by
    intro g u hu r hr
    rw [← Matrix.mul_smul, hu r hr, Matrix.mul_zero]
  have hKmap : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)) (t : E →ₐ[F] Fv F Bs.v₁),
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u).map (piW t) = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (piW t) * u.map (piW t) :=
    fun g u t => Matrix.map_mul
  have hbr := fun (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)) hγ (φ : (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) => GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ
  have hsb := fun (w : (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (φ : (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB _) => GlobalTheory.SchrSB.schr_mem_SB Bs.ψ hstd.1 Bs.v₁ w φ hφ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C φ hφ
    funext Y
    rw [htr (U 0 (Pm C)) (hUat 0 (Pm C)) (hU0 0 (Pm C)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat 0 (Pm C)) φ) Y, hcoP]
  · intro l φ hφ
    funext Y
    have hm := hmu (U (-Lm l) 0) (hUat (-Lm l) 0) (hU1 (-Lm l) 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat (-Lm l) 0) φ)
      (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) (hU1 (-Lm l) 0), hcoP, hU0, linForm_eq l Y]
    congr 2
    simp [Lm, Finset.sum_neg_distrib]
  · intro g C φ hφ
    funext Y
    rw [h4 g _ (hUat 0 (Pm C)) φ hφ, hK']
    have hat := hKat g _ (hUat 0 (Pm C))
    rw [htr _ hat (by rw [hKmap, hU0, Matrix.mul_zero]) _ (hSB g φ hφ) _ (hsb _ _ (hSB g φ hφ)) (hbr _ hat _) Y]
    congr 2
    rw [hKmap, (hK g).2.2, hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA,
      Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  · intro g l φ hφ
    funext Y
    rw [h4 g _ (hUat (-Lm l) 0) φ hφ, hK']
    have hat := hKat g _ (hUat (-Lm l) 0)
    have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * U (-Lm l) 0).map (piW (Bs.τ₁.comp σ)) = 0 := by
      rw [hKmap, hU1, Matrix.mul_zero]
    have hm := hmu _ hat h1 _ (hSB g φ hφ) _ (hsb _ _ (hSB g φ hφ)) (hbr _ hat _) (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) h1, hcoP, hKmap, (hK g).2.1, hU0, linForm_eq l]
    congr 2
    rw [show (∑ k, ∑ j, ((g : Matrix (Fin a') (Fin a') (Fv F Bs.v₁))ᵀ * Y) k j * l (Matrix.single k j 1)) =
      ∑ k, ∑ j, ((g : Matrix (Fin a') (Fin a') (Fv F Bs.v₁))ᵀ * Y) k j * Lm l k j from rfl, sum_transpose_mul]
    simp [Matrix.mul_neg, Finset.sum_neg_distrib]

end GlobalTheory.LinBarOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∀ φ φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ → φ₁ ∈ GlobalTheory.WeilM.SB _ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om' (x, 1)) φ φ₁ →
      ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ₁ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.LocalIsom.lintegral_sq_eq_of_acts | exact GlobalTheory.LocalIsom.lintegral_sq_eq_of_acts | (intros; apply GlobalTheory.LocalIsom.lintegral_sq_eq_of_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentHasRationalWeilOperatorQuadraticChStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerUnipotent_hasRationalWeilOperator_quadraticChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (b : Matrix κ κ F), bᵀ = b →
    HasOp ψ (Matrix.fromBlocks 1 0 b 1) := by
  first | exact @GlobalTheory.RatWeilUnip.hasOp_unip | exact GlobalTheory.RatWeilUnip.hasOp_unip | (intros; apply GlobalTheory.RatWeilUnip.hasOp_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAllGaussianWidthsOfFourierStableSchwartz
section
open FourierTransform MeasureTheory Filter Topology

theorem GlobalTheory.GaussWidths.all_widths : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M :=
  GlobalTheory.GaussWidths.all_widths_of_conv GlobalTheory.T.mem_of_closedSubmodule_gaussian_convolution
end

