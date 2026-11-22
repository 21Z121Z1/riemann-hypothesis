import Formalism.LocalToGlobal.Divisibility.Bundle0004
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0826
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0026
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTiedRowLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
import Formalism.LocalToGlobal.HilbertRowConditions.RowPinMin

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins
section
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
def lamOfCol_alt {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) :
    ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i) :=
  fun u i τ =>
    cast (congrArg (fun R : Ranks => DomWeight (R.N i)) K.kerTie.2.1)
      (K.c.W.lamTrue (K.c.wd (cast K.kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1.symm u)) i
        (cast (congrArg Formalism.L2.Col.Fields.Tau K.kerTie.1) (T.ker.seam.iT.symm τ)))
open Classical in
def columnAddCharacter {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) : ∀ PP : Pl K.X.E, AddChar (kP PP) D.what₂.LL :=
  fun PP => if h : PP ∈ K.c.Pr.vGs then K.c.Ch.psi0 ⟨PP, h⟩ else 1
open Classical in
structure ColumnCharactersCompatible {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) : Prop where
  grpTie : HEq P.grp (inferInstance : Group (Formalism.L2.Col.G0 K.X.E K.c.Pr.vGs K.c.Rk.r))
  psTie : HEq P.Ps K.c.Lv.grp ∧ HEq P.ψs K.c.Lv.chr
  pointCharacterEq : HEq P.P0 (P0 K.c.Pr.vGs K.c.Rk.r (_root_.Formalism.L2.DIV.columnAddCharacter K)).H ∧ HEq P.ψ0 (P0 K.c.Pr.vGs K.c.Rk.r (_root_.Formalism.L2.DIV.columnAddCharacter K)).chi
  wOk : K.c.W.Ok
  chOk : K.c.Ch.Ok
  hcTie : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    HEq (K.c.W.hc (K.c.wd (cast K.kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1.symm u))
      (cast (congrArg Formalism.L2.Col.Fields.Tau K.kerTie.1) (T.ker.seam.iT.symm τ))) (D.hcW u τ)
  wtTie : ∃ (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) (n : D.what₂.Word → ℕ → D.what₂.Tau → ℕ),
    Formalism.L2.Ker.KerEntTied.WtTie T.ker (_root_.Formalism.L2.DIV.lamOfCol_alt K) sh n
  xgTie : ∀ χ : Formalism.L2.Col.G0 K.X.E K.c.Pr.vGs K.c.Rk.r → D.what₂.LL,
    χ ∈ K.c.Xg ↔ (fun g => χ (cast K.gEq (P.I.eG.symm g))) ∈ Formalism.L2.Col.XgE K.c.Am.σ₀ D.ntypes.e0
  qNF : ∀ (t : P.A3.fam3.base3.Tup) (j : ℕ) (b : (K.c.Li t).β j)
      (v : ↥(Formalism.L2.Col.uSG K.c.Pr.vGs (Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL)))),
      v.1 ∉ K.c.Pr.vGs → 1 ≤ j → j + 2 ≤ K.c.Rk.m →
      ∃ (nn : Fin (Formalism.L2.Col.cOf K.c.Rk j) → ℤ) (z : Fin (K.c.Rk.N j) → K.X.E),
        (∀ i, -(j : ℤ) ≤ nn i ∧ nn i ≤ 0) ∧
        (fun l : Fin (K.c.Rk.N j + Formalism.L2.Col.cOf K.c.Rk j) => if h : l.1 < K.c.Rk.N j then z ⟨l.1, h⟩ else 0) ∈
          Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1 ∧
        (Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1).map
                  (((K.c.Li t).h j b v).toLinearMap.restrictScalars (𝓞 K.X.E)) =
          (Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1).map
            ((Matrix.toLin' (nfMat (K.c.Rk.N j) (Formalism.L2.Col.cOf K.c.Rk j) ((Formalism.L2.Col.qOf v.1 : ℕ) : K.X.E) nn z)).restrictScalars
              (𝓞 K.X.E))
  columnEvaluationOk : ∃ hM : (Formalism.L2.Col.rowGSD K.c.W (Formalism.L2.Col.rowTyG K.c.Ch K.c.Lv).inv).Ok, ∀ u : D.what₂.Word,
    ∃ ι : (D.mem u).P.Mt ≃ₗ[ℂ] (Fin ((Formalism.L2.Col.rowGSD K.c.W (Formalism.L2.Col.rowTyG K.c.Ch K.c.Lv).inv).hDim hM) → ℂ),
      (∀ (t : P.A3.fam3.base3.Tup) (ht : P.I.tup t = D.what₂.mu0)
        (hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL) = ∅)
        (y : Fin (rDim D P.A3.A P.Ps P.ψs t) → D.what₂.LL),
        ∃ (F' : (Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).EqFun)
          (hm : F'.1 ∈ (Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Lv).EqFun),
          HEq ((Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).res
              (Formalism.L2.Col.mtildeKOk K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.hX) F')
            ((P.A3.A.fam.R t).S.basis.equivFun.symm
              (((P.A3.A.fam.R t).S.cutE (P.A3.A.fam.R t).r (lvlIdem (P.A3.A.fam.lvl P.Ps P.ψs).P
                (P.A3.A.fam.lvl P.Ps P.ψs).ψ)).mulVec y)) ∧
          ι ((D.eMt u).symm (ht ▸ P.I.jA t y)) =
            Formalism.L2.Col.zOfRow K.c.W K.c.Ch K.c.sel (K.c.mu t) hQ K.c.Lv K.c.Am.σ₀ hM ⟨F'.1, hm⟩) ∧
      ∀ (t : P.A3.fam3.base3.Tup) (ht : P.I.tup t = D.what₂.mu0)
        (hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL) = ∅)
        (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
        ∃ hm : ((K.c.ev P.Zs t F : Formalism.L2.Col.V0X K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Xg K.c.Lv) :
            (Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).EqFun).1 ∈
            (Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Lv).EqFun,
          ι ((D.eMt u).symm (ht ▸ P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))) =
            Formalism.L2.Col.zOfRow K.c.W K.c.Ch K.c.sel (K.c.mu t) hQ K.c.Lv K.c.Am.σ₀ hM ⟨_, hm⟩
end Formalism.L2.DIV
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtOfBuilt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.CoefDuty.ExtBuilt
theorem extOf_built_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ big₀ L₀, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → ∃ big₁, ∀ L₁, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ i₁, ∃ i₀, ExtOf L₀ L₁ i₀ i₁ := by
  intro hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ L₀ hB₀
  obtain ⟨big₁, hR⟩ := _root_.GlobalTheory.T.side_eigen_level_alt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ L₀ hB₀
  refine ⟨big₁, fun L₁ hB₁ i₁ => ?_⟩
  obtain ⟨i₀, hw, hj, e, he⟩ := _root_.GlobalTheory.T.side_eigen_weight_alt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ big₁ L₀ L₁ hB₀ hB₁ i₁
  obtain ⟨φ, hφ, hφa⟩ := hR L₁ hB₁ i₀ i₁ hw
  have hZ := _root_.GlobalTheory.T.side_eigen_conductor_alt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ big₁ L₀ L₁ hB₀ hB₁ i₀ i₁ hw hj e he
  have hchi := _root_.GlobalTheory.T.side_eigen_character_alt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hst hex hsp hCh big₀ big₁ L₀ L₁ hB₀ hB₁ i₀ i₁ hw hj φ hφ hφa
  have hl : L₀.lay.fixZ.nd.l i₀ = L₁.lay.fixZ.nd.l i₁ := by
    rw [← L₀.lay.fixZ.nd.w_l, ← L₁.lay.fixZ.nd.w_l, hw]
  have hQ : L₀.lay.fixZ.nd.Q i₀ = L₁.lay.fixZ.nd.Q i₁ := by
    obtain ⟨Sp₀, -, -⟩ := hB₀
    obtain ⟨Sp₁, -, -⟩ := hB₁
    have h0 := Sp₀.Q_eq _ _ i₀ ((L₀.X.locs_mem _ _ i₀).2 ⟨rfl, rfl⟩)
    have h1 := Sp₁.Q_eq _ _ i₁ ((L₁.X.locs_mem _ _ i₁).2 ⟨rfl, rfl⟩)
    rw [Sp₀.Qc_eq] at h0
    rw [Sp₁.Qc_eq] at h1
    exact h0.trans ((congrArg C.Q hw).trans h1.symm)
  have hS : ∀ v, v ∈ L₀.lay.fixZ.nd.S i₀ ↔ v ∈ L₁.lay.fixZ.nd.S i₁ := by
    intro v
    rw [L₀.lay.fixZ.nd.S_def, L₁.lay.fixZ.nd.S_def, hl]
  have hout : ∀ v, SplitOut L₁.lay.fixZ.nd i₁ v ↔ SplitOut L₀.lay.fixZ.nd i₀ v := by
    intro v
    unfold SplitOut
    rw [hl, hQ, hS v]
  have hinj : Function.Injective (iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁) := by
    unfold iotaO
    exact (RingEquiv.injective _).comp ((RingHom.injective _).comp (IsFractionRing.injective _ _))
  have hcyc : ∀ (l l' : ℕ) (_ : l = l') [Fact l.Prime] [Fact l'.Prime] (σ : GE L₁.lay.fixZ.nd),
      HEq (cycZ (F := D.host.E) (Ω := L₀.lay.fixZ.nd.Om) l σ) (cycZ (F := D.host.E) (Ω := L₁.lay.fixZ.nd.Om) l' σ) := by
    intro l l' h _ _ σ
    subst h
    rfl
  refine ⟨i₀, hw, ⟨LocExt.mk hl φ hφ hφa e hout ?_ hZ (MulEquiv.refl _) continuous_id continuous_id
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun σ => hcyc _ _ hl σ) hchi⟩⟩
  intro v k x hv hk1 hk2
  apply hinj
  rw [hφ]
  exact he v k x hv hk1 hk2
end GlobalTheory.CoefDuty.ExtBuilt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowerMapTieTw
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
namespace GlobalTheory.Mem.Col2.LowerTie
theorem lowerMap_tieTw_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (T : _root_.Formalism.L2.TiedDataSKAlt ex) (he : ex.tw = I.tw l l0 Z), I.StdC l Z T.cols → I.StdTw l Z l0 (he ▸ T.tw) → ∀ u a (ha : a ≠ (I.rec7 l Z).what₂.mu0) (h1 : 1 ≤ B.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u a ha h1 :=
  fun I hO hP l Z l0 _ _ _ _ _ _ _ _ T he hC hTw u a ha h1 => lowerMap_tw_gen I hO hP l Z l0 T.tw he hC hTw u a ha h1
end GlobalTheory.Mem.Col2.LowerTie
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NAllCWithLoc
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.HeightCounting.FitAll
theorem nAllC_withLoc_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), _root_.GlobalTheory.HeightCounting.LpCmpAlt hL → _root_.GlobalTheory.HeightCounting.CgCmpAlt hL → ∀ (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (fr : OmFrame b.D), fr.jE = b.jE → (PhtOn b.A.wd fr fun _ _ _ _ => True) → Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → lowPr b.D ⊆ b.low → ∃ a : _root_.GlobalTheory.HeightCounting.NAllCAlt (withLoc b.L) (chL b.L b.C), (⟨a.cf, a.tp⟩ : Σ c : CharFrame (withLoc b.L), TupTied (withLoc b.L) c (chL b.L b.C)) = ⟨cfL b.L b.cf, tpL b.L b.tp⟩ ∧ a.gal.fr.jE = b.jE ∧ a.gal.mt = mtL b.L b.M ∧ ExpRel b.L b.Bs.exp a.exp ∧ Nonempty (NCharTied (withLoc b.L) (cfL b.L b.cf) (chL b.L b.C) (tpL b.L b.tp)) ∧ NGalChrTied (withLoc b.L) (cfL b.L b.cf) (chL b.L b.C) (tpL b.L b.tp) ∧ ∀ F : RowFrame (withLoc b.L), F.rep = b.rep → _root_.Formalism.L2.RowLocTiedAlt (withLoc b.L) a.gal.lp F := by
  intro hL hLp hCg D' b fr hfr hpht hE hCh hlow
  obtain ⟨g, hgj, hgm, hgt, ⟨dat⟩, ⟨cov⟩, hrow⟩ :=
    _root_.GlobalTheory.FitGal.galTied_withLoc_alt hL hLp D' b fr hfr hpht hE.star hE.int hE.split hCh
  obtain ⟨⟨nt⟩, ⟨lt⟩⟩ := _root_.GlobalTheory.HeightCounting.nTied_locTied_of_built_alt hL hCg D' b
  obtain ⟨TO⟩ := _root_.GlobalTheory.HeightCounting.typesOpen_withLoc_alt b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch b.mt
    hE.star hE.int hE.split hCh b.big b.L b.Sp b.Au b.ss
  have rho : NR.NRhoTied (withLoc b.L) := _root_.GlobalTheory.HeightCounting.nRhoTied_withLoc_alt hL D' b hE.star hE.int hE.split hCh TO
  obtain ⟨Tw, hX⟩ := _root_.GlobalTheory.T.exists_twOpen_expRel_of_chebSplit hL D' b hE hCh
  have ty : NormalizedTypesCompatibility (withLoc b.L) b.jE :=
    { eM := TO.par.eM, eM_K := TO.par.eM_K, tA := TO.grp.tA, tκ := TO.grp.tκ, teichC_def := TO.grp.teichC_def,
      iota_loc := fun i => ⟨TO.plB _, TO.plκ _, TO.plB_loc i, TO.plB_iota i⟩,
      ζ := TO.grp.ζ, ζ_gen := TO.grp.ζ_gen, O := TO.grp.O, eSer_def := TO.grp.eSer_def, kv := TO.grp.kv,
      tg_tame := TO.grp.tg_tame, O_equiv := TO.grp.O_equiv, O_tw := TO.grp.O_tw, eP := TO.par.eP,
      locPar_def := TO.par.locPar_def }
  let F0 : TwFrame (withLoc b.L) := ⟨Tw.twF.K0, Tw.twF.eO0, Tw.twF.j0, Tw.twF.Lw, Tw.twF.eO, Tw.twF.eOk, Tw.twF.iCq, Tw.twF.S0x⟩
  have hlow' : lowPr (withLoc b.L) ⊆ b.low := hlow
  have tw : NTwTied (withLoc b.L) F0 := by
    have T := Tw.tw
    have hN : Ideal.absNorm (withLoc b.L).host.ccK ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (withLoc b.L).host.ccK_ne_bot
    have hd : (NumberField.discr (withLoc b.L).host.E).natAbs ≠ 0 :=
      Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero (withLoc b.L).host.E)
    exact ⟨T.pl_emb, T.ringSpec_baseIntegersEquiv_algebraMap, T.ringSpec_baseEmbedding_compatible, T.eO_alg, T.eOk_alg, T.mu_g, T.hk_split, T.ringSpec_excludedPlaces_eq, T.concreteTwistFrame_extraExcludedPlaces_conj, T.B_range,
      T.sig_inj, T.qs_pos,
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (hlow' (by simp [lowPr, Nat.mem_primeFactors, hp, h, hN])),
      fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (hlow' (by simp [lowPr])), fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (hlow' (by simp [lowPr])),
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (hlow' (by simp [lowPr, Nat.mem_primeFactors, hp, h, hd]))⟩
  refine ⟨
    { gal := g, n := (b.eq ▸ nt), loc := (b.eq ▸ lt), data := dat, cover := (hgm ▸ cov), chiD := Tw.chiD, chi := Tw.chi,
      rho := rho, types := (hgj.symm ▸ ty), twF := F0, tw := tw, nct := Tw.ch.nct, exp := Tw.exp, choice := Tw.ch.choice,
      eMt_level := by rw [hgm]; exact Tw.ch.eMt_level,
      cf := cfL b.L b.cf, tp := tpL b.L b.tp, tupLink := hgt,
      eta_eq := Tw.eta_eq, ringSpec_normalisedCharacter_eq := Tw.ringSpec_normalisedCharacter_eq, del_eq := Tw.del_eq, psi_eq := Tw.psi_eq,
      plB := TO.plB, plκ := TO.plκ, plB_loc := TO.plB_loc, plB_iota := TO.plB_iota,
      etaT_link := Tw.etaT_link, muC_link := Tw.muC_link, iCq_embO := Tw.iCq_embO, embO_star := Tw.embO_star },
    rfl, hgj, hgm, hX, ⟨Tw.chrN⟩, Tw.chrGal, hrow⟩
end GlobalTheory.HeightCounting.FitAll
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
namespace Formalism.L2.Rows
open Formalism.L2.DIV Formalism.L2.Indef
section Joint
variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 I0 Ty T : Type}
  (A3 : FamIn3 D.what₂.LL Gp Pl0 I0 Ty T D.R.m)
end Joint
section Bundle
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
variable {ex : Extra D L hT Gi Gl Kc Y cX}
open Classical in
structure RowSideDeterminedAlt (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) : Prop where
  lowerMap : ∀ u, LowerMapTieS (T.cols.forms u)
  lowerMapTw : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (_hw : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u μ hμ h1
  buDef : Formalism.BasicNotions.Rows.BuDefQ D.what₂
  ambS : ∃ JA : AmbIds D P.A3.A (Formalism.BasicNotions.RowSide.sharp D) ex.amb P.Ps P.ψs P.I.tup,
    AmbTie D P.A3.A (Formalism.BasicNotions.RowSide.sharp D) ex.amb P.Ps P.ψs P.I.tup P.I.jA JA
  faces : ∃ (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs, SPer (Dcf Zs)),
    Dcf P.Zs = P.Dc ∧ HEq (Spf P.Zs) P.Sp
  gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
    ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam
end Bundle
end Formalism.L2.Rows
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsRowPinMin
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
structure RowPinMinAlt (T : _root_.Formalism.L2.TiedDataSKAlt ex) : Prop where
  lowerMap : ∀ u, LowerMapTieS (T.cols.forms u)
  lowerMapTw : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (_hw : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u μ hμ h1
  buDef : Formalism.BasicNotions.Rows.BuDefQ D.what₂
end Formalism.L2.Rows
end
end
end

